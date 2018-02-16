structure LinearLogic =
struct
  (* Linear logic propositions/types *)
  type term = string
  type predicate = string
  type atom = string (* Eventually: predicate * (term list) *)
  type pos = atom list (* Arbitrary tensorings of atoms *)
  datatype neg = NPos of pos | NLolli of pos * neg | NTens of pos * neg

  type rulename = string

  (* Linear logic proof terms *)
  type var = int
  type pattern = var list
  datatype resource = 
      Var of var 
    | App of rulename * (term list) * (resource list)
  (* datatype pos_proof =
    Unit | Res of resource | Pair of pos_proof * pos_proof 
  *)
  type pos_proof = resource list
  datatype neg_proof = 
    Pos of pos_proof
  | Lam of pattern * neg_proof
  | NPair of pos_proof * neg_proof
  | Let of pattern * resource * neg_proof

  (* Signatures and contexts *)
  type action_spec = 
    { name: rulename, 
      args: string list, 
      antecedent: pos,
      consequent: pos}
  type spec = action_spec list
  type state = (var * atom) list


  exception unimpl

  fun lookupRule (rulename : string) (spec : spec) =
    case spec of
         nil => NONE
       | ({name,args,antecedent,consequent}::spec) =>
          if not (name = rulename) then lookupRule rulename spec
          else
            SOME {pre=antecedent : atom list, post=consequent : atom list}


  val gensym = ref 0

  fun fresh() =
  let
    val ans = !gensym
    val () = gensym := ans + 1
  in
    ans
  end

  fun generate_pattern (P : pos) =
    case P of
         [] => []
       | (x::xs) => (fresh(), x)::(generate_pattern xs)
    (*
    case P of 
         One => []
       | Tensor (S1, S2) => (generate_pattern S1)@(generate_pattern S2)
       | At _ => [fresh()]
    *)

(* Not needed if pos-es are lists
  fun posToList (S : pos) : atom list =
    case S of
         One => []
       | Tensor(S1, S2) => (posToList S1)@(posToList S2)
       | At a => [a]

  fun posProofToList (X : pos_proof) : resource list =
    case X of
         Unit => []
       | Pair (X1, X2) => (posProofToList X1)@(posProofToList X2)
       | Res r => [r]

  fun resListToProof rs = 
    case rs of
         [] => Unit
       | [r] => Res r
       | (r::rs) => Pair (Res r, resListToProof rs)
*)
       
  fun rember' x ys f prefix_cont =
    case ys of
         (y::ys) => if f x y then SOME (prefix_cont ys)
                    else rember' x ys f (fn l => (prefix_cont (y::l)))
       | [] => NONE

  (* rember : 'a -> 'b list -> ('a -> 'b -> bool) -> ('b list -> 'b list) 
  *     -> 'b list option
  * rember x ys f => NONE if x isn't in ys
  *               => SOME ys' where ys' = ys - x
  *)
  fun rember x ys f = rember' x ys f (fn l => l)

  fun equal x y = x = y
  fun match_snd x (y1, y2) = x = y2

  fun split (needs : atom list) (haves : (var * atom) list) =
    case needs of
         nil => SOME haves
       | (need::needs) => 
           (case rember need haves match_snd of
                 NONE => NONE (* a need could not be met *)
               | SOME haves' => split needs haves')



  fun zip (xs, ys) =
    case (xs, ys) of
         (x::xs, y::ys) => (x,y)::zip(xs, ys)
       | ([], []) => []
       
  
  (* 
  *  match_lists xs ys f -- use xs to plug ys; return used, unused, and matched
  *
  *  xs : 'a list           --- haves
  *  ys : 'b list           --- needs
  *  f  : 'b -> 'a -> bool  --- determine whether need is satisfied by a have
  *  matched : 'b list      --- accumulator for matched needs so far
  *  unmatched : 'b list    --- accumulator for unmatched needs so far
  *  ===>
  *     {unused : 'a list, matched : 'b list, unmatched : 'b list}
  *
  * where 
  *   [unused] is the subset of xs not used to meet a need in ys,
  *   [matched] is the subset of ys satisfied by an x, and
  *   [unmatched] is the subset of ys not satisfied by an x.
  *)
  fun match_lists xs ys f matched unmatched =
    case ys of 
         []       => {unused = xs, sat = matched, unsat = unmatched}
       | (y::ys)  =>
           (case rember y xs f of
                SOME xs' => match_lists xs' ys f (y::matched) unmatched
               | NONE => match_lists xs ys f matched (y::unmatched))

  (* resourceMaches have need => {unused : , sat : , unsat : } *)
  fun resourceMatches have need =
    match_lists have need match_snd [] []

  val test_resources = [(1, "foo"), (2, "bar"), (3, "foo"), (4, "baz")]
  val test_needs = ["foo", "bar", "bar", "quux"]


  val test_neg = 
    NTens (["a", "b"], 
          NLolli (["c", "d"], NPos ["a", "d"]))

  val test_ctx = generate_pattern ["a", "c"]

  (* returns list of haves and a new neg 
  *
  *   attachHavesToNeeds resources N =>
  *       (resources', N')
  *   where resources' is all of the resources that did not
  *     match up to an input in N,
  *   and N' is the new interface with some of N's holes plugged by input
  *     resources.
  *
  *   Note: this is the "proof-irrelevant" version.
  * *)
  fun attachHavesToNeeds (resources) (N : neg) =
    case N of
         NPos P => (resources, NPos P) (* No holes to plug *)
       | NTens (P, N) => 
          (* No immediate holes to plug, but nester expr might have some *)
           let
             val (unused, N') = attachHavesToNeeds resources N
           in
             (unused, NTens (P, N'))
           end
       | NLolli (P, N) => (* Some immediate holes might be pluggable *)
           let
             val {unused, sat, unsat} = resourceMatches resources P
             val (unused', N') = attachHavesToNeeds unused N
           in
             (unused', NLolli (unsat, N'))
           end

  (* returns a proof term in addition to the above *)
  (* Last case is complex
  fun combineProofs (resources) (Pf : neg_proof) (N : neg) =
    case (Pf, N) of
         (Pos pf, NPos P) => (resources, Pos pf, NPos P)
       | (NPair(posPf, negPf), NTens (P, N)) => 
           let
             val (unused, negPf', N') = combineProofs resources negPf N
           in
             (unused, NPair(posPf, negPf'), NTens (P, N'))
           end
       | (Lam (pat, negProof), NLolli (P, N)) =>
           let
             val {unused, sat, unsat} = resourceMatches resources P
             val (unused', negPf', N') = combineProofs unused negProof N
           in
             (unused', NLolli (unsat, N'))
           end
  *)


  (*

  (* sequence an op of type S1 -o S2 with a term P : N *)
  fun seq (oper : resource) (S1 : pos) (S2 : pos) (P : neg_proof) (N : neg)
    : neg_proof * neg =
    case (P, N) of
         (P, NPos S) => 
          let 
            val pat = generate_pattern S1
          in 
            (Lam (pat, NPair (Res oper, P)), NLolli (S1, NTens (S2, N))) 
          end
       | (NPair(P1, P2), NTens (S3, N)) =>
          let
            val pat = generate_pattern S1
          in
            (Lam (pat, NPair (Res oper, NPair(P1, P2))),
              NLolli (S1, NTens (S2, NTens (S3, N))))
          end
      (* Q: assume all lolli-typed tms are eta-long? *)
       | (Lam (pat3, P), NLolli (S3, N)) =>
          raise unimpl (*
           let
             val pattern1 = generate_pattern S1
             val have_types = posToList S2
             val pattern2 = generate_pattern S2
             val have_resources = zip pattern2 have_types
             val {unused, sat, unsat} = resourceMatches have_resources S3
             val unsatType = atomListToPos unsat
             val pattern3 = generate_pattern unsat
           in
             (Lam (pattern1, Let (pattern2, oper, 
                NPair (resListToProof unused, 
                  Lam (pattern3, *)

  fun compile (alpha : btl) =
    case alpha of
         _ => raise unimpl

  (* tests *)
  *)

end
