structure BTL = struct
  
  (* Linear logic-based interface types *)
  type term = string
  type predicate = string
  type atom = predicate * (term list)
  datatype pos = One | Tensor of pos * pos | At of atom
  datatype neg = NPos of pos | NLolli of pos * neg | NTens of pos * neg

  (* Behavior Tree expressions *)
  type rulename = string
  type btl_op = rulename * (term list)
  (* skip | op; btl | ?pos.btl *)
  datatype btl = Skip | Seq of btl_op * btl | Cond of pos * btl

  (* Linear logic proof terms *)
  type var = int
  type pattern = var list
  datatype resource = 
      Var of var 
    | App of rulename * (term list) * (resource list)
  datatype pos_proof =
    Unit | Res of resource | Pair of pos_proof * pos_proof 
  datatype neg_proof = 
    Pos of pos_proof
  | Lam of pattern * neg_proof
  | NPair of pos_proof * neg_proof
  | Let of pattern * resource * neg_proof

  type op_spec = 
    { name: rulename, 
      args: string list, 
      antecedent: pos,
      consequent: pos}
  type op_sig = op_spec list



  exception unimpl

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
         One => []
       | Tensor (S1, S2) => (generate_pattern S1)@(generate_pattern S2)
       | At _ => [fresh()]

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

  fun rember' x ys f prefix_cont =
    case ys of
         (y::ys) => if f x y then SOME (prefix_cont ys)
                    else rember' x ys f (fn l => (prefix_cont (y::l)))
       | [] => NONE

  fun rember x ys f = rember' x ys f (fn l => l)

  fun match_snd x (y1, y2) = x = y2

  fun zip (xs, ys) =
    case (xs, ys) of
         (x::xs, y::ys) => (x,y)::zip(xs, ys)
       | ([], []) => []
       
  
  fun match_lists xs ys f matched unmatched =
    case ys of 
         []       => {unused = xs, sat = matched, unsat = unmatched}
       | (y::ys)  =>
           (case rember y xs f of
                SOME xs' => match_lists xs' ys f (y::matched) unmatched
               | NONE => match_lists xs ys f matched (y::unmatched))

  fun resourceMatches have need =
    match_lists have need match_snd [] []

  val test_resources = [(1, "foo"), (2, "bar"), (3, "foo"), (4, "baz")]
  val test_needs = ["foo", "bar", "bar", "quux"]


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


end
