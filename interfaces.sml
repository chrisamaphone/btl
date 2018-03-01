structure Interfaces =
struct
  
  open LinearLogic


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

  (* resourceMaches have need => 
  *   { unused : (var * pos) list, 
  *     sat    : pos list, 
  *     unsat  : pos list
  *   } 
  *
  * *)
  fun resourceMatches have need =
    match_lists have need satisfies [] []
    : {unused : (var * pos) list, sat : pos list, unsat : pos list}

  (* posMatches (have : (var * pos) list) (need : pos) =>
  *   { unused : (var * pos) list, 
  *     sat    : pos list, 
  *     unsat  : pos list
  *   } 
  * *)
  fun posMatches (have : (var * pos) list) (need : pos) =
    case need of
         Tensor Ps => resourceMatches have Ps
       | _ => resourceMatches have [need]

  val test_resources = 
      [(1, Atom "foo"), (2, Atom "bar"), (3, Atom "foo"), (4, Atom "baz")]
  val test_needs = ["foo", "bar", "bar", "quux"]


  val test_neg = 
    NTens (tensorize ["a", "b"], 
          NLolli (tensorize ["c", "d"], NPos (tensorize ["a", "d"])))

  val test_ctx = generate_state ["a", "c"]

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
          (* No immediate holes to plug, but nested expr might have some *)
           let
             val (unused, N') = attachHavesToNeeds resources N
           in
             (unused, NTens (P, N'))
           end
       | NPlus (P, N) =>
           let
             val (unused, N') = attachHavesToNeeds resources N
           in
             (unused, NTens (P, N'))
           end
       | NLolli (P, N) => (* Some immediate holes might be pluggable *)
           let
             val {unused, sat, unsat : pos list} = posMatches resources P
             val (unused', N') = attachHavesToNeeds unused N
           in
             (unused', NLolli (Tensor unsat, N'))
           end

  (* returns a proof term in addition to the above *)
  (*  XXX - Last case is complex
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
  *)

  (* The above but w/o proofs *)
  (* sequence an op of type S1 -o S2 with one of type N *)
  fun seq (S1 : pos) (S2 : pos) (N : neg)
    : neg =
    case N of
         NPos S => NLolli (S1, NTens (S2, N))
       | NTens (S3 : pos, N : neg) =>
              NLolli (S1, NTens (S2, NTens (S3, N)))
       | NPlus (S3 : pos, N : neg) =>
              NLolli (S1, NTens (S2, NPlus (S3, N)))
       | NLolli (S3 : pos, N : neg) =>
           let
             val resources = generate_pattern S2
             val {unused, sat, unsat : pos list} = posMatches resources S3
             val unused_props : (pos list) = map (fn (x,A) => A) unused
           in
             NLolli (S1,
                NTens (Tensor unused_props, NLolli (Tensor unsat, N)))
           end

  fun sel (N1 : neg) (N2 : neg) : neg =
    case (N1, N2) of
         (NPos P1, NPos P2) => NPos (OPlus [P1, P2])
       | (NPos P1, NTens (P2, N)) => NPlus (P1, NTens (P2, N))

  open BTL


  fun ruleSpecToNeg rulename args sg =
    (* args ignored for now *)
    case lookupRule rulename sg of
         NONE => NONE
       | SOME {pre, post} => SOME (NLolli (pre, NPos post))

  val NOne = NPos (Tensor []) (* neg for type 1 *)

  fun type_of (prog : btl) (sg : spec) : neg option =
    case prog of
         Skip => SOME NOne
       | Just (rulename, args) => ruleSpecToNeg rulename args sg
       | Seq [] => SOME NOne
       | Seq [Just (rulename, args)] => ruleSpecToNeg rulename args sg
       | Seq ((Just (rulename, args))::rest) =>
           (case (lookupRule rulename sg, type_of (Seq rest) sg) of
                 (NONE, _) => NONE
               | (_, NONE) => NONE
               | (SOME {pre, post}, SOME N) => SOME (seq pre post N))
      (* Missing: Seq (E1, E2) for general E1  *)
       | Sel [] => SOME (NPos (OPlus []))
       | Sel [Just (rulename, args)] => ruleSpecToNeg rulename args sg
       | Sel (E1::rest) =>
          (case (type_of E1 sg, type_of (Sel rest) sg) of
                (NONE, _) => NONE
              | (_, NONE) => NONE
              | (SOME N1, SOME N2) => raise unimpl (* XXX *)
          )

  (* Tests *)

  val test1_prog = Just (Examples.walk_to_door)
  val spec_doors = Examples.door_bot_spec
  val test1_pass =
  SOME (NLolli (Atom "at_L", NPos (Atom "at_door"))) 
  = (type_of test1_prog spec_doors)

  val test2_prog = Just (Examples.unlock_door)
  val test2_pass = 
    SOME 
    (NLolli (Tensor [Atom "at_door", Atom "door_locked", Atom "have_key"], 
            NPos (Tensor [Atom "at_door", Atom "door_unlocked"]))) 
  = (type_of test2_prog spec_doors)

  val test3_prog = Seq [Just Examples.unlock_door, Just Examples.open_door]
  val answer = 
    NLolli (Tensor [Atom "at_door", Atom "door_locked", Atom "have_key"],
              NPos (Tensor [Atom "at_door", Atom "door_open"]))       
  (* XXX - test once sequence interfaces are implemented. *)

  (* Example with selector - for testing once \oplus is available *)
  val test4_prog = Sel [Just Examples.open_door, Just Examples.smash_door]
  (* Answer is roughly: ((at_door * door_unlocked) + (at_door * door_locked))
  *                   -o ((at_door * door_open) + (at_door * door_open)) *)



end
