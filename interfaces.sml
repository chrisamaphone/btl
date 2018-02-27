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
       | NTens (S3, N) =>
              NLolli (S1, NTens (S2, NTens (S3, N)))
       | NLolli (S3, N) =>
           let
             val resources = generate_pattern S2
             val {unused, sat, unsat} = resourceMatches resources S3
             val unused_props = map (fn (x,A) => A) unused
           in
             NLolli (S1,
                NTens (unused_props, NLolli (unsat, N)))
           end


  open BTL

  fun type_of (prog : btl) (sg : spec) : neg option =
    case prog of
         Just (rulename, args) => 
         (case lookupRule rulename sg of
               NONE => NONE
             | SOME {pre, post} => SOME (NLolli (pre, NPos post)))

  (* Tests *)

  val test1_prog = Just (Examples.walk_to_door)
  val spec_doors = Examples.door_bot_spec
  val SOME (NLolli (["at_L"],NPos ["at_door"])) 
  = type_of test1_prog spec_doors

  val test2_prog = Just (Examples.unlock_door)
  val SOME 
    (NLolli (["at_door","door_locked","have_key"], 
            NPos ["at_door","door_unlocked"])) 
  = type_of test2_prog spec_doors

  val test3_prog = Seq [Just Examples.unlock_door, Just Examples.open_door]
  val answer = 
    NLolli (["at_door", "door_locked", "have_key"],
              NPos ["at_door", "door_open"])            


end
