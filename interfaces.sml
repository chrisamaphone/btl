structure Interfaces =
struct
  
  open LinearLogic


  fun zip (xs, ys) =
    case (xs, ys) of
         (x::xs, y::ys) => (x,y)::zip(xs, ys)
       | ([], []) => []
       
  fun removeDupes (f : 'a*'a -> bool) (xs : 'a list) (seen : 'a list) =
    case xs of
         [] => []
       | (x::xs) =>
          if member x seen f then
            removeDupes f xs seen
          else
            x::(removeDupes f xs (x::seen))

  
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


  (* Really should rename "reduce"
  *
  * cut(S, N) --> N' 
  *   S, N |- N'
  *
  * The idea is N' is more "reduced" - resources in S
  *   might interact with resource requirements in N.
  *   
  * *)
  fun cut (SHave : pos) (N : neg) : neg = 
    case posToPosList SHave of
         [] => N
       | _ => (
    case N of
         NPos S => NPos (join SHave S)
       | NTens (S : pos, N : neg) =>
           NTens (join SHave S, N)
       (* | NPlus (N1 : neg, N2 : neg) =>
           NTens (SHave, NPlus (N1, N2))
           (* XXX - why not NPlus (cut SHave N1, cut SHave N2) ? *) *)
       | NWith (N1 : neg, N2 : neg) =>
           NWith (cut SHave N1, cut SHave N2)
       | NLolli (S : pos, N : neg) =>
           (* XXX - recursively cut SHave into N? *)
           let
             val resources = generate_pattern SHave
             val {unused, sat, unsat : pos list} = posMatches resources S
             val unused_props : (pos list) = map (fn (x,A) => A) unused
             val N' = (case unsat of 
                            [] => N
                          | [P] => NLolli (P, N)
                          | _ => NLolli (Tensor unsat, N))
           in
             case unused_props of
                  [] => N'
                | [P] => NTens (P, N')
                | _ => NTens (Tensor unused_props, N')
           end
    )

  fun seq (N1 : neg) (N2 : neg) : neg =
    case (N1, N2) of
         (NPos S, NLolli (S2, N)) => NTens (S, NLolli (S2, N))
       | (NPos S, NTens (S2, N2)) => NTens (join S S2, N2)
       | (NPos S, NPos S2) => NPos (join S S2)
       | (NPos S, NWith(N1, N2)) => NWith (seq (NPos S) N1, seq (NPos S) N2)
       | (NTens (S1, N1), N2) => NTens (S1, (seq N1 N2))
       | (NWith (N1, N2), N)  => NWith (seq N1 N, seq N2 N)
       | (NLolli (S1, N1), N2) => NLolli (S1, seq N1 N2)


  fun posEquiv (P1 : pos) (P2 : pos) : bool =
    (entails P1 P2) andalso (entails P2 P1)


  fun smallerOPlus (P1 : pos, P2 : pos) : pos =
      if posEquiv P1 P2 then P1
      else OPlus [P1, P2]

      (*
  fun smallerNPlus (N1 : neg, N2 : neg) =
    if N1 = N2 then N1 
    else 
      NPlus (N1, N2)
      *)

  (* compute a "smaller" type equiv to N1 + N2 *)
  (* XXX - broken for soundness
  fun sel (N1 : neg) (N2 : neg) : neg =
    case (N1, N2) of
         (NPos P1, NPos P2) => NPos (smallerOPlus (P1, P2))
       | (NPos P1, NPlus (N1, N2)) => smallerNPlus (sel (NPos P1) N1, sel (NPos P1) N2)
       | (_, NPos P2) => sel N2 N1
       | (NLolli (P1, N1), NLolli (P2, N2)) =>
            NLolli (smallerOPlus (P1, P2), sel N1 N2)
       | _ => smallerNPlus (N1, N2) 
  *)

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
       | Seq (E1::rest) =>
           (case (type_of E1 sg, type_of (Seq rest) sg) of
                 (NONE, _) => NONE
               | (_, NONE) => NONE
               | (SOME N1, SOME N2) => SOME (seq N1 N2))
       | Sel [] => SOME (NPos (OPlus []))
       | Sel [E1] => type_of E1 sg
       | Sel (E1::rest) =>
          (case (type_of E1 sg, type_of (Sel rest) sg) of
                (NONE, _) => NONE
              | (_, NONE) => NONE
              | (SOME N1, SOME N2) => SOME (NWith (N1, N2)) (* sel N1 N2 *)
          )
       | Cond (condition : pos, E : btl) =>
           (case type_of E sg of
                 NONE => NONE
               | SOME N => 
                   let
                     val N' =
                          NLolli (condition, cut condition N)
                       (* NLolli (condition, NTens (condition, N)) *)
                   in
                     SOME N'
                   end)

  (* Tests *)

  val test1_prog = Just (DoorsExample.walk_to_door)
  val spec_doors = DoorsExample.door_bot_spec
  val test1_pass =
  SOME (NLolli (Atom "at_L", NPos (Atom "at_door"))) 
  = (type_of test1_prog spec_doors)

  val test2_prog = Just (DoorsExample.unlock_door)
  val test2_pass = 
    SOME 
    (NLolli (Tensor [Atom "at_door", Atom "door_locked", Atom "have_key"], 
            NPos (Tensor [Atom "at_door", Atom "door_unlocked"]))) 
  = (type_of test2_prog spec_doors)

  val test3_prog = Seq [Just DoorsExample.unlock_door, Just DoorsExample.open_door]
  val answer = 
    NLolli (Tensor [Atom "at_door", Atom "door_locked", Atom "have_key"],
              NPos (Tensor [Atom "at_door", Atom "door_open"]))       
  (* XXX - test once sequence interfaces are implemented. *)

  (* Example with selector - for testing once \oplus is available *)
  val test4_prog = Sel [Just DoorsExample.open_door, Just DoorsExample.smash_door]
  (* Answer is roughly: ((at_door * door_unlocked) + (at_door * door_locked))
  *                   -o ((at_door * door_open) + (at_door * door_open)) *)


  (* Debug - Trying to get rid of dupes in oplus
  val (SOME topen) = type_of (Just DoorsExample.open_door) spec_doors
  val (SOME tsmash) = type_of (Just DoorsExample.smash_door) spec_doors
  val (NLolli (_, open_con)) = topen
  val (NLolli (_, smash_con)) = tsmash
  val (NPos open_pos) = open_con
  val (NPos smash_pos) = smash_con
  *)

  val test5_prog = Sel [test3_prog, Just DoorsExample.smash_door]

  val test6_prog = Sel [Just DoorsExample.open_door, test3_prog]

  val test7_prog = 
    Sel [Just DoorsExample.open_door, test3_prog, Just DoorsExample.smash_door]

  val test8_prog = DoorsExample.get_through_door
  
  fun test9 () = 
    type_of 
    InvestigateExample.testInvestigateSound
    InvestigateExample.sound_spec



end
