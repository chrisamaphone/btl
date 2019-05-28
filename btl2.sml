structure BTL2 = struct
  
  open LinearLogic (* for predicate language *)
  open Util

  (* Action expressions *)
  type rulename = string
  type btl_op = rulename * (term list)

  (* BTL expressions 
   *  e ::= e;e | e+e | ?pos.btl | op | skip | e* | e||e 
   *)

  datatype btl = Seq of btl list | Sel of btl list 
               | Cond of pos * btl | Just of btl_op | Skip
               | Repeat of btl | Par of btl list
               (* Repeat = repeat until success *)
               
  fun holds_for (state: state) (cond: pos) =
    entails (stateToPos state) cond

  fun commaSep (l : string list) =
    case l of
         [] => ""
       | [x] => x
       | (x::xs) => x ^ ", " ^ (commaSep xs)

  fun actionToString (rulename, args) =
    rulename ^ "(" ^ (commaSep args) ^ ")"


  (* try doing (action, args) state spec = (state', msg)
  *    where state' = SOME state' if the action transforms state into state';
  *          state' = NONE if the action's preconditions don't hold;
  *    and   msg  is a string indicating the success or failure of the
  *    action.
  *)
  fun try_doing (action : btl_op) (state : state) (spec : spec) 
    : (state option) * string =
    let
      val (rulename, args) = action
      val astring = actionToString action
    in
      case lookupRule rulename spec of
          NONE => (NONE, "no rule for action " ^ astring)
        | SOME f =>
            let
              val {antecedent=pre, consequent=post} = f args
            in
              case split (flatten [pre]) state of
                  NONE => (NONE, "FAILURE: action "^astring)
                | SOME state' => 
                    let
                      val state'' = state' @ (generate_pattern post)
                    in
                      (SOME state'', "SUCCESS: action "^astring)
                    end
            end
    end

  type trace = string list

  datatype status = Running | Succeeded | Failed 

  type path = status list

  (* pi is the last path run *)
  fun eval (alpha : btl) (state : state) (pi : path)
    : path =
    case (alpha, pi) of
         (* Sequences *)
         (_, []) => eval alpha state [Running]
         (Seq [], Running::pi) => Succeeded::pi
       | (Seq (x::xs), Running::pi) =>
           let
             val status::newpath = eval x state pi
           in
             case status of
                  Failed => Failed::pi 
                  Running => Running::newpath
                | Succeeded => XXX (* XXX figure this ooout *)
           end
       | (Seq (x::xs), Succeeded::pi) =>
           let
             val (newpath, actionOpt) = eval (Seq xs) state pi
           in
             (Succeeded::newpath, actionOpt)
           end
       | (Seq (x::xs), Failed::pi) =>
           (Failed::pi, NONE)
          (* Selectors *)
       | (Sel [], Running::pi) => (Failed::pi, NONE)
       | (Sel (x::xs), []) =>
           let
             val () = print "Initiating sel node\n"
           in
             eval x state [Running]
           end
       | (Sel (x::xs), Running::pi) =>
           let 
             val () = print 
           eval x state pi
       | (Sel (x::xs), Succeeded::Running::pi) =>
           (Succeeded::pi, NONE)
       | (Sel (x::xs), Failed::pi) =>
           eval (Sel xs) state (Failed::pi)
       | (Cond (phi, alpha'), pi) =>
           if holds_for state phi then
             let
               val () = print "Cond node\n"
             in
               eval alpha' state (Succeeded::pi)
             end
           else
             (Failed::pi, NONE)
       | (Just btl_op, []) =>
           ([Running], SOME btl_op)
           (* other cases should be impossible? *)
       | _ => (pi, NONE)

  val test_op = ("foo", [])
  val test_op2 = ("bar", [])
  val test_action = Just test_op
  val test_action2 = Just test_op2
  val test_cond = Atom ("p", [])
  val test_cond2 = Atom ("q", [])

  val test_tree : btl = 
    Seq [ Cond ( test_cond, Sel [Cond (test_cond2, test_action), test_action2] )
          , test_action2 ]

  val test_state_succeed = generate_pattern test_cond
  val test_state_fail : state = []
  val test_state2 : state = generate_pattern test_cond2



  (* test call:
  *   eval test_tree test_state_succeed [] *)


  
end
