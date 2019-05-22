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
               | Cond of pos * btl | Just of btl_op * int | Skip
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

  datatype path = Down of path | Right of path | Stop

  val path_example = Down (Down (Right (Down Stop)))
  val path_ex2 = Right (Right (Right (Down Stop)))

  fun path_append p1 p2 =
    case (p1, p2) of
         (Stop, p2) => p2
       | (p1, Stop) => p1
       | (Down p1, p2) => Down (path_append p1 p2)
       | (Right p1, p2) => Right (path_append p1 p2)

  (* Returns SOME path to a node where f applies to the action pointed to by
  *   that path; else NONE *)
  (* XXX - need to consider case where seq above selector *)
  fun traverse (e : btl) (state : state) (f : btl_op -> bool) 
    : path option =
    case e of
         Just (action, n) =>
          if f action then SOME Stop else NONE
       | Seq (e1::es) =>
           let
             val pOpt = traverse e1 state f (* might need same as sel, or
             distinguish success from fail *)
           in
             case pOpt of
                  NONE => NONE
                | SOME p => SOME (Down p)
           end
       | Seq nil => NONE
       | Sel (e1::es) =>
           let
             val pOpt = traverse e1 state f
           in
             case pOpt of
                  NONE =>
                    (case traverse (Sel es) state f of
                          NONE => NONE
                        | SOME p => SOME (Right p))
                | SOME p => SOME (Down p)
           end
        | Sel [] => NONE
        | Cond (cond, e1) =>
            if holds_for state cond then
              let
                val pOpt = traverse e1 state f
              in
                case pOpt of
                     SOME p => SOME (Down p)
                   | NONE => NONE
              end
            else NONE

  val test_op = ("foo", [])
  val test_op2 = ("bar", [])
  val test_action = Just (test_op, 0)
  val test_action2 = Just (test_op2, 0)
  val test_cond = Atom ("p", [])
  val test_cond2 = Atom ("q", [])

  val test_tree : btl = 
    Seq [ Cond ( test_cond, Sel [Cond (test_cond2, test_action), test_action2] )
          , test_action2 ]

  val test_path = Down (Down (Right (Down Stop)))

  val test_state_succeed = generate_pattern test_cond
  val test_state_fail : state = []
  val test_state2 : state = generate_pattern test_cond2

  fun test_f (name, args) = name = "bar"

  (* test call: traverse test_tree test_state_succeed test_f *)

  fun follow_path (tree : btl) (p : path) : btl option =
    case (p, tree) of
         (Stop, e) => SOME e
       | (Down p, Sel (e1::es)) => follow_path e1 p
       | (Right p, Sel (e1::es)) => follow_path (Sel es) p 
       | (Down p, Seq (e1::es)) => follow_path e1 p
       | (Right p, Seq (e1::es)) => follow_path (Seq es) p
       | (Down p, Cond (c,e)) => follow_path e p
       | _ => NONE

  datatype outcome = Fail | Success | Cont of btl * path

  fun eval (e : btl) (state : state) (spec : spec) (f : path -> path)
      : (state * outcome) =
      case e of
           Just (action, n) =>
              let
                val (stateOpt, msg) = try_doing action state spec
              in
                case (n, stateOpt) of
                     (_, NONE) => (state, Fail)
                   | (0, SOME state') => (state', Success)
                   | (_, SOME state') => (state', Cont (Just (action, n-1), f Stop))
              end
          | Seq (e1::es) =>
            let
              val (state', outcome) = eval e1 state spec (fn p => Down (f p))
            in
              case outcome of
                   Fail => (state', Fail) 
                 | Success => (state', Cont (Seq es, f Stop)) 
                 | Cont (e1', p) => (state', Cont (e1', p))
            end
          | Seq [] => (state, Success)
          | Sel (e1::es) =>
              let
                val (state', outcome) = eval e1 state spec (fn p => Down (f p))
              in
                case outcome of
                     Fail => eval (Sel es) state spec (fn p => Right (f p))
                   | Success => (state', Success)
                   | Cont (e1', p) => (state', Cont (e1', p))
              end
          | Sel [] => (state, Fail)

  (* TODO
  * proof of reactivity + memory semantics *)


  (* repeatedly eval e - XXX *)
  (*
  fun repeat_eval e state spec (prev : path) =
  let
    val (state', outcome) = eval e state spec (fn x:path => x)
  in
    case outcome of
         Fail => repeat_eval e state' spec Stop
       | Success => repeat_eval e state' spec Stop
       | Cont (e', new : path) =>
           if prev = new then
             let
               val (state', outcome) = eval e' state' spec Stop
             in
               repeat_eval e state' spec 
             end
           else repeat_eval e state' spec new
           *)

end
