structure BTL = struct
  
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

  datatype outcome = Fail | Success | Cont of btl
  datatype action_outcome = FAIL | DONE of state | RUNNING of action * int * state

  fun eval (e : btl) (state : state) (spec : spec)
      : (state * outcome) =
      case e of
           Seq (e1::es) =>
            let
              val (state', outcome) = eval e1 state spec
            in
              case outcome of
                   Fail => (state', Fail) 
                 | Success => (state', Cont (Seq es)) 
                 | Cont e1' => (state', Cont e1')
            end
          | Seq [] => (state, Success)
          | Sel (e1::es) =>
              let
                val (state', outcome) = eval e1 state spec
              in
                case outcome of
                     Fail => eval (Sel es) state spec
                   | Success => (state', Success)
                   | Cont e1' => (state', Cont e1')
              end
          | Sel [] => (state, Fail)
          | Just action =>
              let
                val (stateOpt, msg) = try_doing action state spec
              in
                case stateOpt of
                     FAIL => (state, Fail)
                   | DONE state' => (state', Success)
                   | RUNNING (action', n, state') => 
                       case n of (* XXX decrement n? *)
                            0 => (state', Success)
                          | _ => (state', Cont (Just action'))
              end


  (* repeatedly eval e - XXX *)
  fun idk e state spec =
  let
    val (state', outcome) = eval e state spec
  in
    case outcome of
         Fail =>
       | Success =>
       | Cont e' => (* pass e to success continuation in rec call? *)


end
