structure BTL = struct
  
  open LinearLogic (* for predicate language *)
  open Util

  (* Behavior Tree expressions *)
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

  (* Values *)
  datatype outcome = Cont of btl | Fail | Success

  (* Rerun-from-root semantics *)
  (*
  fun eval (expr : btl) (state : state) (spec : spec)
    : (state * outcome) =
    case expr of
         Skip => (state, Success, "SUCCESS: Done")
       | Seq nil => (state, Success, "SUCCESS: Out of steps") 
       | Seq
       | Sel 
       | Cond
       | Just
       (*
       | Repeat
       | Par
      *)
  *)

  (* Small step semantics for the parallel case *)
  (* step E D S = (D', E', message)
  *   where E is a BTL expression, D is a state, S is a spec,
  *   D' is the next state, E' is the next expression,
  *   and message is a report of what happened.
  * *)
  fun step (expr : btl) (state : state) (spec : spec)
    : (state * outcome * string) =
    case expr of
         Skip => (state, Success, "SUCCESS: Done")
       | Seq nil => (state, Success, "SUCCESS: Out of steps") (* Seq nil = Skip *)
       | Sel nil => (state, Fail, "FAILURE: Out of options")
       | Seq (B::Bs) =>
           let
             val (state', outcome, message) = step B state spec
           in
             case outcome of
                  Success => (state', Cont (Seq Bs), message)
                | Fail => (state', Fail, message)
                | Cont B' => (state', Cont (Seq (B'::Bs)), message)
           end
       | Sel (B::Bs) =>
           let
             val (state', outcome, message) = step B state spec
           in
             case outcome of
                  Success => (state', Success, message)
                | Fail => (state', Cont (Sel Bs), message)
                | Cont B' => (state', Cont (Sel (B'::Bs)), message)
           end
       | Cond (C, B) =>
            if (holds_for state C) then
              (state, Cont B, "Condition succeeded")
            else (state, Fail, "Condition failed")
       | Just action =>
            let
              val (stateOpt, message) = try_doing action state spec
            in
              case stateOpt of
                   NONE => (state, Fail, message)
                 | SOME state' => (state', Success, message)
            end
       (* Repeat = repeat until success *)
       | Repeat B =>
           let
             val (state', outcome, message) = step B state spec
           in
             case outcome of
                  Cont B' => (state', Cont (Sel [B', Repeat B]), message)
                (* on Failure, repeat B again *)
                | Fail => (state', Fail, message) 
                | Success => (state', Success, message)
           end
       | Par Bs =>
           (* Choose a random process to evolve *)
           (* Alternative: generate list of all possible evolutions *)
           case Bs of
                [] => (state, Success, "SUCCESS: Out of behaviors")
              | Bs =>
           let
             val (B, Bs') = separateRandom Bs
             val (state', outcome, message) = step B state spec
           in
             case outcome of
                  Cont B' => (state', Cont (Par (B'::Bs')), message)
                | _ => (state', Cont (Par Bs'), message)
           end


  (* Apply step as many times as possible; 
  * return trace : (state * outcome * message) * list *)
  fun step_star expr state spec trace =
  let
    val next = step expr state spec
    val trace' = next::trace
    val (state', outcome, message) = next
  in
    case outcome of
         Success => rev trace'
       | Fail => rev trace'
       | Cont expr' => step_star expr' state' spec trace'
  end

  fun step_star_simple expr state spec =
  let
    val trace = step_star expr state spec []
    val msgs_only = map (fn (x,y,z) => z) trace
  in
    msgs_only
  end

  fun foldRandom (f : 'a -> 'b -> 'b) (base : 'b) (l : 'a list)
    : 'b
    =
    case l of
         [] => base : 'b
       | l =>
           let
             val (x:'a, xs:'a list) = separateRandom l
             val acc = foldRandom f base xs
           in
             f x acc : 'b
           end

  (* Return a new state on success; NONE on failure
  * as well as a trace of actions (string list)
  * *)
  fun runTrace (expr : btl) (state : state) (spec: spec) (trace : string list)
    : (state option) * (string list) =
    case expr of
        Skip => (SOME state, (*("SUCCESS: skip")::*)trace)
      | Repeat B =>
          let
            val (stateOpt, trace) = runTrace B state spec trace
          in
            case stateOpt of
                 SOME state' => runTrace (Repeat B) state' spec trace
               | NONE => (NONE, (*"End of repeat"::*)trace)
          end
      | Seq nil => (SOME state, (*("SUCCESS: end of seq")::*)trace)
      | Seq (B::Bs) =>
          let
            val (stateOpt, trace) = runTrace B state spec trace
          in
            case stateOpt of
                 SOME state' => 
                    runTrace (Seq Bs) state' spec trace
               | NONE => (NONE, (*"FAILURE: sequence"::*)trace)
          end
      | Sel nil => (NONE, (*"FAILURE: end of sel"::*)trace)
      | Sel (B::Bs) =>
          let
            val (stateOpt, trace) = runTrace B state spec trace
          in
            case stateOpt of
                 NONE => 
                    runTrace (Sel Bs) state spec trace
               | SOME state' => (SOME state', (*"SUCCESS: selector"::*)trace)
          end
      | Cond (C, B) =>
          if (holds_for state C) then 
            runTrace B state spec ((*"condition satisfied"::*)trace)
          else (NONE, (*"condition failed"::*)trace)
      | Just action => 
          let
            val (state', result) = try_doing action state spec
          in
            (* only include successful actions in trace *)
            case String.substring (result, 0, 7) of
                 "SUCCESS" => (state', result::trace)
               | _ => (state', trace)
          end
      | Par Bs =>
          let
            fun f (e:btl) (s:state, t:string list) =
            let
              val (stateOpt, result) = runTrace e s spec trace
            in
              case stateOpt of
                   NONE => (s, result@t)
                 | SOME s' => (s', result@t)
            end
            val (state', trace) = foldRandom f (state, []) Bs
          in
            (SOME state', trace)
          end

  (* One run through the tree *)
  fun run (e : btl) (state : state) (spec : spec) : (string list) * state = 
    let
      val (stateOpt, trace) = runTrace e state spec []
      val t = rev trace
    in
      case stateOpt of
           NONE => (t, state)
         | SOME state' => (t, state')
    end

  fun run_repeat (e : btl) (state : state) (spec : spec) (n : int) 
    : (string list) * state =
    if n <= 0 then ([], state)
    else
    let
      val (trace, state') = run e state spec
      val (rest, state'') = run_repeat e state' spec (n-1)
    in
      (trace@rest, state'')
    end

end
