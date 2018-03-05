structure BTL = struct
  
  open LinearLogic (* for predicate language *)

  (* Behavior Tree expressions *)
  type rulename = string
  type btl_op = rulename * (term list)
  (* skip | op; btl | ?pos.btl *)
  datatype btl = Seq of btl list | Sel of btl list 
               | Cond of pos * btl | Just of btl_op | Skip
               | Repeat of btl
               
  fun holds_for (state: state) (cond: pos) =
    entails (stateToPos state) cond

  fun try_doing ((action, args) : btl_op) (state : state) (spec : spec) 
    : (state option) * string =
    case lookupRule action spec of
         NONE => (NONE, "no rule for action "^action)
       | SOME {pre : pos, post : pos} =>
           (case split (flatten [pre]) state of
                 NONE => (NONE, "FAILURE: action "^action)
               | SOME state' => 
                   let
                     val state'' = state' @ (generate_pattern post)
                   in
                     (SOME state'', "SUCCESS: action "^action)
                   end
            )

  type trace = string list


  (* Return a new state on success; NONE on failure
  * as well as a trace of actions (string list)
  * *)
  fun runTrace (expr : btl) (state : state) (spec: spec) trace =
    case expr of
        Skip => (SOME state, ("SUCCESS: skip")::trace)
      | Repeat B =>
          let
            val (stateOpt, trace) = runTrace B state spec trace
          in
            case stateOpt of
                 SOME state' => runTrace (Repeat B) state' spec trace
               | NONE => (NONE, "End of repeat"::trace)
          end
      | Seq nil => (SOME state, ("SUCCESS: end of seq")::trace)
      | Seq (B::Bs) =>
          let
            val (stateOpt, trace) = runTrace B state spec trace
          in
            case stateOpt of
                 SOME state' => 
                    runTrace (Seq Bs) state' spec trace
               | NONE => (NONE, "FAILURE: sequence"::trace)
          end
      | Sel nil => (NONE, "FAILURE: end of sel"::trace)
      | Sel (B::Bs) =>
          let
            val (stateOpt, trace) = runTrace B state spec trace
          in
            case stateOpt of
                 NONE => 
                    runTrace (Sel Bs) state spec trace
               | SOME state' => (SOME state', "SUCCESS: selector"::trace)
          end
      | Cond (C, B) =>
          if (holds_for state C) then 
            runTrace B state spec ("condition satisfied"::trace)
          else (NONE, "condition failed"::trace)
      | Just action => 
          let
            val (state', result) = try_doing action state spec
          in
            (state', result::trace)
          end

  fun run e state spec = 
    let
      val (outcome, trace) = runTrace e state spec []
    in
      (rev trace, outcome)
    end

end
