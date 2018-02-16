structure BTL = struct
  
  open LinearLogic (* for predicate language *)

  (* Behavior Tree expressions *)
  type rulename = string
  type btl_op = rulename * (term list)
  (* skip | op; btl | ?pos.btl *)
  datatype btl = Seq of btl list | Sel of btl list 
               | Cond of pos * btl | Just of btl_op | Skip
               
  type state = (var * atom) list
  
  fun satisfies (state: state) (cond: pos) =
    true (* XXX *)

  fun try_doing ((action, args) : btl_op) (state : state) (spec : spec) 
    : (state option) * string =
    case lookupRule action spec of
         NONE => (NONE, "no rule for action "^action)
       | SOME {pre, post} =>
           (case split pre state of
                 NONE => (NONE, "FAILURE: action "^action)
               | SOME state' => 
                   let
                     val state'' = state' @ (generate_pattern post)
                   in
                     (SOME state'', "SUCCESS: action "^action)
                   end
            )

  type trace = string list


  (* Return a new state on success; NONE on failure *)
  fun run (expr : btl) (state : state) (spec: spec) trace =
    case expr of
        Skip => (SOME state, ("SUCCESS: skip")::trace)
      | Seq nil => (SOME state, ("SUCCESS: end of seq")::trace)
      | Seq (B::Bs) =>
          let
            val (stateOpt, trace) = run B state spec trace
          in
            case stateOpt of
                 SOME state' => 
                    run (Seq Bs) state' spec trace
               | NONE => (NONE, "FAILURE: sequence"::trace)
          end
      | Sel nil => (NONE, "FAILURE: end of sel"::trace)
      | Sel (B::Bs) =>
          let
            val (stateOpt, trace) = run B state spec trace
          in
            case stateOpt of
                 NONE => 
                    run (Sel Bs) state spec trace
               | SOME state' => (SOME state', "SUCCESS: selector"::trace)
          end
      | Cond (C, B) =>
          if (satisfies state C) then 
            run B state spec ("condition satisfied"::trace)
          else (NONE, "condition failed"::trace)
      | Just action => 
          let
            val (state', result) = try_doing action state spec
          in
            (state', result::trace)
          end

end
