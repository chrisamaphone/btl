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

  (* Small step semantics for the parallel case *)
  datatype outcome = Cont of btl | Fail | Success

  (* step E D S = (D', E')
  *   where E is a BTL expression, D is a state, S is a spec,
  *   D' is the next state, E' is the next expression.
  * *)
  fun step (expr : btl) (state : state) (spec : spec)
    : (state * outcome) =
    case expr of
         Skip => (state, Success)
       | Seq nil => (state, Success) (* Seq nil = Skip *)
       | Sel nil => (state, Fail)
       | Seq (B::Bs) =>
           let
             val (state', outcome) = step B state spec
           in
             case outcome of
                  Success => (state', Cont (Seq Bs))
                | Fail => (state', Fail)
                | Cont B' => (state', Cont (Seq (B'::Bs)))
           end
       | Sel (B::Bs) =>
           let
             val (state', outcome) = step B state spec
           in
             case outcome of
                  Success => (state', Success)
                | Fail => (state', Cont (Sel Bs))
                | Cont B' => (state', Cont (Sel (B'::Bs)))
           end
       | Cond (C, B) =>
            if (holds_for state C) then
              (state, Cont B)
            else (state, Fail)
       | Just action =>
            let
              val (stateOpt, _) = try_doing action state spec
            in
              case stateOpt of
                   NONE => (state, Fail)
                 | SOME state' => (state', Success)
            end
       | Repeat B =>
           let
             val (state', outcome) = step B state spec
           in
             case outcome of
                  Cont B' => (state', Cont (Seq [B', Repeat B]))
                | _ => (state', Cont (Repeat B)) (* on finish, repeat B again *)
           end
       | Par Bs =>
           (* Choose a random process to evolve *)
           (* Alternative: generate list of all possible evolutions *)
           case Bs of
                [] => (state, Success)
              | Bs =>
           let
             val (B, Bs') = separateRandom Bs
             val (state', outcome) = step B state spec
           in
             case outcome of
                  Cont B' => (state', Cont (Par (B'::Bs')))
                | _ => (state', Cont (Par Bs'))
           end

  (* Apply step as many times as possible *)
  fun step_star expr state spec =
  let
    val (state', outcome) = step expr state spec
  in
    case outcome of
         Success => (state', outcome)
       | Fail => (state', outcome)
       | Cont expr' => step_star expr' state' spec
  end

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
