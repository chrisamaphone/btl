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

  fun try_doing (action, args) state spec =
    NONE (* XXX *)

  (* Return a new state on success; NONE on failure *)
  fun run (expr : btl) (state : state) (spec: spec) =
    case expr of
        Skip => SOME state
      | Seq nil => SOME state
      | Seq (B::Bs) =>
          let
            val stateOpt = run B state spec
          in
            case stateOpt of
                 SOME state' => run (Seq Bs) state' spec
               | NONE => NONE
          end
      | Sel nil => NONE
      | Sel (B::Bs) =>
          let
            val stateOpt = run B state spec
          in
            case stateOpt of
                 NONE => run (Sel Bs) state spec
               | SOME state' => SOME state'
          end
      | Cond (C, B) =>
          if (satisfies state C) then run B state spec
          else NONE
      | Just action => try_doing action state spec

end
