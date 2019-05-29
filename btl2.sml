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
               | Just of btl_op | Cond of pos * btl
  val Skip = Seq []
  val Abort = Sel []

  type path = int list
  datatype status = Failed | Succeeded of state | Path of state * path
               
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
    : state option =
  let
    fun succeed x s = let val () = print ("doing "^ x ^"\n") in SOME s end
    fun fail x = let val () = print ("couldn't do "^ x ^"\n") in NONE end
    val (rulename, args) = action
    val astring = actionToString action
  in
    case lookupRule rulename spec of
         NONE => fail (astring ^ "(no rule in spec)")
       | SOME f =>
           let
             val {antecedent=pre, consequent=post} = f args
           in
             case execute_rule state pre post of
                  NONE => fail astring
                | SOME state' => succeed astring state'
           end
  end

  (* step (e : btl) (state : state) (p : path) 
  *   returns status
  *   = Failed if e results in failure
  *   = Succeeded D if nothing left to be done, and new state is D
  *   = Path (D, P) if next thing to do is at path P and new state is D
  *   *)
  fun step (e : btl) (state : state) (path : path) (spec : spec)
    : status =
  let
    val (i, subpath) =
      case path of
           nil => (0, nil)
         | x::xs => (x, xs)
  in
    case e of
         Seq es => if i = length es then Succeeded state
                   else
                     let
                       val subtree = List.nth (es, i)
                       val outcome = step subtree state subpath spec
                     in
                       case outcome of
                            Failed => Failed
                          | Succeeded s => Path (s, [i+1])
                          | Path (s, p) => Path (s, i::p)
                     end
       | Sel es => if i = length es then Failed
                   else
                     let
                       val subtree = List.nth (es, i)
                       val outcome = step subtree state subpath spec
                     in
                       case outcome of
                            Failed => Path (state, [i+1])
                          | Succeeded s => Succeeded s
                          | Path (s, p) => Path (s, i::p)
                     end
       | Just a =>
           let
             val outcome = try_doing a state spec
           in
             case outcome of
                  SOME s => Succeeded s
                | NONE => Failed
           end
      | Cond (c, e) =>
          if holds_for state c then step e state subpath spec
          else Failed (* XXX - does this recheck the cond? *)
          (*
          if holds_for state c then
            let
              val outcome = step e state subpath spec
            in
              case outcome of
                   Failed => Failed
                 | Succeeded s => Succeeded s
                 | Path (s, p) => Path (s, p) (* XXX - need to update path? *)
            end
          else Failed
          *)
  end

  (* Repeatedly evaluate the tree until success or failure *)
  fun step_iter (e : btl) (state : state) (spec : spec) =
  let
    fun loop (s : state) (p : path) =
      case step e s p spec of
           Failed => NONE
         | Succeeded s => SOME s
         | Path (s', p') => loop s' p'
  in
    loop state nil
  end

  (* Reactive version: always re-eval selectors *)
  (* XXX do this *)

  fun active (s : status) =
    case s of
         Path _ => true
       | _ => false

  fun any_active (bs : (btl * status) list) =
    List.exists (fn (e,st) => active st) bs


  (* Soup-of-processes model of parallel agents
  *
  * step_par (es : btl list) (state : state) (spec : spec)
  *   : (e * status) list * state
  *)
  fun step_par (es : (btl * status) list) (state : state) (spec : spec)
    =
    let
      (* returns a new status *)
      fun advance_one (e : btl, status : status) (s:state) =
        case status of
           (* If we have more to do, take a step *)
             Path (_, p) => step e s p spec
           (* keep status same as before if nothing left to do *)
           | _ => status
      (* process a list of pairs (e, status) and state
      *  into new pairs (e, status) and new state *)
      fun advance_each behaviors state 
        : (btl * status) list * state =
        case behaviors of
             nil => (nil, state)
           | (e,status)::bs =>
               (case advance_one (e,status) state of
                     Path (state', p) =>
                        let (* pass in the new state *)
                          val (rest, s'') = advance_each bs state'
                        in
                          ((e,Path(state',p))::rest, s'') 
                        end
                   | other =>
                        let (* pass in the current state *)
                          val (rest, s') = advance_each bs state
                        in
                          ((e,other)::rest, s')
                        end)
    in
      advance_each es state
    end

  
  (* Repeatedly step a soup of processes *)
  fun step_par_iter (es : btl list) (state : state) (spec : spec)
    : (btl * status) list * state
    =
    let
      fun loop (s : state) (es : (btl * status) list) =
        let
          val (next_soup, next_state) = step_par es s spec
        in
          if any_active next_soup then
            loop next_state next_soup
          else
            (next_soup, next_state)
        end
      val init = map (fn e => (e, Path(state, []))) es
    in
      loop state init
    end
  
  (* Simple tests *)
  val test_op = ("a", []) (* will always succeed *)
  val test_op2 = ("foo", []) (* will always fail *)
  val test_action = Just test_op
  val test_action2 = Just test_op2
  val test_cond = Atom ("p", [])
  val test_cond2 = Atom ("q", [])

  val test_tree : btl = 
    Seq [ Sel [test_action2, test_action] 
          , test_action ]

  val test_state_succeed = generate_pattern test_cond
  val test_state_fail : state = []
  val test_state2 : state = generate_pattern test_cond2

  val a_spec = (* always succeeds *)
    { name = "a",
      spec = fn _ => {antecedent=One, consequent=One}
    }
  
  val foo_spec = (* always fails *)
    { name = "foo",
      spec = fn _ => {antecedent=OPlus [], consequent=One}
    }

  val rules = [a_spec, foo_spec]

  (* test call:
  *   step_iter test_tree [] rules *)


  
end
