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
               | Just of btl_op

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
  (*
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
    *)

  (* Succeeds with same state if action is a b or c, fails otherwise *)
  fun try_doing (action : btl_op) (state : state) =
  let
    fun succeed x = 
      let
        val () = print ("doing "^ x ^"\n")
      in
        SOME state
      end
    fun fail x = 
      let
        val () = print ("couldn't do "^ x ^"\n")
      in
        NONE
      end
  in
    case action of
         ("a", _) => succeed "a"
       | ("b", _) => succeed "b"
       | ("c", _) => succeed "c"
       | (rule, _) => fail rule
  end

  (* step (e : btl) (state : state) (p : path) 
  *   returns status
  *   = Failed if e results in failure
  *   = Succeeded D if nothing left to be done, and new state is D
  *   = Path (D, P) if next thing to do is at path P and new state is D
  *   *)
  fun step (e : btl) (state : state) (path : path) =
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
                       val outcome = step subtree state subpath
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
                       val outcome = step subtree state subpath
                     in
                       case outcome of
                            Failed => Path (state, [i+1])
                          | Succeeded s => Succeeded s
                          | Path (s, p) => Path (s, i::p)
                     end
       | Just a =>
           let
             val outcome = try_doing a state
           in
             case outcome of
                  SOME s => Succeeded s
                | NONE => Failed
           end
  end

  fun step_iter (e : btl) (state : state) =
  let
    fun loop (s : state) (p : path) =
      case step e s p of
           Failed => NONE
         | Succeeded s => SOME s
         | Path (s', p') => loop s' p'
  in
    loop state nil
  end


  
  (* Tests *)
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

  (* test call:
  *   step_iter test_tree [] *)


  
end
