structure SimpleExample =
struct
  open BTL

  fun act action objects = (action, objects)
  
  val do_a : btl_op = act "do_a" []
  val do_b : btl_op = act "do_b" []
  val do_c : btl_op = act "do_c" []

  val ex_bt : btl =
    Seq [Just do_a, Just do_b, Just do_c]
  val ex_cond : btl =
    Cond (Atom "something", Just do_a)

  val do_a_spec =
    {name = "do_a",
     args = [] : string list,
     antecedent = Tensor [],
     consequent = Tensor []
     }

  val do_b_spec =
    {name = "do_b",
     args = [] : string list,
     antecedent = Atom "something",
     consequent = Tensor []
     }

  val do_c_spec =
    {name = "do_c",
     args = [] : string list,
     antecedent = Tensor [],
     consequent = Tensor []
     }

  val ex_spec = [do_a_spec, do_b_spec, do_c_spec]

  fun test prog init = run prog (generate_state init) ex_spec

  fun test1 () = test ex_bt ["something"]
  fun test2 () = test ex_bt ["else"]
  fun test3 () = test ex_cond ["nothing"]
  fun test4 () = test ex_cond ["something"]

end

structure TargetingExample =
struct
  open BTL

  fun act action objects = (action, objects)

  (* TODO how does this produce a target?*)
  val select_target : btl_op = act "select_target" []
  val do_nothing : btl_op = act "do_nothing" []
  val melee_attack : btl_op = act "melee_attack" []
  val use_auto_fire : btl_op = act "use_auto_fire" []
  val use_burst_fire : btl_op = act "use_burst_fire" []
  val ranged_attack : btl_op = act "ranged_attack" []

  val select_target_spec =
    {name = "select_target",
     args = [] : string list,
     antecedent = tensorize ["no_target"],
     consequent = tensorize ["target_T"]
     }

  val do_nothing_spec =
    {name = "do_nothing",
     args = [] : string list,
     antecedent = tensorize [],
     consequent = tensorize []
     }

  val melee_attack_spec =
    {name = "melee_attack",
     args = [] : string list,
     antecedent = tensorize ["target_T"],
     consequent = tensorize ["target_T", "melee_attacking_T"]
     }

  (* TODO this should also remove (if necessary) burst_fire_W *)
  val use_auto_fire_spec =
    {name = "use_auto_fire",
     args = [] : string list,
     antecedent = tensorize [],
     consequent = tensorize ["auto_fire_W"]
     }
  (* TODO this should also remove (if necessary) auto_fire_W *)
  val use_burst_fire_spec =
    {name = "use_burst_fire",
     args = [] : string list,
     antecedent = tensorize [],
     consequent = tensorize ["burst_fire_W"]
     }
  val ranged_attack_spec =
    {name = "ranged_attack",
     args = [] : string list,
     antecedent = tensorize ["target_T"],
     consequent = tensorize ["target_T", "ranged_attacking_T"]
     }

  val bt_spec =
    [ select_target_spec, melee_attack_spec, use_auto_fire_spec, 
      use_burst_fire_spec, ranged_attack_spec, do_nothing_spec ]

  (* from the opening example at 
   * https://takinginitiative.wordpress.com/2014/02/17/synchronized-behavior-trees/
   * TODO this doesn't translate very cleanly and needs to be adjusted to fit
   * into LL better. All the specs are temp.
   *)
  val bt =
    Seq [ Sel [ Cond (Atom "no_target", Just select_target),
                Just do_nothing],
          Sel [ Cond (Atom "melee_range_T", Just melee_attack),
                Seq [ Sel [ Cond (Atom "close_range_T", Just use_auto_fire),
                            Just use_burst_fire],
                      Just ranged_attack]]]

  fun test prog init = run prog (generate_state init) bt_spec

  fun test1 () = test bt ["no_target", "melee_range_T"]
  fun test2 () = test bt ["target_T", "melee_range_T"]
  fun test3 () = test bt ["no_target", "close_range_T"]
  fun test4 () = test bt ["no_target"]

end

structure InstantaneousDoorExample =
struct
  open BTL

  (* the door example, but as a state-chooser instead of a synchronous action *)

  val door : term list = ["door"]
  
  fun act action objects = (action, objects)
  fun nullary action = (action, [])

  fun specToAction {name, args, antecedent, consequent} =
    Just (nullary name) (* XXX assumes no args *)
  
  val walk_to_door : btl_op = act "walk_to" door
  val open_door : btl_op = act "open" door
  val unlock_door : btl_op = act "unlock" door
  val smash_door : btl_op = act "smash" door
  val walk_through_door : btl_op = act "walk_through" door
  val close_door : btl_op = act "close" door
  val done : btl_op = act "done" door

  val door_locked = Atom "door_locked"
  val door_closed = OPlus [Atom "door_closed", Atom "door_locked"]
  val through_door = Atom "through_door"

  val walk_to_spec =
    {name = "walk_to",
     args = [] : string list,
     antecedent = Atom "at_L",
     consequent = tensorize ["at_L", "walking_to_door"]
     }

  val open_spec =
    {name = "open",
     args = [] : string list,
     antecedent = tensorize ["at_door", "door_unlocked"],
     consequent = tensorize ["at_door", "opening_door"]
     }

  val unlock_spec =
    {name = "unlock",
     args = [] : string list,
     antecedent = tensorize ["at_door", "door_locked", "have_key"],
     consequent = tensorize ["at_door", "unlocking_door"]
    }

  val smash_spec =
    {name = "smash",
     args = [] : string list,
     antecedent = tensorize ["at_door", "door_locked"],
     consequent = tensorize ["at_door", "smashing_door"]
    }

  val walk_thru_spec =
    {name = "walk_through",
     args = [] : string list,
     antecedent = tensorize ["at_door", "door_open"],
     consequent = tensorize ["at_door", "door_open", "walking_through_door"]
    }

  val close_spec =
    {name = "close",
     args = [] : string list,
     antecedent = tensorize ["through_door", "door_open"],
     consequent = tensorize ["through_door", "closing_door"]
    }

  val door_bot_spec : spec = 
    [walk_to_spec, open_spec, unlock_spec, smash_spec, walk_thru_spec, close_spec]

  val get_door_open : btl =
    Sel [ Cond(door_locked, Sel [Just unlock_door, Just smash_door]),
          Just open_door ]
  val ensure_closed : btl =
    Sel [ Cond(door_closed, Just done), Just close_door ]

  val get_through_door : btl =
    Sel [ Cond(through_door, ensure_closed),
          Cond(door_closed, get_door_open),
          Just walk_through_door,
          Just walk_to_door]

  fun test init = run get_through_door (generate_state init) door_bot_spec

  fun test1 () = test ["at_L", "door_locked"]
  fun test2 () = test ["at_L", "door_locked", "have_key"]
  fun test3 () = test ["at_door", "door_locked", "have_key"]
end
