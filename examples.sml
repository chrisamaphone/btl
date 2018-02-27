structure Examples =
struct

  open BTL

  val door : term list = ["door"]
  
  fun act action objects = (action, objects)
  
  val walk_to_door : btl_op = act "walk_to" door
  val open_door : btl_op = act "open" door
  val unlock_door : btl_op = act "unlock" door
  val smash_door : btl_op = act "smash" door
  val walk_through_door : btl_op = act "walk_through" door
  val close_door : btl_op = act "close" door

  val get_door_open : btl =
    Sel [Just open_door, Seq [Just unlock_door, Just open_door], Just smash_door]

  val get_through_door : btl =
    Seq [Just walk_to_door, 
          get_door_open, 
          Just walk_through_door, 
          Just close_door]

  
  (* Specification for actions *)

  val walk_to_spec =
    {name = "walk_to",
     args = [] : string list,
     antecedent = Atom "at_L",
     consequent = Atom "at_door"
     }

  val open_spec =
    {name = "open",
     args = [] : string list,
     antecedent = tensorize ["at_door", "door_unlocked"],
     consequent = tensorize ["at_door", "door_open"]
     }

  val unlock_spec =
    {name = "unlock",
     args = [] : string list,
     antecedent = tensorize ["at_door", "door_locked", "have_key"],
     consequent = tensorize ["at_door", "door_unlocked"]
    }

  val smash_spec =
    {name = "smash",
     args = [] : string list,
     antecedent = tensorize ["at_door", "door_locked"],
     consequent = tensorize ["at_door", "door_open"]
    }

  val walk_thru_spec =
    {name = "walk_through",
     args = [] : string list,
     antecedent = tensorize ["at_door", "door_open"],
     consequent = tensorize ["at_door", "through_door", "door_open"]
    }

  val close_spec =
    {name = "close",
     args = [] : string list,
     antecedent = tensorize ["through_door", "door_open"],
     consequent = tensorize ["through_door", "door_unlocked"]
    }

  val door_bot_spec : spec = 
    [walk_to_spec, open_spec, unlock_spec, smash_spec, walk_thru_spec, close_spec]

  (* Initial state *)

  val init_state1 : state =
    generate_state ["at_L", "door_locked"]

  val init_state2 : state =
    generate_state ["at_L", "door_locked", "have_key"]


  fun testDoors init = run get_through_door init door_bot_spec

  fun test1 () = testDoors init_state1
  
  fun test2 () = testDoors init_state2

end
