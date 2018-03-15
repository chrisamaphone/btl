
structure Examples =
struct
  open BTL

  fun act action objects = (action, objects)
  fun nullary action = (action, [])
  fun specToAction {name, args, antecedent, consequent} =
    Just (nullary name) (* XXX assumes no args *)

  fun makePropoSpec (name: string, antecedent : pos, consequent : pos) =
    {name = name, args = [] : string list, antecedent = antecedent, consequent =
    consequent}
end

structure DoorsExample =
struct
  open Examples
  
  (* Doors example *)

  val door : term list = ["door"]
  
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

  val small_example : btl =
    Sel [Just open_door, Seq [Just unlock_door, Just open_door]]

  val paper_example_1 : btl =
    Seq [Just walk_to_door, Just open_door, Just walk_through_door, Just
    close_door]


  val paper_example_2 : btl =
    Seq [ Sel [Just walk_to_door, Seq[]],
          Just walk_through_door ]

  val paper_example_3 : btl =
    Seq [ Sel [Just walk_to_door, Seq[]],
          Sel [ Cond (Atom "door_open", Seq[]), 
                Just open_door,
                Just smash_door],
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

structure InvestigateExample =
struct

  open Examples
  (* Investigating a sound example *)

  (* propositions *)
  val heard_noise : pos = Atom "heard_noise"
  val has_target : pos = Atom "has_target"
  val no_target : pos = Atom "no_target"
  val at_target : pos = Atom "at_target"

  (* action specs *)
  val set_target =
    {name = "set_target",
     args = [] : string list,
     antecedent = no_target,
     consequent = has_target
    }

  val move_to_target =
    {name = "move_to_target",
     args = [] : string list,
     antecedent = has_target,
     consequent = Tensor [has_target, at_target]
     }
     
  val investigate =
    {name = "investigate",
     args = [] : string list,
     antecedent = Tensor [has_target, at_target, heard_noise],
     consequent = Tensor [no_target]
     }

  val idle = 
    {name = "idle",
     args = [] : string list,
     antecedent = Tensor [],
     consequent = Tensor []
     }

  val sound_spec = [set_target, move_to_target, investigate, idle]

  (* actions *)
  val do_set_target : btl = specToAction set_target
  val do_move_to_target : btl = specToAction move_to_target
  val do_investigate : btl = specToAction investigate
  val do_idle_behavior : btl = specToAction idle

  val testInvestigateSound : btl =
    Sel [ Cond (heard_noise, do_set_target),
          Cond (has_target, Seq [do_move_to_target, do_investigate]),
          do_idle_behavior 
        ]

  val testRepeatInvestigate : btl = Repeat testInvestigateSound

  val soundState1 = generate_state ["heard_noise", "no_target"]

  fun testInvestigate init = run testInvestigateSound init sound_spec
  fun testInvestigate2 init = run testRepeatInvestigate init sound_spec

  fun test3 () = testInvestigate soundState1

  (* note: will infloop, eventually doing idle behavior forever *)
  fun test4 () = testInvestigate2 soundState1

end

structure RobotBatteryExample =
struct
  open Examples
  
  (* propositions *)
  val charged_enough : pos = Atom "charged_enough"
  val battery_low : pos = Atom "battery_low"

  (* action specs *)
  val charge_battery = 
    makePropoSpec("charge_battery", OPlus [battery_low, charged_enough], charged_enough)

  val other_tasks =
    makePropoSpec("other_tasks", charged_enough, Tensor [])

  val RobotBatterySpec = [charge_battery, other_tasks]

  (* actions *)

  val do_charge_battery : btl = specToAction charge_battery
  val other_tasks : btl = specToAction other_tasks

  val chargeOrSkip : btl =
    Sel [ Cond (battery_low, do_charge_battery),
          Cond (charged_enough, Skip)
        ]

  val testChargeFirst : btl =
    Seq [
      chargeOrSkip,
      other_tasks
    ]
          
  val batteryState1 = generate_state ["battery_low"]
  val batteryState2 = generate_state ["charged_enough"]
          

end

