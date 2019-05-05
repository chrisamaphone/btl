
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

structure DungeonExample =
struct
  open Examples
  
  (* Two bots, four locations, a key, and a chest *)
  val purple : term = "purple_bot"
  val green : term = "green_bot"
  val key : term = "key"
  val chest : term = "chest"
  val l1 : term = "l1"
  val l2 : term = "l2"
  val l3 : term = "l3"
  val l4 : term = "l4"

  (* Atomic Predicates:
   * - at thing/bot location
   * - has bot thing
   * - locked thing
   * - opened thing
   * - adjacent location location
   *)
  fun atP thing loc : pos = Atom ("at", [thing, loc])
  fun hasP bot thing : pos = Atom ("has", [bot, thing])
  fun lockedP thing : pos = Atom ("locked", [thing])
  fun openedP thing : pos = Atom ("opened", [thing])
  fun adjP loc1 loc2 : pos = Atom ("adjacent", [loc1, loc2])

  (* BTL actions for operators
   * The op names need to match the names of rules in the spec *)
  fun move bot loc1 loc2 : btl_op = act "walk_to" [bot, loc1, loc2]
  fun take bot thing loc : btl_op = act "take" [bot, thing, loc]
  fun give bot1 bot2 thing loc : btl_op = act "give" [bot1, bot2, thing, loc]
  fun drop bot thing loc : btl_op = act "drop" [bot, thing, loc]
  fun unlock bot thing loc : btl_op = act "unlock" [bot, thing, loc]


  (* Rule specifications for operators *)
  val move_spec : action_spec =
    { name = "walk_to",
      spec = fn [bot, loc1, loc2] =>
          { antecedent = 
              Tensor [atP bot loc1, adjP loc1 loc2],
            consequent =
              Tensor [atP bot loc2, adjP loc1 loc2]
          }
    }

  val take_spec : action_spec =
    { name = "take",
      spec = fn [bot, thing, loc] =>
        { antecedent =
            Tensor [atP bot loc, atP thing loc],
          consequent =
            Tensor [atP bot loc, hasP bot thing]
        }
    }

  val give_spec : action_spec =
    { name = "give",
      spec = fn [bot1, bot2, thing, loc] =>
        { antecedent =
            Tensor [atP bot1 loc, atP bot2 loc, hasP bot1 thing],
          consequent =
            Tensor [atP bot1 loc, atP bot2 loc, hasP bot2 thing]
        }
    }

  val drop_spec : action_spec =
    { name = "drop",
      spec = fn [bot, thing, loc] =>
        { antecedent =
            Tensor [atP bot loc, hasP bot thing],
          consequent =
            Tensor [atP bot loc, atP thing loc]
        }
    }

  val unlock_spec : action_spec =
    { name = "unlock",
      spec = fn [bot, thing, loc] =>
        { antecedent =
            Tensor [atP bot loc, atP thing loc, lockedP thing, hasP bot key],
          consequent =
            Tensor [atP bot loc, atP thing loc, openedP thing]
        }

    }

  val dungeonRules : spec =
    [move_spec, take_spec, give_spec, drop_spec, unlock_spec]

  (* Initial states *)
  (* Level 1: 
  *     l1   l2
  *   [ Bp | Bg ]
  *   -----------
  *   [ k  |  c ]
  *     l3   l4
  *)
  val level1 : state =
    generate_pattern
     (Tensor
      [atP purple l1, atP green l2, atP key l3, atP chest l4,
        adjP l1 l2, adjP l2 l1, adjP l1 l3, adjP l3 l1,
        adjP l2 l4, adjP l4 l2,
        adjP l3 l4, adjP l4 l3])

  fun keyAtAdjacent loc1 loc2 : pos = 
    Tensor [atP key loc2, adjP loc1 loc2]

  (* Behavior trees *)
  fun moveToKey bot loc1 loc2 : btl =
    Cond (keyAtAdjacent loc1 loc2,
      Just (move bot loc1 loc2))

  fun pickUpKey bot loc : btl =
    Just (take bot key loc)

  fun waitAndGiveKey bot1 bot2 loc : btl =
    Repeat
     (Just (give bot1 bot2 "key" loc))

  fun waitForGive bot : btl =
    Repeat
      (Cond (hasP bot key, Skip))

  fun openChest bot loc : btl =
    Just (unlock bot chest loc)

  val purpleBotBehavior : btl =
    Seq [moveToKey purple l1 l3, pickUpKey purple l3,
          waitAndGiveKey purple green l3]

  val greenBotBehavior : btl =
    Seq [Just (move green l2 l4), Just (move green l4 l3),
          waitForGive green, Just (move green l3 l4),
          openChest green l4]

  val bothBots = Par [purpleBotBehavior, greenBotBehavior]
          
  fun testStepBoth () =
    step bothBots level1 dungeonRules

  fun stepStarBoth () =
    step_star_simple bothBots level1 dungeonRules

end

structure DoorsExample =
struct
  open Examples
  
  (* Doors example *)

  val bot1 : term list = ["bot1"]
  val bot2 : term list= ["bot2"]
  
  (* These names need to match the names of rules in the spec *)
  fun walk_to_door bot : btl_op = act "walk_to" bot
  fun open_door bot : btl_op = act "open" bot
  fun unlock_door bot : btl_op = act "unlock" bot
  fun smash_door bot : btl_op = act "smash" bot
  fun walk_through_door bot : btl_op = act "walk_through" bot
  fun close_door bot : btl_op = act "close" bot

  fun get_door_open bot : btl =
    Sel [Just (open_door bot), 
          Sel [
            Just (unlock_door bot), 
            Just (open_door bot)], 
            Just (smash_door bot)]

  val doorOpen = Atom ("door_open", [])
  fun getOpenOrGoThrough bot : btl =
    (* Repeat( *)
      Sel [
        Cond (doorOpen,
          Just (walk_through_door bot)),
        Sel [
          get_door_open bot,
          Just (walk_through_door bot)
        ]
      ] (* ) *)
  
  fun closeOrSkip bot : btl =
    Sel [
      Just (close_door bot),
      Skip]


  fun getThroughPar bot : btl =
    Sel [Just (walk_to_door bot),
          getOpenOrGoThrough bot,
          closeOrSkip bot]
          

  fun get_through_door bot : btl =
    Seq [Just (walk_to_door bot),
          get_door_open bot,
          Just (walk_through_door bot),
          Just (close_door bot)]

  val small_example : btl =
    Sel [Just (open_door bot1), 
          Seq [ Just (unlock_door bot1), 
                Just (open_door bot1)]]

  val paper_example_1 : btl =
    Seq [Just (walk_to_door bot1), 
         Just (open_door bot1), 
         Just (walk_through_door bot1), 
         Just (close_door bot1)]


  val paper_example_2 : btl =
    Seq [ Sel [Just (walk_to_door bot1), Seq[]],
          Just (walk_through_door bot1) ]

          (* XXX - add bot1 arg
  val paper_example_3 : btl =
    Seq [ Sel [Just walk_to_door, Seq[]],
          Sel [ Cond (propAt "door_open", Seq[]), 
                Just open_door,
                Just smash_door],
          Just walk_through_door,
          Just close_door]
          *)

  (* Specification for actions *)

  val walk_to_spec : action_spec =
    {name = "walk_to",
     spec = fn agent =>
      { antecedent = Atom ("at_L", agent), 
        consequent = Atom ("at_door", agent) }
     }

  val open_spec : action_spec  =
    { name = "open",
      spec = fn agent =>
        { antecedent = tensorize ["at_door"::agent, ["door_unlocked"]],
          consequent = tensorize ["at_door"::agent, ["door_open"]]}
    }

  val unlock_spec : action_spec  =
    { name = "unlock",
      spec = fn agent =>
        { antecedent = 
            tensorize 
              ["at_door"::agent, ["door_locked"], "have_key"::agent],
          consequent = 
            tensorize 
              ["at_door"::agent, ["door_unlocked"]]}
    }

  val smash_spec : action_spec  =
    { name = "smash",
      spec = fn agent =>
      { antecedent = tensorize ["at_door"::agent, ["door_locked"]],
        consequent = tensorize ["at_door"::agent, ["door_open"]] }
    }

  val walk_thru_spec : action_spec  =
    { name = "walk_through",
      spec = fn agent =>
        { antecedent = tensorize ["at_door"::agent, ["door_open"]],
          consequent = 
            tensorize 
              ["through_door"::agent, ["door_open"]]
        }
    }

  val close_spec : action_spec  =
    { name = "close",
      spec = fn agent =>
        { antecedent = 
            tensorize ["through_door"::agent, ["door_open"]],
          consequent = 
            tensorize ["through_door"::agent, ["door_unlocked"]]
        }
    }

  val door_bot_rules : spec = 
    [walk_to_spec, open_spec, unlock_spec, smash_spec, walk_thru_spec, close_spec]
  (*
  (* ground all rules - XXX not doing this anymore; apply fn when look up rule *)
  val door_bot_spec : spec =
    List.concatMap (fn agent => (map (fn r => r agent) door_bot_rules)) agents 
  *)

  (* Initial state *)

  val init_state1 : state =
    generate_state [atomize ["at_L", "bot1"], atom "door_locked"]

  val init_state2 : state =
    generate_state 
      [atomize ["at_L", "bot1"], 
       atom "door_locked", 
       atomize ["have_key", "bot1"]]

  val init2bots : state =
    generate_state
      [ atomize ["at_L", "bot1"],
        atomize ["at_L", "bot2"],
        atomize ["have_key", "bot1"],
        atom "door_locked" ]


  (* Tests of run *)
  fun testDoors (init : state) = run (get_through_door bot1) init door_bot_rules

  fun test1 () = testDoors init_state1
  
  fun test2 () = testDoors init_state2

  (* Tests of step and step_star *)

  (* REPL interaction with step:
  *  - val (state, Cont next) = step get_through_door init_state1 door_bot_spec;
  * Then do:
  *  - val (state, Cont next) = step next state door_bot_spec;
  * Repeatedly until the "Cont next" raises bind
  *)
  fun testStep () = step (get_through_door bot1) init_state1 door_bot_rules
    (* val (state, Cont next, msg) = testStep() *)

  (* Testing step for parallel procs *)
  val two_bad_door_bots = Par [get_through_door bot1, get_through_door bot2]
  val two_good_door_bots = Par [getThroughPar bot1, getThroughPar bot2]
  fun testStepPar () = step two_good_door_bots init2bots door_bot_rules
  (* val (state, Cont next) = testStepPar() *)

  fun testRunPar () = run two_good_door_bots init2bots door_bot_rules

end

(* XXX - need to fix examples to have new action spec type 

structure InvestigateExample =
struct

  open Examples
  (* Investigating a sound example *)

  (* propositions *)
  val heard_noise : pos = propAt "heard_noise"
  val has_target : pos = propAt "has_target"
  val no_target : pos = propAt "no_target"
  val at_target : pos = propAt "at_target"

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

  val soundState1 = generate_state [atom "heard_noise", atom "no_target"]

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
  val charged_enough : pos = propAt "charged_enough"
  val battery_low : pos = propAt "battery_low"

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
          
  val batteryState1 = generate_state [atom "battery_low"]
  val batteryState2 = generate_state [atom "charged_enough"]

end

*)
