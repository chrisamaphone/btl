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

