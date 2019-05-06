structure Sims =
struct
  open Examples

  val min = 0
  val max = 7

  (* utility fn for inc/dec numbers as strings *)
  fun incString (s : string) : string =
  let
    val SOME n = Int.fromString s
    val n' = if n < max then n+1 else n
  in
    Int.toString n'
  end

  fun decString (s : string) : string =
  let
    val SOME (n : int) = Int.fromString s
    val n' : int = if n > min then n-1 else n
  in
    Int.toString n'
  end

  val jean : term = "jean"
  val rowan : term = "rowan"
  val casey : term = "casey"

  val bed : term = "bed"
  val food : term = "food"
  val raw : term = "raw"
  val stove : term = "stove"
  val kitchen : term = "kitchen"
  val bedroom : term = "bedroom"
  val den : term = "den"

  (* Atomic Predicates:
  * - food sim level
  * - social sim level
  * - sleep sim level
  * - at sim/thing location
  * - adjacent location location
  * - eating sim
  * - sleeping sim
  * - talking sim sim
  * - idling sim
  *)
  fun atP thing loc : pos = Atom ("at", [thing, loc])
  fun foodP sim level : pos = Atom ("food", [sim, level])
  fun socialP sim level : pos = Atom ("social", [sim, level])
  fun sleepP sim level : pos = Atom ("sleep", [sim, level])
  fun adjP loc1 loc2 : pos = Atom ("adjacent", [loc1, loc2])
  fun eatingP sim : pos = Atom ("eating", [sim])
  fun sleepingP sim : pos = Atom ("sleeping", [sim])
  fun talkingP sim1 sim2 : pos = Atom ("talking", [sim1, sim2])
  fun idlingP sim : pos = Atom ("idling", [sim])

  (* BTL actions for operators:
   * - move
   * - cook
   * - eat
   * - talk
   * - sleep
   * - stop eating
   * - stop talking
   * - wake up
   *
   * The op names need to match the names of rules in the spec *)

  fun move sim loc1 loc2 : btl_op = act "walk_to" [sim, loc1, loc2]
  fun cook sim loc : btl_op = act "cook" [sim, loc]
  fun eat sim loc : btl_op = act "eat" [sim, loc]
  fun stop_eating sim loc hunger : btl_op = act "stop_eating" [sim, loc, hunger]
  fun talk sim1 sim2 loc : btl_op = act "talk" [sim1, sim2, loc]
  fun stop_talking sim1 sim2 social1 social2 : btl_op 
    = act "stop_talking" [sim1, sim2, social1, social2]
  fun sleep sim loc : btl_op = act "sleep" [sim, loc]

  (* Rule specifications for operators *)
  val move_spec : action_spec =
    { name = "walk_to",
      spec = fn [bot, loc1, loc2] =>
          { antecedent = 
              Tensor [atP bot loc1, adjP loc1 loc2, idlingP bot],
            consequent =
              Tensor [atP bot loc2, adjP loc1 loc2, idlingP bot]
          }
    }

  val cook_spec : action_spec =
    { name = "cook",
      spec = fn [sim, loc] =>
        { antecedent =
            Tensor [atP sim loc, atP "stove" loc, atP "raw" loc, idlingP sim],
          consequent =
            Tensor [atP sim loc, atP "stove" loc, atP "food" loc, idlingP sim]
        }
    }

  val eat_spec : action_spec =
    { name = "eat",
      spec = fn [sim, loc] =>
        { antecedent =
            Tensor [atP sim loc, atP "food" loc, idlingP sim],
          consequent =
            Tensor [atP sim loc, eatingP sim]
        }
    }

  val stop_eating_spec : action_spec =
    { name = "stop_eating",
      spec = fn [sim, loc, hunger] =>
        { antecedent =
            Tensor [atP sim loc, eatingP sim, foodP sim hunger], 
          consequent =
            Tensor [atP sim loc, idlingP sim, foodP sim (incString hunger)]
        }
    }

  val talk_spec : action_spec =
    { name = "talk",
      spec = fn [sim1, sim2, loc] =>
        { antecedent =
            Tensor [atP sim1 loc, atP sim2 loc, idlingP sim1, idlingP sim2],
          consequent =
            Tensor [atP sim1 loc, atP sim2 loc, talkingP sim1 sim2]
        }
    }

  val stop_talking_spec : action_spec =
    { name = "stop_talking",
      spec = fn [sim1, sim2, social1, social2] =>
        { antecedent =
            Tensor [talkingP sim1 sim2, 
              socialP sim1 social1, socialP sim2 social2],
          consequent =
            Tensor [idlingP sim1, idlingP sim2,
              socialP sim1 (incString social1),
              socialP sim2 (incString social2)]
         }
     }

  val sleep_spec : action_spec =
    { name = "sleep",
      spec = fn [sim, loc] =>
        { antecedent =
            Tensor [atP sim loc, atP "bed" loc, idlingP sim],
          consequent =
            Tensor [atP sim loc, sleepingP sim]
         }
      }

  (* XXX - stop sleeping - also need a "continue sleeping" action? *)

  val simsActions : spec =
    [move_spec, cook_spec, eat_spec, stop_eating_spec, talk_spec,
    stop_talking_spec, sleep_spec]

  (* Initial states *)
  val init : state =
    generate_pattern
      (Tensor
        [atP jean kitchen, atP rowan den, atP casey den,
          foodP jean "4", foodP rowan "7", foodP casey "2",
          socialP jean "2", socialP rowan "1", socialP casey "5",
          sleepP jean "6", sleepP rowan "4", sleepP casey "3",
          idlingP jean, idlingP rowan, idlingP casey,
          atP raw kitchen, atP raw kitchen, atP stove kitchen,
          atP bed bedroom,
          adjP den kitchen, adjP kitchen den,
          adjP den bedroom, adjP bedroom den])


  (* Behavior trees *)
  val rowanTalkToCasey : btl =
    Seq [
      Just (talk rowan casey den),
      Just (stop_talking rowan casey "1" "5")
    ]

  (* run rowanTalkToCasey init simsActions *)

end
