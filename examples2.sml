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
    Seq [
      Sel [
        Cond (Atom "no_target", Just select_target),
        Just do_nothing
      ],
      Sel [
        Cond (Atom "melee_range_T", Just melee_attack),
        Seq [
          Sel [
            Cond (Atom "close_range_T", Just use_auto_fire),
            Just use_burst_fire
          ],
          Just ranged_attack
        ]
      ]
    ]

  fun test prog init = run prog (generate_state init) bt_spec

  fun test1 () = test bt ["no_target", "melee_range_T"]
  fun test2 () = test bt ["target_T", "melee_range_T"]
  fun test3 () = test bt ["no_target", "close_range_T"]
  fun test4 () = test bt ["no_target"]
end
