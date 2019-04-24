structure Util = struct


  (*
  val rando = Random.rand (12345, Time.toSeconds Time.now)
  *)
  val rando = Random.rand (12345, 654321)

  fun separateNth ls n rest =
    case ls of
         [] => NONE
       | x::xs =>
          (case n of
              0 =>SOME (x, xs@rest)
            | n => separateNth xs (n-1) (x::rest))

  (* Never call on empty list *)
  fun separateRandom ls =
  let
    val idx = Random.randRange (0, List.length ls - 1) rando
    val SOME (x, xs) = separateNth ls idx []
  in
    (x, xs)
  end

end
