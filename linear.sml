structure LinearLogic =
struct
  (* Linear logic propositions/types *)
  type term = string
  type predicate = string
  type atom = string (* Eventually: predicate * (term list) *)
  type pos = atom list (* Arbitrary tensorings of atoms *)
  datatype neg = NPos of pos | NLolli of pos * neg | NTens of pos * neg

  type rulename = string

  (* Linear logic proof terms *)
  type var = int
  type pattern = var list
  datatype resource = 
      Var of var 
    | App of rulename * (term list) * (resource list)
  (* datatype pos_proof =
    Unit | Res of resource | Pair of pos_proof * pos_proof 
  *)
  type pos_proof = resource list
  datatype neg_proof = 
    Pos of pos_proof
  | Lam of pattern * neg_proof
  | NPair of pos_proof * neg_proof
  | Let of pattern * resource * neg_proof

  (* Signatures and contexts *)
  type action_spec = 
    { name: rulename, 
      args: string list, 
      antecedent: pos,
      consequent: pos}
  type spec = action_spec list
  type state = (var * atom) list


  exception unimpl

  fun lookupRule (rulename : string) (spec : spec) =
    case spec of
         nil => NONE
       | ({name,args,antecedent,consequent}::spec) =>
          if not (name = rulename) then lookupRule rulename spec
          else
            SOME {pre=antecedent : atom list, post=consequent : atom list}

  fun rember' x ys f prefix_cont =
    case ys of
         (y::ys) => if f x y then SOME (prefix_cont ys)
                    else rember' x ys f (fn l => (prefix_cont (y::l)))
       | [] => NONE

  (* rember : 'a -> 'b list -> ('a -> 'b -> bool) -> ('b list -> 'b list) 
  *     -> 'b list option
  * rember x ys f => NONE if x isn't in ys
  *               => SOME ys' where ys' = ys - x
  *)
  fun rember x ys f = rember' x ys f (fn l => l)

  fun equal x y = x = y
  fun match_snd x (y1, y2) = x = y2

  fun split (needs : atom list) (haves : (var * atom) list) =
    case needs of
         nil => SOME haves
       | (need::needs) => 
           (case rember need haves match_snd of
                 NONE => NONE (* a need could not be met *)
               | SOME haves' => split needs haves')

  val gensym = ref 0

  fun fresh() =
  let
    val ans = !gensym
    val () = gensym := ans + 1
  in
    ans
  end

  fun generate_pattern (P : pos) =
    case P of
         [] => []
       | (x::xs) => (fresh(), x)::(generate_pattern xs)
 

end
