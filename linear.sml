structure LinearLogic =
struct
  (* Linear logic propositions/types *)
  type term = string
  type predicate = string
  type atom = string (* Eventually: predicate * (term list) *)
  (* type pos = atom list (* Arbitrary tensorings of atoms *) *)
  (* Tensor and Opluses:
  *   Positives P ::= *{P1, ..., Pn} | +{P1, ..., Pn}
  * *)
  datatype pos = Atom of atom | Tensor of pos list | OPlus of pos list 
  (* Interfaces N ::= P | P -o N | P * N *)
  datatype neg = NPos of pos | NLolli of pos * neg | NTens of pos * neg
                  | NPlus of neg * neg

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
      consequent: pos }
  type spec = action_spec list
  type state = (var * pos) list


  exception unimpl

  fun lookupRule (rulename : string) (spec : spec) =
    case spec of
         nil => NONE
       | ({name,args,antecedent,consequent}::spec) =>
          if not (name = rulename) then lookupRule rulename spec
          else
            SOME {pre=antecedent : pos, post=consequent : pos}

  fun rember' x ys f prefix_cont =
    case ys of
         (y::ys) => if f x y then SOME (prefix_cont ys)
                    else rember' x ys f (fn l => (prefix_cont (y::l)))
       | [] => NONE

  (* rember : 'a -> 'b list -> ('a -> 'b -> bool)  
  *     -> 'b list option
  * rember x ys f => NONE if x isn't in ys (according to f)
  *               => SOME ys' where ys' = ys - x
  *)
  fun rember x ys f = rember' x ys f (fn l => l)

  fun member x ys f = 
    case ys of
         (y::ys) => if f(x,y) then true else member x ys f
       | [] => false


  fun equal x y = x = y
  fun match_snd x (y1, y2) = x = y2

  fun satisfies (Pneed : pos) (x, Phave : pos) =
    case (Pneed, Phave) of
         (Atom a, Atom b) => a = b
       | (Atom a, OPlus []) => false
       | (Atom a, OPlus (B::Bs)) =>
           (satisfies (Atom a) (x, B)) andalso (satisfies (Atom a) (x, OPlus Bs))
       | (_, Tensor _) => false (* should not happen *)
       | (Tensor _, _) => false (* should not happen *)
       | (OPlus [], _) => true
       | (OPlus (A::As), _) =>  (* Either we satisfy A or something in As *)
           (satisfies A (x, Phave)) orelse (satisfies (OPlus As) (x, Phave))

  fun entails (P1 : pos) (P2 : pos) =
    case (P1, P2) of
         (Atom a, Atom b) => a = b
       | (Atom a, OPlus []) => true
       | (A, OPlus (B::Bs)) =>
           (entails A B) orelse (entails A (OPlus Bs))
       | (Tensor [], Tensor []) => true
       | (Tensor [], Tensor _) => false
       | (Tensor As, Tensor (B::Bs)) => 
           let
             fun reventail b a = entails a b
           in
            case rember B As reventail of
                 NONE => false
               | SOME As' => entails (Tensor As') (Tensor Bs)
           end
       | (OPlus [], _) => true
       | (OPlus (A::As), _) =>  (* Either we satisfy A or something in As *)
           (entails A P2) orelse (entails (OPlus As) P2)
       | (_, _) => false


  fun flatten (P : pos) : pos list =
    case P of
         Atom a => [Atom a]
       | Tensor [] => []
       | Tensor (A::As) => (flatten A)@(flatten (Tensor As))
       | OPlus [] => []
       | OPlus (A::As) =>
           let
             val As' : pos list = flatten (OPlus As)
           in
             [OPlus ((flatten A : pos list)@As')]
           end

  fun split (needs : pos list) (haves : state) : state option =
    case needs of
         nil => SOME haves
       | (need::needs) => 
           (case rember (need : pos) haves satisfies of
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


  fun atomize xs = map (fn x => Atom x) xs
  fun tensorize xs = Tensor (atomize xs)

  fun generate_pattern (P : pos) : (var * pos) list =
    case P of
         Atom a => [(fresh(), Atom a)]
       | OPlus A => [(fresh(), OPlus A)]
       | Tensor [] => []
       | Tensor (P::Ps) => (generate_pattern P)@(generate_pattern (Tensor Ps))
 
  fun generate_state (As : atom list) : (var * pos) list =
    generate_pattern (tensorize As)


end
