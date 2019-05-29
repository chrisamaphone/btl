structure LinearLogic =
struct
  (* Linear logic propositions/types *)
  type term = string
  type predicate = string
  (* type atom = string *)
  type atom = predicate * (term list)
  (* Tensor and Opluses:
  *   Positives P ::= *{P1, ..., Pn} | +{P1, ..., Pn}
  * *)
  datatype pos = Atom of atom | Tensor of pos list | OPlus of pos list 
  val One = Tensor []
  (* Interfaces N ::= P | P -o N | P * N *)
  datatype neg = NPos of pos | NLolli of pos * neg | NTens of pos * neg
                  (* | NPlus of neg * neg *) | NWith of neg * neg

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
      spec: term list ->
        {antecedent: pos, consequent: pos }
    }
  type spec = action_spec list
  type state = (var * pos) list


  exception unimpl

  fun lookupRule (rulename : string) (spec : spec) =
    case spec of
         nil => NONE
       | ({name,spec=f}::rest) =>
          if not (name = rulename) then lookupRule rulename rest
          else
            SOME f

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
       | (OPlus [], _) => false
       | (OPlus (A::As), _) =>  (* Either we satisfy A or something in As *)
           (satisfies A (x, Phave)) orelse (satisfies (OPlus As) (x, Phave))

  (* affine entailment *)
  fun entails (P1 : pos) (P2 : pos) =
    case (P1, P2) of
         (Atom a, Atom b) => a = b
       | (A, OPlus (B::Bs)) =>
           (entails A B) orelse (entails A (OPlus Bs))
       | (_, Tensor []) => true (* make 1st arg Tensor [] for linear *)
       | (Tensor [], Tensor (B::Bs)) => false
       | (Tensor As, Tensor (B::Bs)) => 
           let
             fun reventail b a = entails a b
           in
            case rember B As reventail of
                 NONE => false
               | SOME As' => entails (Tensor As') (Tensor Bs)
           end
       | (Tensor As, B) => member B As (fn (b, a) => entails a b) 
       | (OPlus [], _) => true
       | (OPlus (A::As), _) =>  (* Have to satisfy P2 in all cases *)
           (entails A P2) andalso (entails (OPlus As) P2)
       | (_, _) => false


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


  (* Functions for turning syntactic shorthand into proposition ASTs *)
  fun atomize (p::args : string list) = (p, args) : atom
  fun propifyAtom (a : atom) = Atom a
  fun propifyAll (xs : string list list) = map (propifyAtom o atomize) xs : pos list
    
  fun tensorize (xs : string list list) = Tensor (propifyAll xs) : pos
  
  fun tensor (As : atom list) = Tensor (map (fn x => Atom x) As) : pos
  
  fun atom (s : string) = (s, []) : atom
  fun propAt (s : string) = Atom (s, [])

  fun generate_pattern (P : pos) : (var * pos) list =
    case P of
         Atom a => [(fresh(), Atom a)]
       | OPlus A => [(fresh(), OPlus A)]
       | Tensor [] => []
       | Tensor (P::Ps) => (generate_pattern P)@(generate_pattern (Tensor Ps))
 
  fun generate_state (As : atom list) : (var * pos) list =
    generate_pattern (tensor As)

  (* Pull out any tensors into the flat list *)
  fun flatten (Ps : pos list) : pos list =
    case Ps of [] => []
       | (P::Ps) => 
           (case P of
                 Atom a => P::(flatten Ps)
               | OPlus ps => P::(flatten Ps)
               | Tensor ps => (flatten ps)@(flatten Ps))

  fun join (S1 : pos) (S2 : pos) = 
    case flatten [S1, S2] of
         [X] => X
       | Xs => Tensor Xs

  fun stateToPos (St : (var * pos) list) =
  let
    val props = map (fn (x,A) => A) St
  in
    Tensor props
  end

  fun posToPosList S =
    case S of
         Tensor Ps => Ps
       | _ => [S]

  (* running actions p -o q in state delta *)
  fun execute_rule (delta : state) (p : pos) (q : pos)
    : state option =
    case split (flatten [p]) delta of
         NONE => NONE (* Preconditions don't match *)
       | SOME remainder =>
           let
             val post_state = generate_pattern q
           in
             SOME (remainder @ post_state)
           end


end
