type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t1) -> fold_left f t1 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t1) -> f b (fold_right f a0 t1)

module type DecidableType = 
 sig 
  type t 
  
  val eq_dec : t -> t -> sumbool
 end

module type UsualDecidableTypeBoth = 
 sig 
  type t 
  
  val eq_dec : t -> t -> sumbool
 end

module WFactsOn = 
 functor (E:DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val eq_dec : t -> t -> sumbool
 end) ->
 struct 
  (** val eqb : E.t -> E.t -> bool **)
  
  let eqb x y =
    match E.eq_dec x y with
    | Left -> True
    | Right -> False
 end

module WDecideOn = 
 functor (E:DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val eq_dec : t -> t -> sumbool
 end) ->
 struct 
  module F = WFactsOn(E)(M)
  
  module MSetLogicalFacts = 
   struct 
    
   end
  
  module MSetDecideAuxiliary = 
   struct 
    
   end
  
  module MSetDecideTestCases = 
   struct 
    
   end
 end

module WPropertiesOn = 
 functor (E:DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val eq_dec : t -> t -> sumbool
 end) ->
 struct 
  module Dec = WDecideOn(E)(M)
  
  module FM = Dec.F
  
  (** val coq_In_dec : M.elt -> M.t -> sumbool **)
  
  let coq_In_dec x s =
    match M.mem x s with
    | True -> Left
    | False -> Right
  
  (** val of_list : M.elt list -> M.t **)
  
  let of_list l =
    fold_right M.add M.empty l
  
  (** val to_list : M.t -> M.elt list **)
  
  let to_list =
    M.elements
  
  (** val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2 **)
  
  let fold_rec f i s pempty pstep =
    let l = rev (M.elements s) in
    let pstep' = fun x a s' s'' x0 -> pstep x a s' s'' __ __ __ x0 in
    let rec f0 l0 pstep'0 s0 =
      match l0 with
      | Nil -> pempty s0 __
      | Cons (y, l1) ->
        pstep'0 y (fold_right f i l1) (of_list l1) s0 __ __ __
          (f0 l1 (fun x a0 s' s'' _ _ _ x0 ->
            pstep'0 x a0 s' s'' __ __ __ x0) (of_list l1))
    in f0 l (fun x a s' s'' _ _ _ x0 -> pstep' x a s' s'' x0) s
  
  (** val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) ->
      'a2 **)
  
  let fold_rec_bis f i s pmorphism pempty pstep =
    fold_rec f i s (fun s' _ -> pmorphism M.empty s' i __ pempty)
      (fun x a s' s'' _ _ _ x0 ->
      pmorphism (M.add x s') s'' (f x a) __ (pstep x a s' __ __ x0))
  
  (** val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 **)
  
  let fold_rec_nodep f i s x x0 =
    fold_rec_bis f i s (fun s0 s' a _ x1 -> x1) x (fun x1 a s' _ _ x2 ->
      x0 x1 a __ x2)
  
  (** val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2 **)
  
  let fold_rec_weak f i x x0 x1 s =
    fold_rec_bis f i s x x0 (fun x2 a s' _ _ x3 -> x1 x2 a s' __ x3)
  
  (** val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)
  
  let fold_rel f g i j s rempty rstep =
    let l = rev (M.elements s) in
    let rstep' = fun x a b x0 -> rstep x a b __ x0 in
    let rec f0 l0 rstep'0 =
      match l0 with
      | Nil -> rempty
      | Cons (y, l1) ->
        rstep'0 y (fold_right f i l1) (fold_right g j l1) __
          (f0 l1 (fun x a0 b _ x0 -> rstep'0 x a0 b __ x0))
    in f0 l (fun x a b _ x0 -> rstep' x a b x0)
  
  (** val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1 **)
  
  let set_induction x x0 s =
    fold_rec (fun x1 x2 -> Tt) Tt s x (fun x1 a s' s'' _ _ _ x2 ->
      x0 s' s'' x2 x1 __ __)
  
  (** val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1 **)
  
  let set_induction_bis x x0 x1 s =
    fold_rec_bis (fun x2 x3 -> Tt) Tt s (fun s0 s' a _ x2 -> x s0 s' __ x2)
      x0 (fun x2 a s' _ _ x3 -> x1 x2 s' __ x3)
  
  (** val cardinal_inv_2 : M.t -> nat -> M.elt **)
  
  let cardinal_inv_2 s n =
    let l = M.elements s in
    (match l with
     | Nil -> assert false (* absurd case *)
     | Cons (e, l0) -> e)
  
  (** val cardinal_inv_2b : M.t -> M.elt **)
  
  let cardinal_inv_2b s =
    let x = fun x -> cardinal_inv_2 s x in
    (match M.cardinal s with
     | O -> assert false (* absurd case *)
     | S n -> x n)
 end

module type JoinSemiLattice = 
 sig 
  type t 
  
  val eq_dec : t -> t -> sumbool
  
  val leq : t -> t -> bool
  
  val join : t -> t -> t
  
  val bot : t
 end

type monadType = { tval : (__ -> __ -> __);
                   tbind : (__ -> __ -> __ -> (__ -> __) -> __) }

type 'x t0 = __

(** val tval : monadType -> 'a1 -> 'a1 t0 **)

let tval m x =
  let { tval = tval0; tbind = tbind0 } = m in Obj.magic tval0 __ x

(** val tbind : monadType -> 'a1 t0 -> ('a1 -> 'a2 t0) -> 'a2 t0 **)

let tbind m x x0 =
  let { tval = tval0; tbind = tbind0 } = m in Obj.magic tbind0 __ __ x x0

(** val stateT : monadType -> monadType **)

let stateT m =
  { tval = (fun _ x -> Obj.magic (fun s -> tval m (Pair (x, s)))); tbind =
    (fun _ _ t1 f ->
    Obj.magic (fun s ->
      tbind m (Obj.magic t1 s) (fun p ->
        let Pair (v, s') = p in Obj.magic f v s'))) }

(** val error0 : monadType **)

let error0 =
  { tval = (fun _ x -> Obj.magic (value x)); tbind = (fun _ _ t1 f ->
    match Obj.magic t1 with
    | Some x -> f x
    | None -> Obj.magic error) }

type ('a, 'b, 'c) funcType = monadType -> ('a -> 'b t0) -> 'c t0

module type CSysJoinSemiLat = 
 sig 
  module V : 
   UsualDecidableTypeBoth
  
  module D : 
   JoinSemiLattice
  
  val coq_F : V.t -> (V.t, D.t, D.t) funcType
 end

module SolverRLDtotal = 
 functor (Sys:CSysJoinSemiLat) ->
 functor (VSet:sig 
  type elt = Sys.V.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val eq_dec : t -> t -> sumbool
 end) ->
 functor (VMap:sig 
  type key = Sys.V.t
  
  type 'x t 
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  val find : key -> 'a1 t -> 'a1 option
  
  val remove : key -> 'a1 t -> 'a1 t
  
  val mem : key -> 'a1 t -> bool
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val elements : 'a1 t -> (key, 'a1) prod list
  
  val cardinal : 'a1 t -> nat
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct 
  module Var = Sys.V
  
  module D = Sys.D
  
  module VSetFacts = WFactsOn(Var)(VSet)
  
  module VSetProps = WPropertiesOn(Var)(VSet)
  
  module VS = VSet
  
  module Sigma = VMap
  
  module Infl = VMap
  
  (** val coq_F : Sys.V.t -> (Sys.V.t, Sys.D.t, Sys.D.t) funcType **)
  
  let coq_F =
    Sys.coq_F
  
  type state = ((D.t Sigma.t, Var.t list Infl.t) prod, VS.t) prod
  
  (** val is_stable_b : VS.elt -> state -> bool **)
  
  let is_stable_b x = function
  | Pair (p, stable) -> VS.mem x stable
  
  (** val add_stable : VS.elt -> state -> state **)
  
  let add_stable x = function
  | Pair (p, stable) -> Pair (p, (VS.add x stable))
  
  (** val rem_stable : VS.elt -> state -> state **)
  
  let rem_stable x = function
  | Pair (p, stable) -> Pair (p, (VS.remove x stable))
  
  (** val getval : state -> Sigma.key -> D.t **)
  
  let getval s x =
    let Pair (p, t1) = s in
    let Pair (sigma, t2) = p in
    (match Sigma.find x sigma with
     | Some d -> d
     | None -> D.bot)
  
  (** val setval : Sigma.key -> D.t -> state -> state **)
  
  let setval x d = function
  | Pair (p, stable) ->
    let Pair (sigma, infl) = p in
    Pair ((Pair ((Sigma.add x d sigma), infl)), stable)
  
  (** val get_infl : state -> Infl.key -> Var.t list **)
  
  let get_infl s x =
    let Pair (p, t1) = s in
    let Pair (t2, infl) = p in
    (match Infl.find x infl with
     | Some l -> l
     | None -> Nil)
  
  (** val add_infl : Infl.key -> Var.t -> state -> state **)
  
  let add_infl y x s = match s with
  | Pair (p, stable) ->
    let Pair (sigma, infl) = p in
    let xs = get_infl s y in
    Pair ((Pair (sigma, (Infl.add y (Cons (x, xs)) infl))), stable)
  
  (** val rem_infl : Infl.key -> state -> state **)
  
  let rem_infl x = function
  | Pair (p, stable) ->
    let Pair (sigma, infl) = p in
    Pair ((Pair (sigma, (Infl.remove x infl))), stable)
  
  (** val handle_work : VS.elt list -> state -> state **)
  
  let handle_work w s =
    fold_left (fun s0 x -> rem_stable x s0) w s
  
  (** val extract_work : Infl.key -> state -> (Var.t list, state) prod **)
  
  let extract_work x s =
    let w = get_infl s x in
    let s0 = rem_infl x s in let s1 = handle_work w s0 in Pair (w, s1)
  
  (** val solve : nat -> Var.t -> state -> state t0 **)
  
  let rec solve n x s =
    match n with
    | O -> Obj.magic error
    | S k ->
      (match is_stable_b x s with
       | True -> tval error0 s
       | False ->
         let s0 = add_stable x s in
         tbind error0 (Obj.magic coq_F x (stateT error0) (evalget k x) s0)
           (fun p ->
           let Pair (d, s1) = p in
           let cur = getval s1 x in
           (match D.leq d cur with
            | True -> tval error0 s1
            | False ->
              let new0 = D.join cur d in
              let s2 = setval x new0 s1 in
              let Pair (w, s3) = extract_work x s2 in solve_all k w s3)))
  
  (** val solve_all : nat -> Var.t list -> state -> state t0 **)
  
  and solve_all n w s =
    match n with
    | O -> Obj.magic error
    | S k ->
      (match w with
       | Nil -> tval error0 s
       | Cons (x, l) -> tbind error0 (solve k x s) (solve_all k l))
  
  (** val evalget : nat -> Var.t -> Var.t -> D.t t0 **)
  
  and evalget n x y =
    match n with
    | O -> Obj.magic (fun s -> error)
    | S k ->
      Obj.magic (fun s ->
        tbind error0 (solve k y s) (fun s1 ->
          let s2 = add_infl y x s1 in
          let d = getval s1 y in tval error0 (Pair (d, s2))))
  
  (** val s_init : state **)
  
  let s_init =
    Pair ((Pair (Sigma.empty, Infl.empty)), VS.empty)
  
  (** val main : nat -> Var.t list -> D.t Sigma.t t0 **)
  
  let main n w =
    tbind error0 (solve_all n w s_init) (fun s ->
      let Pair (p, t1) = s in let Pair (sigma, t2) = p in tval error0 sigma)
 end

