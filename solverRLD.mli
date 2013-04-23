type __ = Obj.t

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

val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

val value : 'a1 -> 'a1 option

val error : 'a1 option

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

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

module WFactsOn : 
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
 sig 
  val eqb : E.t -> E.t -> bool
 end

module WDecideOn : 
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
 sig 
  module F : 
   sig 
    val eqb : E.t -> E.t -> bool
   end
  
  module MSetLogicalFacts : 
   sig 
    
   end
  
  module MSetDecideAuxiliary : 
   sig 
    
   end
  
  module MSetDecideTestCases : 
   sig 
    
   end
 end

module WPropertiesOn : 
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
 sig 
  module Dec : 
   sig 
    module F : 
     sig 
      val eqb : E.t -> E.t -> bool
     end
    
    module MSetLogicalFacts : 
     sig 
      
     end
    
    module MSetDecideAuxiliary : 
     sig 
      
     end
    
    module MSetDecideTestCases : 
     sig 
      
     end
   end
  
  module FM : 
   sig 
    val eqb : E.t -> E.t -> bool
   end
  
  val coq_In_dec : M.elt -> M.t -> sumbool
  
  val of_list : M.elt list -> M.t
  
  val to_list : M.t -> M.elt list
  
  val fold_rec :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
    'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_bis :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
    'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2
  
  val fold_rec_nodep :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2
    -> 'a2) -> 'a2
  
  val fold_rec_weak :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
    -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2
  
  val fold_rel :
    (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
    'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3
  
  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) ->
    M.t -> 'a1
  
  val set_induction_bis :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 ->
    'a1) -> M.t -> 'a1
  
  val cardinal_inv_2 : M.t -> nat -> M.elt
  
  val cardinal_inv_2b : M.t -> M.elt
 end

module type JoinSemiLattice = 
 sig 
  type t 
  
  val eq_dec : t -> t -> sumbool
  
  val leq : t -> t -> bool
  
  val join : t -> t -> t
  
  val bot : t
 end

module UtilJoin : 
 functor (D:JoinSemiLattice) ->
 sig 
  
 end

type monadType = { tval : (__ -> __ -> __);
                   tbind : (__ -> __ -> __ -> (__ -> __) -> __) }

type 'x t0 = __

val tval : monadType -> 'a1 -> 'a1 t0

val tbind : monadType -> 'a1 t0 -> ('a1 -> 'a2 t0) -> 'a2 t0

val stateT : monadType -> monadType

val error0 : monadType

type ('a, 'b, 'c) funcType = monadType -> ('a -> 'b t0) -> 'c t0

module type CSysJoinSemiLat = 
 sig 
  module V : 
   UsualDecidableTypeBoth
  
  module D : 
   JoinSemiLattice
  
  val coq_F : V.t -> (V.t, D.t, D.t) funcType
 end

module SolverRLDtotal : 
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
 sig 
  module Var : 
   sig 
    type t = Sys.V.t
    
    val eq_dec : t -> t -> sumbool
   end
  
  module D : 
   sig 
    type t = Sys.D.t
    
    val eq_dec : t -> t -> sumbool
    
    val leq : t -> t -> bool
    
    val join : t -> t -> t
    
    val bot : t
   end
  
  module UtilD : 
   sig 
    
   end
  
  module VSetFacts : 
   sig 
    val eqb : Sys.V.t -> Sys.V.t -> bool
   end
  
  module VSetProps : 
   sig 
    module Dec : 
     sig 
      module F : 
       sig 
        val eqb : Sys.V.t -> Sys.V.t -> bool
       end
      
      module MSetLogicalFacts : 
       sig 
        
       end
      
      module MSetDecideAuxiliary : 
       sig 
        
       end
      
      module MSetDecideTestCases : 
       sig 
        
       end
     end
    
    module FM : 
     sig 
      val eqb : Sys.V.t -> Sys.V.t -> bool
     end
    
    val coq_In_dec : VSet.elt -> VSet.t -> sumbool
    
    val of_list : VSet.elt list -> VSet.t
    
    val to_list : VSet.t -> VSet.elt list
    
    val fold_rec :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> (VSet.t -> __ -> 'a2) ->
      (VSet.elt -> 'a1 -> VSet.t -> VSet.t -> __ -> __ -> __ -> 'a2 -> 'a2)
      -> 'a2
    
    val fold_rec_bis :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> (VSet.t -> VSet.t -> 'a1
      -> __ -> 'a2 -> 'a2) -> 'a2 -> (VSet.elt -> 'a1 -> VSet.t -> __ -> __
      -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_nodep :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> VSet.t -> 'a2 -> (VSet.elt -> 'a1 ->
      __ -> 'a2 -> 'a2) -> 'a2
    
    val fold_rec_weak :
      (VSet.elt -> 'a1 -> 'a1) -> 'a1 -> (VSet.t -> VSet.t -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 -> (VSet.elt -> 'a1 -> VSet.t -> __ -> 'a2 -> 'a2)
      -> VSet.t -> 'a2
    
    val fold_rel :
      (VSet.elt -> 'a1 -> 'a1) -> (VSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
      VSet.t -> 'a3 -> (VSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3
    
    val set_induction :
      (VSet.t -> __ -> 'a1) -> (VSet.t -> VSet.t -> 'a1 -> VSet.elt -> __ ->
      __ -> 'a1) -> VSet.t -> 'a1
    
    val set_induction_bis :
      (VSet.t -> VSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VSet.elt -> VSet.t ->
      __ -> 'a1 -> 'a1) -> VSet.t -> 'a1
    
    val cardinal_inv_2 : VSet.t -> nat -> VSet.elt
    
    val cardinal_inv_2b : VSet.t -> VSet.elt
   end
  
  module VS : 
   sig 
    type elt = Sys.V.t
    
    type t = VSet.t
    
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
   end
  
  module Sigma : 
   sig 
    type key = Sys.V.t
    
    type 'x t = 'x VMap.t
    
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
   end
  
  module Infl : 
   sig 
    type key = Sys.V.t
    
    type 'x t = 'x VMap.t
    
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
   end
  
  val coq_F : Sys.V.t -> (Sys.V.t, Sys.D.t, Sys.D.t) funcType
  
  type state = ((D.t Sigma.t, Var.t list Infl.t) prod, VS.t) prod
  
  val is_stable_b : VS.elt -> state -> bool
  
  val add_stable : VS.elt -> state -> state
  
  val rem_stable : VS.elt -> state -> state
  
  val getval : state -> Sigma.key -> D.t
  
  val setval : Sigma.key -> D.t -> state -> state
  
  val get_infl : state -> Infl.key -> Var.t list
  
  val add_infl : Infl.key -> Var.t -> state -> state
  
  val rem_infl : Infl.key -> state -> state
  
  val handle_work : VS.elt list -> state -> state
  
  val extract_work : Infl.key -> state -> (Var.t list, state) prod
  
  val solve : nat -> Var.t -> state -> state t0
  
  val solve_all : nat -> Var.t list -> state -> state t0
  
  val evalget : nat -> Var.t -> Var.t -> D.t t0
  
  val s_init : state
  
  val main : nat -> Var.t list -> D.t Sigma.t t0
 end

