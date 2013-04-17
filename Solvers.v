Require Export MSetInterface.
Require Export FMapInterface.
Require Export Constr.
Require Export FunctionalExtensionality.
Require Export List.
Require Import Utf8.

Export ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SetsTypeOn := MSetInterface.WSetsOn.
Module Type MapsTypeOn := FMapInterface.WSfun.

(*Module Type Solver (Sys : CSysJoinSemiLat) (SStr : SolverStructs (Sys)).
End Solver.*)

Module Defs (Sys : CSysJoinSemiLat).

Module Var := Sys.V.
Module D   := Sys.D.

Section LeqFun.
Variable X : Type.

Definition leqF : relation (X -> D.t)
  := fun f1 f2 => forall x, D.Leq (f1 x) (f2 x).

Definition leqF_refl : reflexive _ leqF.
Proof. now firstorder. Qed.
Hint Resolve leqF_refl.

Definition leqF_antisym : antisymmetric _ leqF.
Proof.
intros f g H H0.
extensionality x.
now apply D.LeqAntisym.
Qed.
Hint Resolve leqF_antisym.

Definition leqF_trans : transitive _ leqF.
Proof.
intros f g h H1 H2 x.
eapply D.LeqTrans; [eapply H1 |]; auto.
Qed.
End LeqFun.
Hint Resolve leqF_trans.

Definition has_uniq_lookup {X} (rhs : X -> Tree Var.t D.t D.t) :=
  forall x, uniq_lookup (rhs x).

Definition is_monotone {X} (rhs : X -> Tree Var.t D.t D.t) :=
  forall x f g, leqF f g -> D.Leq ([[rhs x]]* f) ([[rhs x]]* g).

Definition is_solution (rhs : Var.t -> Tree Var.t D.t D.t) mu
  := forall x, D.Leq ([[rhs x]]* mu) (mu x).

Definition is_min_solution (rhs : Var.t -> Tree Var.t D.t D.t) mu
  := is_solution rhs mu /\
     forall mu', is_solution rhs mu' -> leqF mu mu'.

End Defs.
