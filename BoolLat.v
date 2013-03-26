Require Export Lattice.
Require Export Bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BoolLat <: Lattice.
  Module DecImpl.
    Definition t : Type := bool.

    Definition eq_dec : forall x y : t, {x=y} + {x<>y}.
    Proof. decide equality. Defined.
  End DecImpl.

  Include Make_UDT (DecImpl).
  
  Definition Leq : relation t :=
    fun x y => x = y \/ x = false.

  Definition top : t := true .
  Definition bot : t := false.

  Definition leq x y : bool := (eqb x y) || (negb x).

  Definition join x y : bool := x || y.

  Definition meet x y : bool := x && y.

  Lemma LeqRefl : reflexive _ Leq.
  Proof. intros x; red; now tauto. Qed.

  Lemma LeqTrans : transitive _ Leq.
  Proof. destruct x, y, z; now firstorder. Qed.

  Lemma LeqAntisym : antisymmetric _ Leq.
  Proof. destruct x, y; now firstorder. Qed.

  Lemma leqProper : BinRelOp Leq leq.
  Proof. destruct x, y; now firstorder. Qed.

  Lemma JoinUnique : forall x y, UniqueBestBound Leq x y join.
  Proof. destruct x, y; now firstorder. Qed.

  Lemma MeetUnique :
    forall x y, UniqueBestBound (flip Leq) x y meet.
  Proof.
    intros x y. split.
    - destruct x,y; now firstorder.
    - intros z; destruct x,y,z; now firstorder.
  Qed.

  Lemma TopIsGreatest : GreatestElem Leq top.
  Proof. intros x; destruct x; now firstorder. Qed.

  Lemma BotIsLeast : LeastElem Leq bot.
  Proof. intros x; destruct x; now firstorder. Qed.

End BoolLat.


