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
    - destruct x,y; cbv; now firstorder.
    - intros z; destruct x,y,z; now firstorder.
  Qed.

  Lemma leqProper : PartOrder Leq.
  Proof.
  split; [|split].
  - firstorder.
  - intros x y z AB BC.
    unfold Leq.
    destruct AB as [Eq1|Ne1];
    destruct BC as [Eq2|Ne2];
    firstorder.
    + rewrite Eq1, Eq2.
      auto.
    + rewrite Eq1.
      auto.
  - intros x y AB BA.
    destruct AB as [Eq1|Ne1];
    destruct BA as [Eq2|Ne2];
    firstorder.
    rewrite Ne1, Ne2.
    reflexivity.
  Qed.

  Lemma JoinIsLub : OpIsBB Leq join.
  Proof.
  intros x y.
  destruct x, y; firstorder.
  Qed.

  Lemma JoinUnique : forall x y:t, UniqueBestBound Leq x y join.
  Proof.
  intros x y.
  destruct x, y; unfold join, orb, andb. 
  - split. firstorder.
    intros z [UB LST]. destruct z. constructor.
    destruct UB as [H _].
    destruct H as [H|H]; apply H.  
  - split. firstorder.
    intros z [UB LST]. destruct z. constructor.
    destruct UB as [H _].
    destruct H as [H|H]; apply H.
  - split. firstorder.
    intros z [UB LST]. destruct z. constructor.
    destruct UB as [_ H].
    destruct H as [H|H]; apply H.
  - split. firstorder.
    intros z [UB LST]. 
    destruct z; destruct (LST false); firstorder.
   Qed.
    
  Lemma TopIsGreatest : GreatestElem Leq top.
  Proof.
  intros x. destruct x; firstorder.
  Qed.

  Lemma MeetIsGlb : OpIsBB (flip Leq) meet.
  Proof.
  intros x y.
  destruct x, y; firstorder.
  Qed.

  Lemma MeetUnique : forall x y:t, UniqueBestBound (flip Leq) x y meet.
  Proof.
  intros x y. 
  destruct x, y; firstorder.
  destruct (H0 true). firstorder. tauto. destruct H2. firstorder.
  Qed.

  Lemma BotIsLeast : LeastElem Leq bot.
  Proof.
  intros x. destruct x; firstorder.
  Qed.
End BoolLat.


