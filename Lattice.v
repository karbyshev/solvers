Require Export Common.
Require Import Relations.Relation_Definitions.
Require Export Structures.Equalities.
Require Export Program.Basics.
Require Import Unicode.Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section order_rel_defs.
  Variable X : Type.
  Variable R : relation X.

  Definition GreatestElem x := forall y, R y x.

  Definition LeastElem x := forall y, R x y.

  Definition BinBound x y z := R y x /\ R z x.

  Definition BinBestBound x y z :=
    BinBound x y z /\ forall w, BinBound w y z -> R x w.

  Definition OpIsBB op :=
    forall x y, BinBestBound (op x y) x y.

  Definition UniqueBestBound x y op :=
    unique (fun d => BinBestBound d x y) (op x y).
End order_rel_defs.

Module Type IsPOSet (Import X : UsualDecidableType).
  Parameter Leq   : relation t.
  Notation "x '⊑' y" := (Leq x y) (at level 60).

  Axiom LeqRefl    : reflexive _ Leq.
  Axiom LeqTrans   : transitive _ Leq.
  Axiom LeqAntisym : antisymmetric _ Leq.
  (*Definition isPO : order _ Leq.
  Proof. split; [refine LeqRefl | refine LeqTrans | refine LeqAntisym]. Defined.*)

  Parameter leq   : t -> t -> bool.
  Axiom leqProper : BinRelOp Leq leq.

  Hint Resolve LeqRefl.
End IsPOSet.

Module Type POSet := UsualDecidableType <+ IsPOSet.

Module Type IsJoinSemiLattice (Import X : POSet).
  Parameter join      : t -> t -> t.
  Notation "x '⊔' y"  := (join x y) (at level 50).
  Axiom JoinUnique    : forall x y, UniqueBestBound Leq x y join.

  Parameter bot     : t.
  Axiom BotIsLeast  : LeastElem Leq bot.
  Notation "⊥"      := bot.
  Hint Resolve BotIsLeast.
End IsJoinSemiLattice.

Module Type JoinSemiLattice := POSet <+ IsJoinSemiLattice.

Module Type IsMeetSemiLattice (Import X : POSet).
  Parameter meet     : t -> t -> t.
  Notation "x '⊓' y" := (meet x y) (at level 50).
  Axiom MeetUnique   : forall x y, UniqueBestBound (flip Leq) x y meet.

  Parameter top       : t.
  Axiom TopIsGreatest : GreatestElem Leq top.
  Notation "⊤"        := top.
  Hint Resolve TopIsGreatest.
End IsMeetSemiLattice.

Module Type MeetSemiLattice := POSet <+ IsMeetSemiLattice.
Module Type Lattice := POSet <+ IsJoinSemiLattice <+ IsMeetSemiLattice.

Module Type HasWidening (Import X : POSet).
  Parameter widen : t -> t -> t.
  Notation "x '∇' y" := (widen x y) (at level 50).
  
  Axiom WidenProper : forall x y, x ⊑ (x ∇ y) ∧ y ⊑ (x ∇ y). 
End HasWidening.
  
Module Type HasNarrowing (Import X : POSet).
  Parameter narrow : t -> t -> t.
  Notation "x 'Δ' y" := (narrow x y) (at level 50).
  
  Axiom NarrowProper : forall x y, y ⊑ x -> y ⊑ (x Δ y) ∧ (x Δ y) ⊑ x.
End HasNarrowing.

Module Type WLattice  := Lattice <+ HasWidening.
Module Type NLattice  := Lattice <+ HasWidening <+ HasNarrowing.
Module Type WNLattice := Lattice <+ HasWidening <+ HasNarrowing.


Module Dual (Import D : Lattice) <: Lattice.
  Module DecImpl.
    Definition t := t.
    Definition eq_dec : forall x y, {eq x y} + {~ eq x y} := D.eq_dec.
  End DecImpl.

  Include Make_UDT (DecImpl).

  Definition Leq : relation t
    := fun x y => D.Leq y x.

  Definition leq : t -> t -> bool
    := fun x y => D.leq y x.

  Definition join : t -> t -> t
    := D.meet.

  Definition meet : t -> t -> t
    := D.join.

  Definition top : t := D.bot.
  Definition bot : t := D.top.

  Lemma LeqRefl : reflexive _ Leq.
  Proof. now apply D.LeqRefl. Qed.

  Lemma LeqTrans : transitive _ Leq.
  Proof. assert (H:=D.LeqTrans); now firstorder. Qed.

  Lemma LeqAntisym : antisymmetric _ Leq.
  Proof. assert (H:=D.LeqAntisym); now firstorder. Qed.

  Lemma leqProper : BinRelOp Leq leq.
  Proof. assert (H:=D.leqProper); now firstorder. Qed.
  
  Lemma JoinUnique : forall x y, UniqueBestBound Leq x y join.
  Proof. now refine D.MeetUnique. Qed.

  Lemma MeetUnique : forall x y, UniqueBestBound (flip Leq) x y meet.
  Proof. now refine D.JoinUnique. Qed.

  Lemma TopIsGreatest : GreatestElem Leq top.
  Proof. now refine D.BotIsLeast. Qed.

  Lemma BotIsLeast : LeastElem Leq bot.
  Proof. now refine D.TopIsGreatest. Qed.

  (*Definition isPO : order _ Leq.
  Proof. split; [ refine LeqRefl | refine LeqTrans | refine LeqAntisym ]. Defined.*)
End Dual.

Module test (L:Lattice).
  Module MSL : MeetSemiLattice := L.
  Module JSL : JoinSemiLattice := L.
End test.

Module UtilPOSet (Import D : POSet).

  Lemma leqRefl x : D.leq x x = true.
  Proof. now apply D.leqProper. Qed.

  (*Lemma if_leq_False x y:
    (if D.leq x y then False else True) -> ~ D.Leq x y.
  Proof.
    intros H e.
    now rewrite (proj1 (D.leqProper _ _) e) in H.
  Qed.*)
End UtilPOSet.


Module UtilJoin (Import D : JoinSemiLattice).

  Lemma FlipJoinIsJoin : OpIsBB D.Leq (flip D.join).
  Proof.
    intros y x.
    unfold flip.
    destruct (D.JoinUnique x y) as [H _].
    now firstorder.
  Qed.

  Lemma joinSym x y : D.join x y = D.join y x.
  Proof.
    apply D.JoinUnique.
    now apply FlipJoinIsJoin.
  Qed.

  Lemma joinSubsume x y : D.Leq x y <-> D.join x y = y.
  Proof.
    split.
    - intros H.
      apply D.JoinUnique.
      now firstorder.
    - intros H.
      rewrite <- H.
      now apply (D.JoinUnique x y).
  Qed.

  Lemma joinSubsumeR x y : D.Leq y x <-> D.join x y = x.
  Proof.
    rewrite joinSym.
    now apply joinSubsume.
  Qed.

  Lemma LeqJoin x y : y ⊑ x ⊔ y.
  Proof.
    now apply D.JoinUnique.
  Qed.
  Hint Resolve LeqJoin.

  Lemma leq_x_joinyz x y z : D.Leq x y -> D.Leq x (D.join y z).
  Proof.
    intros xLEy.
    destruct (D.JoinUnique y z) as [H _]. 
    apply (D.LeqTrans (y:=y)); now firstorder.
  Qed.

  Lemma LeqBotElim a : D.Leq a D.bot -> a = D.bot.
  Proof.
    intros H.
    now apply D.LeqAntisym.
  Qed.

End UtilJoin.

Module UtilMeet (Import D : MeetSemiLattice).

  Lemma meetSubsumed x y : D.Leq y x <-> D.meet x y = y.
  Proof.
    split.
    - intros H.
      apply D.MeetUnique.
      unfold flip.
      now firstorder.
    - intros H.
      rewrite <- H.
      now apply (D.MeetUnique x y).
  Qed.
  
  Lemma FlipMeetIsMeet : OpIsBB (flip D.Leq) (flip D.meet).
  Proof.
    intros y x. 
    unfold flip.
    destruct (D.MeetUnique x y) as [H _].
    now firstorder.
  Qed.

  Lemma meetSym x y : D.meet x y = D.meet y x.
  Proof.
    apply D.MeetUnique.
    now apply FlipMeetIsMeet.
  Qed.

  Lemma meetSubsumedR x y : D.Leq x y <-> D.meet x y = x.
  Proof.
    rewrite meetSym.
    now apply meetSubsumed.
  Qed.

  Lemma leq_meetxy_z x y z : D.Leq x z -> D.Leq (D.meet x y) z.
  Proof.
    intros xLEz.
    destruct (D.MeetUnique x y) as [H _]. 
    apply D.LeqTrans with (y:=x); now firstorder.
  Qed.

End UtilMeet.

Module Util (Import D : Lattice).

  Include UtilPOSet (D).
  Include UtilJoin (D).
  Include UtilMeet (D).

  Lemma MeetBotL b : D.meet D.bot b = D.bot.
  Proof.
    rewrite meetSym.
    now apply meetSubsumed.
  Qed.
  Hint Rewrite MeetBotL.
  
  Lemma MeetBotR b : D.meet b D.bot = D.bot.
  Proof.
    apply meetSubsumed.
    apply D.BotIsLeast.
  Qed.
  Hint Rewrite MeetBotR.

End Util.


Module UtilWiden (Import D : WLattice).
  Module U := Util (D).
 
  Lemma BotWidenElimR a b : D.bot = widen a b -> b = D.bot.
  Proof.
    intros H.
    destruct (WidenProper a b) as [_ H1].
    rewrite <- H in H1.
    now apply U.LeqBotElim.
  Qed.

  Lemma BotWidenElimL a b : D.bot = widen a b -> a = D.bot.
  Proof.
    intros H.
    destruct (WidenProper a b) as [H1 _].
    rewrite <- H in H1.
    now apply U.LeqBotElim.
  Qed.

End UtilWiden.

Module UtilNarrow (Import D : NLattice).
  Module U := Util (D).
 
  Lemma BotNarrowElim : narrow D.bot D.bot = D.bot.
  Proof.
    destruct (NarrowProper (x:=D.bot) (y:=D.bot)) as [A B]; auto.
    now apply D.LeqAntisym.
  Qed.
End UtilNarrow.  


Module OptionLattice (B : Lattice) <: Lattice.
  Module DecImpl.
    Definition t : Type := option B.t.

    Definition eq_dec : forall x y:t, {x=y} + {x<>y}.
    Proof.
      assert (E:=B.eq_dec).
      decide equality.
    Defined.
  End DecImpl.

  Include Make_UDT (DecImpl).

  Definition Leq : relation t := 
    fun x y =>
      match x, y with
        | Some x, Some y => B.Leq x y
        | None, _ => True
        | _, None => False
      end.

  Function leq x y : bool :=
    match x, y with
      | Some x, Some y => B.leq x y
      | None, _ => true
      | _, None => false
    end.
 
  Function join x y :=
    match x, y with
      | Some x, Some y => Some (B.join x y)
      | None, _ => y
      | _, None => x
    end.

  Function meet x y :=
    match x, y with
      | Some x, Some y => Some (B.meet x y)
      | _, _ => None
    end.

  Definition top : t := Some B.top.
  Definition bot : t := None.
  
  (*Lemma OrderInequal (X:Type) (leq:BinRel X) (asym:Antisym leq) :
      forall x y z, x<>y /\ leq x y /\ leq y z -> x<>z.
  Proof.
    intros x y z [XnY [XlY YlZ]] EQ.
    destruct EQ.
    now apply XnY, asym.
  Qed.*)

  Lemma LeqRefl : reflexive _ Leq.
  Proof. intros x. unfold Leq. now destruct x. Qed.

  Lemma LeqTrans : transitive _ Leq.
  Proof.
    assert (H:=B.LeqTrans).
    intros x y z.
    destruct x, y, z; now firstorder.
  Qed.

  Lemma LeqAntisym : antisymmetric _ Leq.
  Proof.
    assert (H:=B.LeqAntisym).
    intros x y A B.
    destruct x, y; try f_equal; now firstorder.
  Qed.

  (*Definition isPO : order _ Leq.
  Proof. split; [refine LeqRefl | refine LeqTrans | refine LeqAntisym]. Defined.*)

  Lemma leqProper : BinRelOp Leq leq.
  Proof.
    assert (H:=B.leqProper).
    intros x y; destruct x, y; unfold leq; now firstorder.
  Qed.
  
  Lemma JoinUnique : forall x y, UniqueBestBound Leq x y join.
  Proof.
    assert (H:=B.JoinUnique).
    intros x y. split.
    - destruct x,y; unfold Leq, join;
      firstorder; now destruct w; firstorder.
    - intros z A. destruct x,y,z; firstorder.
      + unfold join; f_equal. unfold Leq in H0, H2. 
        destruct (H t0 t1) as [D E]. apply E. split; [firstorder|]. 
        intros w. apply (H1 (Some w)); firstorder.
      + unfold join. f_equal. apply B.LeqAntisym; auto.
        apply (H1 (Some t0)). now split; try apply LeqRefl.  
      + unfold join. f_equal. apply B.LeqAntisym; auto.
        apply (H1 (Some t0)). now split; try apply LeqRefl.  
      + exfalso. apply (H1 None). firstorder.
  Qed.

  Lemma MeetUnique : forall x y, UniqueBestBound (flip Leq) x y meet.
  Proof.
    assert (H:=B.MeetUnique).    
    intros x y. split.
    - destruct x,y; cbv; firstorder.
      now destruct w; firstorder.
    - intros z A. destruct x,y,z; firstorder.
      + cbv. f_equal. apply (H t0 t1). firstorder.
        apply (H1 (Some w)). firstorder.
      + exfalso. apply (H1 (Some (B.bot))). unfold flip.
        assert (B:=B.BotIsLeast). firstorder.
  Qed.

  Lemma TopIsGreatest : GreatestElem Leq top.
  Proof.
    assert (H:=B.TopIsGreatest).
    intros x. destruct x; now firstorder.
  Qed.

  Lemma BotIsLeast : LeastElem Leq bot.
  Proof.
    assert (H:=B.BotIsLeast).
    intros x. destruct x; now firstorder.
  Qed.

End OptionLattice.
