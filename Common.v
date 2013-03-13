(*Require Import Arith.*)
Require Import Relations.Relation_Definitions.
Require Import Program.Basics.
Require Export Unicode.Utf8.

Infix "∘" := compose (at level 40, left associativity).

(*Definition SubSet (X:Type) := X -> Prop.

Definition Proj1 {X Y:Type} (S:SubSet (X*Y)) : SubSet X :=
  fun x:X => exists y:Y, S (x, y).

Definition Proj2 {X Y:Type} (S:SubSet (X*Y)) : SubSet Y :=
  fun y:Y => exists x:X, S (x, y).

Definition Filter1 {X Y:Type} (S:SubSet (X*Y)) (x:X) : SubSet Y :=
  fun y:Y => S (x, y).

Definition Filter2 {X Y:Type} (S:SubSet (X*Y)) (y:Y) : SubSet X :=
  fun x:X => S (x, y).

Inductive JustTheseTwo {X:Type} (a b:X) : X -> Prop := 
  | justA : JustTheseTwo a b a 
  | justB : JustTheseTwo a b b
.*)

Definition BinRelOp {X : Type} (R : relation X) (op : X -> X -> bool) :=
  forall x y, R x y <-> op x y = true.

(*Lemma option_eq {A:Type} {a b:A}: Some a = Some b <-> a = b.
Proof.
  split.
  - intros Q.
    inversion Q.
    reflexivity.
  - intros Q.
    rewrite Q. 
    reflexivity.
Qed.

Definition none_dec {A:Type} : forall o:(option A), {o = None}+{o <> None}.
Proof.
  intros o.
  case o.
  - intros a.
    right. intros Q. inversion Q.
  - left. reflexivity.
Qed.

Lemma option_dec {A:Type} (o:option A) : {o=None}+{(exists e:A, o=Some e)}.
Proof.
  case o.
  + intros a. right. exists a. reflexivity.
  + left. reflexivity.
Qed.

Definition from_some {A:Type} (o:option A) (H:o <> None) : A.
Proof.
  case o in H.
  - exact a.
  - tauto.
Defined.

Lemma from_some_ok {A:Type} (o:option A) (H:o <> None) 
                     : o = Some (from_some o H).
Proof.
  unfold from_some.
  destruct o.
  - reflexivity.
  - contradiction H. reflexivity.
Qed.

Lemma Leq_int n m : n<=m -> {k:nat | m=n+k}.
Proof.
intros nLEQm.
induction n.
- induction m.
  + exists 0. auto.
  + exists (S m). auto.
- induction m.
  + apply le_Sn_0 in nLEQm. tauto.
  + destruct (IHn (le_Sn_le (n) (S m) nLEQm)) as [x H].
    destruct (eq_nat_dec x 0) as [Eq|Ne].
    * rewrite H in nLEQm.
      rewrite Eq in nLEQm.
      rewrite plus_0_r in nLEQm.
      apply le_Sn_n in nLEQm. tauto.
    * destruct x. tauto.
      exists x.
      rewrite H. ring.
Qed.

Function LProp (k:nat) (P:nat -> bool) (n:nat) {struct k} : nat :=
  match k with
    | S k => if P n then n else LProp k P (S n)
    | 0   => n
  end
.

Lemma LPropLeast k n (P:nat->bool) (H1:P (k+n) = true) (H2:forall m, m<n -> P m = false)
    : forall m,  m < (LProp k P n) -> P m = false.
Proof.
  intros m mLP.
  functional induction (LProp k P n).
  - apply H2. assumption.
  - apply IHn0.
    + rewrite <- plus_n_Sm.
      apply H1.
    + intros m0 m0LESn.
      apply lt_n_Sm_le in m0LESn.
      destruct (le_lt_eq_dec _ _ m0LESn) as [LT|EQ].
      * auto.
      * rewrite <- EQ in e0. assumption.
    + assumption.
  - apply H2. exact mLP.
Qed.


Lemma LPropProp k n (P:nat->bool) (H1:P (k+n) = true)
    : P (LProp k P n) = true.
Proof.
  functional induction (LProp k P n).
  - assumption.
  - apply IHn0.
    rewrite <- plus_n_Sm.
    apply H1.
  - unfold plus in H1.
    apply H1.
Qed.

Lemma NatPropToLeastNatProp k (P:nat->bool)
    : P k = true -> {n|P n=true & forall m, P m = true -> n <= m}.
Proof.
  intros Pk.
  exists (LProp k P 0).
  - apply LPropProp.
    rewrite <- plus_n_O.
    exact Pk.
  - intros m Pm.
    apply not_gt.
    intros H.
    apply LPropLeast in H.
    + rewrite H in Pm.
      inversion Pm.
    + rewrite <- plus_n_O.
      assumption.
    + intros m0 F.
      inversion F.
Qed.

Definition fst_sig2 {Z} {X Y:Z->Prop} (q:{p:Z|X p & Y p}) : Z :=
  let (p,_,_) := q in p.

Definition nameEq {A:Type} (a : A) : {a':A|a' = a}.
Proof.
  exists a. reflexivity.
Qed.

Lemma IfEqualElim (T:Type) (x:T) (equal:forall x y:T, {x=y}+{x<>y}) (A B:Type) : 
  (if equal x x then A else B) = A .
Proof.
    destruct (equal x x).
    - reflexivity.
    - exfalso.
      apply n. reflexivity.
Qed.
Hint Rewrite IfEqualElim.*)


