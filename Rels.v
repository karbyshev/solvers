Require Import Logic.Eqdep.
Require Export Relations.Relation_Definitions.
Require Export Wellfounded.
Require Import Lists.SetoidList.
Require Import Arith.
Require Import Omega.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section relations.

Variable A : Type.

(* Inverse relation *)
Definition inv (R : relation A) : relation A := fun x y => R y x.

(* Strict subrelation *)
Definition strict (R : relation A) : relation A :=
  fun x y => R x y /\ x <> y.

Definition ascending_chain (R : relation A)
  := well_founded (strict (inv R)).

End relations.

Section SymProduct.

Variable A : Type.
Variable B : Type.
Variable leA : relation A.
Variable leB : relation B.

Inductive symprod : relation (A * B) :=
  | left_sym :
    forall x x', leA x x' ->
                 forall y, symprod (x, y) (x', y)
  | right_sym :
    forall y y', leB y y' ->
                 forall x, symprod (x, y) (x, y').

Variable leA_wf : well_founded leA.
Variable leB_wf : well_founded leB.

Lemma symprod_wf : well_founded symprod.
Proof.
intros [a b].
revert b.
apply Acc_ind with (R:=leA) (x:=a); auto; clear a.
intros a _ Ha b.
apply Acc_ind with (R:=leB) (x:=b); auto; clear b.
intros b _ Hb.
apply Acc_intro; intros [x y] Hxy.
inversion Hxy; subst; now firstorder.
Qed.

End SymProduct.

Section LexProduct.

Variable A : Type.
Variable B : Type.
Variable leA : relation A.
Variable leB : relation B.

Inductive lexprod : relation (A * B) :=
  | left_lex :
    forall x x' y y',
      leA x x' -> lexprod (x,y) (x',y')
  | right_lex :
    forall x y y',
      leB y y' -> lexprod (x,y) (x,y').

Variable leA_wf : well_founded leA.
Variable leB_wf : well_founded leB.

Lemma lexprod_wf : well_founded lexprod.
Proof.
intros [a b].
assert (Ha : Acc leA a) by auto.
revert b.
apply Acc_ind with (R:=leA) (x:=a); auto; clear dependent a.
intros a _ Ha b.
apply Acc_ind with (R:=leB) (x:=b); auto; clear b.
intros b _ Hb.
apply Acc_intro; intros [x y] Hxy.
inversion Hxy; subst; now firstorder.
Qed.

End LexProduct.

Section vector_defs.

Variable A : Type.

Inductive vector : nat -> Type :=
| vec_nil : vector 0
| vec_cons : forall n, A -> vector n -> vector (S n).

Definition eq_vec := eq_dep nat vector.

Fixpoint vector_of (l : list A) : {n : nat & vector n} :=
  match l with
    | nil => existT _ 0 vec_nil
    | cons h t =>
        let (n,l) := vector_of t in
          existT _ (S n) (vec_cons h l)
  end.

Fixpoint list_of n (v : vector n) : list A :=
  match v with
    | vec_nil => nil
    | vec_cons _ h t => cons h (list_of t)
  end.

Lemma len_vector_of (l : list A) :
  projT1 (vector_of l) = length l.
Proof.
induction l as [| h t IH]; auto.
simpl. destruct (vector_of t) as [n v]; simpl; simpl in IH.
now rewrite IH.
Qed.

Definition head' n (v : vector n) :=
  match v in vector x return lt 0 x -> A with
    | vec_nil =>
        fun H : lt O O => (False_rect A (lt_irrefl O H))
    | vec_cons n' h _ =>
        fun H : lt 0 (S n') => h
  end.

Definition head n (v : vector (S n)) :=
  head' (n:=S n) v (lt_O_Sn n).

Definition tail n (v : vector n) :=
  match v in vector x return vector (pred x) with
    | vec_nil => vec_nil
    | vec_cons _ _ v' => v'
  end.

Fixpoint nth_aux n (v : vector n) i :
  lt i n -> A :=
  match v, i with
    | vec_nil, _ => fun (H : i < 0) => False_rect A (lt_n_0 i H)
    | vec_cons n' h _, 0 => fun (H : 0 < S n') => h
    | vec_cons n' _ t, S i' =>
        fun (H : S i' < S n') => @nth_aux n' t i' (lt_S_n _ _ H)
  end.

Definition nth n (v : vector n) (i : {i | i < n}) :=
  nth_aux v (proj2_sig i).


Lemma empty_dep n (v : vector n) :
  n = O -> @eq_vec n v 0 vec_nil.
Proof.
intros e.
dependent inversion v.
- easy.
- now subst.
Qed.
Hint Resolve empty_dep.

Lemma empty (v : vector O) : v = vec_nil.
Proof.
apply (eq_dep_eq nat vector O).
now apply empty_dep.
Qed.
Hint Resolve empty.

Lemma non_empty_dep n (v : vector (S n)) :
  {h : A & {t : vector n |
            @eq_vec (S n) v (S n) (vec_cons h t)}}.
Proof.
dependent inversion_clear v with
  (fun n' (v: vector n') =>
     {a : A & {v' : vector n |
               @eq_vec n' v (S n) (vec_cons a v')}}).
now exists a, v0.
Qed.

Lemma non_empty n (v :vector (S n)) :
  {a : A & {t : vector n | v = vec_cons a t}}.
Proof.
assert (H := non_empty_dep v).
destruct H as [h [t H]].
exists h, t. now apply eq_dep_eq.
Qed.

Lemma split_vec n (v : vector (S n)) :
  v = vec_cons (head v) (tail v).
Proof.
destruct (non_empty v) as [h [t H]].
now subst.
Qed.

Lemma nth_0_is_head n (v : vector (S n)) :
  head v = nth v (exist _ 0 (lt_0_Sn n)).
Proof.
now rewrite (split_vec v).
Qed.

Lemma nth_irrel n (v : vector n) i (H H' : i < n) :
  nth_aux v H = nth_aux v H'.
Proof.
revert i H H'.
induction n as [| n IHn].
- easy.
- rewrite (split_vec v).
  destruct i as [| i]; auto.
  intros H H'.
  now simpl.
Qed.

Lemma nth_cons n (v : vector n) a i H (Hi : i > 0) :
  exists H',
    @nth_aux _ (vec_cons a v) i H = @nth_aux _ v (i-1) H'.
Proof.
destruct i; [easy |].
simpl in H. simpl.
revert H. rewrite <- minus_n_O.
intros H.
assert (H' : i < n) by omega.
exists H'. now apply nth_irrel.
Qed.

End vector_defs.

Section search.

Variable A : Type.

Fixpoint has n (v : vector A n) a : Prop :=
  match v with
    | vec_nil => False
    | vec_cons n' h t => h = a \/ has t a
  end.

Lemma has_nil a : ~ has (vec_nil A) a.
Proof.
easy.
Qed.

Lemma has_cons a n h (t : vector A n) :
  a <> h -> has (vec_cons h t) a -> has t a.
Proof.
simpl. intros ne H. now destruct H; try congruence.
Qed.

Lemma InA_has l a :
  InA eq a l ->
  let (_, v) := vector_of l in has v a.
Proof.
induction l as [| h t IH].
- easy.
- intros H.
  inversion H; subst.
  + simpl.
    destruct (vector_of t) as [nt vt].
    now left.
  + simpl.
    destruct (vector_of t) as [nt vt].
    now right; auto.
Qed.

Variable eq_dec : forall a a' : A, {a = a'} + {a <> a'}.

Fixpoint find'_aux n (v : vector A n) a count :=
  match v return has v a -> nat with
    | vec_nil =>
        fun H : has (vec_nil A) a => False_rect nat (has_nil H)
    | vec_cons n' h t =>
        fun H : has (vec_cons h t) a =>
          match eq_dec a h with
            | left _ => count
            | right ne =>
                @find'_aux n' t a (S count) (has_cons ne H)
          end
  end.

Definition find' n (v : vector A n) a := @find'_aux n v a 0.

Lemma find'_aux_irrel n (v : vector A n) a c (H1 H2 : has v a) :
  find'_aux c H1 = find'_aux c H2.
Proof.
revert c H1 H2.
induction v as [| n' h t IH].
- intros c H1 H2. now elim (has_nil H1).
- intros c H1 H2.
  unfold find'. unfold find' in IH.
  simpl.
  now destruct (eq_dec a h).
Qed.

Lemma find'_aux_shift n (v : vector A n) a c (H : has v a) :
  find'_aux c H = find'_aux 0 H + c.
Proof.
revert c.
induction v as [| n' h t IH].
- now elim (has_nil H).
- intros c. simpl.
  destruct (eq_dec a h); auto.
  rewrite IH with (c:=S c).
  rewrite IH with (c:=1).
  omega.
Qed.

Lemma find'_irrel n (v : vector A n) a (H1 H2 : has v a) :
  find' H1 = find' H2.
Proof.
unfold find'.
now apply find'_aux_irrel.
Qed.

Lemma find'_cons_0 n (v : vector A n) a H :
  @find' _ (vec_cons a v) a H = 0.
Proof.
unfold find', find'_aux. simpl.
now destruct (eq_dec a a); congruence.
Qed.

Lemma find'_cons_1 n (v : vector A n) h a Hcons H (Ha : a <> h) :
  @find' _ (vec_cons h v) a Hcons = S (@find' _ v a H).
Proof.
unfold find'. simpl.
destruct (eq_dec a h) as [e | ne]; [easy |].
rewrite find'_aux_shift.
rewrite find'_aux_irrel with (H2:=H).
omega.
Qed.

Lemma find'_cons_1_bis n (v : vector A n) h a H (Ha : a <> h) :
  exists H', @find' _ (vec_cons h v) a H = @find' _ v a H' + 1.
Proof.
unfold find'. simpl.
destruct (eq_dec a h) as [e | ne]; [easy |].
rewrite find'_aux_shift.
now eauto.
Qed.

Lemma find'_cons_2 n (v : vector A n) h a H (Ha : a <> h) :
  @find' _ (vec_cons h v) a H > 0.
Proof.
destruct (find'_cons_1_bis H Ha) as [H' e].
rewrite e; now auto with arith.
Qed.

Lemma find'_aux_le n (v : vector A n) a (H : has v a) c :
  find'_aux c H < n + c.
Proof.
revert c.
induction v as [| n' h t IH].
- now elim (has_nil H).
- simpl.
  destruct (eq_dec a h).
  + now auto with arith.
  + simpl. intros c.
    now rewrite plus_n_Sm.
Qed.

Lemma find'_le n (v : vector A n) a (H : has v a) : find' H < n.
Proof.
unfold find.
rewrite <- (plus_0_r n).
now apply find'_aux_le.
Qed.

Definition find n (v : vector A n) a (H : has v a) : {i | i < n}.
exists (find' H).
now apply find'_le.
Defined.

Lemma nth_aux_find n (v : vector A n) a (Ha : has v a) H :
    @nth_aux A _ v (find' Ha) H = a.
Proof.
induction v as [| n' h t IH].
- now elim (has_nil Ha).
- destruct (eq_dec a h) as [e | ne] eqn:E; [subst h |].
  + destruct (@find' _ (@vec_cons A _ a t) a Ha) eqn:Habs; auto.
    now rewrite find'_cons_0 in Habs.
  + destruct (@find' (S n') (@vec_cons A n' h t) a Ha) eqn:Hcons.
    * assert (Htmp := find'_cons_2 Ha ne).
      now rewrite Hcons in Htmp.
    * destruct (nth_cons t h H) as [H' e]; auto with arith.
      rewrite e; clear e.
      revert H'. simpl. rewrite <- (minus_n_O n).
      intros H'.
      assert (Htmp := find'_cons_1 Ha (has_cons ne Ha) ne).
      rewrite Htmp in Hcons; clear Htmp.
      inversion Hcons as [H0]; clear Hcons.
      now subst n.
Qed.

Lemma nth_find n (v : vector A n) a (Ha : has v a) :
    @nth A _ v (find Ha) = a.
Proof.
unfold nth, find. simpl.
now apply nth_aux_find.
Qed.

End search.

Section map.

Variables A B : Type.

Fixpoint map n (v : vector A n) (f : A -> B) : vector B n :=
  match v with
    | vec_nil => vec_nil B
    | vec_cons n' h t => vec_cons (f h) (map t f)
  end.

Lemma nth_map n (v : vector A n) (f : A -> B) :
  forall i : {i | i < n},
    nth (map v f) i = f (nth v i).
Proof.
intros i.
induction v.
- now elim i.
- destruct i as [i Hi].
  revert Hi. destruct i as [| i]; auto.
  intros Hi.
  simpl.
  apply (IHv (exist _ i (lt_S_n _ _ Hi))).
Qed.

Lemma map_nth n (va : vector A n) (vb : vector B n) (f : A -> B) :
  (forall i : {i | i < n}, f (nth va i) = nth vb i) ->
  map va f = vb.
Proof.
induction va.
- now rewrite (empty vb).
- intros H.
  rewrite (split_vec vb).
  simpl.
  f_equal.
  + specialize H with (exist _ 0 (lt_0_Sn _)).
    unfold nth in H. simpl in H.
    now rewrite nth_0_is_head.
  + eapply IHva.
    intros [i Hi].
    rewrite (split_vec vb) in H.
    specialize H with (exist _ (S i) (lt_n_S _ _ Hi)).
    unfold nth in H. simpl in H.
    unfold nth. simpl.
    rewrite (nth_irrel va)
            with (H':=lt_S_n i n (lt_n_S i n Hi)).
    now rewrite (nth_irrel (tail vb))
            with (H':=lt_S_n i n (lt_n_S i n Hi)).
Qed.

End map.

Section orderings.

Variable A : Type.
Variable eq_dec : forall x y : A, {x = y} + {x <> y}.

Variable leA : relation A.
Variable leA_wf : well_founded leA.

(* Pointwise ordering on vectors *)
Inductive lp_vector : forall n, relation (vector A n) :=
| lp_nil : @lp_vector 0 (vec_nil A) (vec_nil A)
| lp_cons :
    forall a a' n v v',
      leA a a' ->
      @lp_vector n v v' ->
      @lp_vector (S n) (vec_cons a v) (vec_cons a' v').

Lemma lp_vector_nth n (v w : vector A n) :
  (forall i : {i | i < n}, leA (nth v i) (nth w i)) ->
  lp_vector v w.
Proof.
induction v.
- intros _. rewrite (empty w).
  now apply lp_nil.
- intros H.
  rewrite (split_vec w).
  apply lp_cons.
  + specialize H with (exist _ 0 (lt_0_Sn _)).
    unfold nth in H. simpl in H.
    now rewrite nth_0_is_head.
  + apply IHv.
    intros [i Hi].
    rewrite (split_vec w) in H.
    specialize H with (exist _ (S i) (lt_n_S _ _ Hi)).
    unfold nth in H. simpl in H.
    unfold nth. simpl.
    rewrite (nth_irrel v)
            with (H':=lt_S_n i n (lt_n_S i n Hi)).
    now rewrite (nth_irrel (tail w))
            with (H':=lt_S_n i n (lt_n_S i n Hi)).
Qed.

(* Lexicographical ordering on vectors *)
Inductive lex_vector : forall n, relation (vector A n) :=
| lex_vector_left :
    forall a a' n v v',
      leA a a' ->
      @lex_vector (S n) (vec_cons a v) (vec_cons a' v')
| lex_vector_right :
    forall a n v v',
      @lex_vector n v v' ->
      @lex_vector (S n) (vec_cons a v) (vec_cons a v').

Lemma lex_vector_Acc_step n :
  (forall v, Acc (@lex_vector n) v) ->
  forall a v,
    Acc (@lex_vector (S n)) (vec_cons a v).
Proof.
intros Hn a.
apply Acc_ind with (R := leA) (x:=a); auto; clear a.
intros a _ Ha.
intros v.
apply Acc_ind with (R := lex_vector (n:=n)) (x:=v); auto; clear v.
intros v _ Hv.
constructor.
intros w Hw. inversion Hw; subst.
- apply inj_pair2 in H0.
  apply inj_pair2 in H3.
  now subst; auto.
- apply inj_pair2 in H0.
  apply inj_pair2 in H3.
  now subst; auto.
Qed.

Lemma lex_vector_0_wf : well_founded (@lex_vector 0).
Proof.
intros v.
dependent inversion v.
constructor.
intros w Hw.
now inversion Hw.
Qed.

Lemma lex_vector_wf_step n :
  well_founded (@lex_vector n) ->
  well_founded (@lex_vector (S n)).
Proof.
intros H.
intros v.
dependent inversion v as [| ? a v']; subst.
constructor.
intros w Hw.
dependent inversion w as [| ? b w']; subst.
now apply lex_vector_Acc_step.
Qed.

Theorem lex_vector_wf n : well_founded (@lex_vector n).
Proof.
induction n as [| n IHn].
- now apply lex_vector_0_wf.
- now apply lex_vector_wf_step.
Qed.

End orderings.

Section lp_ascending.

Variable A : Type.
Variable eq_dec : forall x y : A, {x = y} + {x <> y}.

Variable leA : relation A.

Lemma lp_vector_to_lex_vector_inv n (v v' : vector A n) :
  strict (inv (lp_vector leA (n:=n))) v v' ->
  lex_vector (strict (inv leA)) v v'.
Proof.
induction v.
- rewrite (empty v').
  intros H. inversion H. now firstorder.
- rewrite (split_vec v').
  intros H.
  destruct H as [H Hconsv].
  case (eq_dec a (head v')) as [e | ne].
  + rewrite <- e.
    apply lex_vector_right.
    apply IHv; clear IHv.
    rewrite <- e in Hconsv.
    unfold inv in *.
    split.
    * inversion H; subst.
      apply inj_pair2 in H2.
      apply inj_pair2 in H5.
      now subst.
    * intros Hv. now subst; auto.
  + apply lex_vector_left.
    split; auto.
    unfold inv in *.
    now inversion H; subst.
Qed.

Lemma asc_lp_vector n :
  ascending_chain leA ->
  ascending_chain (lp_vector leA (n:=n)).
Proof.
unfold ascending_chain.
intros H.
apply wf_incl with (@lex_vector A (strict (inv leA)) n).
- unfold inclusion. now apply lp_vector_to_lex_vector_inv.
- now apply lex_vector_wf.
Qed.

End lp_ascending.
