Require Import Rels.
Require Import Classical.
Require Import Epsilon.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section noetherian.

Variable A : Type.
Variable leA : relation A.

Definition noetherian :=
  forall c : nat -> A, ~ (forall i, leA (c (S i)) (c i)).

Definition not_acc_inv (x : {n | ~ Acc leA n})
  : {n | leA n (proj1_sig x) /\ ~ Acc leA n}.
Proof.
destruct x as [x Hx].
apply constructive_indefinite_description.
apply not_all_not_ex.
intros H.
assert (Habs : Acc leA x).
{ apply Acc_intro. intros y Hy.
  specialize H with y. tauto. }
easy.
Defined.

Lemma not_acc_inv_leA (x : {n | ~ Acc leA n}) :
  let a := not_acc_inv x in
    leA (proj1_sig a) (proj1_sig x).
Proof.
destruct x as [x Hx].
simpl.
unfold not_acc_inv.
assert (Htmp :=
        proj2_sig (
          (constructive_indefinite_description
           _
           (not_all_not_ex A (λ n : A, leA n x ∧ ¬Acc leA n)
              (λ H : ∀ n : A, ¬(leA n x ∧ ¬Acc leA n),
               False_ind False
                 (Hx
                    (Acc_intro x
                       (λ (y : A) (Hy : leA y x),
                        NNPP (Acc leA y)
                          (λ H0 : ¬Acc leA y,
                           False_ind False (H y (conj Hy H0))))))))))).
now simpl in Htmp.
Qed.

Definition not_acc_chain (x : {n | ~ Acc leA n})
  : nat -> {k | ~ Acc leA k}.
Proof.
destruct x as [x Hx].
intros n. induction n as [| n IHn].
- now exists x.
- idtac.
  exists (proj1_sig (not_acc_inv IHn)).
  assert (Htmp := proj2_sig (not_acc_inv IHn)).
  now simpl in Htmp.
Defined.

Lemma not_acc_chain_0 (x : {n | ~ Acc leA n}) :
  let c := not_acc_chain x in
    c 0 = x.
Proof. now destruct x as [x Hx]. Qed.

Lemma not_acc_chain_S (x : {n | ~ Acc leA n}) k :
  let c := not_acc_chain x in
    proj1_sig (c (S k)) =
      proj1_sig (not_acc_inv (c k)).
Proof. now destruct x as [x Hx]. Qed.

Lemma not_acc_chain_chain (x : {n | ~ Acc leA n}) :
  let c := not_acc_chain x in
    forall i, leA (proj1_sig (c (S i))) (proj1_sig (c i)).
Proof.
intros c i. unfold c. rewrite not_acc_chain_S.
generalize (not_acc_chain x i).
intros a.
now apply not_acc_inv_leA.
Qed.

(* <- is provable classically *)
Theorem wf_noetherian :
  well_founded leA <-> noetherian.
Proof.
split.
- intros Hwf.
  pose (P := fun x:A =>
               forall c,
                 ~ (c 0 = x /\ forall i, leA (c (S i)) (c i))).
  cut (forall x:A, P x).
  { unfold P. intros H c. specialize H with (c 0) c.
    now firstorder. }
  apply well_founded_ind with (R:=leA); auto.
  intros x Hx. unfold P.
  intros c [? Hc]; subst x.
  specialize Hx with (c 1).
  assert (H1 : P (c 1)) by firstorder.
  clear Hx.
  unfold P in H1.
  specialize H1 with (fun i => c (S i)).
  simpl in H1.
  now intuition.
- idtac. intros Hnoe.
  destruct (classic (well_founded leA)) as [? | Hnwf]; auto.
  unfold well_founded in Hnwf.
  apply not_all_ex_not in Hnwf.
  destruct Hnwf as [x Hx].
  assert (e : {x | ~ Acc leA x}) by (exists x; auto).
  pose (c := fun i => proj1_sig (not_acc_chain e i)).
  assert (Hc : forall i, leA (c (S i)) (c i))
    by (apply not_acc_chain_chain).
  now apply Hnoe in Hc.
Qed.

End noetherian.
