Require Import Misc.
Require Export Monads.
Require Import Strategy.
Require Import List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section utils.

Variable A B C : Type.

Definition instr (T : monadType) (f : A -> T B)
  : A -> (StateT (list (A * B)) T) B
  := fun a l =>
       tbind (f a) (fun b => tval _ (b, (l ++ [(a,b)]))).

Fixpoint deps (t : Tree A B C) (f : A -> B) : list (A * B) :=
  match t with
    | Ans _ => nil
    | Que x k => let d := f x in (x, d) :: deps (k d) f
  end.

Definition deps_1 (t : Tree A B C) (f : A -> B) : list (A * B) :=
  let f' : A -> State (list (A * B)) B := @instr Id f in
    snd ([[t]] _ f' []).

Lemma deps_1_app (t : Tree A B C) (f : A -> B)
                 (l : list (A * B)) :
  let f' : A -> State (list (A * B)) B := @instr Id f in
    snd ([[t]] (State (list (A * B))) f' l) =
    l ++ snd ([[t]] (State (list (A * B))) f' []).
Proof.
intros f'.
revert l.
induction t as [| a k IHt].
- simpl. intros l; now rewrite app_nil_r.
- intros l. simpl.
  rewrite IHt. rewrite <- app_assoc. now rewrite <- IHt.
Qed.

Lemma deps_are_same t f : deps t f = deps_1 t f.
Proof.
induction t as [| a k IHt].
- now unfold deps_1.
- simpl. unfold deps_1; simpl.
  rewrite deps_1_app; simpl.
  now rewrite IHt.
Qed.

Definition valid (f : A -> B) (path : list (A * B)) :=
  forall p, In p path -> let (a, b) := p in b = f a.

Fixpoint legal (t : Tree A B C) (path : list (A * B)) :=
  match t, path with
    | _, nil => True
    | Ans _, _ :: _ => False
    | Que x k, (a, b) :: ps => a = x /\ legal (k b) ps
  end.

Fixpoint subtree (t : Tree A B C) (path : list (A * B)) :=
  match t, path with
    | _, nil => t
    | Ans _, _ => t
    | Que x k, (_, b) :: ps => subtree (k b) ps
  end.

Lemma subtree_nil t : subtree t [] = t.
Proof. now destruct t. Qed.
Hint Resolve subtree_nil.

Lemma subtree_nil_eq t t' :
  subtree t [] = t' -> t = t'.
Proof. now rewrite subtree_nil. Qed.

Lemma subtree_cons t l1 l2 :
  subtree t (l1 ++ l2) = subtree (subtree t l1) l2.
Proof.
revert t l2.
induction l1 as [| [a b] l IH].
- intros t l2. now rewrite app_nil_l, subtree_nil.
- intros t l2.
  rewrite <- app_comm_cons.
  destruct t as [c | a0 t].
  + simpl. now destruct l2.
  + simpl. now rewrite IH.
Qed.

Lemma subtree_step t l x k v :
  subtree t l = Que x k ->
  subtree t (l ++ [(x, v)]) = k v.
Proof.
revert t.
induction l as [| [a b] ps IH].
- intros t e.
  rewrite app_nil_l.
  now rewrite (subtree_nil_eq e); simpl.
- intros t Hsub.
  rewrite subtree_cons, Hsub.
  simpl.
  now rewrite subtree_nil.
Qed.

Lemma subtree_Que x k l c :
  subtree (Que x k) l = Ans c ->
  exists p ps, l = p :: ps.
Proof.
intro H. destruct l as [| p ps]; eauto.
now elim (subtree_nil_eq H).
Qed.

Lemma valid_nil f : valid f nil.
Proof. now firstorder. Qed.
Hint Resolve valid_nil.

Lemma valid_cons_elim f p l :
  valid f (p :: l) -> valid f l.
Proof. now firstorder. Qed.

Lemma valid_cons f a l :
  valid f l -> valid f ((a, f a) :: l).
Proof.
intro H. intros p H1. now inversion H1; subst; firstorder.
Qed.
Hint Resolve valid_cons.

Lemma valid_compat f1 f2 l :
  (forall p, In p l -> f1 (fst p) = f2 (fst p)) ->
  valid f1 l -> valid f2 l.
Proof.
intros Hcomp.
induction l as [| [a b] l IH]; auto.
- intros Hval [x y] H.
  assert (Ex : f1 x = f2 x) by firstorder. rewrite <- Ex; clear Ex.
  case (in_inv H) as [e | i].
  + inversion e; subst; now firstorder.
  + now firstorder.
Qed.

Lemma legal_Ans l c : legal (Ans c) l -> l = nil.
Proof. destruct l; now firstorder. Qed.

Lemma legal_nil t : legal t nil.
Proof. case t; now firstorder. Qed.
Hint Resolve legal_nil.

Lemma legal_cons_elim t p l :
  legal t (p :: l) -> exists f, t = Que (fst p) f.
Proof.
intro H. destruct t as [| x k].
- now firstorder.
- exists k. f_equal. destruct p as [a b]. now firstorder.
Qed.

Lemma legal_step t l x k v :
  legal t l ->
  subtree t l = Que x k ->
  legal t (l ++ [(x,v)]).
Proof.
revert t.
induction l as [| [a b] ps IH].
- intros t _ e.
  rewrite app_nil_l.
  now rewrite (subtree_nil_eq e); simpl; auto.
- intros t Hleg Hsub.
  rewrite <- app_comm_cons.
  elim (legal_cons_elim Hleg); intros k1 e.
  simpl in e; subst t.
  now firstorder.
Qed.

Lemma deps_valid t f : valid f (deps t f).
Proof.
induction t as [| x k H]; now simpl; auto.
Qed.
Hint Resolve deps_valid.

Lemma deps_legal t f : legal t (deps t f).
Proof.
induction t as [| x k H]; now simpl; auto.
Qed.
Hint Resolve deps_legal.

Lemma deps_subtree t sigma :
  let c := [[t]]* sigma in
  subtree t (deps t sigma) = Ans c.
Proof.
intro c. induction t as [| x k H]; now firstorder.
Qed.
Hint Resolve deps_subtree.

Lemma deps_val t f :
  forall p, In p (deps t f) -> snd p = f (fst p).
Proof.
induction t; now firstorder; subst.
Qed.

Lemma deps_split_val t f ps :
  ps = deps t f ->
  forall x, In x (fst (split ps)) -> In (x, f x) ps.
Proof.
revert t.
induction ps as [| [pa pb] ps IH].
- now intuition.
- intros t; case t as [c | a k].
  + now intuition.
  + simpl. intros H x Hin.
    destruct (split ps) as [ps1 ps2] eqn:Eps.
    inversion H; subst; clear H. simpl in *.
    destruct Hin; now intuition; eauto.
Qed.

Lemma deps_compat t l f1 f2 :
  l = deps t f1 ->
  (forall p, In p l -> f1 (fst p) = f2 (fst p)) ->
  deps t f1 = deps t f2.
Proof.
revert l.
induction t as [| a k IH ]; auto.
- intros l H H0. subst l. simpl.
  assert (e : f1 a = f2 a)
    by (apply (H0 (a, f1 a)); firstorder).
  rewrite <- e; clear e.
  f_equal. eapply IH; eauto. now firstorder.
Qed.

Lemma valid_app f l1 l2 :
  valid f l1 -> valid f l2 -> valid f (l1 ++ l2).
Proof.
intros H1 H2. intros p H.
apply in_app_or in H. now case H; firstorder.
Qed.

Lemma legal_app t t1 l1 l2 :
  legal t l1 ->
  subtree t l1 = t1 ->
  legal t1 l2 ->
  legal t (l1 ++ l2).
Proof.
revert t t1 l2.
induction l1 as [| [a b] l1 IH1]; simpl.
- intros t t1 l2 _ e. rewrite subtree_nil in e. now inversion e.
- intros t t1 l2 H1 H2 H3.
  elim (legal_cons_elim H1). intros k e1; subst.
  simpl in *. split; auto. destruct H1 as [_ H1].
  now eapply IH1; eauto.
Qed.

Lemma subtree_app t t1 t2 l1 l2 :
  subtree t l1 = t1 ->
  subtree t1 l2 = t2 ->
  subtree t (l1 ++ l2) = t2.
Proof.
revert t t1 t2 l2.
induction l1 as [| [a b] l1 IH1]; simpl.
- intros t t1 t2 l2 e. now rewrite (subtree_nil_eq e).
- intros t t1 t2 l2 H1 H2.
  rewrite app_comm_cons.
  now rewrite subtree_cons, H1.
Qed.

Lemma valid_legal_subtree_Ans t l sigma c :
  valid sigma l ->
  legal t l ->
  subtree t l = Ans c ->
  l = deps t sigma /\ c = [[t]]* sigma.
Proof.
revert t. induction l as [| [a b] ps IH].
- intros t Hval Hleg Hsub.
  now rewrite (subtree_nil_eq Hsub).
- intros t Hval Hleg Hsub.
  destruct (legal_cons_elim Hleg) as [k ?]; subst t.
  simpl in Hsub, Hleg. destruct Hleg as [_ Hleg].
  assert (e : b = sigma a) by (rewrite (Hval (a, b)); intuition).
  subst b. simpl. split.
  + f_equal. now apply IH; firstorder.
  + rewrite evaltree_Que. now apply IH; firstorder.
Qed.

Lemma deps_val_compat t l f1 f2 :
  l = deps t f1 ->
  (forall p, In p l -> f1 (fst p) = f2 (fst p)) ->
  [[t]]* f1 = [[t]]* f2.
Proof.
intros.
assert (Hdeps : deps t f1 = deps t f2)
  by (eapply deps_compat; eauto).
assert (Hf1 := deps_subtree t f1); simpl in Hf1.
assert (Hf2 := deps_subtree t f2); simpl in Hf2.
rewrite <- Hdeps, Hf1 in Hf2.
now inversion Hf2.
Qed.

(* unique lookup trees *)
Definition uniq_lookup t :=
  forall ps, legal t ps -> NoDup (fst (split ps)).

Lemma uniq_lookup_Que a k b :
  uniq_lookup (Que a k) -> uniq_lookup (k b).
Proof.
intros H ps Hleg.
red in H.
specialize H with ((a,b) :: ps).
assert (H0 :  NoDup (fst (split ((a, b) :: ps))))
  by firstorder.
clear - H0.
destruct (split ps) as [ps1 ps2] eqn:Hps.
simpl in *; rewrite Hps in H0; simpl in *.
now apply NoDup_remove_1 with (l:=[]) (a:=a).
Qed.
Hint Resolve uniq_lookup_Que.

Lemma uniq_Que_deps a k b f x y :
  uniq_lookup (Que a k) ->
  In (x,y) (deps (k b) f) ->
  x <> a.
Proof.
set (ps := deps (k b) f).
intros Huniq Hin e. simpl in e. subst x.
red in Huniq.
specialize Huniq with ((a,b) :: ps).
assert (Habs : NoDup (fst (split ((a,b) :: ps))))
  by (apply Huniq; simpl; now unfold ps; auto).
clear - Habs Hin.
apply in_split_l in Hin; simpl in Hin.
destruct (split ps) as [ps1 ps2] eqn:Hps.
simpl in *; rewrite Hps in Habs; simpl in *.
now apply NoDup_remove_2 with (l:=[]) (a:=a) in Habs.
Qed.

Lemma uniq_deps_f
        (Hdec : forall x y : A, {x = y} + {x <> y})
        t c f ps :
  uniq_lookup t ->
  legal t ps ->
  subtree t ps = Ans c ->
  exists f',
    deps t f' = ps /\
    valid f' ps /\
    let vs := fst (split ps) in
      forall x, ~ In x vs -> f x = f' x.
Proof.
revert t.
induction ps as [| [a b] ps IH].
- intros t Huniq Hleg Hsub.
  rewrite (subtree_nil_eq Hsub); clear dependent t.
  now exists f; auto.
- intros t Huniq Hleg Hsub.
  destruct (legal_cons_elim Hleg) as [k ?]; subst.
  specialize IH with (k b).
  assert (Huniq1 : uniq_lookup (k b)) by eauto.
  simpl in Hleg. destruct Hleg as [_ Hleg].
  simpl in Hsub.
  destruct IH as [f0 H]; auto.
  destruct H as [Hdepsf0 [Hvalf0 Hf0] ].
  pose (f1 := fun y => if Hdec y a then b else f0 y).
  assert (ea : f1 a = b)
    by (unfold f1; case Hdec; intuition). 
  exists f1.
  split; [| split].
  + simpl. rewrite ea. f_equal.
    rewrite <- Hdepsf0. symmetry.
    apply deps_compat with (l:=ps); auto.
    intros [pa pb] Hp. simpl.
    rewrite <- Hdepsf0 in Hp.
    assert (ne : pa <> a)
      by (eapply uniq_Que_deps; eauto).
    now unfold f1; case Hdec; intuition.
  + rewrite <- ea. apply valid_cons.
    apply valid_compat with (f1:=f0); auto.
    intros [pa pb] Hp. simpl.
    rewrite <- Hdepsf0 in Hp.
    assert (ne : pa <> a)
      by (eapply uniq_Que_deps; eauto).
    now unfold f1; case Hdec; intuition.
  + simpl.
    destruct (split ps) as [ps1 ps2] eqn:Hps.
    simpl in *.
    intros x Hx.
    case (Hdec x a); [now intuition |].
    case (in_dec Hdec x ps1); [now intuition |].
    intros Hnin ne.
    rewrite Hf0; auto.
    now unfold f1; case Hdec; intuition.
Qed.    

End utils.
