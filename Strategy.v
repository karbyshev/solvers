Require Export Monads.
Require Import Program.Basics.
Require Import Program.Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section functionals.
Variables A B C : Type.

Definition FuncType : Type
  := forall (T : monadType), (A -> T B) -> T C.

Definition FuncStateType : Type
  := forall S, (A -> State S B) -> State S C.
End functionals.

Section strategy.
Variables A B C : Type.

Inductive STree :=
  Ans : C -> STree
| Que : A -> (B -> STree) -> STree.

Fixpoint tree2funT (T : monadType) (t : STree) :=
  match t with
    | Ans c => fun k => tval T c
    | Que a f =>
        fun k => k a >>= (fun b => @tree2funT T (f b) k)
  end.

Definition tree2fun (t : STree) : FuncType A B C.
intro T. refine (tree2funT t).
Defined.

Lemma tree2fun_simpl (t : STree) (T : monadType) :
  @tree2fun t T = tree2funT t.
Proof. now unfold tree2fun. Qed.

Definition evaltree (t : STree) (f : A -> B)
  := @tree2fun t Id f.

Lemma evaltree_Que x k f :
  evaltree (Que x k) f = evaltree (k (f x)) f.
Proof. easy. Qed.

Definition evaltree_unit (t : STree) (f : A -> B)
  := fst ((@tree2fun t (State unit) (compose (@tval _ _) f)) ()).

Lemma evaltree_unit_Que x k f :
  evaltree_unit (Que x k) f = evaltree_unit (k (f x)) f.
Proof. easy. Qed.

Lemma evaltree_same (t : STree) (f : A -> B) :
  evaltree t f = evaltree_unit t f.
Proof. induction t; now firstorder. Qed.

(* Interpreter of trees for relations *)
Inductive wrap_rel_State {S}
  : STree -> (A -> S -> B * S -> Prop) -> S -> C * S -> Prop :=
  | wrapAns :
      forall (f : A -> S -> B * S -> Prop) c s,
        wrap_rel_State (Ans c) f s (c,s)
  | wrapQue :
      forall (f : A -> S -> B * S -> Prop) a k s d0 s0 ds1,
        f a s (d0, s0) ->
        wrap_rel_State (k d0) f s0 ds1 ->
        wrap_rel_State (Que a k) f s ds1.

Lemma wrap_rel_State_Ans_inv S c f s d1 s1 :
  @wrap_rel_State S (Ans c) f s (d1, s1) ->
  d1 = c /\ s1 = s.
Proof. intros H; now inversion H; subst. Qed.

Lemma wrap_rel_State_Que_inv S a k f s ds1 :
  @wrap_rel_State S (Que a k) f s ds1 ->
  exists d0 s0,
    f a s (d0, s0) /\ wrap_rel_State (k d0) f s0 ds1.
Proof. intros H; now inversion H; subst; eauto. Qed.

Lemma wrap_rel_State_fun S t
  (f : A -> S -> (B * S) -> Prop)
  (f' : A -> S -> (B * S) -> Prop)
  (Hfun : forall a s r r', f a s r -> f' a s r' -> r = r') :
  forall s ds1 ds1',
    @wrap_rel_State S t f s ds1 ->
    @wrap_rel_State S t f' s ds1' ->
    ds1 = ds1'.
Proof.
induction t as [c | a k IH].
- intros s [d1 s1] [d1' s1'] H H'.
  destruct (wrap_rel_State_Ans_inv H); subst.
  destruct (wrap_rel_State_Ans_inv H'); subst.
  easy.
- intros s [d1 s1] [d1' s1'] H H'.
  destruct (wrap_rel_State_Que_inv H) as [d0 [s0 [Hf H0] ] ].
  destruct (wrap_rel_State_Que_inv H') as [d0' [s0' [Hf' H0'] ] ].
  assert (H1 := Hfun _ _ _ _ Hf Hf').
  inversion H1; subst; clear H1.
  now firstorder.
Qed.

End strategy.

Implicit Arguments Ans [A B C].
Implicit Arguments Que [A B C].

Notation "[[ t ]]" := (@tree2fun _ _ _ (t : STree _ _ _)) (at level 60).
Notation "[[ t ]]*" := (@evaltree _ _ _ (t : STree _ _ _)) (at level 60).
Notation "[[ t ]]#" := (@wrap_rel_State _ _ _ _ (t : STree _ _ _)) (at level 60).

(*Definition isPure A B C (F : FuncType A B C)
  := exists t, forall (T : monadType), F T = [[t]] T.*)

Definition is_pure A B C (F : FuncType A B C)
  := {t | F = [[t]] }.
