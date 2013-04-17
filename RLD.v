Require Import MSets.MSetFacts.
Require Import MSets.MSetProperties.
Require Import MSets.MSetDecide.
Require Import FSets.FMapFacts.
Require Export Solvers.
Require Import RLDi.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SolverRLD (Sys : CSysJoinSemiLat)
                 (VSet : SetsTypeOn (Sys.V))
                 (VMap : MapsTypeOn (Sys.V)).

Module Var := Sys.V.
Module D <: JoinSemiLattice := Sys.D.

Module UtilD := UtilJoin (D).

Module Import VSetFacts := WFactsOn (Var) (VSet).
Module Import VSetProps := WPropertiesOn (Var) (VSet).
Module Import VSetDecide := WDecideOn (Var) (VSet).
Module Import VMapFacts := WFacts_fun (Var) (VMap).

Module VS := VSet.
Module Sigma := VMap.
Module Infl := VMap.

Definition F := Sys.F.

Module Import Defs := Solvers.Defs (Sys).

Module SI := SolverRLDInstr (Sys) (VSet) (VMap).

(*****************************************************************)
(*********** Non-instrumented algorithm specification ************)
(*****************************************************************)

Definition state :=
  (Sigma.t D.t * Infl.t (list Var.t) * VS.t)%type.

Ltac destruct_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
    destruct s as [ [sig inf] sta].

Ltac destruct_pose_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
    destruct s as [ [sig inf] sta];
    pose (s := (sig, inf, sta));
    fold s.

Definition setval (x : Var.t) d (s : state) : state :=
  let '(sigma, infl, stable) := s in
    (Sigma.add x d sigma, infl, stable).

Definition getval (s : state) x :=
  let '(sigma, _, _) := s in
    match Sigma.find x sigma with
      | Some d => d
      | None => D.bot
    end.

Lemma getval_eq (s1 s2 : state) :
  let '(sigma1, _, _) := s1 in
  let '(sigma2, _, _) := s2 in
    VMap.Equal sigma1 sigma2 ->
    getval s1 = getval s2.
Proof.
destruct_state s1. destruct_state s2. intro e.
extensionality x; simpl. now rewrite e.
Qed.

Definition get_infl (s : state) x : list (Var.t) :=
  let '(_, infl, _) := s in
    match Infl.find x infl with
      | Some l => l
      | None => []
    end.

Lemma get_infl_eq s1 s2 :
  let '(_, infl1, _) := s1 in
  let '(_, infl2, _) := s2 in
    VMap.Equal infl1 infl2 ->
    get_infl s1 = get_infl s2.
Proof.
destruct_state s1. destruct_state s2. intro e.
extensionality x; simpl. now rewrite e.
Qed.

Definition add_infl y x (s : state) : state :=
  let '(sigma, infl, stable) := s in
    let xs := get_infl s y in
    (sigma, Infl.add y (x :: xs) infl, stable).

Definition rem_infl x (s : state) : state :=
  let '(sigma, infl, stable) := s in
    (sigma, Infl.remove x infl, stable).

Definition is_stable x (s : state) :=
  let '(_, _, stable) := s in VS.In x stable.

Lemma is_stable_dec x s : {is_stable x s} + {~ is_stable x s}.
destruct_state s. simpl. now apply VSetProps.In_dec.
Qed.

Definition get_stable (s : state) :=
  let '(_, _, stable) := s in stable.

Definition add_stable x (s : state) : state :=
  let '(sigma, infl, stable) := s in
    (sigma, infl, VS.add x stable).

Definition rem_stable x (s : state) : state :=
  let '(sigma, infl, stable) := s in
    (sigma, infl, VS.remove x stable).

Definition prepare x s := add_stable x s.

Definition handle_work (w : list Var.t) (s : state) :=
    let f s x := rem_stable x s in
    List.fold_left f w s.

Definition extract_work (x : Var.t) (s : state) : (list Var.t * state)
  := let w := get_infl s x in
     let s := rem_infl x s in
     let s := handle_work w s in
       (w, s).

Lemma handle_work_spec s w s' :
  s' = handle_work w s ->
  let '(sigma, infl, stable) := s in
  let '(sigma', infl', stable') := s' in
    sigma' = sigma /\
    infl' = infl /\
    VS.Equal stable' (VS.diff stable (of_list w)).
Proof.
revert s s'.
induction w as [| x w IHw ].
- intros s s' H1. destruct_state s. destruct_state s'. simpl.
  inversion H1. now intuition; fsetdec.
- intros s s' H.
  remember (rem_stable x s) as s1.
  assert (H1 : s' = handle_work w s1) by (subst; auto).
  assert (H2 := IHw _ _ H1). clear IHw H1.
  destruct_state s. destruct_state s1. destruct_state s'.
  inversion Heqs1; subst; simpl.
  now intuition; fsetdec.
Qed.

Lemma extract_work_spec x s w s' :
  (w, s') = extract_work x s ->
  let '(sigma, infl, stable) := s in
  let '(sigma', infl', stable') := s' in
    w = get_infl s x /\
    sigma' = sigma /\
    infl' = Infl.remove x infl /\
    VS.Equal stable' (VS.diff stable (of_list w)).
Proof.
intro H. injection H as H1 Ew; clear H.
assert (H := handle_work_spec H1).
subst w. destruct_state s. destruct_state s'.
now simpl in *; intuition.
Qed.

Definition s_init : state
  := (Sigma.empty D.t,
      Infl.empty (list Var.t),
      VS.empty).

Section algorithm.

Variable Hpure : forall x, is_pure (F x).
Definition rhs x : Tree Var.t D.t D.t := proj1_sig (Hpure x).

Lemma rhs_spec x : F x = [[rhs x]].
Proof. now rewrite (proj2_sig (Hpure x)). Qed.

Inductive EvalGet :
  Var.t -> Var.t -> state -> D.t * state -> Prop :=
  | EvalGet0 :
      forall x y s s0,
        Solve y s s0 ->
        let s1 := add_infl y x s0 in
        let d := getval s0 y in
        EvalGet x y s (d, s1)

with EvalGet_x :
  Var.t -> (Var.t -> state -> D.t * state -> Prop) -> Prop :=
  | EvalGet_x0 :
      forall x (f : Var.t -> state -> D.t * state -> Prop),
        (forall y s0 ds1,
           f y s0 ds1 -> EvalGet x y s0 ds1) ->
        EvalGet_x x f

with Wrap_Eval_x :
  Var.t -> (Var.t -> state -> D.t * state -> Prop) ->
  @Tree Var.t D.t D.t ->
  state -> D.t * state -> Prop :=
  | Wrap_Eval_x0 :
    forall x f t s0 ds1,
      EvalGet_x x f ->
      [[t]]# f s0 ds1 ->
      Wrap_Eval_x x f t s0 ds1

with Eval_rhs :
  Var.t ->
  state -> D.t * state -> Prop :=
  | Eval_rhs0 :
    forall x f s0 ds1,
      EvalGet_x x f ->
      Wrap_Eval_x x f (rhs x) s0 ds1 ->
      Eval_rhs x s0 ds1

with Solve :
  Var.t -> state -> state -> Prop :=
  | Solve0 :
      forall x s, is_stable x s -> Solve x s s
  | Solve1 :
      forall x d s s2,
      ~ is_stable x s ->
      let s1 := prepare x s in
      Eval_rhs x s1 (d, s2) ->
      let cur_val := getval s2 x in
      D.Leq d cur_val ->
      Solve x s s2
  | Solve2 :
      forall x d s s2 s5 s6 work,
      ~ is_stable x s ->
      let s1 := prepare x s in
      Eval_rhs x s1 (d, s2) ->
      let cur_val := getval s2 x in
      ~ D.Leq d cur_val ->
      let new_val := D.join cur_val d in
      let s4 := setval x new_val s2 in
      (work, s5) = extract_work x s4 ->
      SolveAll work s5 s6 ->
      Solve x s s6

with SolveAll :
  list Var.t -> state -> state -> Prop :=
  | SolveAll0 :
      forall s, SolveAll [] s s
  | SolveAll2 :
      forall x xs s s1 s2,
        Solve x s s1 ->
        SolveAll xs s1 s2 ->
        SolveAll (x :: xs) s s2.

(* generate a mutual induction scheme *)
Scheme evalget_min   := Minimality for EvalGet Sort Prop
  with evalgetx_min  := Minimality for EvalGet_x Sort Prop
  with wrapevalx_min := Minimality for Wrap_Eval_x Sort Prop
  with evalrhs_min   := Minimality for Eval_rhs Sort Prop
  with solve_min     := Minimality for Solve Sort Prop
  with solveall_min  := Minimality for SolveAll Sort Prop.

Combined Scheme solve_mut_min from
  evalget_min,
  evalgetx_min,
  wrapevalx_min,
  evalrhs_min,
  solve_min,
  solveall_min.

Definition EvalGet_fun x y s ds1
  := forall ds1', EvalGet x y s ds1' -> ds1 = ds1'.

Definition EvalGet_x_fun x (f : Var.t -> state -> D.t * state -> Prop)
  := forall f',
       EvalGet_x x f' ->
       forall y s ds0 ds0',
         f y s ds0 -> f' y s ds0' -> ds0 = ds0'.

Definition Wrap_Eval_x_fun x (f : Var.t -> state -> D.t * state -> Prop) t s ds1
  := forall f' ds1',
       Wrap_Eval_x x f' t s ds1' ->
       (forall y s ds0 ds0',
          f y s ds0 -> f' y s ds0' -> ds0 = ds0') ->
       ds1 = ds1'.

Definition Eval_rhs_fun x s ds1
  := forall ds1', Eval_rhs x s ds1' -> ds1 = ds1'.

Definition Solve_fun x s s1
  := forall s1', Solve x s s1' -> s1 = s1'.

Definition SolveAll_fun (l : list Var.t) s s1
  := forall s1', SolveAll l s s1' -> s1 = s1'.

Lemma partial_functions_invar :
  (forall x y s1 ds2,
     EvalGet x y s1 ds2 -> EvalGet_fun x y s1 ds2) /\
  (forall x f,
    EvalGet_x x f -> EvalGet_x_fun x f) /\
  (forall x f t s1 ds2,
    Wrap_Eval_x x f t s1 ds2 ->
    Wrap_Eval_x_fun x f t s1 ds2) /\
  (forall x s1 ds2,
    Eval_rhs x s1 ds2 -> Eval_rhs_fun x s1 ds2) /\
  (forall x s1 s2,
    Solve x s1 s2 -> Solve_fun x s1 s2) /\
  (forall w s1 s2,
    SolveAll w s1 s2 -> SolveAll_fun w s1 s2).
Proof.
apply solve_mut_min.

(* EvalGet *)
- idtac. intros x y s s0 Hsol Isol s1 d.
  red. red in Isol.
  intros [d' s1'] Heval'.
  subst.
  inversion Heval' as [? ? ? ? Hsol']; subst; clear Heval'.
  assert (Htmp := Isol _ Hsol').
  unfold d, s1. now subst.

(* EvalGet_x *)
- idtac. intros x f Heval Ieval.
  red in Ieval. red.
  intros f' Heval'.
  intros y s ds0 ds0' Hf Hf'.
  inversion Heval'; subst. now firstorder.

(* Wrap_Eval_x *)
- idtac. intros x f.
  induction t as [c | a k IH].
  + intros s [d s0] Hevalx Ievalx Hf.
    red. intros f' [d' s0'] Hwrap Hfun.
    inversion Hwrap; subst; clear Hwrap.
    now eapply wrap_rel_State_fun; eauto.
  + intros s [d1 s1] Hevalx Ievalx HfQue.
    red.
    intros f' [d' s1'] Hf'Que Hff'.
    inversion Hf'Que; subst.
    now eapply wrap_rel_State_fun; eauto.

(* Eval_rhs *)
- idtac. intros x f s ds0 Hevalx Ievalx Hwrap Iwrap.
  red. intros ds0' Heval.
  red in Iwrap.
  inversion Heval; subst; clear Heval.
  now eapply Iwrap; eauto.

(* Solve 0 *)
- idtac. intros x s Hstaxs.
  red. intros s0' Hsol'.
  now inversion Hsol'.

(* Solve 1 *)
- idtac.
  intros x d1 s s1 Hnstaxs s0 Heval Ieval cur Hleq.
  red. intros s1' Hsol'.
  red in Ieval.
  inversion Hsol' as [| ? ? ? ? ? s0' Heval' |];
    [subst s1'; easy |  |].
  + unfold s0' in Heval'.
    assert (Htmp := Ieval _ Heval').
    now inversion Htmp.
  + subst s2 s6.
    assert (Htmp := Ieval _ H0).
    inversion Htmp.
    unfold cur_val0 in H1.
    unfold cur in Hleq.
    now rewrite <- H7, <- H6 in H1.

(* Solve 2 *)
- idtac.
  intros x d1 s s1 s3 s4 w.
  intros Hnstaxs s0 Heval Ieval.
  intros cur Hnleq new s2 Hwork Hsolall Isolall.
  red. intros s4' Hsol'.
  inversion Hsol' as [| ? ? ? ? ? s0' Heval' |];
    [subst s4'; easy |  |].
  + unfold cur in Hnleq.
    unfold cur_val in H0.
    red in Ieval.
    assert (Htmp := Ieval _ Heval').
    inversion Htmp; subst s4' d; clear Htmp.
    now rewrite <- H6 in H0.
  + clear H Hnstaxs.
    assert (Htmp := Ieval _ H0); clear Heval Ieval.
    inversion Htmp; clear Htmp.
    unfold new, cur in s2.
    unfold new_val, cur_val in s10.
    unfold s2 in Hwork.
    unfold s10 in H2.
    rewrite <- H8, H4 in H2.
    assert (Hw : (w,s3) = (work,s7))
      by (rewrite Hwork, H2, H7; auto).
    inversion Hw; subst s7 work.
    now eapply Isolall; eauto.

(* SolveAll 0 *)
- idtac.
  intros s. red. intros s0' Hsolall'.
  now inversion Hsolall'; subst.

(* SolveAll 1 *)
- idtac.
  intros x xs s s0 s1 Hsol Isol Hsolall Isolall.
  red. intros s1' Hsolall'.
  inversion Hsolall' as [| ? ? ? s1'' ? Hsol'' Hsolall''];
    subst; auto.
  red in Isol. assert (e := Isol _ Hsol''); subst s1''.
  red in Isolall. now apply Isolall; auto.
Qed.

(* a nicer reformulation of partial_functions_invar: *)
Lemma partial_functions :
  (forall x y s1 ds2 ds2',
     EvalGet x y s1 ds2 ->
     EvalGet x y s1 ds2' -> ds2 = ds2') /\
  (forall x y f f' s ds ds',
    EvalGet_x x f ->
    EvalGet_x x f' ->
    f y s ds -> f' y s ds' -> ds = ds') /\
  (forall x f f' t s1 ds2 ds2',
    Wrap_Eval_x x f t s1 ds2 ->
    Wrap_Eval_x x f' t s1 ds2' ->
    (forall y s ds ds',
       f y s ds -> f' y s ds' -> ds = ds') ->
    ds2 = ds2') /\
  (forall x s1 ds2 ds2',
    Eval_rhs x s1 ds2 -> Eval_rhs x s1 ds2' -> ds2 = ds2') /\
  (forall x s1 s2 s2',
    Solve x s1 s2 -> Solve x s1 s2' -> s2 = s2') /\
  (forall w s1 s2 s2',
    SolveAll w s1 s2 -> SolveAll w s1 s2' -> s2 = s2').
Proof.
pose proof partial_functions_invar as H.
unfold EvalGet_fun, EvalGet_x_fun, Wrap_Eval_x_fun,
  Eval_rhs_fun, Solve_fun, SolveAll_fun in H.
destruct H as [Hevalget [Hevalgetx [Hwrap [Heval [Hsol Hsolall] ] ] ] ].
split; [| split; [| split; [| split; [| split] ] ] ].
- intros; now eapply Hevalget; eauto.
- intros; now eapply Hevalgetx; [refine H | refine H0 | |]; eauto.
- intros; now eapply Hwrap; eauto.
- intros; now eapply Heval; eauto.
- intros; now eapply Hsol; eauto.
- intros; now eapply Hsolall; eauto.
Qed.

Section instrumentation.

(*Definition state := S.state.*)
Definition state' := SI.state'.

Definition projI (si : state') : state :=
  let '(sigma, infl, stable, _, _) := si in
    (sigma, infl, stable).

Definition sim (s : state) (si : state') := projI si = s.

(* lifted simulation relation *)
Definition simT
  (f : Var.t -> State state D.t)
  (f' : Var.t -> State state' D.t)
  := forall x s s1 s' s1' d d',
       sim s s' ->
       f x s = (d, s1) ->
       f' x s' = (d', s1') ->
       d = d' /\ sim s1 s1'.

(* lifted simulation relation *)
(*Definition simTrel
  (f : Var.t -> state -> D.t * state -> Prop)
  (f' : Var.t -> state' -> D.t * state' -> Prop)
  := forall x s s1 s' s1' d d',
       sim s s' ->
       f x s (d, s1) ->
       f' x s'(d', s1') ->
       d = d' /\ sim s1 s1'.*)

Definition simTrel
  (f : Var.t -> state -> D.t * state -> Prop)
  (f' : Var.t -> state' -> D.t * state' -> Prop)
  := forall x s s1 s' d,
       sim s s' ->
       f x s (d, s1) ->
       exists ds1',
       f' x s' ds1' /\
       let (d',s1') := ds1' in
       d = d' /\ sim s1 s1'.

Lemma sim_init : sim s_init SI.s_init.
easy.
Qed.

Ltac destruct_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
    destruct s as [ [sig inf] sta].

Ltac destruct_state' s :=
  let sig := fresh "sigma'" in
  let inf := fresh "infl'" in
  let sta := fresh "stable'" in
  let cal := fresh "called'" in
  let que := fresh "queued'" in
    destruct s as [ [ [ [sig inf] sta] cal] que].

Lemma sim_projI s' : sim (projI s') s'.
now destruct_state' s'.
Qed.
Hint Resolve sim_projI.

Lemma sim_prepare x s s' (H : sim s s') :
  sim (prepare x s) (SI.prepare x s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_prepare.

Lemma sim_getval s s' (H : sim s s') :
  getval s = SI.getval s'.
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_getval.

Lemma sim_setval x d s s' (H : sim s s') :
  sim (setval x d s) (SI.setval x d s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_setval.

Lemma sim_add_infl x y s s' (H : sim s s') :
  sim (add_infl x y s) (SI.add_infl x y s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_add_infl.

Lemma sim_is_stable x s s' (H : sim s s') :
  is_stable x s <-> SI.is_stable x s'.
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_is_stable.

Lemma sim_add_stable x s s' (H : sim s s') :
  sim (add_stable x s) (SI.add_stable x s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_add_stable.

Lemma sim_rem_called x s s' (H : sim s s') :
  sim s (SI.rem_called x s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_rem_called.

Lemma sim_rem_queued x s s' (H : sim s s') :
  sim s (SI.rem_queued x s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_rem_queued.

Lemma sim_handle_work s s' w (H : sim s s') :
  sim (handle_work w s) (SI.handle_work w s').
Proof.
revert s s' H. induction w as [| x xs IH].
- now firstorder.
- intros s s' Hsims. simpl.
  destruct_state s.
  destruct_state' s'.
  apply IH. now inversion Hsims.
Qed.
Hint Resolve sim_handle_work.

Lemma sim_extract_work x s s' w w' s0 s0' (H : sim s s') :
  (w, s0) = extract_work x s ->
  (w', s0') = SI.extract_work x s' ->
  w = w' /\ sim s0 s0'.
Proof.
destruct_state s.
destruct_state' s'.
intros Hw Hw'.
assert (Ew : w = w')
  by (inversion Hw; inversion Hw'; now inversion H; subst).
split; auto.
- subst w'. inversion H; subst.
  inversion Hw. inversion Hw'. now apply sim_handle_work.
Qed.

(* simulation 'invariants' *)
Definition EvalGet_sim x y s ds1
  := forall s',
       sim s s' ->
       exists ds1',
         let '(d,s1) := ds1 in
         let '(d',s1') := ds1' in
       SI.EvalGet Hpure x y s' (d',s1') /\
       d = d' /\ sim s1 s1'.

Definition EvalGet_x_sim (x : Var.t)
                         (f : Var.t -> state -> D.t * state -> Prop)
  := exists f', SI.EvalGet_x Hpure x f' /\ simTrel f f'.

Definition Wrap_Eval_x_sim x f t s ds1
  := forall f' s' l',
       sim s s' ->
       simTrel f f' ->
       SI.EvalGet_x Hpure x f' ->
       exists ds1' l1',
         let '(d,s1) := ds1 in
         let '(d',s1') := ds1' in
       SI.Wrap_Eval_x Hpure x f' t (s',l') (d',(s1',l1')) /\
       d = d' /\ sim s1 s1'.

Definition Eval_rhs_sim x s ds1
  := forall s',
       sim s s' ->
       exists ds1' l',
         let '(d,s1) := ds1 in
         let '(d',s1') := ds1' in
       SI.Eval_rhs Hpure x s' (d',(s1',l')) /\
       d = d' /\ sim s1 s1'.

Definition Solve_sim x s s1
  := forall s',
       sim s s' ->
       exists s1',
         SI.Solve Hpure x s' s1' /\ sim s1 s1'.

Definition SolveAll_sim (l : list Var.t) s s1
  := forall s',
       sim s s' ->
       exists s1',
         SI.SolveAll Hpure l s' s1' /\ sim s1 s1'.

Require Import Classical.
Require Import Epsilon.
Require Import ChoiceFacts.

Theorem simulation :
  (forall x y s1 ds2,
     EvalGet x y s1 ds2 -> EvalGet_sim x y s1 ds2) /\
  (forall x f,
    EvalGet_x x f -> EvalGet_x_sim x f) /\
  (forall x f t s1 ds2,
    Wrap_Eval_x x f t s1 ds2 ->
    Wrap_Eval_x_sim x f t s1 ds2) /\
  (forall x s1 ds2,
    Eval_rhs x s1 ds2 -> Eval_rhs_sim x s1 ds2) /\
  (forall x s1 s2,
    Solve x s1 s2 -> Solve_sim x s1 s2) /\
  (forall w s1 s2,
    SolveAll w s1 s2 -> SolveAll_sim w s1 s2).
Proof.
apply solve_mut_min.

(* EvalGet *)
- idtac.
  intros x y s s0 Hsol Hsolsim s1 d.
  red. intros s' Hsims.
  red in Hsolsim.
  elim (Hsolsim _ Hsims); intros s0' [Hsol' Hsims0].
  pose (d' := SI.getval s0' y).
  assert (e : d = d')
    by (subst d; unfold d'; now erewrite sim_getval).
  pose (s1' := SI.add_infl y x s0').
  assert (Hsims1 : sim s1 s1')
    by (subst s1; apply sim_add_infl; auto).
  exists (d',s1').
  split; [| split]; try apply SI.EvalGet0; easy.

(* Eval_x *)
- idtac.
  intros x f H H0.
  red. red in H0.
  pose (f' := fun y s' ds1' =>
          let '(d',s1') := ds1' in
          match (constructive_definite_descr_excluded_middle
                   constructive_definite_description
                   classic)
                  (f y (projI s') (d',(projI s1'))) with
            | right _ => False
            | left e =>
                let ds1'' :=
                    proj1_sig
                      (constructive_indefinite_description
                         _
                         (H0 y (projI s') (d',(projI s1'))
                             e s' (sim_projI s'))
                      ) in
                ds1'' = ds1'
          end).
  exists f'.
  split.
  + apply SI.EvalGet_x0.
    intros y s' [d' s0'] Hf'.
    unfold f' in Hf'.
    simpl in Hf'.
    destruct
      (constructive_definite_descr_excluded_middle
         constructive_definite_description classic
         (f y (projI s') (d', projI s0'))); try easy.
    assert (Hf'0 :=
            proj2_sig
              (constructive_indefinite_description
                 _
                 (H0 y (projI s') (d', projI s0') f0 s' (sim_projI s')))).
    now rewrite Hf' in Hf'0.
  + red. intros y s s0 s' d Hsims Hf.
    destruct (H0 _ _ _ Hf _ Hsims)
             as [ [d' s0'] [Heval' [? Hsims0] ] ]; subst d'.
    exists (d,s0').
    split; [| now auto].
    unfold f'.
    change (
        match
          constructive_definite_descr_excluded_middle
            constructive_definite_description classic
            (f y (projI s') (d, projI s0'))
        with
          | left e =>
              proj1_sig
                (constructive_indefinite_description
                   _
                   (H0 y (projI s') (d, projI s0')
                       e s' (sim_projI s'))) =
            (d, s0')
          | right _ => False
        end
      ).
    assert (Hfproj : f y (projI s') (d, projI s0')).
    { rewrite Hsims. red in Hsims0; now rewrite Hsims0. }
    destruct
      (constructive_definite_descr_excluded_middle
         constructive_definite_description classic
         (f y (projI s') (d, projI s0'))) as [p | n]; auto.
    assert (eHf : p = Hfproj) by (apply proof_irrelevance).
    subst p.
    set (p' :=
         proj1_sig
           (constructive_indefinite_description
              _
              (H0 y (projI s') (d, projI s0')
                  Hfproj s' (sim_projI s')))).
    assert (Hp' :=
            proj2_sig
              (constructive_indefinite_description
                 _
                 (H0 y (projI s') (d, projI s0') Hfproj s' (sim_projI s')))).
    simpl in Hp'. fold p' in Hp'.
    destruct p' as [pd' ps'].
    destruct Hp' as [Hp' _].
    now rewrite <- (proj1 (SI.partial_functions Hpure)
                     _ _ _ _ _ Heval' Hp').

(* Wrap_Eval_x *)
- idtac.
  intros x f.
  induction t as [a | q k IH].
  + idtac.
    intros s [d s0] Hevalx Hevalxsim Ht.
    destruct (wrap_rel_State_Ans_inv Ht); subst; clear Ht.
    red. intros f' s' l' Hsims Hsimf Hevalx'.
    exists (a,s'), l'.
    split; auto.
    apply SI.Wrap_Eval_x0; auto.
    now apply wrapAns.
  + intros s [d1 s1] Hevalx Hevalxsim Ht.
    destruct (wrap_rel_State_Que_inv Ht)
      as [d0 [s0 [Hf Hwrapf] ] ]; clear Ht.
    assert (Hwrapeval : Wrap_Eval_x_sim x f (k d0) s0 (d1, s1))
      by (apply IH; auto). clear IH.
    red. intros f' s' l' Hsims Hsimf Hevalx'.
    red in Hwrapeval.
    red in Hevalxsim.
    assert (Htmp := Hsimf _ _ _ _ _ Hsims Hf).
    destruct Htmp as [ [d' s0'] [Hf' [? Hsims0 ] ] ].
    subst d'.
    assert (Htmp := Hwrapeval f' s0' (l' ++ [(q,d0)]) Hsims0 Hsimf Hevalx').
    destruct Htmp as [ [d1' s1'] [l1' [Hwrapeval' [? Hsims1] ] ] ];
      clear Hwrapeval.
    subst d1'.
    exists (d1,s1'), l1'. split; auto.
    apply SI.Wrap_Eval_x0; auto.
    apply wrapQue with (d0:=d0) (s0:= (s0', l' ++ [(q,d0)])).
    * now apply SI.instrR0.
    * now inversion Hwrapeval'; subst.

(* Eval_rhs *)
- idtac.
  intros x f s [d s0] Hevalx Ievalx Hwrapx Iwrapx.
  red. intros s' Hsims.
  red in Ievalx. destruct Ievalx as [f' [Hevalx' Hsimff'] ].
  red in Iwrapx.
  destruct (Iwrapx f' _ [] Hsims) as [ [d' s0'] H]; auto.
  destruct H as [l1' [Hwrapeval' [e Hsims0] ] ].
  exists (d',s0'), l1'.
  split; [| split]; try apply (SI.Eval_rhs0 (f:=f')); easy.

(* Solve0 *)
- idtac.
  intros x s Hsta.
  red. intros s' Hsims.
  exists s'. split; auto.
  apply SI.Solve0. now eapply sim_is_stable; eauto.

(* Solve1 *)
- idtac.
  intros x d s s1 Hxnsta s0 Hevalrhs Hevalrhssim cur Hleq.
  red. intros s' Hsims.
  assert (Hxnsta' : ~ SI.is_stable x s')
    by (contradict Hxnsta; now eapply sim_is_stable; eauto).
  red in Hevalrhssim.
  pose (s0' := SI.prepare x s').
  assert (Hsims0 : sim s0 s0') by (apply sim_prepare; auto).
  destruct (Hevalrhssim _ Hsims0) as [ [d' s1'] [l1' [Hevalrhs' [e Hsims1] ] ] ].
  clear Hevalrhssim. subst d'.
  pose (s1'' := SI.rem_called x s1').
  pose (cur' := SI.getval s1'' x).
  assert (Hsims1' : sim s1 s1'') by (apply sim_rem_called; auto).
  assert (Hle' : SI.D.Leq d cur')
    by (unfold cur'; now erewrite <- sim_getval; eauto).
  exists s1''. split; auto.
  eapply (SI.Solve1); eauto.

(* Solve2 *)
- idtac.
  intros x d s s1 s4 s5 w.
  intros Hxnsta s0 Hevalrhs Hevalrhssim cur Hleq new s3 Hw Hsolall Hsolallsim.
  red. intros s' Hsims.
  assert (Hxnsta' : ~ SI.is_stable x s')
    by (contradict Hxnsta; now eapply sim_is_stable; eauto).
  red in Hevalrhssim.
  pose (s0' := SI.prepare x s').
  assert (Hsims0 : sim s0 s0') by (apply sim_prepare; auto).
  destruct (Hevalrhssim _ Hsims0) as [ [d' s1'] [l1' [Hevalrhs' [e Hsims1] ] ] ].
  clear Hevalrhssim. subst d'.
  pose (s2' := SI.rem_called x s1').
  pose (cur' := SI.getval s2' x).
  pose (new' := SI.D.join cur' d).
  assert (Hsims1' : sim s1 s2') by (apply sim_rem_called; auto).
  assert (Hnle' : ~ SI.D.Leq d cur')
    by (unfold cur'; now erewrite <- sim_getval; eauto).
  pose (s3' := SI.setval x new' s2').
  assert (Hsims3 : sim s3 s3').
  { unfold s3, s3', new, new', cur, cur'.
    rewrite <- (sim_getval Hsims1'). now apply sim_setval. }
  destruct (SI.extract_work x s3') as (w', s4') eqn:Hw'.
  assert (Htmp1 : w = w' /\ sim s4 s4')
    by (eapply sim_extract_work; eauto).
  destruct Htmp1 as [? Hsims4]; subst w'.
  destruct (Hsolallsim _ Hsims4) as [s5' [Hsolall' Hsims5] ].
  exists s5'. split; auto.
  now eapply (SI.Solve2); eauto.

(* SolveAll0 *)
- idtac.
  intros s.
  red. intros s' Hsims.
  exists s'. split; auto.
  now eapply (SI.SolveAll0); eauto.

(* SolveAll1 *)
- idtac.
  intros x xs s s0 s1 Hsols Hsolsim Hsolall Hsolallsim.
  red. intros s' Hsims.
  destruct (Hsolsim _ Hsims) as [s0' [Hsols'  Hsims0] ].
  destruct (Hsolallsim _ Hsims0) as [s1' [Hsolall'  Hsims1] ].
  exists s1'. split; auto.
  now eapply (SI.SolveAll2); eauto.
Qed.

End instrumentation.

Theorem correctness s w :
  SolveAll w s_init s ->
  (forall z, In z w -> is_stable z s) /\
  (forall z v d,
     is_stable z s ->
     In (v,d) (deps (rhs z) (getval s)) ->
     is_stable v s) /\
  (forall z,
     is_stable z s -> D.Leq ([[rhs z]]* (getval s)) (getval s z)).
Proof.
intros Hsolall.
apply simulation in Hsolall.
assert (Htmp := Hsolall _ sim_init).
destruct Htmp as [s' [Hsolall' Hsims] ].
apply SI.correctness in Hsolall'.
destruct Hsolall' as [H0 [H1 H2] ].
split; [| split].
- clear - Hsims H0.
  intros. now eapply sim_is_stable; eauto.
- clear - Hsims H1.
  rewrite <- (sim_getval Hsims) in H1.
  intros z v d Hsta Hin. apply <- (sim_is_stable v Hsims).
  eapply H1; [| refine Hin].
  now apply (sim_is_stable z Hsims).
- clear - H2 Hsims.
  intros z Hsta.
  rewrite <- (sim_getval Hsims) in H2.
  now apply -> (sim_is_stable z Hsims) in Hsta; auto.
Qed.

Theorem exactness :
  has_uniq_lookup rhs ->
  is_monotone rhs ->
  forall mu w s,
    is_solution rhs mu ->
    SolveAll w s_init s ->
    leqF (getval s) mu.
Proof.
intros Huniq Hmon mu w s Hsolmu Hsolall.
apply simulation in Hsolall.
assert (Htmp := Hsolall _ sim_init).
destruct Htmp as [s' [Hsolall' Hsims] ].
apply SI.exactness with (mu:=mu) in Hsolall'; try rewrite <- rhs_same; auto.
now rewrite (sim_getval Hsims).
Qed.

Section termination.

Require Import Rels.
Require Import Arith.
Require Import Omega.

(* We prove termination of RLD on the two assumptions: *)
Variable Hasc : ascending_chain D.Leq.

Variable varSet : {s : VS.t | forall x, VS.In x s}.
Let V := proj1_sig varSet.
Let cardV := VS.cardinal V.

Definition varVec :
  {n : nat &
    {v : vector Var.t n &
       forall x, {i : {k : nat | k < n} | nth v i = x}}}.
Proof.
pose (l := VS.elements V).
destruct (vector_of l) as [n v] eqn:Hl.
exists n, v.
intros x.
assert (Hx : has v x).
{ assert (Htmp:= InA_has).
  specialize Htmp with (l:=l) (a:=x).
  rewrite Hl in Htmp.
  apply Htmp; clear Htmp.
  apply elements_1.
  now apply (proj2_sig varSet). }
exists (find Var.eq_dec Hx).
now apply nth_find.
Defined.

Definition phi (f : Var.t -> D.t) : vector D.t _ :=
  let v := projT1 (projT2 varVec) in map v f.

Definition psi (dv : vector D.t (projT1 varVec)) : Var.t -> D.t :=
  fun x =>
    let v := projT1 (projT2 varVec) in
    let H := projT2 (projT2 varVec) in
    let i := proj1_sig (H x) in
      nth dv i.

Lemma psi_phi f : psi (phi f) = f.
extensionality x.
unfold phi, psi.
rewrite nth_map.
f_equal.
now apply (proj2_sig (projT2 (projT2 varVec) x)).
Qed.

Lemma phi_inj f g : phi f = phi g -> f = g.
Proof.
intros H.
rewrite <- (psi_phi f).
rewrite <- (psi_phi g).
now f_equal.
Qed.

(* TODO : rename lemmas *)
Let R_phi (R : relation D.t) : relation (Var.t -> D.t)
  := fun f g => lp_vector R (phi f) (phi g).

Lemma leqF_sub_inverse_lp_vector f g :
  leqF f g -> R_phi D.Leq f g. 
Proof.
intros H.
unfold R_phi.
apply lp_vector_nth.
intros i.
unfold phi.
now rewrite !nth_map.
Qed.

Lemma lem4 f g :
  strict (inv (leqF (X:=Var.t))) f g ->
  strict (inv (lp_vector D.Leq (n:=projT1 varVec)))
         (phi f) (phi g).
Proof.
intros [H ne].
unfold inv, strict.
unfold inv, strict in H.
split; [now apply leqF_sub_inverse_lp_vector |
        intros e; now apply phi_inj in e].
Qed.

Lemma lem4_bis :
  inclusion
    _
    (strict (inv (leqF (X:=Var.t))))
    (fun f g =>
       (strict (inv (lp_vector D.Leq (n:=projT1 varVec))))
         (phi f)
         (phi g)).
Proof.
unfold inclusion. intros f g.
now apply lem4.
Qed.

Lemma prec_1_wf :
  well_founded (strict (inv (leqF (X:=Var.t)))).
Proof.
pose (H := fun n => asc_lp_vector (D.eq_dec) (n:=n) Hasc).
unfold ascending_chain in H.
specialize H with (projT1 varVec).
apply wf_inverse_image with (f:=phi) in H.
now apply (wf_incl _ _ _ lem4_bis).
Qed.

Lemma subset_V s : VS.Subset s V.
Proof.
intros x _.
now apply (proj2_sig varSet).
Qed.
Hint Resolve subset_V.

Lemma le_cardVar s : VS.cardinal s <= cardV.
Proof.
now apply VSetProps.subset_cardinal; auto.
Qed.
Hint Resolve le_cardVar.

Lemma cardVar_equal_V s :
  VS.cardinal s = cardV ->
  VS.Equal s V.
Proof.
intros H.
apply subset_antisym; [now apply subset_V |].
intros x Hx.
destruct (VSetProps.In_dec x s) as [e | n]; auto.
assert (Hcard : VSet.cardinal s < VSet.cardinal V)
  by (apply VSetProps.subset_cardinal_lt with x; auto).
rewrite H in Hcard.
now apply Lt.lt_irrefl in Hcard.
Qed.

Definition strictS (R : relation VS.t) : relation VS.t :=
  fun s t => R s t /\ ~ VS.Equal s t.

Lemma card_Acc n :
  forall s,
    n + VS.cardinal s = cardV ->
    Acc (strictS (inv (VS.Subset))) s.
Proof.
apply (lt_wf_ind n); clear n.
intros n IH.
intros s H.
constructor.
intros t Ht.
unfold strictS, inv in Ht.
pose (d := VS.diff t s).
assert (Hd : ~ VS.Empty d).
{ clear - Ht.
  destruct Ht as [Hst Hne].
  contradict Hne. now fsetdec. }
assert (Hdcard : VS.cardinal d <> 0).
{ contradict Hd. now apply VSetProps.cardinal_inv_1. }
assert (Hdcardpos : VS.cardinal d > 0).
{ unfold gt. now apply neq_0_lt; auto. }
assert (Et : VS.Equal t (VS.union s d)) by fsetdec.
assert (Hs' : VS.cardinal t = VS.cardinal s + VS.cardinal d)
  by (rewrite Et; apply VSetProps.union_cardinal; now fsetdec).
pose (m := n - VS.cardinal d).
assert (Hdn : VS.cardinal d <= n).
{ apply plus_le_reg_l with (VS.cardinal s).
  rewrite (plus_comm _ n), H, <- Hs'.
  now auto. }
assert (Hm : m < n) by (apply lt_minus; auto).
assert (Hm1 : m + VS.cardinal t = cardV)
  by (unfold m; rewrite Hs', <- H; omega).
now apply IH with m.
Qed.

Lemma prec_2_wf : well_founded (strictS (inv VS.Subset)).
Proof.
unfold well_founded.
intros s.
pose (n := cardV - VS.cardinal s).
assert (Hcard : VS.cardinal s <= cardV) by auto.
assert (H : n + VS.cardinal s = cardV) by (unfold n; omega).
now apply card_Acc with n.
Qed.

Definition sigma_fun (sigma : Sigma.t D.t) : Var.t -> D.t :=
  fun x =>
    match Sigma.find x sigma with
      | Some d => d
      | None => D.bot
    end.

Lemma getval_sigma sigma infl stable :
  getval (sigma, infl, stable) = sigma_fun sigma.
Proof.
easy.
Qed.

Definition prec_sigma : relation (Sigma.t D.t) :=
  fun sigma1 sigma2 =>
    strict (inv (leqF (X:=Var.t))) (sigma_fun sigma1) (sigma_fun sigma2).

Lemma prec_sigma_irrefl s : ~ prec_sigma s s.
Proof.
now firstorder.
Qed.
Hint Resolve prec_sigma_irrefl.

Lemma prec_sigma_trans : transitive _ prec_sigma.
Proof.
intros s1 s2 s3.
unfold prec_sigma, strict, inv.
intros [H10 H11].
intros [H20 H21].
split.
- now eapply leqF_trans; eauto.
- contradict H11. rewrite <- H11 in H20.
  now apply leqF_antisym.
Qed.

Lemma prec_sigma_wf : well_founded prec_sigma.
Proof.
unfold prec_sigma.
apply wf_inverse_image with (f:=sigma_fun).
now apply prec_1_wf.
Qed.

Definition prec_stable : relation VS.t :=
  fun s1 s2 => strictS (inv VS.Subset) s1 s2.

Lemma prec_stable_irrefl s : ~ prec_stable s s.
Proof.
now firstorder.
Qed.
Hint Resolve prec_stable_irrefl.

Lemma prec_stable_trans : transitive _ prec_stable.
Proof.
intros s1 s2 s3.
unfold prec_stable, strict, inv.
intros [H10 H11].
intros [H20 H21].
split.
- now fsetdec.
- contradict H11. now fsetdec.
Qed.

Lemma prec_stable_wf : well_founded prec_stable.
Proof.
refine prec_2_wf.
Qed.

Definition prec_ss := lexprod prec_sigma prec_stable.

Lemma prec_ss_wf : well_founded prec_ss.
Proof.
apply lexprod_wf;
  [now apply prec_sigma_wf | now apply prec_stable_wf].
Qed.

Definition forget_infl (s : state) :=
  let '(sigma, _, stable) := s in (sigma, stable).

Definition prec_state : relation state :=
  fun s1 s2 => prec_ss (forget_infl s1) (forget_infl s2).

Lemma prec_state_wf : well_founded prec_state.
Proof.
unfold prec_state.
apply wf_inverse_image with (f:=forget_infl).
now apply prec_ss_wf.
Qed.

Local Infix "<" := prec_state (at level 70).

Lemma prec_state_irrefl s : ~ s < s.
Proof.
unfold prec_state, prec_ss.
destruct_state s. simpl.
intros H. inversion H; subst; now firstorder.
Qed.
Hint Resolve prec_state_irrefl.

Lemma prec_state_trans : transitive _ prec_state.
Proof.
intros s1 s2 s3.
unfold prec_state, prec_ss.
destruct_state s1.
destruct_state s2.
destruct_state s3.
simpl.
intros H1 H2.
inversion H1 as [? ? ? ? H10 | ? ? ? H10]; subst; clear H1.
- inversion H2 as [? ? ? ? H20 | ? ? ? H20]; subst; clear H2.
  + left. now eapply prec_sigma_trans; eauto.
  + now left.
- inversion H2 as [? ? ? ? H20 | ? ? ? H20]; subst; clear H2.
  + now left.
  + right. now eapply prec_stable_trans; eauto.
Qed.

Definition eq_state : relation state :=
  fun s1 s2 =>
    let '(sigma1, _, stable1) := s1 in
    let '(sigma2, _, stable2) := s2 in
      sigma1 = sigma2 /\ stable1 = stable2.

Lemma eq_state_refl : reflexive _ eq_state.
Proof.
intros s; now destruct_state s.
Qed.
Hint Resolve eq_state_refl.

Lemma eq_state_sym : symmetric _ eq_state.
Proof.
intros s1 s2.
destruct_state s1.
destruct_state s2.
intros [? ?].
now subst.
Qed.
Hint Resolve eq_state_sym.

Lemma eq_state_trans : transitive _ eq_state.
Proof.
intros s1 s2 s3.
destruct_pose_state s1.
destruct_pose_state s2.
destruct_pose_state s3.
intros H1 H2.
destruct H1 as [H10 H11]; destruct H2 as [H20 H21].
red. split; congruence.
Qed.

Definition precEq_state : relation state
  := fun s1 s2 => prec_state s1 s2 \/ eq_state s1 s2.

Local Infix "<=" := precEq_state (at level 70).

Lemma precEq_state_refl : reflexive _ precEq_state.
Proof.
now right; auto.
Qed.
Hint Resolve precEq_state_refl.

Lemma prec_eq_state s1 s2 s3 :
  s1 < s2 -> eq_state s2 s3 -> s1 < s3.
Proof.
destruct_state s1.
destruct_state s2.
destruct_state s3.
intros H1 H2. destruct H2.
inversion H1; subst; clear H1.
- now left.
- now right.
Qed.

Lemma eq_prec_state s1 s2 s3 :
  eq_state s1 s2 -> s2 < s3 -> s1 < s3.
Proof.
destruct_state s1.
destruct_state s2.
destruct_state s3.
intros H1 H2. destruct H1.
inversion H2; subst; clear H2.
- now left.
- now right.
Qed.

Lemma prec_precEq_state s1 s2 s3 :
  s1 < s2 -> s2 <= s3 -> s1 < s3.
Proof.
intros H1 H2. destruct H2 as [H2 | H2].
- now eapply prec_state_trans; eauto.
- now eapply prec_eq_state; eauto.
Qed.

Lemma precEq_prec_state s1 s2 s3 :
  s1 <= s2 -> s2 < s3 -> s1 < s3.
Proof.
intros H1 H2. destruct H1 as [H1 | H1].
- now eapply prec_state_trans; eauto.
- now eapply eq_prec_state; eauto.
Qed.

Lemma precEq_state_trans : transitive _ precEq_state.
Proof.
intros s1 s2 s3.
intros H1 H2.
destruct H1 as [H1 | H1]. 
- left. now eapply prec_precEq_state; eauto.
- destruct H2 as [H2 | H2].
  + left. now eapply eq_prec_state; eauto.
  + right. now eapply eq_state_trans; eauto.
Qed.

Lemma eq_precEq_state s1 s2 s3 :
  eq_state s1 s2 -> s2 <= s3 -> s1 <= s3.
Proof.
intros H1 H2. destruct H2 as [H2 | H2].
- left. now eapply eq_prec_state; eauto.
- right. now eapply eq_state_trans; eauto.
Qed.

Lemma precEq_eq_state s1 s2 s3 :
  s1 <= s2 -> eq_state s2 s3 -> s1 <= s3.
Proof.
intros H1 H2. destruct H1 as [H1 | H1].
- left. now eapply prec_eq_state; eauto.
- right. now eapply eq_state_trans; eauto.
Qed.

Lemma eq_state_add_infl x y s :
  eq_state (add_infl x y s) s.
Proof.
now destruct_state s.
Qed.
Local Hint Resolve eq_state_add_infl.

Lemma prec_prepare x s :
  ~ is_stable x s -> prepare x s < s.
Proof.
destruct_state s.
intros H. simpl in *.
unfold prec_state, prec_ss.
right.
unfold prec_stable, strictS, inv; simpl.
split; now fsetdec.
Qed.

Lemma precEq_invariant :
  (forall x y s1 ds2,
     EvalGet x y s1 ds2 ->
     let (d,s2) := ds2 in s2 <= s1) /\
  (forall x f,
     EvalGet_x x f ->
     forall y s1 ds2,
       f y s1 ds2 ->
       let (d,s2) := ds2 in s2 <= s1) /\
  (forall x f t s1 ds2,
     Wrap_Eval_x x f t s1 ds2 ->
     let (d,s2) := ds2 in s2 <= s1) /\
  (forall x s1 ds2,
     Eval_rhs x s1 ds2 ->
     let (d,s2) := ds2 in s2 <= s1) /\
  (forall x s1 s2,
     Solve x s1 s2 -> s2 <= s1) /\
  (forall w s1 s2,
     SolveAll w s1 s2 -> s2 <= s1).
Proof.
apply solve_mut_min.

(* EvalGet *)
- idtac. intros x y s s0 _ Isol s1 d.
  subst s1.
  now apply eq_precEq_state with (s2:=s0); auto.

(* EvalGet_x *)
- idtac. easy.

(* Wrap_Eval_x *)
- idtac. intros x f.
  induction t as [c | a k IH].
  + intros s [d s0] _ Ievalx Ht.
    now destruct (wrap_rel_State_Ans_inv Ht); subst.
  + intros s [d1 s1] Hevalx Ievalx Ht.
    destruct (wrap_rel_State_Que_inv Ht)
      as [d0 [s0 [Hf Hwrapf] ] ]; clear Ht.
    assert (H := Ievalx _ _ _ Hf).
    simpl in H.
    assert (H1 : s1 <= s0)
      by (eapply (@IH _ _ (d1,s1)); eauto).
    now eapply precEq_state_trans; eauto.

(* Eval_rhs *)
- idtac. now firstorder.

(* Solve 0 *)
- idtac. now auto.

(* Solve 1 *)
- idtac.
  intros x d s s1 Hnstaxs s0 _ Ievalrhs cur Hleq.
  assert (H : s0 < s) by (apply prec_prepare; auto).
  left. now eapply precEq_prec_state; eauto.

(* Solve 2 *)
- idtac.
  intros x d s s1 s3 s4 w.
  intros Hnstaxs s0 _ Ievalrhs cur Hnleq new s2 Hw _ Isolveall.
  assert (H : s0 < s) by (apply prec_prepare; auto).
  clear Hnstaxs.
  apply (precEq_state_trans Isolveall); clear Isolveall.
  left.
  apply (precEq_prec_state (s2:=s0)); auto.
  apply (@precEq_state_trans s3 s1 s0); auto.
  clear - Hnleq Hw.
  assert (Hwspec := extract_work_spec Hw); clear Hw.
  assert (Hvals1 : forall z, x <> z -> getval s3 z = getval s1 z).
  { clear - Hwspec. intros z ne.
    destruct_state s1; destruct_state s3.
    destruct Hwspec as [_ [H _ ] ].
    simpl in *; subst. now rewrite add_neq_o. }
  assert (Hvals1x : getval s3 x = D.join cur d).
  { clear - Hwspec.
    destruct_state s1; destruct_state s3.
    destruct Hwspec as [_ [H _ ] ].
    simpl in *; subst. now rewrite add_eq_o. }
  left. unfold prec_state, prec_ss.
  destruct_state s1.
  destruct_state s3.
  left. unfold prec_sigma, strict, inv.
  rewrite !getval_sigma in Hvals1.
  rewrite getval_sigma in Hvals1x.
  split.
  + intros u. destruct (Var.eq_dec x u) as [e | n].
    * subst u. rewrite Hvals1x.
      now apply D.JoinUnique.
    * now rewrite Hvals1; auto.
  + contradict Hnleq. unfold cur.
    rewrite getval_sigma, <- Hnleq, Hvals1x.
    now apply D.JoinUnique.

(* SolveAll 0 *)
- idtac. now auto.

(* SolveAll 1 *)
- idtac. intros x xs s s0 s1 _ Isolve _ Isolveall.
  now eapply precEq_state_trans; eauto.
Qed.

Lemma prec_call_SolveAll x s d s1 s3 w :
  ~ is_stable x s ->
  let s0 := prepare x s in
  Eval_rhs x s0 (d, s1) ->
  let cur_val := getval s1 x in
  ~ D.Leq d cur_val ->
  let new_val := D.join cur_val d in
  let s2 := setval x new_val s1 in
  (w, s3) = extract_work x s2 ->
  s3 < s.
Proof.
intros Hnstaxs s0 Evalrhs cur Hnleq new s2 Hw.
assert (H : s0 < s) by (apply prec_prepare; auto).
clear Hnstaxs.
apply precEq_invariant in Evalrhs.
apply (@prec_state_trans s3 s0 s); auto. clear H.
apply (prec_precEq_state (s2:=s1)); auto. clear Evalrhs.
assert (Hwspec := extract_work_spec Hw); clear Hw.
assert (Hvals1 : forall z, x <> z -> getval s3 z = getval s1 z).
{ clear - Hwspec. intros z ne.
  destruct_state s1; destruct_state s3.
  destruct Hwspec as [_ [H _ ] ].
  simpl in *; subst. now rewrite add_neq_o. }
assert (Hvals1x : getval s3 x = D.join cur d).
{ clear - Hwspec.
  destruct_state s1; destruct_state s3.
  destruct Hwspec as [_ [H _ ] ].
  simpl in *; subst. now rewrite add_eq_o. }
unfold prec_state, prec_ss.
destruct_state s1.
destruct_state s3.
left. unfold prec_sigma, strict, inv.
rewrite !getval_sigma in Hvals1.
rewrite getval_sigma in Hvals1x.
split.
+ intros u. destruct (Var.eq_dec x u) as [e | n].
  * subst u. rewrite Hvals1x.
    now apply D.JoinUnique.
  * now rewrite Hvals1; auto.
+ contradict Hnleq. unfold cur.
  now rewrite getval_sigma, <- Hnleq, Hvals1x.
Qed.

Theorem termination :
  forall x s1, exists s2, Solve x s1 s2.
Proof.
intros x s; revert s x.
apply (@well_founded_ind _ _ prec_state_wf
        (fun s => forall x, exists s2, Solve x s s2)); auto.
intros s IH x.
destruct (is_stable_dec x s) as [Hstaxs | Hnstaxs];
  [exists s; now apply Solve0 |].
pose (s0 := prepare x s).
assert (Hprecs0 : s0 < s) by (apply prec_prepare; auto).
assert (Heval: forall y s1,
                 s1 < s -> exists ds2, EvalGet x y s1 ds2).
{ intros y s1 Hprecs1.
  destruct (IH _ Hprecs1 y) as [s2 Hs2].
  pose (s3 := add_infl y x s2).
  pose (d := getval s2 y).
  exists (d, s3). now apply EvalGet0 with (s0:=s2). }
pose (f := (fun y s' ds1' => EvalGet x y s' ds1')
           : Var.t -> state -> D.t * state -> Prop).
assert (Hevalxf : EvalGet_x x f).
{ apply EvalGet_x0.
  intros y q0 [d q2] Hf. now firstorder. }
assert (H : forall t q,
              q < s -> exists ds1, Wrap_Eval_x x f t q ds1).
{ induction t as [c | a k IHt].
  - intros q _. exists (c,q).
    apply Wrap_Eval_x0; auto.
    now apply wrapAns.
  - intros q Hprecq.
    destruct (Heval a _ Hprecq) as [ [d0' s0'] Heval0'].
    assert (Hf : f a q (d0',s0')) by (unfold f; auto).
    assert (Hprecs0' : s0' < s).
    { apply precEq_prec_state with (s2:=q); auto.
      unfold f in Hf. now apply precEq_invariant in Hf. }
    destruct (IHt d0' _ Hprecs0') as [ [d1 s1] Hwrap']; clear IHt.
    exists (d1,s1). apply Wrap_Eval_x0; auto.
    eapply wrapQue; eauto. now inversion Hwrap'; subst. }
 destruct (H (rhs x) _ Hprecs0) as [ [d s1] Hwrapx]; clear H.
assert (Hevalrhs : Eval_rhs x s0 (d,s1))
  by (apply Eval_rhs0 with (f:=f); auto).
pose (cur := getval s1 x).
pose (new := D.join cur d).
destruct (D.eq_dec new cur) as [e | n].
- assert (Hleq : D.Leq d cur) by now rewrite <- e; subst.
  exists s1. now apply Solve1 with (d:=d); auto.
- assert (Hnleq : ~ D.Leq d cur).
  { contradict n. unfold new. now apply UtilD.joinSubsume2. }
  pose (s2 := setval x new s1).
  destruct (extract_work x s2) as [w s3] eqn: Hwork.
  symmetry in Hwork.
  assert (Hprecs3 : s3 < s)
    by (eapply prec_call_SolveAll; eauto).
  assert (H : forall l q, q < s -> exists s4, SolveAll l q s4).
  { induction l as [| y ys IHl].
    - intros q _. exists q. now apply SolveAll0.
    - intros q Hprecq.
      destruct (IH _ Hprecq y) as [s3' Hsol'].
      assert (Hprecs3' : s3' < s).
      { apply precEq_prec_state with (s2:=q); auto.
        now apply precEq_invariant in Hsol'. }
      destruct (IHl _ Hprecs3') as [s4 Hsolall']; clear IHl.
      exists s4. now eapply SolveAll2; eauto. }
  destruct (H w _ Hprecs3) as [s4 Hsolall].
  exists s4. now eapply Solve2; eauto.
Qed.

End termination.

End algorithm.

End SolverRLD.

(* TODO this should go elsewhere actually *)
Module SolverRLDcomplete (Sys : CSys)
                         (VSet : SetsTypeOn (Sys.V))
                         (VMap : MapsTypeOn (Sys.V)).

Include SolverRLD (Sys)(VSet)(VMap).

Section exactness.

Variable Hpure : forall x, is_pure (F x).
(*Definition rhs x : Tree Var.t D.t D.t := proj1_sig (Hpure x).*)

Definition is_local_solution
             (X X' : VS.t) (sigma : Var.t -> Sys.D.t)
  := (forall z, VS.In z X -> VS.In z X') /\
     (forall z v d,
        VS.In z X' ->
        In (v,d) (deps (rhs Hpure z) sigma) ->
        VS.In v X') /\
     (forall z,
        VS.In z X' ->
        D.Leq ([[rhs Hpure z]]* sigma) (sigma z)).

Definition sol_ext X X' sigma (H : is_local_solution X X' sigma)
  : Var.t -> Sys.D.t
  := fun z =>
       match VSetProps.In_dec z X' with
           | left _ => sigma z
           | right _ => Sys.D.top
       end.

Import Defs.

Lemma sol_ext_is_solution
        X X' sigma (H : @is_local_solution X X' sigma) :
  is_solution (rhs Hpure) (@sol_ext X X' sigma H).
Proof.
destruct H as [H [H0 H1] ].
intros x.
unfold sol_ext at 2.
case (VSetProps.In_dec x X') as [e | n]; auto.
- rewrite <- (@deps_val_compat _ _ _ _ _ sigma _ eq_refl).
  + now apply H1.
  + intros [v d] i.
    unfold sol_ext; simpl.
    now case (VSetProps.In_dec v X'); firstorder.
Qed.

End exactness.
End SolverRLDcomplete.
