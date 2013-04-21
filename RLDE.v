Require Import MSets.MSetFacts.
Require Import MSets.MSetProperties.
Require Import MSets.MSetDecide.
Require Import FSets.FMapFacts.
Require Export Solvers.
Require Import RLDEi.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SolverRLDE (Sys : CSysJoinSemiLat)
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

Module SI := SolverRLDEInstr (Sys) (VSet) (VMap).

(*****************************************************************)
(*********** Non-instrumented algorithm specification ************)
(*****************************************************************)

Definition state :=
  (Sigma.t D.t * Infl.t (list Var.t) * VS.t * VS.t)%type.

Ltac destruct_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
  let cal := fresh "called" in
    destruct s as [ [ [sig inf] sta] cal].

Ltac destruct_pose_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
  let cal := fresh "called" in
    destruct s as [ [ [sig inf] sta] cal];
    pose (s := (sig, inf, sta, cal));
    fold s.

Definition setval (x : Var.t) d (s : state) : state :=
  let '(sigma, infl, stable, called) := s in
    (Sigma.add x d sigma, infl, stable, called).

Definition getval (s : state) x :=
  let '(sigma, _, _, _) := s in
    match Sigma.find x sigma with
      | Some d => d
      | None => D.bot
    end.

Lemma getval_eq (s1 s2 : state) :
  let '(sigma1, _, _, _) := s1 in
  let '(sigma2, _, _, _) := s2 in
    VMap.Equal sigma1 sigma2 ->
    getval s1 = getval s2.
Proof.
destruct_state s1. destruct_state s2. intro e.
extensionality x; simpl. now rewrite e.
Qed.

Definition get_infl (s : state) x : list (Var.t) :=
  let '(_, infl, _, _) := s in
    match Infl.find x infl with
      | Some l => l
      | None => []
    end.

Lemma get_infl_eq s1 s2 :
  let '(_, infl1, _, _) := s1 in
  let '(_, infl2, _, _) := s2 in
    VMap.Equal infl1 infl2 ->
    get_infl s1 = get_infl s2.
Proof.
destruct_state s1. destruct_state s2. intro e.
extensionality x; simpl. now rewrite e.
Qed.

Definition add_infl y x (s : state) : state :=
  let '(sigma, infl, stable, called) := s in
    let xs := get_infl s y in
    (sigma, Infl.add y (x :: xs) infl, stable, called).

Definition rem_infl x (s : state) : state :=
  let '(sigma, infl, stable, called) := s in
    (sigma, Infl.remove x infl, stable, called).

Definition is_stable x (s : state) :=
  let '(_, _, stable, _) := s in VS.In x stable.

Lemma is_stable_dec x s : {is_stable x s} + {~ is_stable x s}.
destruct_state s. simpl. now apply VSetProps.In_dec.
Qed.

Definition get_stable (s : state) :=
  let '(_, _, stable, _) := s in stable.

Definition add_stable x (s : state) : state :=
  let '(sigma, infl, stable, called) := s in
    (sigma, infl, VS.add x stable, called).

Definition rem_stable x (s : state) : state :=
  let '(sigma, infl, stable, called) := s in
    (sigma, infl, VS.remove x stable, called).

Definition is_called x (s : state) :=
  let '(_, _, _, called) := s in VS.In x called.

Definition get_called (s : state) :=
  let '(_, _, _, called) := s in called.

Definition add_called x (s : state) : state :=
  let '(sigma, infl, stable, called) := s in
    (sigma, infl, stable, VS.add x called).

Definition rem_called x (s : state) : state :=
  let '(sigma, infl, stable, called) := s in
    (sigma, infl, stable, VS.remove x called).

Definition prepare x s :=
  let s1 := add_stable x s in
  let s2 := add_called x s1 in
    s2.

Definition handle_work (w : list Var.t) (s : state) :=
    let f s x :=
      let s := rem_called x s in
      let s := rem_stable x s in
        s in
    List.fold_left f w s.

Definition extract_work (x : Var.t) (s : state) : (list Var.t * state)
  := let w := get_infl s x in
     let s := rem_infl x s in
     let s := handle_work w s in
       (w, s).

Lemma handle_work_spec (s : state) w (s' : state) :
  s' = handle_work w s ->
  let '(sigma, infl, stable, called) := s in
  let '(sigma', infl', stable', called') := s' in
    sigma' = sigma /\
    infl' = infl /\
    VS.Equal stable' (VS.diff stable (of_list w)) /\
    VS.Equal called' (VS.diff called (of_list w)).
Proof.
revert s s'.
induction w as [| x w IHw ].
- intros s s' H1. destruct_state s. destruct_state s'. simpl.
  inversion H1. now intuition; fsetdec.
- intros s s' H.
  remember (rem_called x s) as s1.
  remember (rem_stable x s1) as s2.
  assert (H1 : s' = handle_work w s2) by (subst; auto).
  assert (H2 := IHw _ _ H1). clear IHw H1.
  destruct_state s.
  destruct_state s1.
  destruct_state s2.
  destruct_state s'.
  inversion Heqs1; subst; simpl in *.
  inversion Heqs2; subst.
  now intuition; fsetdec.
Qed.

Lemma extract_work_spec x s w s' :
  (w, s') = extract_work x s ->
  let '(sigma, infl, stable, called) := s in
  let '(sigma', infl', stable', called') := s' in
    w = get_infl s x /\
    sigma' = sigma /\
    infl' = Infl.remove x infl /\
    VS.Equal stable' (VS.diff stable (of_list w)) /\
    VS.Equal called' (VS.diff called (of_list w)).
Proof.
intro H. injection H as H1 Ew; clear H.
assert (H := handle_work_spec H1).
subst w. destruct_state s. destruct_state s'.
now simpl in *; intuition.
Qed.

Definition s_init : state
  := (Sigma.empty D.t,
      Infl.empty (list Var.t),
      VS.empty,
      VS.empty).

Section algorithm.

Variable Hpure : forall x, is_pure (F x).
Definition rhs x : Tree Var.t D.t D.t := proj1_sig (Hpure x).

Lemma rhs_spec x : F x = [[rhs x]].
Proof. now rewrite (proj2_sig (Hpure x)). Qed.

Inductive EvalGet :
  Var.t -> Var.t -> state -> Exc D.t * state -> Prop :=
  | EvalGet0 :
      forall x y s s0,
        Solve y s s0 ->
        let s1 := add_infl y x s0 in
        let d := getval s0 y in
        ~ is_called x s0 ->
        EvalGet x y s (error, s1)
  | EvalGet1 :
      forall x y s s0,
        Solve y s s0 ->
        let s1 := add_infl y x s0 in
        let d := getval s0 y in
        is_called x s0 ->
        EvalGet x y s (value d, s1)

with EvalGet_x :
  Var.t ->
  (Var.t -> state -> Exc D.t * state -> Prop) -> Prop :=
  | EvalGet_x0 :
      forall x (f : Var.t -> state -> Exc D.t * state -> Prop),
        (forall y s0 ds1,
           f y s0 ds1 -> EvalGet x y s0 ds1) ->
        EvalGet_x x f

with Wrap_Eval_x :
  Var.t -> (Var.t -> state -> Exc D.t * state -> Prop) ->
  @Tree Var.t D.t D.t ->
  state -> Exc D.t * state -> Prop :=
  | Wrap_Eval_x0 :
    forall x f t s0 ds1,
      EvalGet_x x f ->
        [[t]]## f s0 ds1 ->
      Wrap_Eval_x x f t s0 ds1

with Eval_rhs :
  Var.t ->
  state -> Exc D.t * state -> Prop :=
  | Eval_rhs0 :
    forall x f s ds0,
      EvalGet_x x f ->
      Wrap_Eval_x x f (rhs x) s ds0 ->
      Eval_rhs x s ds0

with Solve :
  Var.t -> state -> state -> Prop :=
  | Solve0 :
      forall x s, is_stable x s -> Solve x s s
  | Solve1 :
      forall x s s2,
      ~ is_stable x s ->
      let s1 := prepare x s in
      Eval_rhs x s1 (error, s2) ->
      Solve x s s2
  | Solve2 :
      forall x d s s2,
      ~ is_stable x s ->
      let s1 := prepare x s in
      Eval_rhs x s1 (value d, s2) ->
      let s3 := rem_called x s2 in
      let cur_val := getval s3 x in
      D.Leq d cur_val ->
      Solve x s s3
  | Solve3 :
      forall x d s s2 s5 s6 work,
      ~ is_stable x s ->
      let s1 := prepare x s in
      Eval_rhs x s1 (value d, s2) ->
      let s3 := rem_called x s2 in
      let cur_val := getval s3 x in
      ~ D.Leq d cur_val ->
      let new_val := D.join cur_val d in
      let s4 := setval x new_val s3 in
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

Definition EvalGet_x_fun
             x (f : Var.t -> state -> Exc D.t * state -> Prop)
  := forall f',
       EvalGet_x x f' ->
       forall y s ds0 ds0',
         f y s ds0 -> f' y s ds0' -> ds0 = ds0'.

Definition Wrap_Eval_x_fun
             x (f : Var.t -> state -> Exc D.t * state -> Prop) t s ds1
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

(* EvalGet0 *)
- idtac. intros x y s s0 Hsol Isol s1 d.
  red. red in Isol.
  intros Hncalx [d' s1'] Heval'.
  unfold d, s1.
  inversion Heval' as [? ? ? ? Hsol' | ? ? ? ? Hsol'];
    subst; clear Heval';
    assert (Htmp := Isol _ Hsol'); now subst.

(* EvalGet0 *)
- idtac. intros x y s s0 Hsol Isol s1 d.
  red. red in Isol.
  intros Hncalx [d' s1'] Heval'.
  unfold d, s1.
  inversion Heval' as [? ? ? ? Hsol' | ? ? ? ? Hsol'];
    subst; clear Heval';
    assert (Htmp := Isol _ Hsol'); now subst.

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
    now eapply wrap_rel_ErrorT_State_fun; eauto.
  + intros s [d1 s1] Hevalx Ievalx HfQue.
    red.
    intros f' [d' s1'] Hf'Que Hff'.
    inversion Hf'Que; subst.
    now eapply wrap_rel_ErrorT_State_fun; eauto.

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
- idtac. intros x s s1 Hnstaxs s0 Heval Ieval s2 Hsol.
  inversion Hsol as [| ? ? ? ? s1' Heval' | ? ? ? ? ? s1' Heval' | ? ? ? ? ? ? ? ? s1' Heval']; 
    [ subst s2; easy | | |].
  + assert (Htmp := Ieval _ Heval').
    now inversion Htmp; subst.
  + assert (Htmp := Ieval _ Heval').
    now inversion Htmp; subst.
  + subst s2 s3.
    assert (Htmp := Ieval _ Heval').
    now inversion Htmp; subst d1 s1.

(* Solve 2 *)
- idtac.
  intros x d1 s s1 Hnstaxs s0 Heval Ieval s2 cur Hleq s3 Hsol.
  red in Ieval.
  inversion Hsol as [| ? ? ? ? s1' Heval' | ? ? ? ? ? s1' Heval' | ? ? ? ? ? ? ? ? s1' Heval'].
  + subst s3; easy.
  + assert (Htmp := Ieval _ Heval').
    now inversion Htmp; subst.
  + idtac.
    assert (Htmp := Ieval _ Heval').
    unfold s2.
    now inversion Htmp; subst s7 s3.
  + idtac.
    subst s4 s7.
    assert (Htmp := Ieval _ Heval').
    unfold cur, new_val, cur_val, cur_val0 in *.
    now inversion Htmp; subst s9 s10 s8 s5 d1.

(* Solve 3 *)
- idtac.
  intros x d1 s s1 s4 s5 w.
  intros Hnstaxs s0 Heval Ieval.
  intros s2 cur Hnleq new s3 Hwork Hsolall Isolall.
  red. intros s5' Hsol'.
  inversion Hsol' as [| ? ? ? ? s0' Heval' | ? ? ? ? ? s1' Heval' | ? ? ? ? ? ? ? ? s1' Heval'];
    [subst s5'; easy | | |].
  + idtac.
    unfold cur in Hnleq.
    red in Ieval.
    assert (Htmp := Ieval _ Heval').
    now inversion Htmp; subst s5' s7 d; clear Htmp.
  + idtac.
    unfold cur in Hnleq.
    unfold cur_val in H0.
    red in Ieval.
    assert (Htmp := Ieval _ Heval').
    inversion Htmp; subst s5' d; clear Htmp.
    unfold s9 in H0. now rewrite <- H6 in H0.
  + clear H Hnstaxs.
    assert (Htmp := Ieval _ Heval'); clear Heval Ieval.
    inversion Htmp; clear Htmp.
    unfold new, cur in s3.
    unfold new_val, cur_val in s11.
    unfold s3 in Hwork.
    unfold s11, s12 in H1.
    rewrite <- H7, H3 in H1.
    assert (Hw : (w,s4) = (work,s8)).
    { rewrite Hwork, H1, H6.
      unfold s2, s10.
      now rewrite <- H7, H3. }
    inversion Hw; subst s8 work.
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

(* a nicer reformulation of partial_functions_inv: *)
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

Definition state' := SI.state'.

Definition projI (si : state') : state :=
  let '(sigma, infl, stable, called, _) := si in
    (sigma, infl, stable, called).

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
Definition simTrel
  (f : Var.t -> state -> Exc D.t * state -> Prop)
  (f' : Var.t -> state' -> Exc D.t * state' -> Prop)
  := forall x s s1 s' d,
       sim s s' ->
       f x s (d, s1) ->
       exists ds1',
       f' x s' ds1' /\
       let (d',s1') := ds1' in
       d = d' /\ sim s1 s1'.

Lemma sim_init : sim s_init SI.s_init.
Proof. easy. Qed.

Ltac destruct_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
  let cal := fresh "called" in
    destruct s as [ [ [sig inf] sta] cal].

Ltac destruct_state' s :=
  let sig := fresh "sigma'" in
  let inf := fresh "infl'" in
  let sta := fresh "stable'" in
  let cal := fresh "called'" in
  let que := fresh "queued'" in
    destruct s as [ [ [ [sig inf] sta] cal] que].

Lemma sim_projI s' : sim (projI s') s'.
Proof. now destruct_state' s'. Qed.
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

Lemma sim_is_called x s s' (H : sim s s') :
  is_called x s <-> SI.is_called x s'.
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_is_called.

Lemma sim_rem_called x s s' (H : sim s s') :
  sim (rem_called x s) (SI.rem_called x s').
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
                         (f : Var.t -> state -> Exc D.t * state -> Prop)
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

(* EvalGet0 *)
- idtac.
  intros x y s s0 Hsol Hsolsim s1 d.
  red. intros Hncal s' Hsims.
  red in Hsolsim.
  elim (Hsolsim _ Hsims); intros s0' [Hsol' Hsims0].
  pose (d' := SI.getval s0' y).
  assert (Ed : d = d') by (unfold d, d'; now erewrite sim_getval).
  pose (s1' := SI.add_infl y x s0').
  assert (Hsims1 : sim s1 s1') by (apply sim_add_infl; auto).
  assert (Hncal' : ~ SI.is_called x s0').
  { contradict Hncal. now eapply sim_is_called; eauto. }
  exists (error,s1').
  split; [| split]; try apply SI.EvalGet0; easy.

(* EvalGet1 *)
- idtac.
  intros x y s s0 Hsol Hsolsim s1 d.
  red. intros Hncal s' Hsims.
  red in Hsolsim.
  elim (Hsolsim _ Hsims); intros s0' [Hsol' Hsims0].
  pose (d' := SI.getval s0' y).
  assert (Ed : d = d') by (unfold d, d'; now erewrite sim_getval).
  pose (s1' := SI.add_infl y x s0').
  assert (Hsims1 : sim s1 s1') by (apply sim_add_infl; auto).
  assert (Hncal' : SI.is_called x s0').
  { now eapply sim_is_called; eauto. }
  exists (value d',s1').
  now split; [| split]; auto; try apply SI.EvalGet1; auto.

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
    destruct (wrap_rel_ErrorT_State_Ans_inv Ht); subst; clear Ht.
    red. intros f' s' l' Hsims Hsimf Hevalx'.
    exists (value a,s'), l'.
    split; auto.
    apply SI.Wrap_Eval_x0; auto.
    now apply wrapESAns.
  + intros s [od1 s1] Hevalx Hevalxsim Ht.
    {
    case od1 as [d1 |].
    - destruct (wrap_rel_ErrorT_State_Que_value_inv Ht)
        as [d0 [s0 [Hf Hwrapf] ] ]; clear Ht.
      assert (Hwrapeval : Wrap_Eval_x_sim x f (k d0) s0 (value d1, s1))
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
      exists (value d1,s1'), l1'. split; auto.
      apply SI.Wrap_Eval_x0; auto.
      apply wrapESQueValue with (d0:=d0) (s0:= (s0', l' ++ [(q,d0)])).
      + now apply SI.instrRvalue.
      + now inversion Hwrapeval'; subst.
    - idtac.
      destruct (wrap_rel_ErrorT_State_Que_error_inv Ht)
        as [Hf | [d0 [s0 [Hf Hwrapf] ] ] ]; clear Ht.
      + idtac.
        red. intros f' s' l' Hsims Hsimf Hevalx'.
        red in Hevalxsim.
        assert (Htmp := Hsimf _ _ _ _ _ Hsims Hf).
        destruct Htmp as [ [d' s0'] [Hf' [? Hsims0 ] ] ].
        subst d'.
        exists (error,s0'), l'.
        split; [| split]; auto.
        apply SI.Wrap_Eval_x0; auto.
        apply wrapESQueError.
        now apply SI.instrRerror.
      + idtac.
        assert (Hwrapeval : Wrap_Eval_x_sim x f (k d0) s0 (error, s1))
          by (apply IH; auto). clear IH.
        red. intros f' s' l' Hsims Hsimf Hevalx'.
        red in Hwrapeval.
        red in Hevalxsim.
        assert (Htmp := Hsimf _ _ _ _ _ Hsims Hf).
        destruct Htmp as [ [d' s0'] [Hf' [? Hsims0 ] ] ].
        subst d'.
        assert (Htmp := Hwrapeval f' s0' (l' ++ [(q,d0)]) Hsims0 Hsimf Hevalx').
        destruct Htmp
          as [ [d1' s1'] [l1' [Hwrapeval' [? Hsims1] ] ] ];
          clear Hwrapeval.
        subst d1'.
        exists (error,s1'), l1'. split; auto.
        apply SI.Wrap_Eval_x0; auto.
        apply wrapESQueValue with (d0:=d0) (s0:= (s0', l' ++ [(q,d0)])).
        * now apply SI.instrRvalue.
        * now inversion Hwrapeval'; subst.
    }

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
  intros x s s1 Hxnsta s0 Hevalrhs Hevalrhssim.
  red. intros s' Hsims.
  assert (Hxnsta' : ~ SI.is_stable x s')
    by (contradict Hxnsta; now eapply sim_is_stable; eauto).
  red in Hevalrhssim.
  pose (s0' := SI.prepare x s').
  assert (Hsims0 : sim s0 s0') by (apply sim_prepare; auto).
  destruct (Hevalrhssim _ Hsims0) as [ [d' s1'] [l1' [Hevalrhs' [e Hsims1] ] ] ].
  clear Hevalrhssim. subst d'.
  (*assert (Hncalxs1' : ~ SI.is_called x s1')
    by (contradict Hncalxs1; now eapply sim_is_called; eauto).*)
  exists s1'. split; auto.
  now eapply (SI.Solve1); eauto.

(* Solve2 *)
- idtac.
  intros x d s s1 Hxnsta s0 Hevalrhs Hevalrhssim s2 cur Hleq.
  red. intros s' Hsims.
  assert (Hxnsta' : ~ SI.is_stable x s')
    by (contradict Hxnsta; now eapply sim_is_stable; eauto).
  red in Hevalrhssim.
  pose (s0' := SI.prepare x s').
  assert (Hsims0 : sim s0 s0') by (apply sim_prepare; auto).
  destruct (Hevalrhssim _ Hsims0) as [ [d' s1'] [l1' [Hevalrhs' [e Hsims1] ] ] ].
  clear Hevalrhssim. subst d'.
  (*assert (Hncalxs1' : SI.is_called x s1')
    by (eapply sim_is_called; eauto).*)
  pose (s2' := SI.rem_called x s1').
  pose (cur' := SI.getval s2' x).
  assert (Hsims1' : sim s2 s2') by (apply sim_rem_called; auto).
  assert (Hle' : SI.D.Leq d cur')
    by (unfold cur'; now erewrite <- sim_getval; eauto).
  exists s2'. split; auto.
  now eapply (SI.Solve2); eauto.

(* Solve3 *)
- idtac.
  intros x d s s1 s4 s5 w Hxnsta s0 Hevalrhs Hevalrhssim s2 cur Hleq new s3 Hw Hsolall Hsolallsim.
  red. intros s' Hsims.
  assert (Hxnsta' : ~ SI.is_stable x s')
    by (contradict Hxnsta; now eapply sim_is_stable; eauto).
  red in Hevalrhssim.
  pose (s0' := SI.prepare x s').
  assert (Hsims0 : sim s0 s0') by (apply sim_prepare; auto).
  destruct (Hevalrhssim _ Hsims0) as [ [d' s1'] [l1' [Hevalrhs' [e Hsims1] ] ] ].
  clear Hevalrhssim. subst d'.
  (*assert (Hncalxs1' : SI.is_called x s1')
    by (eapply sim_is_called; eauto).*)
  pose (s2' := SI.rem_called x s1').
  pose (cur' := SI.getval s2' x).
  pose (new' := SI.D.join cur' d).
  assert (Hsims2' : sim s2 s2') by (apply sim_rem_called; auto).
  assert (Hnle' : ~ SI.D.Leq d cur')
    by (unfold new', cur'; now erewrite <- sim_getval; eauto).
  pose (s3' := SI.setval x new' s2').
  assert (Hsims3 : sim s3 s3').
  { unfold s3, s3', new, new', cur, cur'.
    rewrite <- (sim_getval Hsims2'). now apply sim_setval. }
  destruct (SI.extract_work x s3') as (w', s4') eqn:Hw'.
  assert (Htmp1 : w = w' /\ sim s4 s4')
    by (eapply sim_extract_work; eauto).
  destruct Htmp1 as [? Hsims4]; subst w'.
  destruct (Hsolallsim _ Hsims4) as [s5' [Hsolall' Hsims5] ].
  exists s5'. split; auto.
  now eapply (SI.Solve3); eauto.

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
  is_monotone rhs ->
  forall mu w s,
    is_solution rhs mu ->
    SolveAll w s_init s ->
    leqF (getval s) mu.
Proof.
intros Hmon mu w s Hsolmu Hsolall.
apply simulation in Hsolall.
assert (Htmp := Hsolall _ sim_init).
destruct Htmp as [s' [Hsolall' Hsims] ].
apply SI.exactness with (mu:=mu) in Hsolall';
  try rewrite <- rhs_same; auto.
now rewrite (sim_getval Hsims).
Qed.

End algorithm.

End SolverRLDE.
