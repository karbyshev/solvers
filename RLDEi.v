Require Import MSetFacts.
Require Import MSetProperties.
Require Import MSetDecide.
Require Import FMapFacts.
Require Export Solvers.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SolverRLDEInstr (Sys : CSysJoinSemiLat)
                       (VSet : SetsTypeOn (Sys.V))
                       (VMap : MapsTypeOn (Sys.V)).

Module Var := Sys.V.
Module D   := Sys.D.

Module Import VSetFacts := WFactsOn (Var) (VSet).
Module Import VSetProps := WPropertiesOn (Var) (VSet).
Module Import VSetDecide := WDecideOn (Var) (VSet).
Module Import VMapFacts := WFacts_fun (Var) (VMap).

Module VS := VSet.
Module Sigma := VMap.
Module Infl := VMap.

Module Import Defs := Solvers.Defs (Sys).

(*****************************************************************)
(************* Instrumented algorithm specification **************)
(*****************************************************************)

(* equation system *)
Definition F := Sys.F.

Definition state' :=
  (Sigma.t D.t * Infl.t (list Var.t) * VS.t * VS.t * VS.t)%type.

Ltac destruct_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
  let cal := fresh "called" in
  let que := fresh "queued" in
    destruct s as [ [ [ [sig inf] sta] cal] que].

Ltac destruct_pose_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
  let cal := fresh "called" in
  let que := fresh "queued" in
    destruct s as [ [ [ [sig inf] sta] cal] que];
    pose (s := (sig, inf, sta, cal, que));
    fold s.

Definition setval (x : Var.t) d (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    (Sigma.add x d sigma, infl, stable, called, queued).

Definition getval (s : state') x :=
  let '(sigma, _, _, _, _) := s in
    match Sigma.find x sigma with
      | Some d => d
      | None => D.bot
    end.

Lemma getval_eq s1 s2 :
  let '(sigma1, _, _, _, _) := s1 in
  let '(sigma2, _, _, _, _) := s2 in
    VMap.Equal sigma1 sigma2 ->
    getval s1 = getval s2.
Proof.
destruct_state s1. destruct_state s2. intro e.
extensionality x; simpl. now rewrite e.
Qed.

Lemma setval_getval_corr x d s :
  getval (setval x d s) x = d.
Proof.
destruct_state s; simpl. now rewrite add_eq_o.
Qed.

Definition get_infl (s : state') x : list (Var.t) :=
  let '(_, infl, _, _, _) := s in
    match Infl.find x infl with
      | Some l => l
      | None => []
    end.

Lemma get_infl_eq s1 s2 :
  let '(_, infl1, _, _, _) := s1 in
  let '(_, infl2, _, _, _) := s2 in
    VMap.Equal infl1 infl2 ->
    get_infl s1 = get_infl s2.
Proof.
destruct_state s1. destruct_state s2. intro e.
extensionality x; simpl. now rewrite e.
Qed.

Definition add_infl y x (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    let xs := get_infl s y in
    (sigma, Infl.add y (x :: xs) infl, stable, called, queued).

Definition rem_infl x (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    (sigma, Infl.remove x infl, stable, called, queued).

Lemma get_add_infl_corr y x s :
  In x (get_infl (add_infl y x s) y).
Proof.
destruct_state s; simpl. now rewrite add_eq_o; intuition.
Qed.
Local Hint Resolve get_add_infl_corr.

Definition is_stable x (s : state') :=
  let '(_, _, stable, _, _) := s in VS.In x stable.

Lemma is_stable_dec x s : {is_stable x s} + {~ is_stable x s}.
Proof.
destruct_state s. simpl. now apply VSetProps.In_dec.
Qed.

Definition get_stable (s : state') :=
  let '(_, _, stable, _, _) := s in stable.

Definition add_stable x (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    (sigma, infl, VS.add x stable, called, queued).

Lemma add_stable_corr x (s : state') : is_stable x (add_stable x s).
Proof.
destruct_state s; simpl; now fsetdec.
Qed.

Definition rem_stable x (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    (sigma, infl, VS.remove x stable, called, queued).

Lemma rem_stable_corr x s : ~ is_stable x (rem_stable x s).
Proof.
destruct_state s; simpl; auto with set.
Qed.

Definition is_called x (s : state') :=
  let '(_, _, _, called, _) := s in VS.In x called.

Lemma is_called_dec x s : {is_called x s} + {~ is_called x s}.
destruct_state s. simpl. now apply VSetProps.In_dec.
Qed.

Definition get_called (s : state') :=
  let '(_, _, _, called, _) := s in called.

Definition add_called x (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    (sigma, infl, stable, VS.add x called, queued).

Lemma add_called_corr x s : is_called x (add_called x s).
Proof.
destruct_state s; simpl; now fsetdec.
Qed.

Definition rem_called x (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    (sigma, infl, stable, VS.remove x called, queued).

Lemma rem_called_corr x s : ~ is_called x (rem_called x s).
Proof.
destruct_state s; simpl; auto with set.
Qed.

Definition is_solved x (s : state') :=
  let '(_, _, stable, called, _) := s in
    VS.In x (VS.diff stable called).

Definition get_solved (s : state') :=
  let '(_, _, stable, called, _) := s in VS.diff stable called.

Definition is_queued x (s : state') :=
  let '(_, _, _, _, queued) := s in VS.In x queued.

Definition get_queued (s : state') :=
  let '(_, _, _, _, queued) := s in queued.

Definition add_queued x (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    (sigma, infl, stable, called, VS.add x queued).

Lemma add_queued_corr x s : is_queued x (add_queued x s).
Proof.
destruct_state s; simpl; now fsetdec.
Qed.

Definition rem_queued x (s : state') : state' :=
  let '(sigma, infl, stable, called, queued) := s in
    (sigma, infl, stable, called, VS.remove x queued).

Lemma rem_queued_corr x s : ~ is_queued x (rem_queued x s).
Proof.
destruct_state s; simpl; auto with set.
Qed.

Definition prepare x s :=
  let s1 := rem_queued x s in
  let s2 := add_stable x s1 in
  let s3 := add_called x s2 in
    s3.

Lemma is_solved_prepare x s :
  is_called x s ->
  forall u, is_solved u s -> is_solved u (prepare x s).
Proof.
destruct_state s; simpl. now fsetdec.
Qed.

Definition handle_work (w : list Var.t) (s : state') :=
    let f s x :=
      let s := rem_called x s in
      let s := rem_stable x s in
      let s := add_queued x s in
      s in
    List.fold_left f w s.

Definition extract_work (x : Var.t) (s : state')
  : (list Var.t * state')
  := let w := get_infl s x in
     let s := rem_infl x s in
     let s := handle_work w s in
       (w, s).

Lemma handle_work_spec s w s' :
  s' = handle_work w s ->
  let '(sigma, infl, stable, called, queued) := s in
  let '(sigma', infl', stable', called',  queued') := s' in
    sigma' = sigma /\
    infl' = infl /\
    VS.Equal stable' (VS.diff stable (of_list w)) /\
    VS.Equal called' (VS.diff called (of_list w)) /\
    VS.Equal queued' (VS.union queued (of_list w)).
Proof.
revert s s'.
induction w as [| x w IHw ].
- intros s s' H1. destruct_state s. destruct_state s'. simpl.
  inversion H1. now intuition; fsetdec.
- intros s s' H.
  remember (add_queued x (rem_stable x (rem_called x s))) as s1.
  assert (H1 : s' = handle_work w s1) by (subst; auto).
  assert (H2 := IHw _ _ H1). clear IHw H1.
  destruct_state s. destruct_state s1. destruct_state s'.
  inversion Heqs1; subst; simpl.
  now intuition; fsetdec.
Qed.

Lemma extract_work_spec x s w s' :
  (w, s') = extract_work x s ->
  let '(sigma, infl, stable, called, queued) := s in
  let '(sigma', infl', stable', called',  queued') := s' in
    w = get_infl s x /\
    sigma' = sigma /\
    infl' = Infl.remove x infl /\
    VS.Equal stable' (VS.diff stable (of_list w)) /\
    VS.Equal called' (VS.diff called (of_list w)) /\
    VS.Equal queued' (VS.union queued (of_list w)).
Proof.
intro H. injection H as H1 Ew; clear H.
assert (H := handle_work_spec H1).
subst w. destruct_state s. destruct_state s'.
now simpl in *; intuition.
Qed.

(* Function instrumentation *)
Inductive instrR {S} A B (f : A -> S -> B * S -> Prop)
  : A -> (S * list (A * B)) -> B * (S * list (A * B)) -> Prop :=
  | instrR0 :
      forall a s l b s1,
        f a s (b,s1) -> instrR f a (s,l) (b, (s1, l ++ [(a,b)])).

Lemma instrR_inv S A B (f : A -> S -> B * S -> Prop)
                 a s l b s1 l1 :
  instrR f a (s,l) (b, (s1,l1)) ->
  f a s (b,s1) /\ l1 = l ++ [(a,b)].
Proof. intros H; now inversion H; subst; auto. Qed.

Section algorithm.

Variable Hpure : forall x, is_pure (F x).
Definition rhs x : Tree Var.t D.t D.t := proj1_sig (Hpure x).

Lemma rhs_spec x : F x = [[rhs x]].
Proof. now rewrite (proj2_sig (Hpure x)). Qed.

Definition argType := Var.t -> state' -> D.t * state' -> Prop.

Inductive EvalGet :
  Var.t -> Var.t -> state' -> D.t * state' -> Prop :=
  | EvalGet0 :
      forall x y s s0,
        Solve y s s0 ->
        let s1 := add_infl y x s0 in
        let d := getval s0 y in
          EvalGet x y s (d, s1)

with EvalGet_x :
  Var.t -> (Var.t -> state' -> D.t * state' -> Prop) -> Prop :=
  | EvalGet_x0 :
      forall x (f : Var.t -> state' -> D.t * state' -> Prop),
        (forall y s0 ds1,
           f y s0 ds1 -> EvalGet x y s0 ds1) ->
        EvalGet_x x f

with Wrap_Eval_x :
  Var.t -> (Var.t -> state' -> D.t * state' -> Prop) ->
  @Tree Var.t D.t D.t ->
  state' * list (Var.t * D.t) ->
  D.t * (state' * list (Var.t * D.t)) -> Prop :=
  | Wrap_Eval_x0 :
    forall x f t sl dsl0,
      EvalGet_x x f ->
      let f' := instrR f in
        [[t]]# f' sl dsl0 ->
      Wrap_Eval_x x f t sl dsl0

with Eval_rhs :
  Var.t ->
  state' -> D.t * (state' * list (Var.t * D.t)) -> Prop :=
  | Eval_rhs0 :
    forall x f s dsl0,
      EvalGet_x x f ->
      Wrap_Eval_x x f (rhs x) (s,[]) dsl0 ->
      Eval_rhs x s dsl0

with Solve :
  Var.t -> state' -> state' -> Prop :=
  | Solve0 :
      forall x s, is_stable x s -> Solve x s s
  | Solve1 :
      forall x d s s2 ps,
      ~ is_stable x s ->
      let s1 := prepare x s in
      Eval_rhs x s1 (d, (s2, ps)) ->
      ~ is_called x s2 ->
      Solve x s s2
  | Solve2 :
      forall x d s s2 ps,
      ~ is_stable x s ->
      let s1 := prepare x s in
      Eval_rhs x s1 (d, (s2, ps)) ->
      is_called x s2 ->
      let s3 := rem_called x s2 in
      let cur_val := getval s3 x in
      D.Leq d cur_val ->
      Solve x s s3
  | Solve3 :
      forall x d s s2 s5 s6 ps work,
      ~ is_stable x s ->
      let s1 := prepare x s in
      Eval_rhs x s1 (d, (s2, ps)) ->
      is_called x s2 ->
      let s3 := rem_called x s2 in
      let cur_val := getval s3 x in
      ~ D.Leq d cur_val ->
      let new_val := D.join cur_val d in
      let s4 := setval x new_val s3 in
      (work, s5) = extract_work x s4 ->
      SolveAll work s5 s6 ->
      Solve x s s6

with SolveAll :
  list Var.t -> state' -> state' -> Prop :=
  | SolveAll0 :
      forall s, SolveAll [] s s
  | SolveAll2 :
      forall x xs s s1 s2,
        Solve x s s1 ->
        SolveAll xs s1 s2 ->
        SolveAll (x :: xs) s s2.

Definition s_init : state'
  := (Sigma.empty D.t,
      Infl.empty (list Var.t),
      VS.empty,
      VS.empty,
      VSet.empty).

(* generate mutual induction scheme *)
Scheme evalget_ind   := Minimality for EvalGet Sort Prop
  with evalgetx_ind  := Minimality for EvalGet_x Sort Prop
  with wrapevalx_ind := Minimality for Wrap_Eval_x Sort Prop
  with evalrhs_ind   := Minimality for Eval_rhs Sort Prop
(*with prepare_ind   := Minimality for Prepare Sort Prop*)
(*with extract_ind   := Minimality for ExtractWork Sort Prop*)
  with solve_ind     := Minimality for Solve Sort Prop
  with solveall_ind  := Minimality for SolveAll Sort Prop.
  
Combined Scheme solve_mut_ind from
  evalget_ind,
  evalgetx_ind,
  wrapevalx_ind,
  evalrhs_ind,
  solve_ind,
  solveall_ind.

(*****************************************************************)
(************************   Function   ***************************)
(*****************************************************************)

(* We prove that the above inductive relation defines a graph
 * of a partial function *)

Definition EvalGet_fun x y s ds1
  := forall ds1', EvalGet x y s ds1' -> ds1 = ds1'.

Definition EvalGet_x_fun
  x (f : Var.t -> state' -> D.t * state' -> Prop)
  := forall f',
       EvalGet_x x f' ->
       forall y s ds0 ds0',
         f y s ds0 -> f' y s ds0' -> ds0 = ds0'.

Definition Wrap_Eval_x_fun
  x (f : Var.t -> state' -> D.t * state' -> Prop) t s ds1
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
apply solve_mut_ind.

(* EvalGet *)
- idtac. intros x y s s0 Hsol Isol s1 d.
  red. red in Isol.
  intros [d' s1'] Heval'.
  unfold d, s1.
  inversion Heval' as [? ? ? ? Hsol']; subst; clear Heval'.
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
  + intros [s l] [d [s0 l0] ] Hevalx Ievalx fi Hfi.
    red. intros f' [d' [s0' l0'] ] Hwrap Hfun.
    inversion Hwrap as [? ? ? ? ? Hevalx' fi' Hfi']; subst; clear Hwrap.
    eapply wrap_rel_State_fun; [| refine Hfi | refine Hfi'].
    clear - Hfun.
    intros y [s l] [d [s0 l0] ] [d' [s0' l0'] ].
    unfold fi, fi'. intros Hfi Hfi'.
    inversion Hfi; subst. inversion Hfi'; subst.
    assert (Htmp := Hfun _ _ _ _ H1 H2).
    now inversion Htmp; subst.
  + intros [s l] [d [s1 l1] ] Hevalx Ievalx fi Hfi.
    red.
    intros f' [d' [s1' l1'] ] Hf'Que Hff'.
    inversion Hf'Que as [? ? ? ? ? Hevalx' fi' Hfi']; subst.
    eapply wrap_rel_State_fun; [| refine Hfi | refine Hfi'].
    clear - Hff'.
    intros y [s l] [d [s0 l0] ] [d' [s0' l0'] ].
    unfold fi, fi'. intros Hfi Hfi'.
    inversion Hfi; subst. inversion Hfi'; subst.
    assert (Htmp := Hff' _ _ _ _ H1 H2).
    now inversion Htmp; subst.

(* Eval_rhs *)
- idtac. intros x f s [d [s0 l0] ] Hevalx Ievalx Hwrap Iwrap.
  red. intros [d' [s0' l0'] ] Heval.
  red in Iwrap.
  inversion Heval; subst; clear Heval.
  now eapply Iwrap; eauto.

(* Solve 0 *)
- idtac. intros x s Hstaxs.
  red. intros s0' Hsol'.
  now inversion Hsol'.

(* Solve 1 *)
- idtac.
  intros x d1 s s1 l2 Hnstaxs s0 Heval Ieval Hncalx s2' Hsol'.
  red in Ieval.
  inversion Hsol' as [| ? ? ? ? ? ? s1' Heval' | ? ? ? ? ? ? s1' Heval' Hcalx | ? ? ? ? ? ? ? ? ? s1' Heval' Hcalx];
    [subst s2'; easy | | |].
  + unfold s1' in Heval'.
    assert (Htmp := Ieval _ Heval').
    now inversion Htmp; subst.
  + idtac. unfold s1' in Heval'.
    assert (Htmp := Ieval _ Heval').
    now inversion Htmp; subst.
  + idtac.
    subst s2 s6.
    assert (Htmp := Ieval _ Heval').
    now inversion Htmp; subst d1 s1 l2.

(* Solve 2 *)
- idtac.
  intros x d1 s s1 l2 Hnstaxs s0 Heval Ieval Hcalx.
  intros s2 cur Hleq s3 Hsol.
  red in Ieval.
  inversion Hsol as [| ? ? ? ? ? ? s1' Heval' | ? ? ? ? ? ? s1' Heval' Hcalx' | ? ? ? ? ? ? ? ? ? s1' Heval' Hcalx'];
    [subst s3; easy | | |].
  + unfold s1' in Heval'.
    assert (Htmp := Ieval _ Heval').
    unfold s2.
    now inversion Htmp; subst s3 s5.
  + idtac. unfold s1' in Heval'.
    assert (Htmp := Ieval _ Heval').
    unfold s2.
    now inversion Htmp; subst s7 s3.
  + idtac.
    subst s4 s7.
    assert (Htmp := Ieval _ Heval').
    unfold cur, new_val, cur_val, cur_val0 in *.
    now inversion Htmp; subst s9 s10 s8 s5 d1; clear Htmp Ieval Heval Hcalx'.

(* Solve 3 *)
- idtac.
  intros x d1 s s1 s4 s5 l w.
  intros Hnstaxs s0 Heval Ieval.
  intros Hcal s2 cur Hnleq new s3 Hwork Hsolall Isolall.
  red. intros s5' Hsol'.
  inversion Hsol' as [| ? ? ? ? ? ? s0' Heval' | ? ? ? ? ? ? s1' Heval' Hcalx' | ? ? ? ? ? ? ? ? ? s1' Heval' Hcalx'];
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

(*****************************************************************)
(***********************   Invariants   **************************)
(*****************************************************************)

Definition Inv_0 (s : state') :=
  let '(sigma, infl, stable, called, queued) := s in
    VS.Subset called stable /\
    VS.Empty (VS.inter stable queued).

Definition Inv_1 (s s' : state') :=
  let '(_, _, stable, called, queued) := s in
  let '(_, _, stable', called',  queued') := s' in
    VS.Subset stable  stable' /\
    VS.Subset called' called  /\
    VS.Subset queued' queued.

Lemma Inv_1_refl s : Inv_1 s s.
Proof.
destruct_state s; simpl; now auto with set.
Qed.
Local Hint Resolve Inv_1_refl.

Lemma Inv_1_trans s1 s2 s3 :
  Inv_1 s1 s2 -> Inv_1 s2 s3 -> Inv_1 s1 s3.
Proof.
destruct_state s1; destruct_state s2; destruct_state s3.
simpl. intuition; now fsetdec.
Qed.

Definition Inv_sigma (s s' : state') :=
  leqF (getval s) (getval s').

Lemma Inv_sigma_refl (s : state') : Inv_sigma s s.
Proof. destruct_state s; now firstorder. Qed.
Local Hint Resolve Inv_sigma_refl.

Lemma Inv_sigma_trans s1 s2 s3 :
  Inv_sigma s1 s2 -> Inv_sigma s2 s3 -> Inv_sigma s1 s3.
Proof. intros; now eapply leqF_trans; eauto. Qed.

Lemma Inv_sigma_prepare x s : Inv_sigma s (prepare x s).
Proof. intro; now destruct_state s. Qed.
Local Hint Resolve Inv_sigma_prepare.

Lemma Inv_sigma_lemma1 s1 s2 x y :
  Inv_sigma s1 s2 ->
  Inv_sigma s1 (add_infl y x s2).
Proof. now destruct_state s1; destruct_state s2. Qed.

Lemma Inv_sigma_extract_work s1 s2 s3 x work:
  Inv_sigma s1 s2 ->
  (work, s3) = extract_work x s2 ->
  Inv_sigma s1 s3.
Proof.
destruct_pose_state s1.
destruct_pose_state s2.
destruct_pose_state s3.
intros I12 Hwork z.
destruct (extract_work_spec Hwork) as [_ [H _] ]; clear Hwork.
simpl in *. now rewrite H; firstorder.
Qed.

Definition Inv_corr (s : state') :=
  let sigma := getval s in
    (forall (x v : Var.t) d,
       is_solved x s ->
       In (v,d) (deps (rhs x) sigma) ->
       In x (get_infl s v) /\
       (is_stable v s \/ is_queued v s)) /\
    (forall x : Var.t,
       is_solved x s ->
       let val := [[rhs x]]* sigma in
       D.Leq val (sigma x)).

Definition Inv_corr_var (s : state') x :=
  let '(_, _, stable, _, queued) := s in
  let sigma := getval s in
    forall v d,
      In (v,d) (deps (rhs x) sigma) ->
      In x (get_infl s v) /\
      (is_stable v s \/ is_queued v s).

Lemma Inv_corr_prepare s (x : Var.t) :
  Inv_corr s -> Inv_corr (prepare x s).
Proof.
destruct_pose_state s.
set (s1 := prepare x s).
intros Hcorrs.
red.
assert (Egetv : getval s1 = getval s) by auto.
assert (Einfl : get_infl s1 = get_infl s) by auto.
rewrite Egetv, Einfl; clear Egetv Einfl.
assert (Hsol : forall z, is_solved z s1 -> is_solved z s)
  by (simpl; now fsetdec).
assert (Hsta : forall z, is_stable z s -> is_stable z s1)
  by (simpl; now fsetdec).
assert (Hque : forall z, is_queued z s1 -> is_queued z s)
  by (simpl; now fsetdec).
unfold Inv_corr in Hcorrs.
intuition; try apply (H _ _ _ (Hsol _ H1) H2).
case (proj2 (H _ _ _ (Hsol _ H1) H2)); auto.
case (eq_dec v x); [intro e | intro ne].
- subst v. left. now simpl; fsetdec.
- simpl. right; now fsetdec.
Qed.

Lemma Inv_corr_lemma1 s (x y : Var.t) :
  Inv_corr s -> Inv_corr (add_infl y x s).
Proof.
destruct_pose_state s. intro H.
set (s' := add_infl y x s).
red.
assert (Hval : getval s' = getval s) by firstorder.
assert (Hsol : forall x, is_solved x s' = is_solved x s) by auto.
assert (Hsta : forall x, is_stable x s' = is_stable x s) by auto.
assert (Hque : forall x, is_queued x s' = is_queued x s) by auto.
rewrite Hval.
setoid_rewrite Hsol.
setoid_rewrite Hsta.
setoid_rewrite Hque.
split; [| now firstorder].
intros z v d Hz Hvd.
split.
- cut (In z (get_infl s v)); [| now firstorder].
  intro H1.
  case (eq_dec v y) as [e | ne].
  + subst. simpl. rewrite add_eq_o; auto. now apply in_cons.
  + simpl. now rewrite add_neq_o; auto.
- destruct H as [H _].
  now destruct (H _ _ _ Hz Hvd).
Qed.

Lemma Inv_corr_called s x :
  is_called x s ->
  Inv_corr s ->
  Inv_corr_var s x ->
  let f := getval s in
  D.Leq ([[rhs x]]* f) (f x) ->
  Inv_corr (rem_called x s).
Proof.
destruct_pose_state s.
intros Hcal Hs Hsx f Hleq.
set (s' := rem_called x s).
assert (H0 : getval s' = getval s) by firstorder.
assert (H1 : get_infl s' = get_infl s) by firstorder.
unfold Inv_corr.
rewrite H0, H1; clear H0 H1. split.
- intros z v d. case (eq_dec x z) as [e | ne].
  + subst z. now intro; apply Hsx.
  + intro Hz.
    assert (Hz1 : is_solved z s)
      by (clear - Hz ne; simpl in *; fsetdec).
    destruct Hs as [H1 _]. now apply H1.
- intro z. case (eq_dec x z) as [e | ne].
  + now subst z.
  + intro Hz.
    assert (Hz1 : is_solved z s)
      by (clear - Hz ne; simpl in *; fsetdec).
    now firstorder.
Qed.

Lemma Inv_corr_notcalled s x :
  ~ is_called x s -> Inv_corr s -> Inv_corr (rem_called x s).
Proof.
destruct_pose_state s.
intros Hncal Hs.
set (s' := rem_called x s).
assert (H0 : getval s' = getval s) by firstorder.
assert (H1 : get_infl s' = get_infl s) by firstorder.
unfold Inv_corr.
rewrite H0, H1; clear H0 H1.
unfold s'. unfold s.
unfold rem_called, is_stable, is_queued, is_solved.
now setoid_rewrite (remove_equal Hncal).
Qed.

Lemma Inv_corr_lemma4 s x :
  (is_called x s -> Inv_corr_var s x) ->
  (~ is_called x s -> is_solved x s) ->
  Inv_corr s ->
  Inv_corr_var s x.
Proof.
destruct_pose_state s.
intros Hpos Hneg Hs.
red.
destruct Hs as [Hs _].
case (VSetProps.In_dec x called) as [Hin | Hnotin].
- intros v d. now apply Hpos.
- intros v d. now apply Hs; firstorder.
Qed.

Lemma inlist_oflist x l : In x l <-> VS.In x (of_list l).
Proof.
split.
- intros Hin. apply of_list_1. apply InA_alt. now exists x; auto.
- intros Hin. apply of_list_1, InA_alt in Hin. inversion Hin as [y [e Hy] ]. now subst.
Qed.

Lemma oflist_cons x l : of_list (x :: l) = VS.add x (of_list l).
Proof. easy. Qed.

Lemma Inv_corr_step2 s x d work s2 :
  let cur := getval s x in
  let new := D.join cur d in
  let s0 := rem_called x s in
  let s1 := setval x new s0 in
  (work, s2) = extract_work x s1 ->
  (is_called x s -> d = [[rhs x]]* (getval s)) ->
  Inv_corr s ->
  Inv_corr_var s x ->
  Inv_corr s2.
Proof.
rename s2 into s0.
destruct_pose_state s.
destruct_pose_state s0.
intros cur new s' s'' Ework H Icors Icorvarsx.
destruct Icors as [H0 H1].
hnf in Icorvarsx.
assert (H2 := extract_work_spec Ework). hnf in H2.
destruct H2 as [Hw [Hsig0 [Hinf0 [Hsta0 [Hcal0 Hque0] ] ] ] ].
assert (Hwork : work = get_infl s x) by auto. clear Hw.
assert (Hvalx : getval s0 x = D.join (getval s x) d)
  by (clear - Hsig0; simpl in *; subst; now rewrite add_eq_o).
assert (Hsols0case : forall z,
               is_solved z s0 ->
               {x = z /\ is_stable z s} + {x <> z /\ is_solved z s}).
{ intros z Hsols0.
  case (eq_dec x z) as [e | ne]; [left | right]; split; auto.
  - subst z. clear - Hsols0 Hsta0. simpl in *. now fsetdec.
  - clear - Hsta0 Hcal0 Hsols0 ne. simpl in *. now fsetdec. }
assert (H3 : forall z, x <> z -> get_infl s0 z = get_infl s z).
{ intros z ne. clear - Hinf0 ne. simpl in *. subst. now rewrite remove_neq_o. }
assert (H4 : forall z, x <> z -> getval s0 z = getval s z).
{ intros z ne. clear - Hsig0 ne. simpl in *. subst. now rewrite add_neq_o. }
assert (H5 : getval s0 x = new)
  by (clear - Hsig0; simpl in *; subst; now rewrite add_eq_o).
assert (H6 : In x work ->
             forall z, is_solved z s0 -> x <> z /\ ~ In z work /\ is_solved z s).
{ intros Hxwork. apply inlist_oflist in Hxwork.
  intros z Hsolzs0. split; [| split].
  - contradict Hsolzs0. subst z. clear - Hxwork Hsta0 Hcal0.
    simpl in *. now fsetdec.
  - contradict Hsolzs0. apply inlist_oflist in Hsolzs0.
    clear - Hsolzs0 Hsta0. simpl in *. now fsetdec.
  - clear - Hxwork Hsolzs0 Hsta0 Hcal0. simpl in *. now fsetdec. }
split.
- intros z v d0 Hsolzs0 Hvd0.
  case (in_dec eq_dec x work) as [Hinwork | Hninwork].
  + destruct (H6 Hinwork z) as [ne [Hninwz Hsolz] ]; auto.
    assert (H7 : ~ In (x, getval s x) (deps (rhs z) (getval s)))
      by (contradict Hninwz; rewrite Hwork; now eapply H0; eauto).
    assert (H8 : deps (rhs z) (getval s) =
                 deps (rhs z) (getval s0)).
    { apply (deps_compat (l:=deps (rhs z) (getval s))); auto.
      intros [pv pd] Hpdeps.
      assert (Hpd : pd = getval s pv) by apply (deps_val Hpdeps).
      subst pd. unfold fst.
      assert (Hpv : pv <> x) by (contradict H7; now subst pv).
      now rewrite H4; auto. }
    rewrite <- H8 in Hvd0; auto.
    assert (Hd0 : d0 = getval s v) by (apply (deps_val Hvd0)).
    subst d0.
    assert (nevx : x <> v) by (contradict H7; now subst v).
    rewrite H3; auto. split.
    * now firstorder.
    * assert (Halt : is_stable v s \/ is_queued v s)
        by apply (proj2 (H0 _ _ _ Hsolz Hvd0)).
      clear - Halt Hsta0 Hque0.
      case (VSetProps.In_dec v (of_list work)) as [i | n];
        [ right; simpl; clear - i Hque0; now fsetdec |
          simpl in *; intuition; now fsetdec ].
  + case (Hsols0case _ Hsolzs0) as [ [e Hstazs] | [ne Hsolz] ].
    * subst z.
      assert (H7 : ~ In (x, getval s x) (deps (rhs x) (getval s)))
        by (subst work; firstorder).
      assert (H8 : deps (rhs x) (getval s) = deps (rhs x) (getval s0)).
      { apply (deps_compat (l:=deps (rhs x) (getval s))); auto.
        intros [pv pd] Hpdeps.
        assert (Hpd : pd = getval s pv) by apply (deps_val Hpdeps).
        subst pd. unfold fst.
        assert (Hpv : pv <> x) by (contradict H7; now subst pv).
        now rewrite H4; auto. }
      rewrite <- H8 in *.
      assert (Hd0 : d0 = getval s v) by (apply (deps_val Hvd0)).
      subst d0.
      assert (Hv : x <> v) by (contradict H7; now subst v).
      rewrite H3; auto.
      split; [now firstorder |].
      assert (Halt : is_stable v s \/ is_queued v s)
        by apply (proj2 (Icorvarsx _ _ Hvd0)).
      clear - Halt Hsta0 Hque0.
      case (VSetProps.In_dec v (of_list work)) as [i | n];
        [ right; simpl; clear - i Hque0; now fsetdec | 
          simpl in *; intuition; now fsetdec ].
    * assert (H10 : ~ In z work).
      { cut (~ VS.In z (of_list work));
          [assert (Htmp := inlist_oflist); clear - Htmp; now firstorder |].
        clear - ne Hsolz Hsolzs0 Hsta0 Hcal0. simpl in *.
        now fsetdec. }
      assert (H7 : ~ In (x, getval s x) (deps (rhs z) (getval s)))
        by (subst work; clear - H0 H10 Hsolz; firstorder).
      assert (H8 : deps (rhs z) (getval s) =
                   deps (rhs z) (getval s0)).
      { apply (deps_compat (l:=deps (rhs z) (getval s))); auto.
        intros [pv pd] Hpdeps.
        assert (Hpd : pd = getval s pv) by apply (deps_val Hpdeps).
        subst pd. unfold fst.
        assert (Hpv : pv <> x) by (contradict H7; now subst pv).
        now rewrite H4; auto. }
      rewrite <- H8 in Hvd0; auto.
      assert (Hd0 : d0 = getval s v) by (apply (deps_val Hvd0)).
      subst d0.
      assert (Hv : x <> v) by (contradict H7; now subst v).
      rewrite H3; auto.
      split; [now firstorder |].
      assert (Halt : is_stable v s \/ is_queued v s)
        by apply (proj2 (H0 _ _ _ Hsolz Hvd0)).
      clear - Halt Hsta0 Hque0.
      case (VSetProps.In_dec v (of_list work)) as [i | n];
        [ right; simpl; clear - i Hque0; now fsetdec | 
          simpl in *; intuition; now fsetdec ].
- intros z Hsolzs0.
  case (Hsols0case _ Hsolzs0) as [ [e Hstazs] | [ne Hsolz] ].
  + subst z.
    assert (Hninwork : ~ In x work).
    { cut (~ VS.In x (of_list work));
        [assert (Htmp := inlist_oflist); clear - Htmp; now firstorder |].
      clear - Hsolzs0 Hsta0 Hcal0. simpl in *.
      now fsetdec. }
    assert (H7 : ~ In (x, getval s x) (deps (rhs x) (getval s)))
      by (subst work; firstorder).
    assert (Hdeps : deps (rhs x) (getval s) = deps (rhs x) (getval s0)).
    { apply (deps_compat (l:=deps (rhs x) (getval s))); auto.
      intros [pv pd] Hpdeps.
      assert (Hpd : pd = getval s pv)
        by apply (deps_val Hpdeps).
      subst pd. unfold fst.
      assert (Hpv : pv <> x) by (contradict H7; now subst pv).
      now rewrite H4; auto. }
    assert (Heval : [[rhs x]]* (getval s0) = [[rhs x]]* (getval s)).
    { apply (deps_val_compat (l:=deps (rhs x) (getval s))); auto.
      intros [pv pd] Hpdeps.
      assert (Hpd : pd = getval s pv)
        by apply (deps_val Hpdeps).
      subst pd. unfold fst.
      assert (Hpv : pv <> x) by (contradict H7; now subst pv).
      now rewrite H4; auto. }
    rewrite Heval, Hvalx.
    case (is_called_dec x s) as [Hcalx | Hncalx].
    * rewrite <- H; auto. hnf.
      now apply D.JoinUnique.
    * assert (Hsolx : is_solved x s)
        by (clear - Hncalx Hstazs; simpl in *; fsetdec).
      hnf.
      apply D.LeqTrans with (y:=getval s x);
        [now firstorder | now apply D.JoinUnique].
  + assert (H10 : ~ In z work).
    { cut (~ VS.In z (of_list work));
        [assert (Htmp := inlist_oflist); clear - Htmp; now firstorder |].
      clear - ne Hsolz Hsolzs0 Hsta0 Hcal0. simpl in *.
      now fsetdec. }
    assert (H7 : ~ In (x, getval s x) (deps (rhs z) (getval s)))
      by (subst work; clear - H10 H0 Hsolz; firstorder).
    assert (Hdeps : deps (rhs z) (getval s) =
                    deps (rhs z) (getval s0)).
    { apply (deps_compat (l:=deps (rhs z) (getval s))); auto.
      intros [pv pd] Hpdeps.
      assert (Hpd : pd = getval s pv) by apply (deps_val Hpdeps).
      subst pd. unfold fst.
      assert (Hpv : pv <> x) by (contradict H7; now subst pv).
      now rewrite H4; auto. }
    assert (Heval : [[rhs z]]* (getval s0) = [[rhs z]]* (getval s)).
    { apply (deps_val_compat (l:=deps (rhs z) (getval s))); auto.
      intros [pv pd] Hpdeps.
      assert (Hpd : pd = getval s pv)
        by apply (deps_val Hpdeps).
      subst pd. unfold fst.
      assert (Hpv : pv <> x) by (contradict H7; now subst pv).
      now rewrite H4; auto. }
    now rewrite Heval, H4; auto.
Qed.

Definition Inv_sigma_infl (s0 s1 : state') :=
  forall z,
    let d0 := getval s0 z in
    let d1 := getval s1 z in
    (D.Leq d1 d0 -> incl (get_infl s0 z) (get_infl s1 z)) /\
    (~ D.Leq d1 d0 ->
     forall u,
       In u (get_infl s0 z) -> is_solved u s1).

Lemma Inv_sigma_infl_refl s : Inv_sigma_infl s s.
Proof.
intro z. split; [now intuition |].
assert (H : D.Leq (getval s z) (getval s z))
  by (apply D.LeqRefl).
now intuition.
Qed.
Local Hint Resolve Inv_sigma_infl_refl.

Lemma Inv_sigma_infl_trans s1 s2 s3 :
  (VS.Subset (get_solved s2) (get_solved s3)) ->
  Inv_sigma s1 s2 ->
  Inv_sigma s2 s3 ->
  Inv_sigma_infl s1 s2 ->
  Inv_sigma_infl s2 s3 ->
  Inv_sigma_infl s1 s3.
Proof.
destruct_pose_state s1.
destruct_pose_state s2.
destruct_pose_state s3.
intros H Hsig12 Hsig23 H12 H23 z.
set (d1 := getval s1 z).
set (d2 := getval s2 z).
set (d3 := getval s3 z).
destruct (H12 z) as [H1 H2].
destruct (H23 z) as [H3 H4].
clear H12 H23. try fold d1 d2 d3 in H1, H2, H3, H4.
split.
- intro Hleq31. clear H2 H4.
  assert (He : d3 = d1)
    by (apply D.LeqAntisym; auto; try eapply D.LeqTrans; eauto).
  rewrite He in H3. rewrite <- He in H1.
  now eapply incl_tran; eauto.
- intro Hnleq31. intros u Hu.
  clear H3.
  case (D.eq_dec d1 d2) as [e | ne].
  + apply H4; [now rewrite <- e |].
    apply H1; auto. now rewrite e.
  + assert (Hne23 : ~ D.Leq d2 d1)
      by (contradict ne; apply D.LeqAntisym; try apply Hsig12; auto).
    assert (Hs2 : is_solved u s2) by auto.
    clear - H Hs2. simpl in *. now fsetdec.
Qed.

Lemma Inv_sigma_infl_prepare s x : Inv_sigma_infl s (prepare x s).
Proof.
destruct_pose_state s. set (s1 := prepare x s).
red.
assert (Hval : getval s1 = getval s) by auto.
assert (Hinfl : get_infl s1 = get_infl s) by auto.
rewrite Hval, Hinfl.
assert (H := D.LeqRefl). now firstorder.
Qed.
Local Hint Resolve Inv_sigma_infl_prepare.

Lemma Inv_sigma_infl_lemma1 s1 s2 x y :
  Inv_sigma_infl s1 s2 ->
  Inv_sigma_infl s1 (add_infl y x s2).
Proof.
destruct_pose_state s1.
destruct_pose_state s2.
set (s3 := add_infl y x s2).
unfold Inv_sigma_infl.
assert (Hval : getval s3 = getval s2)
  by (apply (getval_eq s3 s2); intuition).
rewrite Hval; clear Hval.
assert (Hsol : forall u, is_solved u s2 -> is_solved u s3)
  by auto.
intros H z. split.
- destruct (H z) as [H0 _]. intro Hle.
  assert (H1 : incl (get_infl s2 z) (get_infl s3 z)).
  { case (eq_dec y z) as [e | ne].
    - assert (He : get_infl s3 z = x :: get_infl s2 z)
        by (simpl; subst z; now rewrite add_eq_o).
      rewrite He. now apply incl_tl, incl_refl.
    - assert (He : get_infl s3 z = get_infl s2 z)
        by (simpl; now rewrite add_neq_o).
      rewrite He. now apply incl_refl. }
  now eapply incl_tran; eauto.
- destruct (H z) as [_ H0].
  now intuition.
Qed.

Lemma Inv_sigma_infl_lemma2 s s1 x :
  Inv_sigma_infl s s1 ->
  Inv_sigma_infl s (rem_called x s1).
Proof.
destruct_pose_state s.
destruct_pose_state s1.
set (s2 := rem_called x s1).
unfold Inv_sigma_infl.
rewrite (getval_eq s2 s1); [| intuition].
intros H z. destruct (H z) as [H0 H1]; clear H.
split; auto.
assert (H2 : forall u, is_solved u s1 -> is_solved u s2)
  by (intro u; simpl; fsetdec).
now intuition.
Qed.

Lemma Lem_x_infl_getval s s1 x (vlist : list (Var.t * D.t)) :
    is_called x s1 ->
    Inv_sigma s s1 ->
    Inv_sigma_infl s s1 ->
    (forall p, In p vlist -> In x (get_infl s (fst p))) ->
    forall p, In p vlist -> getval s (fst p) = getval s1 (fst p).
Proof.
intros Hcal HIsig1 HIsig2 H1 [v d] Hpin. simpl.
set (f := getval s).
set (f1 := getval s1).
case (D.eq_dec (f v) (f1 v)) as [e | ne]; auto.
- assert (Hnleq : ~ D.Leq (f1 v) (f v))
    by (contradict ne; now apply D.LeqAntisym).
  clear ne HIsig1.
  destruct (HIsig2 v) as [_ H2]; clear HIsig2.
  assert (Habs : is_solved x s1) by firstorder.
  clear - Habs Hcal.
  destruct_state s1. simpl in *; now fsetdec.
Qed.

Definition Inv_EvalGet
  (x y : Var.t) (s : state') (p : D.t * state') :=
  let (d,s') := p in
  Inv_0 s ->
  Inv_corr s ->
  Inv_0 s' /\
  Inv_1 s s' /\
  d = getval s' y /\
  is_stable y s' /\
  Inv_sigma s s' /\
  Inv_sigma_infl s s' /\
  Inv_corr s' /\
  In x (get_infl s' y) /\
  (* monotonic case *)
  (forall mu,
    is_monotone rhs ->
    is_solution rhs mu ->
    leqF (getval s) mu -> leqF (getval s') mu).

Definition Inv_EvalGet_x
  (x : Var.t) (f : Var.t -> state' -> D.t * state' -> Prop) :=
  forall y s ds1,
    f y s ds1 -> Inv_EvalGet x y s ds1.

Definition Inv_Wrap_Eval_x
  (x : Var.t) (f : Var.t -> state' -> D.t * state' -> Prop)
  (t : Tree Var.t D.t D.t)
  (sl : state' * list (Var.t * D.t))
  (dsl' : D.t * (state' * list (Var.t * D.t))) :=
  let (s, ps) := sl in
  let '(d, (s', ps')) := dsl' in
  (*is_stable x s ->*)
  Inv_0 s ->
  Inv_corr s ->
  (forall p,
     In p ps ->
     is_stable (fst p) s /\ D.Leq (snd p) (getval s (fst p))) ->
  legal (rhs x) ps ->
  subtree (rhs x) ps = t ->
  Inv_0 s' /\
  Inv_1 s s' /\
  (*incl ps ps' /\*)
  (*(forall p, In p ps' -> is_stable (fst p) s') /\*)
  (*(forall p,
     In p ps' ->
     ~ In p ps ->
     D.Leq (getval s (fst p)) (snd p)) /\*)
  (forall p,
     In p ps' ->
     D.Leq (snd p) (getval s' (fst p))) /\
  Inv_corr s' /\
  Inv_sigma s s' /\
  Inv_sigma_infl s s' /\
  legal (rhs x) ps' /\
  subtree (rhs x) ps' = Ans d /\
  (* case: x is called in s' *)
  (is_called x s' ->
   valid (getval s) ps ->
   (forall p,
      In p ps -> In x (get_infl s (fst p))) ->
   valid (getval s') ps' /\
   (forall p,
      In p ps' -> In x (get_infl s' (fst p))) /\
   Inv_corr_var s' x) /\
  (* monotonic case *)
  (forall mu,
    is_monotone rhs ->
    is_solution rhs mu ->
    leqF (getval s) mu -> leqF (getval s') mu).

Definition Inv_Eval_rhs
  (x : Var.t) (s : state')
  (dsl' : D.t * (state' * list (Var.t * D.t))) :=
  let '(d, (s', ps)) := dsl' in
  (*is_stable x s ->*)
  Inv_0 s ->
  Inv_corr s ->
  Inv_0 s' /\
  Inv_1 s s' /\
  Inv_corr s' /\
  Inv_sigma s s' /\
  Inv_sigma_infl s s' /\
  (forall p,
     In p ps ->
     (*D.Leq (getval s (fst p)) (snd p) /\*)
     D.Leq (snd p) (getval s' (fst p))) /\
  legal (rhs x) ps /\
  subtree (rhs x) ps = Ans d /\
  (is_called x s' ->
   d = [[rhs x]]* (getval s') /\
   deps (rhs x) (getval s') = ps /\
   (forall p,
      In p ps -> In x (get_infl s' (fst p))) /\
   Inv_corr_var s' x) /\
  (* monotonic case *)
  (forall mu,
    is_monotone rhs ->
    is_solution rhs mu ->
    leqF (getval s) mu ->
    leqF (getval s') mu /\ (is_called x s' -> D.Leq d (mu x))).

Definition Inv_Solve
  (x : Var.t) (s s' : state') :=
  Inv_0 s ->
  Inv_corr s ->
  Inv_0 s' /\
  Inv_1 s s' /\
  Inv_sigma s s' /\
  Inv_sigma_infl s s' /\
  Inv_corr s' /\
  (* case 1: x is stable *)
  (*(is_stable x s -> s = s') /\*)
  (* case 2: x is not stable *)
  (*(~ is_stable x s ->
     is_stable x s' /\ ~ is_called x s' /\ ~ is_queued x s') /\*)
  (~ is_stable x s -> is_solved x s') /\
  (* monotonic case *)
  (forall mu,
     is_monotone rhs ->
     is_solution rhs mu ->
     leqF (getval s) mu -> leqF (getval s') mu).

Definition Inv_SolveAll
  (w : list Var.t) (s s' : state') :=
  Inv_0 s ->
  Inv_corr s ->
  (forall x, In x w -> ~ is_called x s) ->
  Inv_0 s' /\
  Inv_1 s s' /\
  Inv_sigma s s' /\
  Inv_sigma_infl s s' /\
  Inv_corr s' /\
  (*(VS.Subset
     (VS.union (of_list w) (get_stable s))
     (get_stable s')) /\
  (VS.Subset
     (get_queued s')
     (VS.diff (get_queued s) (of_list w))) /\*)
  (* all variables from worklist are solved: *)
  (VS.Subset
     (VS.union (of_list w) (get_solved s))
     (get_solved s')) /\
  (* monotonic case *)
  (forall mu,
    is_monotone rhs ->
    is_solution rhs mu ->
    leqF (getval s) mu -> leqF (getval s') mu).

(*****************************************************************)
(*********************** Invariants Lemma ************************)
(*****************************************************************)

Lemma VDeq_dec (px py : Var.t * D.t) : {px = py} + {~ px = py}.
Proof.
destruct px as [x a]; destruct py as [y b].
now case (eq_dec x y); [case (D.eq_dec a b); [left | right] | right]; congruence.
Qed.

Lemma InvariantsLemma :
  (forall x y s1 p,
     EvalGet x y s1 p -> Inv_EvalGet x y s1 p) /\
  (forall x f,
    EvalGet_x x f -> Inv_EvalGet_x x f) /\
  (forall x f t slist1 dslist2,
    Wrap_Eval_x x f t slist1 dslist2 ->
    Inv_Wrap_Eval_x x f t slist1 dslist2) /\
  (forall x s1 dslist2,
    Eval_rhs x s1 dslist2 -> Inv_Eval_rhs x s1 dslist2) /\
  (forall x s1 s2,
    Solve x s1 s2 -> Inv_Solve x s1 s2) /\
  (forall w s1 s2,
    SolveAll w s1 s2 -> Inv_SolveAll w s1 s2).
(*Admitted.*)
(*XXX*)

Proof.
apply solve_mut_ind.

(* EvalGet *)
- intros x y s s0. idtac.
  destruct_pose_state s.
  destruct_pose_state s0.  
  intros H Hinv s1 d.
  intros (*Hstab*) I0s Icorrs. unfold fst, snd.
  assert (Hval : getval s1 = getval s0) by auto.
  rewrite Hval.
  unfold Inv_Solve in Hinv.
  destruct Hinv as [I0 [I1 [Isig [Isiginfl [Icor (*[Hstaby*) [Hnstaby Hmon] (*]*) ] ] ] ] ]; auto.
  split; [| split; [| split; [| split; [| split; [| split; [| split] ] ] ] ] ]; auto.
  + clear - Hnstaby I1.
    case (is_stable_dec y s) as [i | n];
      simpl in *; now intuition; fsetdec.
  + now apply Inv_sigma_infl_lemma1.
  + now apply Inv_corr_lemma1.
  + simpl. now rewrite add_eq_o; auto with *.

(* Inv_EvalGet_x *)
- idtac. now intuition.

(* Inv_Wrap_Eval_x *)
- idtac.
  intros x f.
  induction t as [| v k IH].
  + intros [s ps] [d [s0 ps'] ] Evalgetx Ievalgetx f' Hf'.
    inversion_clear Hf'; subst.
    destruct_pose_state s.
    destruct_pose_state s0.
    hnf. intuition.
      (** now firstorder.*)
      * now firstorder.
      * assert (Hps' : ps' = deps (rhs x) (getval s0))
          by (eapply valid_legal_subtree_Ans; eauto).
        hnf. rewrite <- Hps'; clear Hps'.
        now firstorder.
  + intros [s ps] [d [s1 ps'] ] Evalgetx Ievalgetx f' Hf'.
    destruct (wrap_rel_State_Que_inv Hf') as [d0 [ [s0 ps0] [Hf'1 Hf'2] ] ]; clear Hf'.
    destruct (instrR_inv Hf'1) as [Hf Hps0]; clear Hf'1.
    rename Hf'2 into Hf'.
    subst ps0.
    revert Hf Hf'.
    destruct_pose_state s.
    destruct_pose_state s0.
    destruct_pose_state s1.
    intros Hf Hf'.
    red. intros (*Hxsta*) I0s Icorrs Hps Hpsleg Hpssub.
    red in Ievalgetx.
    assert (Htmp := Ievalgetx _ _ _ Hf).
    unfold Inv_EvalGet, snd, fst in Htmp.
    destruct Htmp as [I0s0 [I1s0 [e [Hstabvs0 [Isigs0 [Isiginfls0 [Icorrs0 [Hxinfl Hmons] ] ] ] ] ] ] ]; auto.
    assert (Iwrap1 := IH _ _ _ Evalgetx Ievalgetx Hf').
    (*assert (Hxstas' : is_stable x s0)
      by (clear - Hxsta I1s0; simpl in *; now fsetdec).*)
    assert (Hcons : forall p,
                      In p (ps ++ [(v, d0)]) ->
                      is_stable (fst p) s0 /\
                      D.Leq (snd p) (getval s0 (fst p))).
    { intros p Hp.
      apply in_app_or in Hp.
      case Hp as [Hin | ep].
      - assert (Htmp := Hps _ Hin).
        split.
        + clear - Htmp I1s0.
          simpl in *; now intuition; fsetdec.
        + now apply (D.LeqTrans (proj2 Htmp)).
      - simpl in ep.
        destruct ep as [ep | ?]; [| easy].
        subst p. unfold fst, snd. now subst d0; auto. }
    assert (Hlegcons : legal (rhs x) (ps ++ [(v, d0)]))
      by (eapply legal_step; eauto).
    assert (Hsubcons : subtree (rhs x) (ps ++ [(v, d0)]) = k d0)
      by (eapply subtree_step; eauto).
    red in Iwrap1.
    destruct Iwrap1 as [I0s1 [I1s1 (*[Hincl*) (*[H0ps1*) (*[H1ps1*) [H2ps1 [Icorrs1 [Isigs1 [Isiginfls1 [Hlegps1 [Hsubps1 [H Hmons0] ] ] ] ] ] ] (*]*) (*]*) (*]*) ] ]; auto.
    assert (Hsol01 : VS.Subset (get_solved s0) (get_solved s1))
      by (clear - I1s1; simpl in *; now fsetdec).
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split(*; [| split; [| split; [| split] ] ]*) ] ] ] ] ] ] ] ]; auto.
    * now eapply Inv_1_trans; eauto.
    (** clear - Hincl; now firstorder.*)
    (** intros p Hp1 Hp2.
      case (in_dec VDeq_dec p (ps ++ [(v, d0)])) as [i | n];
        [| now apply D.LeqTrans with (y:=getval s0 (fst p)); auto].
      assert (ep : p = (v, d0)).
      { clear - i Hp2. apply in_app_or in i. now firstorder. }
      now rewrite ep, e; unfold fst, snd.*)
    * now eapply Inv_sigma_trans; eauto.
    * now eapply Inv_sigma_infl_trans; eauto.
    * intros Hcalxs1 Hval Hpsinfl.
      assert (Hcalxs0 : is_called x s0)
        by (clear - Hcalxs1 I1s1; simpl in *; now fsetdec).
      assert (H1 : forall p, In p ps -> getval s (fst p) = getval s0 (fst p))
        by (eapply Lem_x_infl_getval; eauto).
      assert (Hvalcons : valid (getval s0) (ps ++ [(v, d0)])).
      { simpl.
        apply valid_app; [| rewrite e; now apply valid_cons].
        now apply valid_compat with (f1:=getval s). }
      assert (H2 : forall p, In p (ps ++ [(v, d0)]) ->
                             In x (get_infl s0 (fst p))).
      { intros p Hin. apply in_app_or in Hin.
        case Hin as [n | i].
        - apply (proj1 (Isiginfls0 (fst p))); auto.
          now rewrite H1; auto.
        - destruct i as [i | ?]; [| easy].
          now subst p; unfold fst. }
      now auto.

(* Inv_Eval_rhs *)
- idtac.
  intros x f s [d [s0 vlist] ].
  destruct_pose_state s.
  destruct_pose_state s0.
  intros Hevalgetx Ievalgetx Hwrapx Iwrapx.
  intros (*Hstabx*) I0s Icorrs.
  red in Iwrapx.
  assert (H : forall p : Var.t * D.t,
                In p [] ->
                is_stable (fst p) s /\
                D.Leq (snd p) (getval s (fst p))) by firstorder.
  assert (Htmp := Iwrapx (*Hstabx*) I0s Icorrs H (legal_nil _) (subtree_nil _)); clear Iwrapx H.
  destruct Htmp as [I0s0 [I1ss0 (*[_ [_*) (*[ Hvlist1*) [Hvlist2 [Icorrs0 [Isigs0 [Isiginfls0 [Hleg [Hsub [H Hmons] ] ] ] ] ] ] (*]*) (*] ]*) ] ].
  split; [| split; [| split; [| split; [| split;
    [| split; [| split; [| split; [| split] ] ] ] ] ] ] ]; auto.
  + intros Hcalxs0.
    assert (Htmp : forall p : Var.t * D.t, In p [] -> In x (get_infl s (fst p))) by firstorder.
    assert (H0 := H Hcalxs0 (valid_nil _) Htmp); clear H Htmp; rename H0 into H.
    split; [| split; [| split ] ]; try easy.
    * eapply valid_legal_subtree_Ans; eauto; now intuition.
    * symmetry.
      eapply valid_legal_subtree_Ans; eauto; now intuition.
  + split; auto.
    intros Hcalxs0.
    assert (Hval : valid (getval s0) vlist) by now apply H.
    assert (Hd : d = [[rhs x]]* (getval s0))
      by now eapply valid_legal_subtree_Ans; eauto.
    rewrite Hd.
    now apply D.LeqTrans with (y:=[[rhs x]]* mu); auto.

(* Inv_Solve 0 *)
- idtac. red. now intuition; auto.

(* Inv_Solve 1 *)
- idtac. intros x d s s0 vlist.
  destruct_pose_state s.
  destruct_pose_state s0.
  intros Hnstabx s' Hevalrhs Ievalrhs Hncalxs0.
  red. intros I0s Icorrs.
  assert (Hcalxs' : is_called x s') by (simpl; now fsetdec).
  assert (I0s' : Inv_0 s')
    by (clear - I0s; simpl in *; split; now fsetdec).
  assert (Icorrs' : Inv_corr s')
    by (now apply Inv_corr_prepare).
  assert (H := Ievalrhs I0s' Icorrs'); clear Ievalrhs.
  destruct H as [I0s0 [I1s0 [Icorrs0 [Isigs' [Isiginfls' H] ] ] ] ].
   split; [| split; [| split; [| split; [| split; [| split ] ] ] ] ]; auto; try easy.
  + clear - I1s0 Hncalxs0. simpl in *. intuition; now fsetdec.
  + intros _.
    clear - I1s0 Hncalxs0. simpl in *. now fsetdec.
  + destruct H as [_ [_ [_ [_ H] ] ] ].
    now firstorder.

(* Inv_Solve 2 *)
- idtac. intros x d s s0 vlist.
  destruct_pose_state s.
  destruct_pose_state s0.
  intros Hnstabx s' Hevalrhs Ievalrhs.
  intros Hcalxs0 s1 cur Hleq.
  assert (Egets' : getval s' = getval s) by auto.
  assert (Egets1 : getval s1 = getval s0) by auto.
  red. intros I0s Icorrs.
  (*assert (Hstaxs' : is_stable x s') by (simpl; now fsetdec).*)
  assert (I0s' : Inv_0 s')
    by (clear - I0s; simpl in *; split; now fsetdec).
  assert (Icorrs' : Inv_corr s')
    by (now apply Inv_corr_prepare).
  assert (H := Ievalrhs (*Hstaxs'*) I0s' Icorrs'); clear Ievalrhs.
  destruct H as [I0s0 [I1s0 [Icorrs0 [Isigs' [Isiginfls' H] ] ] ] ].
  destruct H as [_ H].
  split; [| split; [| split; [| split; [| split; [| split(*; [| split]*) ] ] ] ] ].  
  + clear - I0s0. simpl in *. split; now fsetdec.
  + clear - I1s0. simpl in *. intuition; now fsetdec.
  + red. now rewrite <- Egets'; rewrite Egets1.
  + apply Inv_sigma_infl_lemma2.
    apply (Inv_sigma_infl_trans (s2 := s')); auto.
    * clear - I1s0. simpl in *. now fsetdec.
    * now unfold s'.
    * now unfold s'.
  + case (is_called_dec x s0); [intro Hin | intro Hnotin].
    * apply Inv_corr_called; auto; [intuition |].
      destruct H as (*[_*) [_ [_ [H _] ] ] (*]*).
      destruct H as [H _]; auto.
      now rewrite <- H; fold cur.
    * now apply Inv_corr_notcalled.
  (*+ now intuition.*)
  + intros _. clear - I1s0 I0s. simpl in *. now fsetdec.
  + rewrite Egets1.
    rewrite Egets' in H.
    destruct H as (*[_*) [_ [_ [_ H] ] ] (*]*).
    now firstorder.

(* Inv_Solve_3 *)
- idtac. intros x d s s0 s1 s2 vlist work.
  destruct_pose_state s.
  destruct_pose_state s0.
  destruct_pose_state s1.
  destruct_pose_state s2.
  intros Hnstabx s' Hevalrhs Ievalrhs.
  intros Hcalxs0 s0' cur Hleq new s0'' Hhand Hsolveall Isolveall.
  intros I0s Icorrs.
  assert (Egets' : getval s' = getval s) by auto.
  (*assert (Hstaxs' : is_stable x s') by (simpl; now fsetdec).*)
  assert (I0s' : Inv_0 s')
    by (clear - I0s; simpl in *; split; now fsetdec).
  assert (Icorrs' : Inv_corr s')
    by (now apply Inv_corr_prepare).
  assert (H := Ievalrhs (*Hstaxs'*) I0s' Icorrs'); clear Ievalrhs.
  destruct H as [I0s0 [I1s0 [Icorrs0 [Isigs' [Isiginfls' H] ] ] ] ].
  destruct H as [_ H].
  assert (I0s0' : Inv_0 s0')
    by (clear - I0s0; simpl in *; now intuition).
  assert (I0s1 : Inv_0 s1).
  { assert (Hwork := extract_work_spec Hhand).
    destruct Hwork as [_ [_ Hwork] ].
    clear - I0s0' Hwork. simpl in *. split; now fsetdec. }
  assert (Icorrs1 : Inv_corr s1).
  { apply (Inv_corr_step2 (s:=s0) Hhand); auto.
    - now intuition.
    - apply Inv_corr_lemma4; auto.
      + now intuition.
      + clear - I1s0; simpl in *; now fsetdec. }
  assert (Hwspec := extract_work_spec Hhand).
  assert (Hworkncal : forall z, In z work -> ~ is_called z s1).
  { intros z Hz. clear - Hwspec Hz.
    apply inlist_oflist in Hz.
    simpl in *; now fsetdec. }
  assert (H0 := Isolveall I0s1 Icorrs1 Hworkncal); clear Isolveall.
  destruct H0 as [I0s2 [I1s2 [Isigs2 [Isiginfls2 [Icorrs2 [Hsol2 Hmon2] ] ] ] ] ].
  assert (Isigss0 : Inv_sigma s s0) by auto.
  assert (Isigs0s1 : Inv_sigma s0 s1).
  { eapply Inv_sigma_extract_work; [| now refine Hhand]; clear Hhand.
    intros z. case (eq_dec x z) as [e | n].
    - subst z. unfold s0''. rewrite setval_getval_corr.
      now apply D.JoinUnique.
    - simpl. now rewrite add_neq_o. }
  assert (Isigss1 : Inv_sigma s s1)
    by (eapply Inv_sigma_trans; eauto).
  assert (Isigss2 : Inv_sigma s s2)
    by (eapply Inv_sigma_trans; eauto).
  assert (Hsols2 : VS.Subset (get_solved s1) (get_solved s2))
    by (clear - I1s2 Hsol2; simpl in *; now fsetdec).
  assert (Einfls : forall z, get_infl s' z = get_infl s z) by auto.
  assert (Einfls1 : forall z, x <> z -> get_infl s1 z = get_infl s0 z).
  { intros z ne. clear - ne Hwspec.
    destruct Hwspec as [_ [_ [H _] ] ].
    simpl in *. rewrite H. now rewrite remove_neq_o. }
  assert (Hvals' : forall z, getval s' z = getval s z) by auto.
  assert (Evals1 : forall z, x <> z -> getval s1 z = getval s0 z).
  { clear - Hwspec. intros z ne.
    destruct Hwspec as [_ [H _ ] ].
    simpl in *; subst. now rewrite add_neq_o. }
  assert (Hvals1 : getval s1 x = D.join cur d).
  { clear - Hwspec.
    destruct Hwspec as [_ [H _ ] ].
    simpl in *; subst. now rewrite add_eq_o. }
  assert (Hwork : work = get_infl s0 x) by (now inversion Hhand).
  assert (Hsta2 : VS.Subset
                    (VS.union (of_list work) (get_stable s1))
                    (get_stable s2))
    by (clear - I1s2 Hsol2; simpl in *; now fsetdec).
  assert (Hque2 : VS.Subset
                    (get_queued s2)
                    (VS.diff (get_queued s1) (of_list work)))
    by (clear - Hsta2 I0s2 I1s2; simpl in *; now fsetdec).
  assert (I1ss2 : Inv_1 s s2).
  { clear - I1s0 I1s2 Hwspec Hsta2 Hque2 I0s.
    destruct Hwspec as [_ [_ [_ H] ] ].
    simpl in *.
    split; [| split].
    - clear - H Hsta2 I1s0.
      destruct H as [H _].
      destruct I1s0 as [H0 _].
      now fsetdec.
    - clear - H I0s I1s0 I1s2.
      destruct H as [_ [H _] ].
      destruct I1s0 as [_ [H0 _] ].
      destruct I1s2 as [_ [H1 _] ].
      destruct I0s as [H2 _].
      now fsetdec.
    - clear - Hque2 H I1s0 I1s2.
      destruct H as [_ [_ H] ].
      destruct I1s0 as [_ [_ H0] ].
      destruct I1s2 as [_ [_ H1] ].
      now fsetdec. }
  assert (Isiginflss2 : Inv_sigma_infl s s2).
  { intros z. split.
    - intros Hleqs1s.
      assert (Evalz2 : getval s2 z  = getval s z)
        by (apply D.LeqAntisym; auto; eapply D.LeqTrans; eauto).
      assert (Evalz1 : getval s1 z = getval s z)
        by (apply D.LeqAntisym; [rewrite <- Evalz2 |]; now firstorder).
      assert (Evalz12 : getval s1 z = getval s2 z)
        by (rewrite Evalz1, Evalz2; auto).
      assert (Evalz0 : getval s0 z = getval s z).
      { apply D.LeqAntisym; auto.
        apply D.LeqTrans with (y:=getval s1 z); auto.
        now rewrite Evalz1. }
      assert (Evalz0' : getval s0' z = getval s0 z) by auto.
      assert (ne : x <> z).
      { contradict Hleq. subst z.
        unfold cur. rewrite Evalz0', Evalz0, <- Evalz1, Hvals1.
        now apply D.JoinUnique. }
      destruct (Isiginfls' z) as [Htmp1 _].
      rewrite Hvals', Evalz0, Einfls, <- Einfls1 in Htmp1; auto.
      apply incl_tran with (m:=get_infl s1 z); auto.
      clear Htmp1.
      destruct (Isiginfls2 z) as [Htmp2 _].
      now rewrite Evalz12 in Htmp2; auto.
    - intros Hnleqs1s.
      red in Isiginfls'.
      case (D.eq_dec (getval s z) (getval s0 z)) as [e0 | n0].
      + destruct (Isiginfls' z) as [Htmp1 _].
        rewrite Einfls, Hvals' in Htmp1.
        assert (Hleqs0s : D.Leq (getval s0 z) (getval s z))
          by (rewrite <- e0; auto).
        intros u Hu.
        assert (Hinflz0 : In u (get_infl s0 z)) by intuition.
        case (eq_dec x z) as [e | n].
        * subst z.
          assert (Huwork : VS.In u (of_list work))
            by (apply inlist_oflist; rewrite Hwork; now intuition).
          clear - Huwork Hsol2; simpl in *; now fsetdec.
        * rewrite <- Einfls1 in Hinflz0; auto.
          rewrite <- Evals1 in Hleqs0s; auto.
          red in Isiginfls2.
          assert (Hnleqs2s1 : ~ D.Leq (getval s2 z) (getval s1 z))
            by (contradict Hnleqs1s; now rewrite e0, <- Evals1).
          destruct (Isiginfls2 z) as [_ Htmp2].
          now intuition.
      + assert (Hnleqs0s : ~ D.Leq (getval s0 z) (getval s z))
          by (contradict n0; now apply D.LeqAntisym).
        destruct (Isiginfls' z) as [_ Htmp2].
        rewrite Hvals', Einfls in Htmp2.
        intros u Hu.
        assert (Hsolus0 : is_solved u s0) by auto.
        clear - Hwspec Hsol2 Hsolus0.
        destruct Hwspec as [_ [_ [_ H] ] ].
        simpl in *. now fsetdec. }
  split; [| split; [| split; [| split; [| split; [| split(*; [| split]*) ] ] ] ] ]; auto.
  (*+ now intuition.*)
  + intros _.
    destruct Hwspec as [_ [_ [_ Htmp] ] ].
    clear - Htmp Hsol2 I1s0 I1s2.
    (*destruct H0 as [H01 [H02 [H03 _] ] ].*)
    simpl in *. now intuition; fsetdec.
  + intros mu Huniq Hmon Hsolmu. (*Hlemu.*)
    cut (leqF (getval s1) mu); [now intuition |].
    intros z.
    destruct H as (*[_*) [_ [_ [_ H] ] ] (*]*).
    destruct (Var.eq_dec z x) as [e | n].
    * subst z.
      rewrite Hvals1.
      apply D.JoinUnique.
      split; [ unfold cur; now eapply H | now eapply H].
    * rewrite Evals1; auto.
      now eapply H.

(* Inv_SolveAll_0 *)
- idtac. intros s I0s Icorrs _.
  now intuition; auto; firstorder.

(* Inv_SolveAll_1 *)
- idtac. intros x w s s0 s1.
  destruct_pose_state s.
  destruct_pose_state s0.
  destruct_pose_state s1.
  intros Hsolve Isolve Hsolveall Isolveall.
  red. intros I0s Icorrs Hs.
  assert (H := Isolve I0s Icorrs); clear Isolve.
  destruct H as
    [I0s0 [I1s0 [Isigs0 [Isiginfls0 [Icorrs0 (*[Hsta0*) [Hnsta0 Hmons] (*]*) ] ] ] ] ].
  assert (Hxwset : forall u, VS.In u (of_list (x :: w)) -> ~ is_called u s).
  { clear - Hs. intros u.
    assert (Htmp :=proj2 (@inlist_oflist u (x :: w))).
    now firstorder. }
  assert (Hws0 : forall z, In z w -> ~ is_called z s0)
    by (clear - Hs I1s0; firstorder).
  assert (H := Isolveall I0s0 Icorrs0 Hws0); clear Isolveall.
  destruct H as [I0s1 [I1s1 [Isigs1 [Isiginfls1 [Icorrs1 (*[Hsta1 [Hque1*) [Hsol1 Hmons0] (*] ]*) ] ] ] ] ].
  assert (Hsol : VS.Subset (get_solved s0) (get_solved s1))
    by (clear - I1s1; simpl in *; now fsetdec).
  assert (Hxwsta1 : forall u,
                      In u (x :: w) \/ is_stable u s ->
                      is_stable u s1).
  { intros u Hu. destruct Hu as [ [e | Hinu] | Hstabu].
    - subst u.
      case (is_stable_dec x s) as [i | n].
      + clear - i I1s0 I1s1. now simpl in *; fsetdec.
        (*assert (e : s = s0) by auto. rewrite e in i.
        clear - Hnsta0 I1s1 i. now simpl in *; fsetdec.*)
      + idtac.
        assert (Htmp : is_stable x s0)
          by (clear - n Hnsta0; simpl in *; now fsetdec).
        clear - Htmp I1s1. simpl in *; now fsetdec.
    - apply inlist_oflist in Hinu.
      clear - Hinu (*Hsta1*) Hsol1; simpl in *; now fsetdec.
    - clear - I1s0 I1s1 Hstabu; simpl in *; now fsetdec. }
  assert (Hxwsta1set : VS.Subset (VS.union (of_list (x :: w))
                                           (get_stable s))
                                 (get_stable s1)).
  { clear - Hxwsta1. intros u Hu.
    assert (Htmp := proj2 (@inlist_oflist u (x :: w))).
    apply VS.union_spec in Hu.
    simpl in *. now intuition. }
  clear Hxwsta1.
  rewrite oflist_cons. rewrite oflist_cons in Hxwsta1set.
  split; [| split; [| split; [| split; [| split; [| split(*;
    [| split; [| split] ]*) ] ] ] ] ]; auto.
  + now eapply Inv_1_trans; eauto.
  + now eapply Inv_sigma_trans; eauto.
  + now eapply Inv_sigma_infl_trans; eauto.
  (*+ clear - Hque1 I1s1 I1s0 Hxwsta1set I0s1.
    simpl in *; now fsetdec.*)
  + clear - Hxwset Hxwsta1set I1s0 I1s1.
    intros u Hu.
    rewrite VS.union_spec in Hu. case Hu as [Hu1 | Hu2].
    * assert (Huncals : ~ is_called u s)
        by (clear - Hu1 Hxwset; simpl in *; now firstorder).
      clear - Hxwsta1set I1s0 I1s1 Hu1 Huncals; simpl in *; now fsetdec.
    * clear - I1s0 I1s1 Hu2; simpl in *; now fsetdec.
Qed.
(*XXX*)

Lemma Inv_0_init : Inv_0 s_init.
Proof. simpl; split; now fsetdec. Qed.

Lemma Inv_corr_init : Inv_corr s_init.
Proof.
red. simpl. now split; intros; fsetdec.
Qed.

Theorem correctness w s :
  SolveAll w s_init s ->
  (forall z, In z w -> is_stable z s) /\
  (forall z v d,
     is_stable z s ->
     In (v,d) (deps (rhs z) (getval s)) ->
     is_stable v s) /\
  (forall z,
     is_stable z s -> D.Leq ([[rhs z]]* (getval s)) (getval s z)).
Proof.
destruct_pose_state s.
intros Hsolveall.
assert (Isolveall : Inv_SolveAll w s_init s)
  by (now apply InvariantsLemma).
red in Isolveall.
assert (Htmp : forall x, In x w -> ~ is_called x s_init)
  by (simpl; intros; fsetdec).
assert (H := Isolveall Inv_0_init Inv_corr_init Htmp).
clear Htmp Isolveall.
destruct H as [I0 [I1 [Isig [Isiginfl [Icorr (*[Hsta*) [Hsol Hque] (*]*) ] ] ] ] ].
split; [| split].
- intros u Hu.
  assert (Htmp := proj1 (inlist_oflist u w)).
  simpl in *; intuition; now fsetdec.
- intros z v d Hstaz Hin. red in Icorr.
  assert (Hsolz : is_solved z s)
    by (clear - Hstaz I1; simpl in *; fsetdec).
  assert (Hnquez : ~ is_queued z s)
    by (clear - Hstaz I1; simpl in *; fsetdec).
  destruct Icorr as [H _].
  destruct (H _ _ _ Hsolz Hin) as [_ ?];
    clear H Isiginfl Isig; now firstorder.
- intros z Hstaz.
  assert (Hsolz : is_solved z s)
    by (clear - Hstaz I1; simpl in *; fsetdec).
  destruct Icorr as [_ H]. now intuition.
Qed.

Lemma leqF_init mu : leqF (getval s_init) mu.
Proof.
intros x. simpl. now rewrite empty_o.
Qed.
Local Hint Resolve leqF_init.

Theorem exactness :
  is_monotone rhs ->
  forall mu w s,
    is_solution rhs mu ->
    SolveAll w s_init s ->
    leqF (getval s) mu.
Proof.
intros Hmon mu w s Hsolmu Hsolallw.
assert (Isolveall : Inv_SolveAll w s_init s)
  by (now apply InvariantsLemma).
red in Isolveall.
assert (Htmp : forall x, In x w -> ~ is_called x s_init)
  by (simpl; intros; fsetdec).
assert (H := Isolveall Inv_0_init Inv_corr_init Htmp).
clear Htmp Isolveall.
now intuition; auto.
Qed.

End algorithm.

End SolverRLDEInstr.
