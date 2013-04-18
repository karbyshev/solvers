Require Import MSetFacts.
Require Import MSetProperties.
Require Import MSetDecide.
Require Import FMapFacts.
Require Export Solvers.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SolverRLDtotalI (Sys : CSysJoinSemiLat)
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
Module Import UtilD := UtilJoin (D).

(*****************************************************************)
(************* Instrumented algorithm specification **************)
(*****************************************************************)

(* equation system *)
Definition F := Sys.F.


Section algorithm.

Variable Hpure : forall x, is_pure (F x).
Definition rhs x : Tree Var.t D.t D.t := proj1_sig (Hpure x).

Lemma rhs_spec x : F x = [[rhs x]].
Proof. now rewrite (proj2_sig (Hpure x)). Qed.

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

Definition is_stable_b x (s : state') : bool :=
  let '(_, _, stable, _, _) := s in VS.mem x stable.


Lemma is_stable_1 x (s : state') :
  is_stable x s -> is_stable_b x s = true.
Proof.
destruct_state s; simpl. now auto with set.
Qed.

Lemma is_stable_2 x (s : state') :
  is_stable_b x s = true -> is_stable x s.
Proof.
destruct_state s; simpl. now auto with set.
Qed.
Local Hint Resolve is_stable_1 is_stable_2.

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
Proof.
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
Definition instr A B S (f : A -> (StateT S Error) B)
  : A -> (StateT (S * list (A * B)) Error) B
  := fun a s' =>
       let (s, l) := s' in
       do ds1 <- f a s;
       let (d, s1) := ds1 in
         return _ (d, (s1, l ++ [(a, d)])).

Fixpoint solve (n : nat) (x : Var.t) (s : state') : Error state' :=
  match n with
    | 0 => error
    | S k =>
        if is_stable_b x s then
          return _ s
        else
          let s0 := prepare x s in
          do p <- F x (instr (evalget k x)) (s0,[]);
          let '(d, (s1, vlist)) := p in
          let s3 := rem_called x s1 in
          let cur := getval s1 x in
            if D.leq d cur then
              return _ s3
            else
              let new := D.join cur d in
              let s4 := setval x new s3 in
              let (w,s5) := extract_work x s4 in
                solve_all k w s5
  end

with solve_all (n : nat) w s : Error state' :=
  match n with
    | 0 => error
    | S k =>
        match w with
          | [] => Some s
          (*| [x] => solve k x s*)
          | x :: l => (solve k x s) >>= solve_all k l
        end
  end

with evalget (n : nat) (x y : Var.t) : (StateT state') Error D.t :=
  match n with
    | 0 => fun s => error
    | S k =>
        fun s =>
          do s1 <- solve k y s;
          let s2 := add_infl y x s1 in
          let d := getval s1 y in
          return _ (d, s2)
  end.

Definition s_init : state'
  := (Sigma.empty D.t,
      Infl.empty (list Var.t),
      VS.empty,
      VS.empty,
      VSet.empty).

Definition main n (w : list Var.t) :=
  do s <- solve_all n w s_init;
  let '(sigma,_,_) := s in
    return _ sigma.

Section graph.

Inductive EvalGet :
  nat -> Var.t -> Var.t -> state' -> option (D.t * state') -> Prop :=
  | EvalGet0 :
      forall x y s,
        EvalGet 0 x y s error
  | EvalGet1 :
      forall m x y s,
        Solve m y s error ->
        EvalGet (S m) x y s error
  | EvalGet2 :
      forall m x y s s0,
        Solve m y s (value s0) ->
        let s1 := add_infl y x s0 in
        let d := getval s0 y in
          EvalGet (S m) x y s (value (d, s1))

with EvalGet_x :
  nat -> Var.t -> (Var.t -> (StateT state' Error) D.t) -> Prop :=
  | EvalGet_x0 :
      forall n x f,
        (forall y s0 ds1,
           f y s0 = ds1 -> EvalGet n x y s0 ds1) ->
        EvalGet_x n x f

with Wrap_Eval_x :
  nat -> Var.t -> (Var.t -> (StateT state' Error) D.t) ->
  @Tree Var.t D.t D.t ->
  state' * list (Var.t * D.t) ->
  option (D.t * (state' * list (Var.t * D.t))) -> Prop :=
  | Wrap_Eval_x0 :
      forall n x f t sl dsl0,
        EvalGet_x n x f ->
        let f' := instr f in
        [[t]] _ f' sl = dsl0 ->
        Wrap_Eval_x n x f t sl dsl0

with Eval_rhs :
  nat ->
  Var.t ->
  state' -> option (D.t * (state' * list (Var.t * D.t))) -> Prop :=
  | Eval_rhs0 :
    forall n x f s dsl0,
      EvalGet_x n x f ->
      Wrap_Eval_x n x f (rhs x) (s,[]) dsl0 ->
      Eval_rhs n x s dsl0

with Solve :
  nat -> Var.t -> state' -> Error state' -> Prop :=
  | Solve0 :
      forall x s, Solve 0 x s error
  | Solve1 :
      forall m x s,
        is_stable x s -> Solve (S m) x s (value s)
  | Solve2 :
      forall m x s,
        ~ is_stable x s ->
        let s1 := prepare x s in
        Eval_rhs m x s1 error ->
        Solve (S m) x s error
  | Solve3 :
      forall m x d s s2 ps,
        ~ is_stable x s ->
        let s1 := prepare x s in
        Eval_rhs m x s1 (value (d, (s2, ps))) ->
        let cur_val := getval s2 x in
        let s3 := rem_called x s2 in
        D.Leq d cur_val ->
        Solve (S m) x s (value s3)
  | Solve4 :
      forall m x d s s2 s5 os6 ps work,
        ~ is_stable x s ->
        let s1 := prepare x s in
        Eval_rhs m x s1 (value (d, (s2,ps))) ->
        let cur_val := getval s2 x in
        let s3 := rem_called x s2 in
        ~ D.Leq d cur_val ->
        let new_val := D.join cur_val d in
        let s4 := setval x new_val s3 in
        (work, s5) = extract_work x s4 ->
        SolveAll m work s5 os6 ->
        Solve (S m) x s os6

with SolveAll :
  nat -> list Var.t -> state' -> Error state' -> Prop :=
  | SolveAll0 :
      forall w s, SolveAll 0 w s error
  | SolveAll1 :
      forall m s, SolveAll (S m) [] s (value s)
  | SolveAll2 :
      forall m x xs s,
        Solve m x s error ->
        SolveAll (S m) (x :: xs) s error
  | SolveAll3 :
      forall m x xs s s1 os2,
        Solve m x s (value s1) ->
        SolveAll m xs s1 os2 ->
        SolveAll (S m) (x :: xs) s os2.

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

Hint Constructors
     EvalGet EvalGet_x Wrap_Eval_x Eval_rhs Solve SolveAll.

Lemma evalget_step n x y s :
  evalget (S n) x y s =
  do s1 <- solve n y s;
  let s2 := add_infl y x s1 in
  let d := getval s1 y in
     return _ (d, s2).
Proof. easy. Qed.

Lemma solve_step n x s :
  solve (S n) x s =
  if is_stable_b x s then
    value s
  else
    let s0 := prepare x s in
    do p <- F x (instr (evalget n x)) (s0,[]);
    let '(d, (s1, ps)) := p in
    let cur := getval s1 x in
    let s3 := rem_called x s1 in
      if D.leq d cur then
        return _ s3
      else
        let new := D.join cur d in
        let s4 := setval x new s3 in
        let (w,s5) := extract_work x s4 in
          solve_all n w s5.
Proof. easy. Qed.

Lemma solve_all_step n w s :
  solve_all (S n) w s =
  match w with
    | nil => value s
    | x :: l => do X <- solve n x s; solve_all n l X
  end.
Proof. easy. Qed.

Lemma graph_is_correct :
  forall n,
    (forall x y s os',
       evalget n x y s = os' -> EvalGet n x y s os') /\
    (forall x, EvalGet_x n x (evalget n x)) /\
    (forall x t sl odsl',
       [[t]] _ (instr (evalget n x)) sl = odsl' ->
       Wrap_Eval_x n x (evalget n x) t sl odsl') /\
    (forall x s ods',
       F x (instr (evalget n x)) (s,[]) = ods' ->
       Eval_rhs n x s ods') /\
    (forall x s os', solve n x s = os' -> Solve n x s os') /\
    (forall w s os', solve_all n w s = os' -> SolveAll n w s os').
Proof.
induction n as [| n [IHevalget [IHevalgetx [IHwrapevalx [IHevalrhs [IHsolve IHsolveall] ] ] ] ] ].
- assert (Hevalgetx0 : forall x, EvalGet_x 0 x (evalget 0 x))
    by (intros; apply EvalGet_x0; intros; simpl in *; now subst).
split; [| split; [| split; [| split; [| split ] ] ] ]; auto;
    try (intros; simpl in *; now subst).
  + intros x s ods' H. rewrite rhs_spec in H.
    now apply Eval_rhs0 with (f:=evalget 0 x); auto.
- idtac.
  assert (Hevalget :
          forall x y s os',
            evalget (S n) x y s = os' -> EvalGet (S n) x y s os').
  { intros x y s os'.
    rewrite evalget_step.
    destruct (solve n y s) as [s0 |] eqn:Esol;
      simpl; intros; now subst; auto. }
  split; [| split; [| split; [| split; [| split] ] ] ]; auto.
  + intros x s ods' HF. rewrite rhs_spec in HF.
    now apply Eval_rhs0 with (f:=evalget (S n) x); auto.
  + intros x s os'. rewrite solve_step.
    case_eq (is_stable_b x s); intro Hb;
      [assert (is_stable x s) by auto; intros; now subst; auto |].
    assert (Hnstaxs : ~ is_stable x s)
      by (intros Hsta; now rewrite (is_stable_1 Hsta) in Hb).
    set (s0 := prepare x s).
    destruct (F x (instr (evalget n x)) (s0,[])) as [ [d1 [s1 ps1] ] |] eqn:EF;
      [| simpl; rewrite EF; intros; now subst; auto].
    set (cur := getval s1 x).
    set (new := D.join cur d1).
    case (D.eq_dec new cur) as [e | ne].
    * assert (Hle : D.Leq d1 cur) by now rewrite <- e; subst.
      assert (Ele : D.leq d1 cur = true)
        by now apply D.leqProper.
      simpl. rewrite EF. fold cur. rewrite Ele.
      now intros; subst; eauto.
    * assert (Hnle : ~ D.Leq d1 cur).
      { contradict ne. unfold new. now apply UtilD.joinSubsume2. }
      assert (Enle : D.leq d1 cur = false).
      { case_eq (D.leq d1 cur); auto.
        intros Ele. now apply D.leqProper in Ele. }
      simpl. rewrite EF. fold cur new. rewrite Enle.
      set (s2 := rem_called x s1).
      set (s3 := setval x new s2).
      set (w := get_infl s3 x).
      set (s4 := handle_work w (rem_infl x s3)).
      intros H.
      assert (Hw : (w, s4) = extract_work x s3) by auto.
      now eauto.
  + intros w s os'. rewrite solve_all_step.
    destruct w as [| x xs]; [intros; now subst |].
    destruct (solve n x s) as [s0 |] eqn:Esol;
      simpl; intros; now subst; eauto.
Qed.

End graph.

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
    * now rewrite <- H.
    * assert (Hsolx : is_solved x s)
        by (clear - Hncalx Hstazs; simpl in *; fsetdec).
      hnf.
      now apply D.LeqTrans with (y:=getval s x); auto.
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

Lemma Lem_x_infl_getval s s1 x (ps : list (Var.t * D.t)) :
    is_called x s1 ->
    Inv_sigma s s1 ->
    Inv_sigma_infl s s1 ->
    (forall p, In p ps -> In x (get_infl s (fst p))) ->
    forall p, In p ps -> getval s (fst p) = getval s1 (fst p).
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
  (x y : Var.t) (s : state') (op : option (D.t * state')) :=
  forall p, op = value p ->
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
    has_uniq_lookup rhs ->
    is_monotone rhs ->
    is_solution rhs mu ->
    leqF (getval s) mu -> leqF (getval s') mu).

Definition Inv_EvalGet_x
  (x : Var.t) (f : Var.t -> (StateT state' Error) D.t) :=
  forall y s ds1,
    f y s = ds1 -> Inv_EvalGet x y s ds1.

Definition Inv_Wrap_Eval_x
  (x : Var.t) (f : Var.t -> (StateT state' Error) D.t)
  (t : Tree Var.t D.t D.t)
  (sl : state' * list (Var.t * D.t))
  (odsl' : option (D.t * (state' * list (Var.t * D.t)))) :=
  forall dsl', odsl' = Some dsl' ->
  let (s, ps) := sl in
  let '(d, (s', ps')) := dsl' in
  Inv_0 s ->
  Inv_corr s ->
  (forall p,
     In p ps ->
     is_stable (fst p) s /\ D.Leq (snd p) (getval s (fst p))) ->
  legal (rhs x) ps ->
  subtree (rhs x) ps = t ->
  Inv_0 s' /\
  Inv_1 s s' /\
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
    has_uniq_lookup rhs ->
    is_monotone rhs ->
    is_solution rhs mu ->
    leqF (getval s) mu -> leqF (getval s') mu).


Definition Inv_Eval_rhs
  (x : Var.t) (s : state')
  (odsl' : option (D.t * (state' * list (Var.t * D.t)))) :=
  forall dsl', odsl' = Some dsl' ->
  let '(d, (s', ps)) := dsl' in
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
    has_uniq_lookup rhs ->
    is_monotone rhs ->
    is_solution rhs mu ->
    leqF (getval s) mu ->
    leqF (getval s') mu /\ D.Leq d (mu x)).

Definition Inv_Solve
  (x : Var.t) (s : state') (os' : Error state') :=
  forall s', os' = Some s' ->
  Inv_0 s ->
  Inv_corr s ->
  Inv_0 s' /\
  Inv_1 s s' /\
  Inv_sigma s s' /\
  Inv_sigma_infl s s' /\
  Inv_corr s' /\
  (~ is_stable x s -> is_solved x s') /\
  (* monotonic case *)
  (forall mu,
     has_uniq_lookup rhs ->
     is_monotone rhs ->
     is_solution rhs mu ->
     leqF (getval s) mu -> leqF (getval s') mu).

Definition Inv_SolveAll
  (w : list Var.t) (s : state') (os' : Error state') :=
  forall s', os' = Some s' ->
  Inv_0 s ->
  Inv_corr s ->
  (forall x, In x w -> ~ is_called x s) ->
  Inv_0 s' /\
  Inv_1 s s' /\
  Inv_sigma s s' /\
  Inv_sigma_infl s s' /\
  Inv_corr s' /\
  (* all variables from worklist are solved: *)
  (VS.Subset
     (VS.union (of_list w) (get_solved s))
     (get_solved s')) /\
  (* monotonic case *)
  (forall mu,
    has_uniq_lookup rhs ->
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
  (forall n x y s1 p,
     EvalGet n x y s1 p -> Inv_EvalGet x y s1 p) /\
  (forall n x f,
    EvalGet_x n x f -> Inv_EvalGet_x x f) /\
  (forall n x f t sl1 dsl2,
    Wrap_Eval_x n x f t sl1 dsl2 ->
    Inv_Wrap_Eval_x x f t sl1 dsl2) /\
  (forall n x s1 dsl2,
    Eval_rhs n x s1 dsl2 -> Inv_Eval_rhs x s1 dsl2) /\
  (forall n x s1 s2,
    Solve n x s1 s2 -> Inv_Solve x s1 s2) /\
  (forall n w s1 s2,
    SolveAll n w s1 s2 -> Inv_SolveAll w s1 s2).
(*Admitted.*)
(*XXX*)

Proof.
apply solve_mut_ind.

(* EvalGet0 *)
- easy.

(* EvalGet1 *)
- easy.

(* EvalGet2 *)
- idtac.
  intros n x y s s0.
  destruct_pose_state s.
  destruct_pose_state s0.
  intros H Hinv s1 d.
  intros p ep. inversion ep; subst; clear ep.
  intros I0s Icorrs. unfold fst, snd.
  assert (Hval : getval s1 = getval s0) by auto.
  rewrite Hval; clear Hval.
  unfold Inv_Solve in Hinv.
  specialize Hinv with s0.
  destruct Hinv as [I0 [I1 [Isig [Isiginfl [Icor [Hnstaby Hmon] ] ] ] ] ]; auto.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split] ] ] ] ] ] ]; auto.
  + clear - Hnstaby I1.
    case (is_stable_dec y s) as [i | n];
      simpl in *; now intuition; fsetdec.
  + now apply Inv_sigma_infl_lemma1.
  + now apply Inv_corr_lemma1.
  + simpl. now rewrite add_eq_o; auto with *.

(* EvalGet_x0 *)
- easy.

(* Wrap_Eval_x0 *)
- idtac.
  intros n x f.
  induction t as [| v k IH].
  + intros [s ps] odsl0 Evalgetx Ievalgetx f' Hf'.
    destruct odsl0 as [ [d [s0 ps'] ] |]; [| now intuition].
    inversion_clear Hf'; subst.
    destruct_pose_state s.
    destruct_pose_state s0.
    red. intros dsp' E.
    inversion E; subst dsp'; clear E.
    hnf. intuition.
      (** now firstorder.*)
      * now firstorder.
      * assert (Hps' : ps' = deps (rhs x) (getval s0))
          by (eapply valid_legal_subtree_Ans; eauto).
        hnf. rewrite <- Hps'; clear Hps'.
        now firstorder.
  + intros [s ps] odsl1 Evalgetx Ievalgetx f' Hf'.
    destruct odsl1 as [ [d1 [s1 ps1] ] |]; [| now intuition].
    destruct (f v s) as [ [d0 s0] |] eqn:Hf;
      [| now simpl in Hf'; rewrite Hf in Hf'].
    simpl in Hf'; rewrite Hf in Hf'; simpl in Hf'.
    revert Hf Hf'.
    destruct_pose_state s.
    destruct_pose_state s0.
    destruct_pose_state s1.
    intros Hf Hf'.
    red. intros dsp' E.
    inversion E; subst dsp'; clear E.
    intros (*Hxsta*) I0s Icorrs Hps Hpsleg Hpssub.
    red in Ievalgetx.
    assert (Htmp := Ievalgetx _ _ _ Hf).
    unfold Inv_EvalGet, snd, fst in Htmp.
    specialize Htmp with (d0,s0).
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
    specialize Iwrap1 with (d1,(s1,ps1)).
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
        case Hin as [? | i].
        - apply (proj1 (Isiginfls0 (fst p))); auto.
          now rewrite H1; auto.
        - destruct i as [i | ?]; [| easy].
          now subst p; unfold fst. }
      now auto.

(* Eval_rhs0 *)
- idtac.
  intros m x f s odsl0.
  destruct odsl0 as [ [d [s0 vlist] ] |]; [| now intuition].
  destruct_pose_state s.
  destruct_pose_state s0.
  intros Hevalgetx Ievalgetx Hwrapx Iwrapx.
  red. intros dsp' E.
  inversion E; subst dsp'; clear E.
  intros (*Hstabx*) I0s Icorrs.
  red in Iwrapx.
  specialize Iwrapx with (d,(s0,vlist)).
  assert (H : forall p : Var.t * D.t,
                In p [] ->
                is_stable (fst p) s /\
                D.Leq (snd p) (getval s (fst p))) by firstorder.
  assert (Htmp := Iwrapx eq_refl I0s Icorrs H (legal_nil _) (subtree_nil _)); clear Iwrapx H.
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
  + intros mu Huniq Hmon Hsol Hlemu.
    split; auto.
    assert (Htmp := uniq_deps_f Var.eq_dec (getval s) (Huniq x) Hleg Hsub).
    destruct Htmp as [f' [Hdepf' [Hvalf' Hf'] ] ].
    assert (Hdf' : d = [[rhs x]]* f')
      by (eapply valid_legal_subtree_Ans; eauto).
    assert (Hlef' : leqF f' (getval s0)).
    { intros z.
      destruct (in_dec Var.eq_dec z (fst (split vlist)))
               as [Hi | Hn].
      - assert (Hin : In (z, f' z) vlist)
          by (eapply deps_split_val; eauto).
        now apply Hvlist2 with (p:=(z, f' z)).
      - now rewrite <- Hf'. }
    rewrite Hdf'.
    apply D.LeqTrans with (y:=[[rhs x]]* mu); auto.
    now apply D.LeqTrans with (y:=[[rhs x]]* (getval s0)); auto.
    
(* Solve0 *)
- easy.

(* Solve1 *)
- idtac. red.
  intros _ x s Hstax s' es'. inversion es'; subst s'; clear es'.
  now intuition; auto.

(* Solve2 *)
- easy.

(* Solve3 *)
- idtac. intros m x d s s0 vlist.
  destruct_pose_state s.
  destruct_pose_state s0.
  intros Hnstabx s' Hevalrhs Ievalrhs.
  intros cur s1 Hleq.
  assert (Egets' : getval s' = getval s) by auto.
  assert (Egets1 : getval s1 = getval s0) by auto.
  red. intros s0' es0'; inversion es0'; subst s0'; clear es0'.
  intros I0s Icorrs.
  (*assert (Hstaxs' : is_stable x s') by (simpl; now fsetdec).*)
  assert (I0s' : Inv_0 s')
    by (clear - I0s; simpl in *; split; now fsetdec).
  assert (Icorrs' : Inv_corr s')
    by (now apply Inv_corr_prepare).
  red in Ievalrhs. specialize Ievalrhs with (d,(s0,vlist)).
  assert (H := Ievalrhs eq_refl I0s' Icorrs'); clear Ievalrhs.
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

(* Solve4 *)
- idtac. intros m x d s s0 s1 os2 vlist work.
  destruct_pose_state s.
  destruct_pose_state s0.
  destruct_pose_state s1.
  destruct os2 as [s2 |]; [| now intuition].
  destruct_pose_state s2.
  intros Hnstabx s' Hevalrhs Ievalrhs.
  intros cur s0' Hleq new s0'' Hhand Hsolveall Isolveall.
  red. intros s2' es2'; inversion es2'; subst s2'; clear es2'.
  intros I0s Icorrs.
  assert (Egets' : getval s' = getval s) by auto.
  (*assert (Hstaxs' : is_stable x s') by (simpl; now fsetdec).*)
  assert (I0s' : Inv_0 s')
    by (clear - I0s; simpl in *; split; now fsetdec).
  assert (Icorrs' : Inv_corr s')
    by (now apply Inv_corr_prepare).
  red in Ievalrhs. specialize Ievalrhs with (d,(s0,vlist)).
  assert (H := Ievalrhs eq_refl I0s' Icorrs'); clear Ievalrhs.
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
  red in Isolveall. specialize Isolveall with s2.
  assert (H0 := Isolveall eq_refl I0s1 Icorrs1 Hworkncal); clear Isolveall.
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
        unfold cur. rewrite Evalz0, <- Evalz1, Hvals1.
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
  + intros mu Huniq Hmon Hsolmu Hlemu.
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

(* SolveAll0 *)
- easy.

(* SolveAll1 *)
- idtac. intros _ s.
  red. intros s' es'; inversion es'; subst s'; clear es'.
  intros I0s Icorrs _.
  now intuition; auto; firstorder.

(* SolveAll2 *)
- easy.

(* SolveAll3 *)
- idtac. intros m x w s s0 os1.
  destruct_pose_state s.
  destruct_pose_state s0.
  destruct os1 as [s1 |]; [| now intuition].
  destruct_pose_state s1.
  intros Hsolve Isolve Hsolveall Isolveall.
  red.
  intros s1' es1'; inversion es1'; subst s1'; clear es1'.
  intros I0s Icorrs Hs.
  assert (H := Isolve s0 eq_refl I0s Icorrs); clear Isolve.
  destruct H as
    [I0s0 [I1s0 [Isigs0 [Isiginfls0 [Icorrs0 (*[Hsta0*) [Hnsta0 Hmons] (*]*) ] ] ] ] ].
  assert (Hxwset : forall u, VS.In u (of_list (x :: w)) -> ~ is_called u s).
  { clear - Hs. intros u.
    assert (Htmp :=proj2 (@inlist_oflist u (x :: w))).
    now firstorder. }
  assert (Hws0 : forall z, In z w -> ~ is_called z s0)
    by (clear - Hs I1s0; firstorder).
  assert (H := Isolveall s1 eq_refl I0s0 Icorrs0 Hws0); clear Isolveall.
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
Proof. red; simpl; now split; intros; fsetdec. Qed.

Theorem correctness n w s :
  SolveAll n w s_init (Some s) ->
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
eapply InvariantsLemma in Hsolveall.
rename Hsolveall into Isolveall.
red in Isolveall.
assert (Htmp : forall x, In x w -> ~ is_called x s_init)
  by (simpl; intros; fsetdec).
assert (H := Isolveall s eq_refl Inv_0_init Inv_corr_init Htmp).
clear Htmp Isolveall.
destruct H as [I0 [I1 [Isig [Isiginfl [Icorr [Hsol Hque] ] ] ] ] ].
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
    clear H Isiginfl Isig Hin; now firstorder.
- intros z Hstaz.
  assert (Hsolz : is_solved z s)
    by (clear - Hstaz I1; simpl in *; fsetdec).
  destruct Icorr as [_ H]. now intuition.
Qed.

Lemma leqF_init mu : leqF (getval s_init) mu.
Proof. intros x; simpl; now rewrite empty_o. Qed.
Local Hint Resolve leqF_init.

Theorem exactness : 
  has_uniq_lookup rhs ->
  is_monotone rhs ->
  forall n mu w s,
    is_solution rhs mu ->
    SolveAll n w s_init (Some s) ->
    leqF (getval s) mu.
Proof.
intros Huniq Hmon n mu w s Hsolmu Hsolallw.
eapply InvariantsLemma in Hsolallw.
rename Hsolallw into Isolveall.
red in Isolveall.
assert (Htmp : forall x, In x w -> ~ is_called x s_init)
  by (simpl; intros; fsetdec).
assert (H := Isolveall _ eq_refl Inv_0_init Inv_corr_init Htmp).
clear Htmp Isolveall.
now intuition; auto.
Qed.

End algorithm.

End SolverRLDtotalI.
