Require Import MSetFacts.
Require Import MSetProperties.
(*Require Import MSetDecide.*)
(*Require Import FMapWeakList.
Require Import FMapFacts.*)
Require Export Solvers.
Require Import RLDtoti.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SolverRLDtotal (Sys : CSysJoinSemiLat)
                      (VSet : SetsTypeOn (Sys.V))
                      (VMap : MapsTypeOn (Sys.V)).

Module Var := Sys.V.
Module D   := Sys.D.

Module Import VSetFacts := WFactsOn (Var) (VSet).
Module Import VSetProps := WPropertiesOn (Var) (VSet).
(*Module Import VSetDecide := WDecideOn (Var) (VSet).*)

(*Module Import VMapFacts := WFacts_fun (Var) (VMap).*)

Module VS := VSet.
Module Sigma := VMap.
Module Infl := VMap.

Definition F := Sys.F.

Definition state :=
  (Sigma.t D.t * Infl.t (list Var.t) * VS.t)%type.

Ltac destruct_state s :=
  let sig := fresh "sigma" in
  let inf := fresh "infl" in
  let sta := fresh "stable" in
    destruct s as [ [sig inf] sta].

Definition is_stable x (s : state) :=
  let '(_, _, stable) := s in VS.In x stable.
Definition is_stable_b x (s : state) : bool :=
  let '(_, _, stable) := s in VS.mem x stable.

Lemma is_stable_1 x (s : state) :
  is_stable x s -> is_stable_b x s = true.
Proof.
destruct_state s; simpl. now auto with set.
Qed.

Lemma is_stable_2 x (s : state) :
  is_stable_b x s = true -> is_stable x s.
Proof.
destruct_state s; simpl. now auto with set.
Qed.
Local Hint Resolve is_stable_1 is_stable_2.

Definition add_stable x (s : state) : state :=
  let '(sigma, infl, stable) := s in
    (sigma, infl, VS.add x stable).

Definition rem_stable x (s : state) : state :=
  let '(sigma, infl, stable) := s in
    (sigma, infl, VS.remove x stable).

Definition getval (s : state) x : D.t :=
  let '(sigma, _, _) := s in
    match Sigma.find x sigma with
      | Some d => d
      | None => D.bot
    end.

Definition setval x d (s : state) : state :=
  let '(sigma, infl, stable) := s in
    (Sigma.add x d sigma, infl, stable).

Definition get_infl (s : state) x : list (Var.t) :=
  let '(_, infl, _) := s in
    match Infl.find x infl with
      | Some l => l
      | None => []
    end.

Definition add_infl y x (s : state) : state :=
  let '(sigma, infl, stable) := s in
    let xs := get_infl s y in
    (sigma, Infl.add y (x :: xs) infl, stable).

Definition rem_infl x (s : state) : state :=
  let '(sigma, infl, stable) := s in
    (sigma, Infl.remove x infl, stable).

Definition handle_work w (s : state) : state :=
  fold_left (fun s x => rem_stable x s) w s.

Definition extract_work x (s : state) : (list Var.t * state) :=
  let w := get_infl s x in
  let s0 := rem_infl x s in
  let s1 := handle_work w s0 in
    (w, s1).

Fixpoint solve (n : nat) (x : Var.t) (s : state) : Error state :=
  match n with
    | 0 => error
    | S k =>
        if is_stable_b x s then
          return _ s
        else
          let s0 := add_stable x s in
          do p <- F x (evalget k x) s0;
          let (d,s1) := p in
          let cur := getval s1 x in
            if D.leq d cur then
              return _ s1
            else
              let new := D.join cur d in
              let s2 := setval x new s1 in
              let (w,s3) := extract_work x s2 in
                solve_all k w s3
  end

with solve_all (n : nat) w s : Error state :=
  match n with
    | 0 => error
    | S k =>
        match w with
          | [] => return _ s
          (*| [x] => solve k x s*)
          | x :: l => (solve k x s) >>= solve_all k l
        end
  end

with evalget (n : nat) (x y : Var.t) : (StateT state) Error D.t :=
  match n with
    | 0 => fun s => error
    | S k =>
        fun s =>
          do s1 <- solve k y s;
          let s2 := add_infl y x s1 in
          let d := getval s1 y in
          return _ (d, s2)
  end.

Definition s_init : state
  := (Sigma.empty D.t, Infl.empty (list Var.t), VS.empty).

Definition main n (w : list Var.t) :=
  do s <- solve_all n w s_init;
  let '(sigma,_,_) := s in
    return _ sigma.

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
    return _ s
  else
    let s0 := add_stable x s in
    do p <- F x (evalget n x) s0;
    let (d,s1) := p in
    let cur := getval s1 x in
      if D.leq d cur then
        return _ s1
      else
        let new := D.join cur d in
        let s2 := setval x new s1 in
        let (w,s3) := extract_work x s2 in
          solve_all n w s3.
Proof. easy. Qed.

Lemma solve_all_step n w s :
  solve_all (S n) w s =
  match w with
    | nil => return _ s
    | x :: l => do X <- solve n x s; solve_all n l X
  end.
Proof. easy. Qed.

End SolverRLDtotal.


Extraction Language Ocaml.
Set Extraction AccessOpaque.
Extraction "solverRLD" SolverRLDtotal.

Module SolverRLDtotalCorrect.

Declare Module Sys : CSysJoinSemiLat.
Declare Module VSet : SetsTypeOn (Sys.V).
Declare Module VMap : MapsTypeOn (Sys.V).

Module S  := SolverRLDtotal (Sys) (VSet) (VMap).
Module SI := RLDtoti.SolverRLDtotalI (Sys) (VSet) (VMap).

Module Var := Sys.V.
Module D   := Sys.D.
Definition F := Sys.F.

Module Import Defs := Solvers.Defs (Sys).

Module Import VSetFacts := WFactsOn (Var) (VSet).
Module Import VSetProps := WPropertiesOn (Var) (VSet).


Section correctness.

Variable Hpure : forall x, is_pure (F x).
Definition rhs x : Tree Var.t D.t D.t := proj1_sig (Hpure x).

Lemma rhs_spec x : F x = [[rhs x]].
Proof. now rewrite (proj2_sig (Hpure x)). Qed.

Section instrumentation.

Definition state := S.state.
Definition state' := SI.state'.

Definition projI (si : state') : state :=
  let '(sigma, infl, stable, _, _) := si in
    (sigma, infl, stable).

Definition sim (s : state) (si : state') := projI si = s.

(* lifted simulation relation *)
Definition simT
  (f  : Var.t -> (StateT state Error) D.t)
  (f' : Var.t -> (StateT state' Error) D.t)
  := forall x s s1 s' s1' d d',
       sim s s' ->
       f x s = Some (d, s1) ->
       f' x s' = Some (d', s1') ->
       d = d' /\ sim s1 s1'.

Lemma sim_init : sim S.s_init SI.s_init.
Proof. easy. Qed.

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
Proof. now destruct_state' s'. Qed.
Hint Resolve sim_projI.

Lemma sim_prepare x s s' (H : sim s s') :
  sim (S.add_stable x s) (SI.prepare x s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_prepare.

Lemma sim_getval s s' (H : sim s s') :
  S.getval s = SI.getval s'.
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_getval.

Lemma sim_setval x d s s' (H : sim s s') :
  sim (S.setval x d s) (SI.setval x d s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_setval.

Lemma sim_add_infl x y s s' (H : sim s s') :
  sim (S.add_infl x y s) (SI.add_infl x y s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_add_infl.

Lemma sim_get_infl s s' (H : sim s s') :
  S.get_infl s = SI.get_infl s'.
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.

Lemma sim_rem_infl x s s' (H : sim s s') :
  sim (S.rem_infl x s) (SI.rem_infl x s').
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_rem_infl.

Lemma sim_is_stable x s s' (H : sim s s') :
  S.is_stable x s <-> SI.is_stable x s'.
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.
Hint Resolve sim_is_stable.

Lemma sim_is_stable_b x s s' (H : sim s s') :
  S.is_stable_b x s = SI.is_stable_b x s'.
Proof.
destruct_state s.
destruct_state' s'.
now inversion H; subst.
Qed.

Lemma sim_add_stable x s s' (H : sim s s') :
  sim (S.add_stable x s) (SI.add_stable x s').
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
  sim (S.handle_work w s) (SI.handle_work w s').
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
  (w, s0) = S.extract_work x s ->
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
Definition evalget_sim n x y s ds1
  := forall s',
       sim s s' ->
       exists ds1',
         SI.evalget n x y s' = Some ds1' /\
         let '(d,s1) := ds1 in
         let '(d',s1') := ds1' in
           d = d' /\ sim s1 s1'.

Definition wrap_eval_x_sim n x t s ds1
  := forall s' l',
       sim s s' ->
       exists (dsl1' : D.t * (state' * list (Var.t * D.t))),
         [[t]] _ (SI.instr (SI.evalget n x)) (s',l') =
           Some dsl1' /\
         let '(d,s1) := ds1 in
         let '(d',(s1',l1')) := dsl1' in
         d = d' /\ sim s1 s1'.

Definition eval_rhs_sim n x s ds1
  := forall s',
       sim s s' ->
       exists dsl1',
       F x (SI.instr (SI.evalget n x)) (s',[]) = Some dsl1' /\
       let '(d,s1) := ds1 in
       let '(d',(s1',_)) := dsl1' in
         d = d' /\ sim s1 s1'.

Definition solve_sim n x s s1
  := forall s',
       sim s s' ->
       exists s1',
         SI.solve n x s' = Some s1' /\ sim s1 s1'.

Definition solve_all_sim n (w : list Var.t) s s1
  := forall s',
       sim s s' ->
       exists s1',
         SI.solve_all n w s' = Some s1' /\ sim s1 s1'.

Theorem simulation :
  forall n,
  (forall x y s1 ds2,
     S.evalget n x y s1 = Some ds2 ->
     evalget_sim n x y s1 ds2) /\
  (forall x t s1 ds2,
    [[t]] _ (S.evalget n x) s1 = Some ds2 ->
    wrap_eval_x_sim n x t s1 ds2) /\
  (forall x s1 ds2,
    F x (S.evalget n x) s1 = Some ds2 ->
    eval_rhs_sim n x s1 ds2) /\
  (forall x s1 s2,
    S.solve n x s1 = Some s2 -> solve_sim n x s1 s2) /\
  (forall w s1 s2,
    S.solve_all n w s1 = Some s2 -> solve_all_sim n w s1 s2).
Proof.
induction n as [| n [IHeval [IHwrapx [IHevalrhs [IHsol IHsolall] ] ] ] ].
- split; [| split; [| split; [| split] ] ];
  try (intros; intuition; easy).
  + intros x t s1 [d2 s2].
    case t as [d |]; simpl; [| now intuition].
    intros e; inversion e; subst s2 d2; clear e.
    red. intros s1' l' Hsims1.
    exists (d,(s1',l')); now auto.
  + intros x s1 [d2 s2] Hf.
    red. intros s1' Hsims.
    rewrite rhs_spec. rewrite rhs_spec in Hf.
    destruct (rhs x) as [d |].
    * simpl in *. inversion Hf; subst d2 s2; clear Hf.
      exists (d,(s1',[])); auto.
    * easy.
- assert (Heval : forall x y s1 ds2,
            S.evalget (S n) x y s1 = Some ds2 ->
            evalget_sim (S n) x y s1 ds2).
  { intros x y s [d2 s2] Heval.
    red. intros s' Hsims.
    simpl in Heval.
    destruct (S.solve n y s) as [s1 |] eqn:Hsol; [| easy].
    apply IHsol in Hsol. red in Hsol.
    destruct Hsol with (s':=s') as [s1' [Hsol' Hsims1] ]; auto.
    clear Hsol.
    pose (s2' := SI.add_infl y x s1').
    inversion Heval; subst s2.
    exists (d2,s2').
    simpl. rewrite Hsol'.
    rewrite <- sim_getval with (s:=s1); auto.
    subst d2. now unfold s2'; auto. }
  assert (Hwrapx : forall x t s1 ds2,
            tree2fun t (S.evalget (S n) x) s1 = Some ds2 ->
            wrap_eval_x_sim (S n) x t s1 ds2).
  { intros x.
    induction t as [d | a k IHt].
    - intros s [d2 s2] Hwrap.
      simpl in Hwrap.
      inversion Hwrap; subst s2 d2.
      red. simpl. intros s' l' Hsims.
      now exists (d,(s',l')); auto.
    - intros s [d2 s2] Hwrap.
      red. intros s' l' Hsims.
      pose (f := S.evalget (S n) x). fold f in Hwrap.
      simpl in Hwrap.
      destruct (f a s) as [ [d1 s1] |] eqn:Hf; [| easy].
      set (f' := SI.evalget (S n) x).
      assert (Htmp := Heval _ _ _ _ Hf). red in Htmp.
      destruct Htmp with (s':=s') as [ [d1' s1'] [Hf' [? Hsims1] ] ]; auto; subst d1'; clear Htmp.
      fold f' in Hf'.
      assert (Htmp := IHt _ _ _ Hwrap).
      red in Htmp. fold f' in Htmp.
      destruct Htmp with (s':=s1') (l':= l'++[(a,d1)])
               as [ [d2' [s2' l2'] ] [Hwrap' [? Hsims2] ] ]; auto.
      subst d2'.
      exists (d2,(s2',l2')).
      simpl. now rewrite Hf'; auto. }
  split; [| split; [| split; [| split] ] ]; auto.
  + intros x s [d s1]. red.
    rewrite rhs_spec. set (t := rhs x).
    intros Ht s' Hsims.
    now apply Hwrapx in Ht; auto.
  + intros x s s5 Hsols.
    red. intros s' Hsims.
    rewrite S.solve_step in Hsols.
    rewrite SI.solve_step.
    case_eq (S.is_stable_b x s); intros Hb; rewrite Hb in Hsols;
    rewrite <- sim_is_stable_b with (s := s); auto;
    rewrite Hb;
    [inversion Hsols; subst; now eauto |].
    set (s0 := S.add_stable x s).
    set (s0' := SI.prepare x s').
    assert (Hsims0 : sim s0 s0') by (apply sim_prepare; auto).
    destruct (S.F x (S.evalget n x) s0) as [ [d1 s1] |] eqn:HF;
      [| simpl in Hsols; unfold s0 in HF; now rewrite HF in Hsols].
    simpl in Hsols. unfold s0 in HF; rewrite HF in Hsols.
    fold s0 in HF.
    apply IHevalrhs in HF. red in HF.
    destruct HF with (s':=s0') as [ [d1' [s1' l'] ] [HF' [? Hsims1] ] ]; auto.
    subst d1'. clear HF.
    assert (HF'tmp : F x (SI.instr (SI.evalget n x)) (s0', []) = Some (d1, (s1', l'))) by auto.
    clear HF'; rename HF'tmp into HF'.
    assert (eF : SI.F = F) by auto; rewrite eF; clear eF.
    simpl. rewrite HF'.
    rewrite <- (sim_getval (s:=s1)); auto.
    set (cur := S.getval s1 x).
    set (new := D.join cur d1).
    fold cur new in Hsols.
    set (s2' := SI.rem_called x s1').
    assert (Hsims12' : sim s1 s2') by (apply sim_rem_called; auto).
    set (s3 := S.setval x new s1). fold s3 in Hsols.
    set (s3' := SI.setval x new s2').
    assert (Hsims3 : sim s3 s3') by (apply sim_setval; auto).
    rewrite <- (sim_get_infl (s:=s3)); auto.
    set (w := S.get_infl s3 x). fold w in Hsols.
    set (s4 := S.handle_work w (S.rem_infl x s3)).
    fold s4 in Hsols.
    set (s4' := SI.handle_work w (SI.rem_infl x s3')).
    assert (Hsims4 : sim s4 s4')
      by (apply sim_handle_work; now apply sim_rem_infl).
    destruct (D.leq d1 cur) eqn:Ele.
    * inversion Hsols; subst s5; clear Hsols.
      now exists s2'; auto.
    * apply IHsolall in Hsols.
      now apply Hsols.
  + intros w s s2 Hsolall.
    red. intros s' Hsims.
    rewrite S.solve_all_step in Hsolall.
    destruct w as [| x xs].
    * inversion Hsolall; subst s2.
      now exists s'; auto.
    * simpl in Hsolall.
      destruct (S.solve n x s) as [s1 |] eqn:Hsol; [| easy]. 
      apply IHsol in Hsol. red in Hsol.
      destruct Hsol with (s':=s') as [s1' [Hsol' Hsims1] ]; auto.
      apply IHsolall in Hsolall.
      destruct Hsolall with (s':=s1') as [s2' [Hsolall' Hsims2] ]; auto.
      exists s2'.
      simpl. now rewrite Hsol'; auto.
Qed.

End instrumentation.

Lemma sim_s_init : sim S.s_init SI.s_init.
Proof. easy. Qed.

Theorem correctness n w s :
  S.solve_all n w S.s_init = Some s ->
  (forall z, In z w -> S.is_stable z s) /\
  (forall z v d,
     S.is_stable z s ->
     In (v,d) (deps (rhs z) (S.getval s)) ->
     S.is_stable v s) /\
  (forall z,
     S.is_stable z s ->
     D.Leq ([[rhs z]]* (S.getval s)) (S.getval s z)).
Proof.
intros Hsolall.
eapply simulation in Hsolall.
assert (Htmp := Hsolall (SI.s_init) sim_s_init).
destruct Htmp as [s' [Hsolall' Hsims] ].
eapply (SI.graph_is_correct Hpure) in Hsolall'.
eapply SI.correctness in Hsolall'.
split; [| split].
- intros z. rewrite sim_is_stable; eauto; now intuition.
- intros z v d.
  repeat rewrite sim_is_stable with (s':=s'); auto.
  rewrite sim_getval with (s':=s'); auto.
  now eapply Hsolall'.
- intros z.
  rewrite sim_is_stable with (s':=s'); auto.
  rewrite sim_getval with (s':=s'); auto.
  now intuition.
Qed.

Theorem exactness : 
  has_uniq_lookup rhs ->
  is_monotone rhs ->
  forall n mu w s,
    is_solution rhs mu ->
    S.solve_all n w S.s_init = Some s ->
    leqF (S.getval s) mu.
Proof.
intros Huniq Hmon n mu w s Hsolmu Hsolall.
eapply simulation in Hsolall.
assert (Htmp := Hsolall (SI.s_init) sim_s_init); clear Hsolall.
destruct Htmp as [s' [Hsolall' Hsims] ].
eapply (SI.graph_is_correct Hpure) in Hsolall'.
eapply SI.exactness in Hsolall'; eauto.
now rewrite sim_getval with (s':=s'); auto.
Qed.

End correctness.

End SolverRLDtotalCorrect.
