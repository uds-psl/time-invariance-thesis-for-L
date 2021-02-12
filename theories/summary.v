From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import TimeInvarianceTermination TimeInvarianceComputability.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector Lists.

From Undecidability.TM Require Import TM_facts.
Import VectorNotations2.

From Undecidability.L Require Import TM.TMinL.TMinL_extract.
From Undecidability.L Require Import Functions.FinTypeLookup Functions.EqBool.

From Undecidability.TM.L Require CompilerBoolFuns.Compiler.
From Undecidability.TM.L Require Import CompilerBoolFuns.Compiler   Alphabets StepTM M_LHeapInterpreter LMBounds_Loop.

From Undecidability.TM.L Require Import (*JumpTargetTM*) Alphabets StepTM M_LHeapInterpreter LMBounds_Loop.
From Undecidability Require Import L.AbstractMachines.FlatPro.LM_heap_correct.

Import L_Notations.

From Equations Require Import Equations.

Require Import Ring ZArith Arith Lia.
From Undecidability Require Import ProgrammingTools LM_heap_def (*WriteValue CaseList Copy*) ListTM Hoare LsimTMterm.

Import Vector.VectorNotations.
Import ListNotations ResourceMeasures.


(****************)
(** THEOREM 1.1 *)
(****************)
Theorem TimeInvarianceThesis_wrt_Simulation_L_to_TM :
  {C : nat & 
  let p := fun i m => C * (3*i+2)^2 * (3*i+1+m) * m in
  let M := projT1 M_LHeapInterpreter.Loop in
  forall s, closed s ->
    let tps := [|inTape _ retr_closures_step [(0,compile s)]%list;inTape _ retr_closures_step []%list;inTape _ retr_heap_step []%list|] ++ Vector.const (inVoid _) _ in
      (forall v i,
          s ⇓(i) v ->
          exists q tps',
          loopM (initc M tps) (p i (size (compile s)) ) = Some (mk_mconfig q tps') /\
          exists g H, reprC H g v /\ tps'[@Fin1] ≃(retr_closures_step) [g]%list /\ tps'[@Fin2] ≃(retr_heap_step) H) /\
      (forall i q tps', loopM (initc M tps) i = Some (mk_mconfig q tps') -> exists v, L.eval s v)}.
Proof.
  evar (c:nat). exists c. intros p M s cs tps. split.
  - intros v i R.
    edestruct (@completenessTime s v i) as (g&H&rep&R'). now eapply timeBS_evalIn. easy.
    edestruct @TripleT_loopM_correct with (pM:= M_LHeapInterpreter.Loop) (t:=tps) as (q&tps'&Hloop&Htps').
    {eapply Interpreter_SpecT. eassumption. inversion 1. }
    {eapply tspec_tspec_withSpace. hnf. intros i'. cbn; destruct_fin i';cbn. 1-8:eapply inVoid_correct. all:eapply inTape_correct. }
    do 2 eexists. hnf. split.
    { eapply loop_monotone. eassumption.
     unshelve (erewrite UpToC.correct__leUpToC with (l:=@Loop_steps_nice ) (x:=(_,_))).
     unfold p. cbn ["^"]. replace (3 * i + 1 + 1) with (3 * i + 2) by nia. rewrite Nat.mul_1_r. rewrite !mult_assoc.
     rewrite sizeP_le_size. unfold c. reflexivity.
    }
    do 2 eexists. split. eassumption.
    hnf in Htps'.
    split.
    1:specialize (Htps' Fin1).
    2:specialize (Htps' Fin2).
    all:unfold withSpace in Htps'; cbn in Htps'. 1,2:try contains_ext.
  - 
    intros i q tps' H. unshelve eassert (Htmp:=Triple_loopM_sound (Interpreter_Spec [(0,compile s)] [] [])%list _ H).
    {intros i'. cbn; destruct_fin i';cbn. 1-8:eapply inVoid_correct. all:eapply inTape_correct. }
    edestruct Htmp as ([[[T' V'] H'] k] & (HR&HHalt) & G').
    cbn in HR.
    edestruct soundness with (1:=cs) as (g&H''&t&Heq&HE&?). { split. eapply pow_star in HR. exact HR. eassumption. }
    injection Heq as [= -> -> ->]. eexists. eapply eval_iff. eassumption.
Qed.


(****************)
(** THEOREM 1.2 *)
(****************)
Theorem TimeInvarianceThesis_wrt_Simulation_TM_to_L : let C := 10 in
  forall n (Σ : finType), forall M : TM Σ n, forall tps,
          (forall tps' i q',
              loopM (mk_mconfig (start M) tps) i = Some (mk_mconfig q' tps') ->
              evalLe (C * (S i) * sizeTM M + C) (s_sim (encTM M) (encTps tps)) (encTps tps')) /\
          (forall v, L_facts.eval (s_sim (encTM M) (encTps tps)) v -> exists q' tps' i, loopM (mk_mconfig (start M) tps) i = Some (mk_mconfig q' tps')).
Proof.
  intros C n Σ. subst C.
  pose (reg_sig := @encodable_finType Σ).
  intros M tps. split.
  - intros tps' i q' H.
    rewrite TM_alt.loopSumM_loopM_iff in H.
    eapply TimeInvarianceNF_forward in H.
    eapply evalLe_trans_rev with (k := 7) in H as (H1 & H & _).
    2:{ unfold s_sim. Lsimpl. } cbn -[mult].
    unfold s_sim. unfold encTM, encTps.
    eapply evalIn_mono. Lsimpl. eapply (evalIn_refl 0). Lproc.
    fold (sizeTM M). ring_simplify. lia.
  - intros v (q' & t' & [] & H) % TimeInvarianceNF_backward. inv H. setoid_rewrite TM_alt.loopSumM_loopM_iff. eauto.
Qed.



Definition encBoolsListTM {Σ : Type} (s b : Σ) (l : list bool) :=
  (map (fun (x : bool) => (if x then s else b)) l).

Definition encBoolsTM {Σ : Type} (s b : Σ) (l : list bool) :=
  @midtape Σ [] b (encBoolsListTM s b l).

Definition encNatTM {Σ : Type} (s b : Σ) (n : nat) :=
  @midtape Σ [] b (repeat s n).

Definition TM_bool_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : nat -> Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (1 + k + n),
  forall v : Vector.t (list bool) k, 
  (forall l, R v l -> exists q t i, loopM (mk_mconfig (start M) (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n))) i = Some (mk_mconfig q t) /\ (τ (length l) (Vector.map (@length bool) v)) i /\ Vector.hd t = encBoolsTM s b l) /\
  (forall q t, TM.eval M (start M) (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n)) q t ->
          exists l, R v l).

Definition encBoolsL (l : list bool) := Eval cbv in (enc l).

Definition L_bool_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : nat -> Vector.t nat k -> nat -> Prop) := 
  exists s, closed s /\ forall v : Vector.t (list bool) k, 
      (forall l, R v l -> exists i, (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) ⇓(<= i) (encBoolsL l) /\ τ (length l) (Vector.map (@length bool) v) i) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) o -> exists l, R v l).

      

(****************)
(** THEOREM 2.1 *)
(****************)
Theorem TimeInvarianceThesis_wrt_Computability_L_to_TM {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : nat -> Vector.t nat k -> nat -> Prop) :
  L_bool_computable R τ -> exists p1, TM_bool_computable R (fun m v i => exists j, τ m v j /\ p1 m v j = i).
Proof.
  intros (s & Hcl & H).
  unshelve epose proof (@Compiler.compiler_correct k R _). 
  - eapply help_L_bool_computable. exists s. eauto.
  - evar (C : nat).
    exists (fun m v i =>
         C * (m + sumn (Vector.to_list v) + 1 + i)^5).
    eapply Compiler_facts.TM_bool_computable_hoare'_spec in H0.
    2:{ eapply Compiler_facts.L_bool_computable_function.
        edestruct @help_L_bool_computable. exists s. eauto. exists x. eapply H1. }
    destruct H0 as (n & Σ & s_ & b & Heq & M & HM).
    exists n, Σ, s_, b. split. eauto. exists M. intros v. split.
    + intros ? (q & t & [i He] % TM_eval_iff & Hteq) % HM.
      exists q, t, i. split. eapply He. split. 2:eapply Hteq.
      admit. (* polynomial bound *)
    + intros q t' He.
      pose proof He as [l Hl] % HM.
      exists l. eapply HM. eauto.
Admitted.

(****************)
(** THEOREM 2.2 *)
(****************)
Theorem TimeInvarianceThesis_wrt_Computability_TM_to_L {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : nat -> Vector.t nat k -> nat -> Prop) :
  TM_bool_computable R τ -> exists p1, L_bool_computable R (fun m v i => exists j, τ m v j /\ p1 v j = i).
Proof.
  intros (n & Σ & s & b & Heq & M & H).
  pose (p := fun (v : Vector.t nat k) N =>
       1 + 3 * k +
       (1 +
        (10 * S N * sizeTM M + 10 + 12 * n +
         (c__prepare * (1 + sumn (Vector.to_list v) + k) + (N * c__unencListTM Σ + c__unencListTM Σ + 25))))
       ).
  exists p, (the_term s b M).
  split. eapply the_term_closed.
  intros v. specialize (H v) as [H1 H2]. split.
  - intros l (q & t & i & H & He & Hi) % H1.
    exists (p (Vector.map (length (A :=bool)) v) i).
    split. 2: eauto. 
    eapply evalIn_mono.
    econstructor. 2:{ change (lambda (enc l)). Lproc. }
    eapply the_term_forward; eauto. unfold list_size. unfold p.
    assert (Hleq : (| encBoolsListTM s b l |) <= i). {
      transitivity (sizeOfTape (Vector.hd t)). rewrite Hi.
      cbn. lia.
      assert (Vector.hd t = t[@Fin0]) as -> by now depelim t.
      eapply TM_size_diff in H. cbn in H. rewrite H. cbn. lia.
    }
    rewrite Hleq, vector_map_to_list, vector_to_list_length. solverec.
  - intros o (? & ? & ?) % the_term_backward. now eapply H2. eauto.
Qed.




