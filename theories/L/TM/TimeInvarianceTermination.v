(* From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import TM.TMinL.TMinL_extract.
From Undecidability.TM Require Import Compiler_facts Compiler_spec. *)
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector.
From Undecidability.L Require Import Functions.FinTypeLookup Functions.EqBool.
From Undecidability Require Import TMEncoding.

Require Import Undecidability.L.TM.TMinL.TMinL_extract.
Require Import Undecidability.L.Functions.UnboundIteration.
From Undecidability.TM Require Import TM TM_alt TM_facts.
Require Import Undecidability.L.Util.L_facts.
From Undecidability.L.Datatypes Require Import LNat.

Import L_Notations.

Notation PAIR := (lam (lam (lam (0 2 1)))).
Notation PAIR_ x y := (lam (0 x y)).

Section TimeInvarianceNF.

Import HOAS_Notations.

Variable Σ : finType.

Let reg_sig := @registered_finType Σ.
Existing Instance reg_sig.

Variable n_tps : nat.

Definition s_sim : term := Eval cbn -[enc] in [L_HOAS (λ M_q0 tps, ha M_q0 (λ M q0, !!uiter M (!!PAIR q0 tps)))]. 

Variable M : TM Σ n_tps.
Variables (q q' : state M) (t t' : tapes Σ n_tps).

Let reg_state := @registered_finType (state M).
Existing Instance reg_state.

Definition step_fun := (fun cfg : mconfig Σ (state M) n_tps =>
                          if haltConf cfg then inr (ctapes cfg) else inl (TM_facts.step cfg)).

Notation STEPTIME := (haltTime M + n_tps* 130+ transTime M + 185). 

Instance step_fun_comp : computableTime' step_fun (fun _ _ => (STEPTIME,tt)).
Proof.
  extract. solverec. 
Qed.

Lemma TimeInvarianceNF_forward i :
    loopSumM (M := M) (mk_mconfig q t) i = Some (mk_mconfig q' t') ->
    evalLe (7 + i * (STEPTIME + 11) ) (s_sim (PAIR_ (ext step_fun) (enc q)) (enc t)) (enc t').
Proof.
  intros H.
  assert (Hi : loopSum i step_fun (mk_mconfig q t) = Some t').
  { clear - H.  revert H. generalize (mk_mconfig q t). intros cfg H.
    induction i in H, cfg,t'|-*; cbn in *.
    - congruence.
    - unfold step_fun. destruct haltConf. inv H. reflexivity.
      eapply IHi. eapply H.
  }
  eapply evalLe_trans. unfold s_sim. Lsimpl. reflexivity.
  unshelve eapply uiter_sound in Hi. exact _. exact _. 2: eapply step_fun_comp.
  unfold s_sim. eapply evalIn_mono. econstructor. 2:Lproc. destruct Hi as [Hi ?].
  unfold enc at 1 in Hi. cbn in Hi. unfold enc at 1 in Hi. cbn in Hi.
  Lsimpl. reflexivity. rewrite <- plus_n_O.
  clear. fold (transTime M).
  change (  uiterTime step_fun
    (fun (_ : mconfig Σ (state M) n_tps) (_ : unit) =>
     (haltTime M + n_tps * 130 +
      transTime M + 185, tt)) i (mk_mconfig q t) <= i * (STEPTIME + 11)).
  generalize STEPTIME as C. intros C. generalize (mk_mconfig q t). intros cfg. induction i in cfg |- *.
  - cbn. lia. 
  - cbn. destruct _. rewrite IHi. lia. lia.
Qed.

Lemma TimeInvarianceNF_backward v :
  eval (s_sim (PAIR_ (ext step_fun) (enc q)) (enc t)) v -> exists q' t' i, loopSumM (M := M) (mk_mconfig q t) i = Some (mk_mconfig q' t').
Proof.
  intros H.
  assert ((s_sim (PAIR_ (ext step_fun) (enc q)) (enc t)) >* uiter (ext step_fun) (lam (O (enc q) (enc t)))).
  { clear H.
    unfold s_sim. now Lsimpl. }
  rewrite H0 in H. clear H0.
  change (lam (O (enc q) (enc t))) with (enc (mk_mconfig q t)) in H. 
  eapply uiter_complete in H as (n & tps' & H). clear t'. rename tps' into t'.
  revert H. generalize (mk_mconfig q t) as cfg. intros cfg H.
  induction n in cfg, H |- *; cbn in *.
  - congruence.
  - destruct step_fun eqn:E.
    + eapply IHn in H as (q'' & t'' & i & IH). exists q'', t'', (S i). rewrite <- IH.
      cbn.
      unfold step_fun in E.
      destruct haltConf; try congruence; try inv E.
      reflexivity.
    + inv H. unfold step_fun in E.
      destruct haltConf eqn:EE; try congruence. inv E.
      exists (cstate cfg), (ctapes cfg), 1. cbn. rewrite EE. now destruct cfg.
Qed.

End TimeInvarianceNF.

Definition sizeTM Σ n (M : TM Σ n) := (haltTime M + n* 130+ transTime M + 185 + 11).

Definition encTM {n} {Σ : finType} : TM Σ n -> term.
Proof.
  pose (reg_sig := @registered_finType Σ).
  intros M.
  pose (reg_state := @registered_finType (state M)).
  unshelve refine (PAIR_ (extT (step_fun (M := M))) (enc (start M))). 3:eapply step_fun_comp.
Defined.

Definition encTps  {n} {Σ : finType} : tapes Σ n -> term.
Proof.
  pose (reg_sig := @registered_finType Σ).
  intros tps. exact (enc tps).  
Defined.

Theorem TimeInvarianceThesis_wrt_Termination_TM_to_L : let C := 10 in
  forall n (Σ : finType), forall M : TM Σ n, forall tps,
          (forall tps' i q',
              loopM (mk_mconfig (start M) tps) i = Some (mk_mconfig q' tps') ->
              evalLe (C * (S i) * sizeTM M + C) (s_sim (encTM M) (encTps tps)) (encTps tps')) /\
          (forall v, eval (s_sim (encTM M) (encTps tps)) v -> exists q' tps' i, loopM (mk_mconfig (start M) tps) i = Some (mk_mconfig q' tps')).
Proof.
  intros C n Σ. subst C.
  pose (reg_sig := @registered_finType Σ).
  intros M tps. split.
  - intros tps' i q' H.
    rewrite loopSumM_loopM_iff in H.
    eapply TimeInvarianceNF_forward in H.
    eapply evalLe_trans_rev with (k := 7) in H as (H1 & H & _).
    2:{ unfold s_sim. Lsimpl. } cbn -[mult].
    unfold s_sim. unfold encTM, encTps.
    eapply evalIn_mono. Lsimpl. eapply (evalIn_refl 0). Lproc.
    fold (sizeTM M). ring_simplify. lia.
  - intros v (q' & t' & [] & H) % TimeInvarianceNF_backward. inv H. setoid_rewrite loopSumM_loopM_iff. eauto.
Qed.

(* Theorem TimeInvarianceThesis_wrt_Termination_TM_to_L : *)
(*   forall n Σ, exists encTM : TM Σ n -> term, exists encTps : tapes Σ n -> term, *)
(*       exists sₛᵢₘ : term, exists C1 C2 : nat, forall M : TM Σ n, forall tps, *)
(*               (forall tps' i q', *)
(*                   loopM (mk_mconfig (start M) tps) i = Some (mk_mconfig q' tps') -> *)
(*                   evalLe (C1 * (S i) * sizeTM M + C2) (sₛᵢₘ (encTM M) (encTps tps)) (encTps tps')) /\ *)
(*               (forall v, eval (sₛᵢₘ (encTM M) (encTps tps)) v -> exists q' tps' i, loopM (mk_mconfig (start M) tps) i = Some (mk_mconfig q' tps')). *)
(* Proof. *)
(*   intros n Σ. *)
(*   pose (reg_sig := @registered_finType Σ). *)
(*   unshelve eexists. *)
(*   { intros M. *)
(*     pose (reg_state := @registered_finType (state M)). *)
(*     unshelve refine (PAIR (extT (step_fun (M := M))) (enc (start M))). 3:eapply step_fun_comp. *)
(*   } *)
(*   unshelve eexists. *)
(*   { intros tps. exact (enc tps). } *)
(*   exists s_sim. *)
(*   eexists 10, 10. *)
(*   intros M tps. split. *)
(*   - intros tps' i q' H. *)
(*     rewrite loopSumM_loopM_iff in H. *)
(*     eapply TimeInvarianceNF_forward in H. *)
(*     eapply evalLe_trans_rev with (k := 9) in H as (H1 & H & _). *)
(*     2:{ unfold s_sim. Lsimpl. } cbn -[mult]. *)
(*     unfold s_sim.  *)
(*     eapply evalIn_mono. Lsimpl. eapply (evalIn_refl 0). Lproc. *)
(*     fold (sizeTM M). ring_simplify. lia. *)
(*   - intros v (q' & t' & [] & H) % TimeInvarianceNF_backward. inv H. setoid_rewrite loopSumM_loopM_iff. eauto. *)
(* Qed. *)
