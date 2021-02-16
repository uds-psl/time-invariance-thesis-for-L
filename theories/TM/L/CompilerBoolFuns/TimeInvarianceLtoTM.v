From Coq Require Import Vector List.
From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import Datatypes.Lists Tactics.LTactics Util.L_facts.
From Undecidability.TM  Require Import TM_facts ProgrammingTools .

Import ListNotations VectorNotations.

From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec Compiler_facts.

Require Import Equations.Equations.

From Undecidability.TM Require Import Hoare.

From Undecidability Require Import LsimTMterm.


Definition L_bool_computable_time {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : nat -> Vector.t nat k -> nat -> Prop) := 
  exists s, closed s /\ forall v : Vector.t (list bool) k, 
      (forall l, R v l -> exists i, (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) ⇓(<= i) (encBoolsL l) /\ τ (length l) (Vector.map (@length bool) v) i) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) o -> exists l, R v l).


Lemma L_bool_computable_time_function {k} R τ:
  @L_bool_computable_time k R τ -> functional R.
Proof.
  intros [s Hs] v m1 m2 H1 H2.
  eapply Hs in H1 as (?&H1&?). eapply Hs in H2 as (?&H2&?).
  eapply evalLe_eval_subrelation in H1 as (H1&?&?). eapply evalLe_eval_subrelation in H2 as (H2&?&?).
  eapply encBoolsL_inj, L_facts.unique_normal_forms; eauto.
  1,2:now change (encBoolsL) with (enc (X:=list bool));Lproc.
  now rewrite <- H1, H2.
Qed.

Definition TM_bool_computable_time_hoare {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : nat -> Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b , s <> b /\ 
    exists M : pTM (Σ^+) unit (1 + k + n),
    forall v, 
      (forall res, R v res -> exists i, TripleT ≃≃([],TM_bool_computable_hoare_in s b v) i M (fun y => ≃≃([]%list,TM_bool_computable_hoare_out s b res))
          /\ (τ (length res) (Vector.map (@length bool) v)) i)
      /\ Triple ≃≃([],TM_bool_computable_hoare_in s b v) M (fun y t => exists res, t ≃≃ ([R v res]%list,TM_bool_computable_hoare_out s b res)).

Definition TM_bool_computable_time {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : nat -> Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (1 + k + n),
  forall v : Vector.t (list bool) k, 
  (forall l, R v l -> exists q t i, loopM (mk_mconfig (start M) (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n))) i = Some (mk_mconfig q t) /\ (τ (length l) (Vector.map (@length bool) v)) i /\ Vector.hd t = encBoolsTM s b l) /\
  (forall q t, TM.eval M (start M) (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n)) q t ->
          exists l, R v l).

Lemma TM_bool_computable_hoare_spec k R τ:
  functional R ->
  @TM_bool_computable_time_hoare k R τ -> @TM_bool_computable_time k R τ.
Proof.
  intros Hfun (n & Σ & s & b & Hdiff & [M lab] & H).
  eexists n, _, s, b. split. exact Hdiff. exists M.
  intros v. specialize (H v) as [H2 H1]. split.
  - intros m HR.
    specialize H2 as (k__steps&H2&?). eassumption.
    specialize @TripleT_loopM_correct with (1:=H2) as (?&?&?&?%TM_bool_computable_hoare_out_spec).
    now apply TM_bool_computable_hoare_in_spec.
    do 3 eexists. split. 2:split. 2:easy. all:eassumption.
  - intros q t [steps Hter] % TM_eval_iff.
    eapply H1 in Hter as (m & Hm1 & Hm2%TM_bool_computable_hoare_out_spec).
    now apply TM_bool_computable_hoare_in_spec. eauto.
Qed.

From Undecidability.TM.L Require Import Compiler.


(* * The tape-order is different than in the implemented machine, so here again with the tape-order implemented: *)

Definition TM_bool_computable_time_hoare' {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : nat -> Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b , s <> b /\ 
    exists M : pTM (Σ^+) unit (1 + n+k),
    forall v, 
      (forall res, R v res -> exists i, TripleT ≃≃([],TM_bool_computable_hoare_in' s b v) i M (fun y => ≃≃([]%list,TM_bool_computable_hoare_out' s b res))
          /\ (τ (length res) (Vector.map (@length bool) v)) i)
      /\ Triple ≃≃([],TM_bool_computable_hoare_in' s b v) M (fun y t => exists res, t ≃≃ ([R v res]%list,TM_bool_computable_hoare_out' s b res)).
      
Local Set Keyed Unification.



Lemma TM_bool_computable_hoare'_spec k R τ:
  functional R ->
  @TM_bool_computable_time_hoare' k R τ -> TM_bool_computable_time R τ.
Proof.
  intros Hfun (n & Σ & s & b & Hdiff & M & H).
  eapply TM_bool_computable_hoare_spec. eassumption.
  exists n, Σ, s, b. split. exact Hdiff.
  eexists (LiftTapes M (Compiler_facts.tapeOrderSwap n k)).
  intros v. specialize (H v) as [H1 H2].
  rewrite TM_bool_computable_hoare_in'_spec in H1,H2.
  split.
  - intros. specialize H1 as (x&H1&?). easy. exists x. split. 2:easy. 
    refine (ConsequenceT _ _ _ _). refine (LiftTapes_SpecT _ _). now apply Compiler_facts.tapeOrderSwap_dupfree.
    exact H1. reflexivity. cbn beta. intros. 2:easy. now rewrite <- TM_bool_computable_hoare_out'_spec.
  - refine (Consequence _ _ _). refine (LiftTapes_Spec_ex _ _). now apply Compiler_facts.tapeOrderSwap_dupfree.
    exact H2. reflexivity. intro. eapply EntailsI. intros ? [].  eexists.
    erewrite TM_bool_computable_hoare_out'_spec. eassumption. 
Qed.

Theorem compiler_correct_timeInv {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) τ:
  L_bool_computable_time R τ ->
  exists c, TM_bool_computable_time_hoare' R
      (fun m_r v i => exists j, τ m_r v j /\ 
            let m_v := sumn (Vector.to_list v) in
                      i <= c*(j + 1) * (j + m_v + 1) * ((m_v + 1) * (j + 1) + m_r)).
Proof.
  intros H. assert (Hf:= L_bool_computable_time_function H). destruct H as [sim [cs Hsim]].
  eexists. hnf. 
  eexists _, _, sym_s, sym_b. split. eapply syms_diff. exists (M_main k sim).
  intros v. split.
  - specialize (Hsim v) as (H1&H2).
    intros ? (?&(?&?&?)%evalLe_evalIn&?)%H1. eexists;split.
    eapply (projT2 (M_main_SpecT _ cs)). eassumption. cbn zeta.
    eexists;split. eassumption.
     rewrite (correct__leUpToC (correct__UpToC _)),H. rewrite !Nat.mul_assoc. reflexivity.
  -eapply M_main_Spec. easy.
   +intros. edestruct Hsim as [H0 H'].  specialize (H' _ H) as (?&?).
    specialize (H0 _ H1) as (?&?&?).
    replace x with m in *. easy.
    eapply encBoolsL_inj, L_facts.unique_normal_forms.
    1,2:now change (encBoolsL) with (enc (X:=list bool));Lproc.
    eapply L_facts.eval_iff in H. eapply evalLe_eval_subrelation in H0.
    destruct H as (H&?). rewrite <- H. destruct H0 as (H0&?). rewrite <- H0. reflexivity. 
   +intros. edestruct Hsim as [Hsim' (?&?)]. eassumption.
   eapply Hsim in H0 as (?&?&?). eexists.
   eapply L_facts.eval_iff in H as (H&?&->).
   destruct H0 as ((?&?&H0%pow_star)&?&?).
  eapply L_facts.unique_normal_forms. 1:Lproc.
  1:now change (encBoolsL) with (enc (X:=list bool));Lproc.
  rewrite <- H. rewrite H0. reflexivity. 
Qed.
