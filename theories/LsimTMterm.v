From Undecidability Require Import L.Util.L_facts.

From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
Require Import List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools LM_heap_def (*WriteValue CaseList Copy*) ListTM Hoare.
From Undecidability.TM.L Require Import (*JumpTargetTM*) Alphabets StepTM M_LHeapInterpreter LMBounds_Loop.
From Undecidability Require Import L.AbstractMachines.FlatPro.LM_heap_correct.

Require Import List.

Import Vector.VectorNotations.
Import ListNotations ResourceMeasures.

(*From Undecidability.TM.L Require Import UnfoldClos.*)

Require Import Equations.Prop.DepElim.

Import CasePair Code.CaseList.

Set Default Proof Using "Type".

Section inEnc.
  Variable (sig : finType).

  Variable (sigX : Type) (X : Type) (cX : codable sigX X) (I : Retract sigX sig).

  Definition inTape (x : X) : tape sig^+ :=
    midtape [] (inl START) (map inr (Encode_map cX I x) ++ [inl STOP]).

  Lemma inTape_correct x:
    inTape x ≃ x.
  Proof. eexists. reflexivity. Qed.

  Definition inVoid : tape sig^+ := midtape [] (inl STOP) nil.
  Lemma inVoid_correct:
  isVoid inVoid.
  Proof. do 2 eexists. reflexivity. Qed.
  
End inEnc.

Lemma TripleT_loopM_correct {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q t:
  TripleT P k pM Q -> P t -> exists q t', loopM (initc (projT1 pM) t) k = Some (mk_mconfig q t') /\ Q (projT2 pM q) t'.
Proof.
  intros [H1%Triple_iff H2]%TripleT_iff Ht. edestruct H2 as [[q t'] H2'].
  {split. eassumption. reflexivity. }
  exists q, t'. split. easy. apply H1 in H2'. hnf in H2'. apply H2'. easy.
Qed.

Lemma Triple_loopM_sound {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q t q t':
  Triple P pM Q -> P t -> loopM (initc (projT1 pM) t) k = Some (mk_mconfig q t') -> Q (projT2 pM q) t'.
Proof.
  intros H1%Triple_iff Ht Hloop. apply H1 in Hloop. now eapply Hloop.
Qed.

