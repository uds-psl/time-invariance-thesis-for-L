Require Import Undecidability.TM.Util.TM_facts.
Require Import Undecidability.L.Prelim.LoopSum.

Definition loopSumM {Σ : finType} {n} {M : TM Σ n} (c : mconfig Σ (state M) n) : nat -> option (mconfig Σ (state M) n) :=
  fun i =>
  loopSum i (fun cfg => if haltConf cfg then inr cfg else inl (step cfg)) c.

Lemma loopSumM_loopM_iff (Σ : finType) n (M : TM Σ n) c1 c2 i :
  loopM (M := M) c1 i = Some c2 <-> loopSumM (M := M) c1 (S i) = Some c2.
Proof.
  induction i in c1, c2 |- *; cbn.
  - cbn. destruct haltConf; reflexivity.
  - destruct haltConf. 1: reflexivity.
    rewrite IHi. reflexivity.
Qed.

Lemma TM_loopsum_iff (Σ : finType) n (M : TM Σ n) q t q' t' :
  TM.eval M q t q' t' <-> exists n, loopSumM (M := M) (mk_mconfig q t) n = Some (mk_mconfig q' t').
Proof.
  rewrite TM_eval_iff.
  setoid_rewrite loopSumM_loopM_iff.
  split; intros [i H]; eauto.
  destruct i. inv H. eauto.
Qed.