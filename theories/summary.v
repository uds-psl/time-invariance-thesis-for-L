From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import TimeInvarianceTermination TimeInvarianceComputability.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector Lists.

From Undecidability.TM Require Import TM_facts.
Import VectorNotations2.

From Undecidability.L Require Import TM.TMinL.TMinL_extract.
From Undecidability.L Require Import Functions.FinTypeLookup Functions.EqBool .

Import L_Notations.

From Equations Require Import Equations.

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
  exists s, forall v : Vector.t (list bool) k, 
      (forall l, R v l -> exists i, (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) ⇓(<= i) (encBoolsL l) /\ τ (length l) (Vector.map (@length bool) v) i) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) o -> exists l, R v l).

Theorem TimeInvarianceThesis_wrt_Termination_TM_to_L : let C := 10 in
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
  exists p, (the_term s b M). intros v. specialize (H v) as [H1 H2]. split.
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


