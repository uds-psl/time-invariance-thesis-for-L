From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import TM.TMinL.TMinL_extract L_facts.
From Undecidability.TM Require Import Compiler_facts Compiler_spec.
From Undecidability.L.Datatypes Require Import LNat Lists LProd LFinType LVector Lists.
From Undecidability.TM Require Import TM_facts NaryApp.
From Undecidability.L Require Import Functions.FinTypeLookup TimeInvarianceTermination Functions.EqBool .

Import L_Notations.

Lemma many_app_eq {k} (v : Vector.t (list bool) k) s :  many_app s (Vector.map enc v) = Vector.fold_left (fun (s : term) n => s (encBoolsL n)) s v.
Proof.
   induction v in s |- *.
   * cbn. reflexivity.
   * cbn. now rewrite IHv.
Qed.

Import HOAS_Notations.


Lemma equiv_many_app_L k (v : Vector.t term k) s t n :
  s >(<= n) t -> many_app s v >(<= n) many_app t v.
Proof.
  induction v in s, t |- *; intros H; cbn.
  - eassumption.
  - eapply IHv. replace n with (n + 0) by lia. eapply redLe_app_helperL. eauto.
    reflexivity.
Qed.

Lemma beta_red s t t' : lambda t -> t' = subst s 0 t -> (lam s) t ≻ t'.
Proof.
  intros [u ->] ->. repeat econstructor.
Qed.

Lemma many_beta k (v : Vector.t term k) s : 
  (forall x, Vector.In x v -> proc x) ->
  many_app (many_lam k s) v >(<= k) many_subst s 0 v.
Proof.
  induction v in s |- *; cbn; intros Hv.
  - reflexivity.
  - eapply redLe_trans with (i := 1) (j := n).
    eapply equiv_many_app_L.
    { assert (proc h). {eapply Hv. econstructor.} exists 1. split. lia. econstructor. split. 2:reflexivity.
      eapply beta_red. Lproc. reflexivity. }
    rewrite subst_many_lam. replace (n + 0) with n by lia.
    eapply IHv. intros. eapply Hv. now econstructor.
Qed.

Definition cont_vec (k : nat) : term := lam (many_lam k (k (Vector.fold_right (fun n s => (extT (@cons (list bool)) (var n)) s) (many_vars k)  (ext (@nil bool))))).

Lemma helper_closed k :
  bound k (Vector.fold_right (fun (n : nat) (s0 : term) => extT (@cons (list bool)) n s0) (many_vars k) (ext (@nil bool))).
Proof.
  induction k.
  - cbn. cbv. repeat econstructor.
  - rewrite many_vars_S. cbn. econstructor. econstructor. eapply closed_dcl_x. Lproc.
    econstructor. lia.
    eapply bound_ge. eauto. lia.
Qed.

Lemma subst_closed s n u :
  closed s -> subst s n u = s.
Proof.
  now intros ->.
Qed.

Lemma vector_closed:
  forall (k : nat) (v : Vector.t (list bool) k) (x : term), Vector.In x (Vector.map enc v) -> proc x.
Proof.
  intros k v.
  induction v; cbn; intros ? Hi. inversion Hi. inv Hi. Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. subst. eauto. eapply nat_eq_dec.
Qed.

Lemma cont_vec_correct k s (v : Vector.t (list bool) k) :
  proc s ->
  many_app (cont_vec k s) (Vector.map enc v) >(<= 1 + 3 * k) s (enc v).
Proof.
  intros Hs.
  unfold cont_vec.
  eapply redLe_trans with (i := 1) (j := 3 * k).
  eapply equiv_many_app_L. exists 1. split. lia. econstructor. split. 2:reflexivity.
  eapply beta_red. Lproc. rewrite subst_many_lam. replace (k + 0) with k by lia. reflexivity.
  cbn -[plus mult]. rewrite Nat.eqb_refl.
  rewrite bound_closed_k. 2:eapply helper_closed.
  replace (3 * k) with (k + 2 * k) by lia.
  eapply redLe_trans.
  eapply many_beta. eapply vector_closed.
  rewrite many_subst_app.
  rewrite many_subst_closed. 2:Lproc.
  replace (2 * k) with (2 * k + 0) by lia.
  eapply redLe_app_helperR. 2:reflexivity.
  induction v.
  - cbn. reflexivity.
  - rewrite many_vars_S. cbn -[mult]. rewrite subst_closed; [ | now Lproc].
    rewrite Nat.eqb_refl.
    rewrite !many_subst_app.
    repeat (rewrite many_subst_closed; [ | now Lproc]).
    eapply redLe_mono.
    eapply redLe_app_helperR.
    rewrite bound_closed_k. 2:eapply helper_closed. eapply IHv.
    rewrite !enc_vector_eq. Lsimpl. Lreflexivity. cbn.
    lia.
Qed.

Definition TM_bool_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (1 + k + n),
  forall v : Vector.t (list bool) k, 
  (forall l, R v l -> exists q t i, loopM (mk_mconfig (start M) (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n))) i = Some (mk_mconfig q t) /\ (τ (Vector.map (@length bool) v)) i /\ Vector.hd t = encBoolsTM s b l) /\
  (forall q t, TM.eval M (start M) (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n)) q t ->
          exists l, R v l).

Definition L_bool_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : Vector.t nat k -> nat -> Prop) := 
  exists s, forall v : Vector.t (list bool) k, 
      (forall l, R v l -> exists i, (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) ⇓(<= i) (encBoolsL l) /\ τ (Vector.map (@length bool) v) i) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) o -> exists l, R v l).

Section loopM.
  Context (sig : finType).
  Let reg_sig := @registered_finType sig.
  Existing Instance reg_sig.

  Variable s b : sig.

  Definition f (x : bool) := if x then s else b.

  Instance f_comp : computableTime' f (fun _ _ => (4,tt)).
  Proof.
    extract. solverec.
  Qed.

  Definition c__encBoolsList := 4 + c__map.

  Instance encBoolsListTM_comp : computableTime' (@encBoolsListTM sig s b) (fun l _ => (S (length l) * c__encBoolsList,tt)).
  Proof.
    change (@encBoolsListTM sig s b) with (fun l => map f l).
    extract. solverec.  unfold c__encBoolsList. rewrite map_time_const. solverec.
  Qed.

  Definition c__encBools := c__encBoolsList + 6.

  Instance encBoolsTM_comp : computableTime' (@encBoolsTM sig s b) (fun l _ => (S (length l) * c__encBools,tt)).
  Proof.
    extract. solverec. unfold c__encBools. solverec.
  Qed.

  Local Instance eqb_sig : eqbClass _ := @eqbFinType_inst sig.

  Local Instance eqbT_sig : eqbCompT sig := @eqbFinType sig.

  Fixpoint unencListTM l :=
    match l with
    | x :: l =>
      match unencListTM l with None => None | Some l =>
      if eqb s x then Some (true :: l) else if eqb b x then Some (false :: l) else None end
    | nil => Some nil
    end.

  Definition c__unencListTM := 12 * c__eqbComp sig * length (elem sig) + 36.

  Instance unencListTM_comp : computableTime' (unencListTM) (fun l _ => (S (length l) * c__unencListTM, tt)).
  Proof.
    extract. solverec. all: unfold c__unencListTM. lia.
    all: try rewrite !eqbTime_le_r.
    all: unfold reg_sig, finType_eqb, eqb.
    all: try rewrite !size_finType_le. 
    all: solverec.
  Qed.

  Definition unencTM t :=
    match t with
    | midtape ls m rs => unencListTM rs
    | _ => None
    end.

  Instance unencTM_comp : computableTime' unencTM (fun l _ => (S (length (right l)) * c__unencListTM + 15, tt)).
  Proof.
    extract. solverec.
  Qed.

  Variable n : nat.

  Variable k : nat.

  Variable M : TM sig (1 + k + n).

  Definition prepare v : list (tape sig) := (app (niltape :: map (encBoolsTM s b) v) (repeat niltape n)).

  Fixpoint prepare_time (l : list (list bool)) :=
    match l with
    | [] => 18
    | l :: L => c__map * length l + prepare_time L
    end.


  Definition list_size {X} (l : list (list X)) := sumn (map (@length X) l) + length l.

  
  Lemma list_size_length {X} (l : list (list X)) : length l <= list_size l. Proof. clear. unfold list_size. lia. Qed.
  Lemma list_size_sum {X} (l : list (list X)) : sumn (map (@length X) l) <= list_size l. Proof. clear. unfold list_size. lia. Qed.

  Let C :=  c__leUpToC (H := mapTime_upTo (fun x0 : list bool => S (| x0 |) * c__encBools)).

  Definition c__prepare :=  (S c__app * S C * S c__encBools * S c__map  + 18).

  Axiom F : False.

  Lemma lemma_map_time:
    forall x : list (list bool), map_time (fun x0 : list bool => S (| x0 |) * c__encBools) x <= S (list_size x) * S c__encBools * c__map.
  Proof.
    intros x.    
    generalize c__encBools. clear. intros.
    induction x.
    - cbn. unfold c__map. lia.
    - cbn [map_time]. rewrite IHx. unfold list_size. cbn -[plus mult]. unfold c__map. ring_simplify. lia.
  Qed.
      
  Instance prepare_comp : computableTime' prepare (fun l _ => (12 * n + c__prepare * (1 + list_size l), tt)).
  Proof.
    extract. solverec.
    rewrite map_length, list_size_length.
    rewrite lemma_map_time.
    unfold c__prepare, c__app, c__encBools, c__encBoolsList, c__map. ring_simplify. lia.
  Qed.

  Definition the_term :=
    cont_vec k (lam ((s_sim (encTM M) (extT prepare 0)) I (lam (lam (extT unencTM 1 I I))))).

  Require Import Equations.Prop.DepElim.

  Variable Heq : s <> b.

  Lemma unenc_enc' l :
    unencListTM (map (fun x : bool => if x then s else b) l) = Some l.
  Proof using Heq.
    induction l as [ | [] l IH]; cbn.
    - congruence.
    - rewrite IH. destruct (eqb_spec s s); try congruence.
    - rewrite IH. destruct (eqb_spec s b); try congruence. destruct (eqb_spec b b); try congruence.
  Qed.

  Lemma unenc_enc l :
    unencTM (encBoolsTM s b l) = Some l.
  Proof using Heq.
    induction l; cbn.
    - reflexivity.
    - rewrite unenc_enc'. destruct a.
      destruct (eqb_spec s s); try congruence.
      destruct (eqb_spec s b); try congruence.
      destruct (eqb_spec b b); try congruence.
  Qed.

  Lemma enc_prepare_eq:
    forall v : Vector.t (list bool) k, enc (prepare (Vector.to_list v)) = enc (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n)).
  Proof.
    intros v.
    
    rewrite enc_vector_eq. unfold prepare.
    rewrite <- !VectorPrelim.vector_to_list_correct.
    rewrite VectorPrelim.vector_app_to_list. cbn.
    rewrite VectorPrelim.vector_to_list_map.
    assert ( VectorPrelim.vector_to_list (Vector.const niltape n) = repeat (niltape sig) n) as ->.
    { clear. induction n; cbn; congruence. }
    reflexivity.
  Qed.

  Lemma the_term_forward (v : Vector.t (list bool) k) i q t l :
    loopM (mk_mconfig (start M) (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n))) i = Some (mk_mconfig q t) ->
    Vector.hd t = encBoolsTM s b l ->
    (Vector.fold_left (fun s n => L.app s (encBoolsL n)) the_term v) >(<= (1 + 3 * k) + (1 + ((10 * (S i) * sizeTM M + 10) + 12 * n + (c__prepare * (1 + list_size (Vector.to_list v)) + ((| encBoolsListTM s b l |) * c__unencListTM + c__unencListTM + 25))))) enc l.
  Proof using Heq.
    assert (Hs_sim : proc s_sim). unfold s_sim. Lproc.
    assert (HencTM : closed (encTM M)). unfold encTM. Lproc.
    intros H Ht.
    rewrite <- many_app_eq.
    unfold the_term.
    eapply redLe_trans.
    eapply cont_vec_correct. Lproc.
    Lsimpl.
    rewrite !enc_vector_eq.
    eapply redLe_mono.
    Lsimpl. 
    eapply TimeInvarianceThesis_wrt_Termination_TM_to_L in H.
    unfold encTps in H.
    rewrite enc_prepare_eq.
    eapply redLe_app_helperL. eapply redLe_app_helperL.  eapply H. reflexivity.
    eapply redLe_mono. depelim t. cbn in Ht. subst.
    rewrite (enc_vector_eq (encBoolsTM s b l ::: t)).
    rewrite <- !VectorPrelim.vector_to_list_correct. cbn.
    rewrite !VectorPrelim.vector_to_list_correct. Lsimpl.
    rewrite unenc_enc. Lsimpl. reflexivity. reflexivity.

    cbn -[plus mult]. solverec.
  Qed.

  Lemma converges_eval S : converges S -> exists v, S ⇓ v.
  Proof.
    intros (v & H1 & H2). exists v. rewrite H1. econstructor. reflexivity. eauto.
  Qed.

  From Undecidability.L Require Import Seval.
  
  Lemma the_term_backward (v : Vector.t (list bool) k) t :
    L.eval ((Vector.fold_left (fun s n => L.app s (encBoolsL n)) the_term v)) t ->
    exists q t, TM.eval M (start M) (Vector.append (niltape ::: Vector.map (encBoolsTM s b) v) (Vector.const niltape n)) q t.
  Proof using Heq.
    intros H % L_facts.eval_iff.
    assert (Hs_sim : proc s_sim). unfold s_sim. Lproc.
    assert (HencTM : closed (encTM M)). unfold encTM. Lproc.
    setoid_rewrite TM_eval_iff.
    assert (Vector.fold_left (fun (s : term) (n : list bool) => s (encBoolsL n)) the_term v >*
            ((s_sim (encTM M) (enc (prepare (Vector.to_list v)))) I (lam (lam (extT unencTM 1 I I))))).
    { eapply redLe_star_subrelation.
      rewrite <- many_app_eq.
      unfold the_term.
      eapply redLe_trans.
      eapply cont_vec_correct. Lproc.
      rewrite !enc_vector_eq.
      eapply redLe_mono.
      Lsimpl. reflexivity. reflexivity. }

    rewrite H0 in H.
    rewrite enc_prepare_eq in H.

    eapply eval_converges in H.
    eapply app_converges in H as [H _].
    eapply app_converges in H as [H _].
    eapply converges_eval in H as [vv H].

    edestruct (TimeInvarianceNF_backward) as (q & t' & i & HH).
    2:{ destruct i. inv HH. 
        setoid_rewrite TM_alt.loopSumM_loopM_iff. eauto. }

    eauto.
  Qed.

End loopM.

Theorem TimeInvarianceThesis_wrt_Computability_TM_to_L {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) (τ : Vector.t nat k -> nat -> Prop) :
  TM_bool_computable R τ -> exists p1, L_bool_computable R (fun v i => exists j, τ v j /\ p1 v j = i).
Proof.
  intros (n & Σ & s & b & Heq & M & H).
  exists (fun v N =>
       1 + 3 * k +
       (1 +
        (10 * S N * sizeTM M + 10 + 12 * n +
         (c__prepare * (1 + sumn (Vector.to_list v) + k) + (N * c__unencListTM Σ + c__unencListTM Σ + 25))))
    ).
  exists (the_term s b M). intros v. specialize (H v) as [H1 H2]. split.
  - intros l (q & t & i & H & He & Hi) % H1. eexists. split.
    eapply evalIn_mono.
    econstructor. 2:{ change (lambda (enc l)). Lproc. }
    eapply the_term_forward; eauto. unfold list_size. instantiate (1 := _ + _).
    eapply le_plus_l. exists i. split. eauto.
    assert ((| encBoolsListTM s b l |) <= i). admit.
    rewrite vector_map_to_list, vector_to_list_length. admit.
  - intros o (? & ? & ?) % the_term_backward. now eapply H2. eauto.
Admitted.

