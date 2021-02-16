From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import L_facts LM_heap_def UpToCNary.


From Coq Require Import List.
Import Vector.VectorNotations ListNotations.

From Undecidability.TM Require Import TM_facts ProgrammingTools WriteValue CaseList Copy ListTM Hoare.
From Undecidability.TM.L Require Import Alphabets Eval.
From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec Compiler_facts ClosedLAdmissible.

Require Import Equations.Prop.DepElim.


Set Default Proof Using "Type".

Section APP_right.

  Definition APP_right : pTM (sigPro)^+ unit 2 :=
    App _;;
    WriteValue ( [appT]%list) @ [|Fin1|];;
    App _.
  
  Lemma APP_right_Spec :
    { f : UpToC (fun '(s1,s2)=>size (compile s1) + size (compile s2)) & forall s1 s2 : term,
    TripleT ≃≃([],[|Contains _ (compile s1);Contains _ (compile s2)|])
    (f (s1,s2)) APP_right (fun _ => ≃≃([],[|Contains _ (compile (L.app s1 s2));Void|])) }.
  Proof.
    eexists_UpToC f. [f]:refine (fun '(s1,s2) => _).
    intros s1 s2.
    unfold APP_right.
    hsteps_cbn.
    -rewrite app_assoc.  reflexivity.
    -reflexivity.
    - rewrite !(correct__leUpToC (App_steps_nice _) (_,_)).
      rewrite Encode_list_hasSize with (xs:=(compile s1 ++ compile s2)%list).
      rewrite Encode_list_hasSize_app, <- !Encode_list_hasSize. reflexivity.
    -assert (H': (fun x => 1) <=c (fun '(s1,s2)=>size (compile s1) + size (compile s2))).
     { eapply upToC_le. intros []. setoid_rewrite Encode_list_hasSize. setoid_rewrite <- Encode_list_hasSize_ge1. nia. }
    unfold f. unfold sigPro. cbn - ["-" "+"]. smpl_upToC. cbn. all:try smpl_upToC_solve.
  Qed.
 

End APP_right.



Lemma tabulate_nth [X : Type] [n : nat] (v : Vector.t X n): tabulate (fun i => v[@i]) = v.
Proof. depind v;cbn. all:congruence. Qed.


Hint Rewrite  Nat.eqb_refl tabulate_nth nth_tabulate: cleanupParamTM.
  
Ltac cleanupParamTM :=
  try fold Nat.add;rewrite ?Nat.eqb_refl, ?tabulate_nth, ?nth_tabulate;cbn.

Section MK_isVoid.

  Context {Σ : finType}.
  
  Definition MK_isVoid : pTM Σ^+ unit 1 := 
    Write (inl UNKNOWN).

  Lemma MK_isVoid_Sem :
    RealiseIn MK_isVoid (fun t '(r, t') => t = [| niltape|] -> isVoid (t'[@Fin0])) 1.
  Proof. 
    eapply RealiseIn_monotone.
    { unfold MK_isVoid. TM_Correct. }
    easy.
    intros ? [] H ->. hnf in H. cbn in *. rewrite H. hnf. eauto.
  Qed.

  Lemma MK_isVoid_Spec :
   TripleT ≃≃([],[|Custom (eq niltape)|]) 1 MK_isVoid (fun _ => ≃≃([],[|Void|])).
  Proof.
    eapply RealiseIn_TripleT. now apply MK_isVoid_Sem. cbn. intros ? ? ? ? [_ H']%tspecE.
    specialize  (H' Fin0). eapply tspecI. easy. intros i; destruct_fin i;cbn. apply H. now vector_destruct tin.
  Qed.  

  Fixpoint MK_isVoid_multi m' : pTM (Σ) ^+ unit m' :=
    match m' with
    0 => Nop
    | S m' => MK_isVoid @ [|Fin0|];;MK_isVoid_multi m'@(tabulate (fun i => Fin.FS i))
    end.

  Lemma helper n m i f: 
    injective f ->
      lookup_index_vector (m:=m) (n:=n)
    (tabulate f) 
    (f i) = Some i.
  Proof.
    revert n i f. induction m;cbn. easy.
    intros n i f Hinj. specialize (Fin.eqb_eq _ (f i) (f Fin0)) as H'.
    destruct Fin.eqb.
    -destruct H' as [H' _]. specialize (H' eq_refl). apply Hinj in H' as ->. easy.
    -destruct H' as [_ H']. destruct (fin_destruct_S i) as [[i' ->]| ->]. 2:now discriminate H'.
     specialize IHm with (f:= fun m => f (Fin.FS m) ). cbn in IHm. rewrite IHm. easy. intros ? ? ?%Hinj. now apply Fin.FS_inj.
  Qed.

  Instance Proper_tabulate X n: Proper (pointwise_relation _ eq ==> eq) (@tabulate X n).
  Proof.
    unfold pointwise_relation.
    induction n;hnf;intros f g H;cbn. reflexivity. f_equal. apply H. now apply IHn.
  Qed.  

  Theorem MK_isVoid_multi_SpecT m' :
  TripleT ≃≃([],Vector.const (Custom (eq niltape)) m')
    (m'*2) (MK_isVoid_multi m')
    (fun _ => ≃≃([],Vector.const Void m')).
  Proof using All.
    depind m';cbn. now hsteps_cbn.
    hstep. {hsteps_cbn;cbn. apply MK_isVoid_Spec. }
    cbn;intros _. rewrite Nat.eqb_refl,tabulate_nth;cbn. 
    eapply ConsequenceT.
    {
      eapply LiftTapes_SpecT with (Q:=fun _ => _)(Q':=fun _ => _) (P:= Void:::Vector.const (Custom (eq niltape)) _). now eapply dupfree_tabulate_injective,Fin.FS_inj.
      eapply ConsequenceT . eassumption. 2:cbn;intro;reflexivity. 2:reflexivity.
      unfold Downlift,select. rewrite Vector_map_tabulate. cbn. now rewrite tabulate_nth.
    }
    1,3,4:reflexivity. cbn. intros _.
    rewrite lookup_index_vector_None. 2:{rewrite in_tabulate. intros (?&?). congruence. }
    eapply EntailsI. intros ? [_ H]%tspecE. eapply tspecI. easy. intros i. cbn.
    specialize (H i);cbn in H. destruct (fin_destruct_S i) as [[i' ->]| ->];cbn in H|-*. 2:easy.
    rewrite nth_tabulate in H. rewrite helper in H. easy. hnf. eapply Fin.FS_inj.
  Qed.

End MK_isVoid.
Opaque MK_isVoid_multi.

From Undecidability Require Import TM.L.Transcode.Boollist_to_Enc.
From Undecidability Require Import EncBoolsTM_boolList.
From Undecidability.TM.L Require Import SizeBoundsL.

Section mk_init_one.

  Variable Σ : finType.

  Variable s b : Σ^+.
  Variable (H_disj : s <> b).

  Variable (retr_pro : Retract sigPro Σ).
  Variable (retr_list : Retract (sigList bool) Σ).



   (* Tapes: 
       0: bs (input, encBoolsTM)
       1: ter (input) 
       2: intern, bs als listBool
       3: intern 
       4: intern 
       5: intern 
     *)
  

  Definition M_init_one : pTM (Σ) ^+ unit 6:= 
    encBoolsTM2boollist.M s retr_list @[|Fin0;Fin3|];;
    Rev _ ⇑ retr_list @ [|Fin3;Fin2;Fin4|];;
    BoollistToEnc.M retr_list retr_pro @[|Fin2;Fin3;Fin4;Fin5|];;
    APP_right ⇑ retr_pro  @[|Fin1;Fin3|].

    
  Lemma M_init_one_Spec :
    { f : UpToC (fun '(bs,ter)=>length bs + L_facts.size ter + 1) & forall (bs:list bool) (ter : L.term),
    TripleT ≃≃([],[|Custom (eq (encBoolsTM s b bs));Contains _ (compile ter);Void;Void;Void;Void|])
    (f (bs,ter)) M_init_one (fun _ => ≃≃([],[|Custom (eq (encBoolsTM s b bs));Contains _ (compile (L.app ter (encBoolsL bs)));Void;Void;Void;Void|])) }.
  Proof using H_disj.
    eexists_UpToC f. 
    { 
    [f]:refine (fun '(bs,ter) => _).
    intros bs ter.
    unfold M_init_one.
    hstep. { hsteps_cbn. cbn. eapply (projT2 (encBoolsTM2boollist.SpecT _ H_disj)). }
    cbn. intros _. hstep. { hsteps_cbn. cbn. tspec_ext. } 2:reflexivity.
    cbn. intros _. hstep.
    {
      hsteps_cbn. cbn. eapply ConsequenceT. eapply BoollistToEnc.SpecT with (bs:=rev bs).
      all:cbn. now tspec_ext. now rewrite rev_involutive. reflexivity.
    } 2:reflexivity.
    cbn. intros _. hsteps_cbn.
     now eapply (projT2 (APP_right_Spec)). 1,2:now cbn;tspec_ext.
     subst f. cbn beta. cbn beta iota.  reflexivity.
    }
    etransitivity.
    {
       unfold f. eapply upToC_le with (F:=fun '(bs,ter) => _). intros [bs ter].
       rewrite (correct__leUpToC (Rev_steps_nice _)).
       rewrite (correct__leUpToC (BoollistEnc.boollist_size)).
       do 3 rewrite (correct__leUpToC (correct__UpToC _)).
       rewrite rev_length.
       rewrite !size_le_sizeP.
       unfold sizeP;rewrite !sizeP_size.
       rewrite (correct__leUpToC size_L_enc_bools).
       reflexivity.
    }
       smpl_upToC_solve.
  Qed.

End  mk_init_one.



Section mk_init.

  Variable Σ : finType.
  Variable s b : Σ^+.
  Variable (H_disj : s <> b).

  Context (retr_pro : Retract sigPro Σ) (retr_bools : Retract (sigList bool) Σ).

  Variable m k : nat.

  Notation aux n := (Fin.L k (Fin.L m n)) (only parsing).
  Notation auxm n := (Fin.L k (Fin.R 6 n)) (only parsing).
  Notation auxk n := (Fin.R (6 + m) n) (only parsing).

  Fixpoint M_init' (sim:term) {k'} : (Vector.t (Fin.t k) k') -> pTM (Σ) ^+ unit ((6 + m)+ k).
  Proof using m s retr_bools retr_pro. 
    simple notypeclasses refine (match k' with
    0 => fun _ => MK_isVoid_multi _ @ [|aux Fin1;aux Fin2;aux Fin3;aux Fin4; aux Fin5|];;
        WriteValue ( (compile sim)) ⇑ retr_pro @ [|aux Fin1|]
    | S k' => 
    fun ren =>
      _;;M_init_one s retr_pro retr_bools @ [|auxk (ren[@Fin0]);aux Fin1;aux Fin2;aux Fin3;aux Fin4;aux Fin5|]
    end). all:try exact _.
    2:{apply (M_init' sim _ (Vector.tl ren)). }
  Defined. (* because definition *)



  Theorem M_init'_SpecT k' (ren :Vector.t (Fin.t k) k') : 
  { f : UpToC (fun '(sim,v) => L_facts.size sim + sumn (Vector.to_list (Vector.map (length (A:=bool)) v)) + 1)
  & forall sim (v:Vector.t (list bool) k),
  TripleT ≃≃([],Vector.const (Custom (eq niltape)) (6+m) ++ Vector.map (fun bs => Custom (eq (encBoolsTM s b bs))) v)
    (f (sim,v)) (M_init' sim ren)
    (fun _ => ≃≃([],
      ([|Custom (eq niltape);
        Contains retr_pro (compile (Vector.fold_right (fun l_i s => L.app s (encBoolsL l_i)) (select ren v) sim))
         ;Void;Void;Void;Void|]++Vector.const (Custom (eq niltape)) m) ++ Vector.map (fun bs => Custom (eq (encBoolsTM s b bs))) v))}.
  Proof using All.
    depind ren. all:cbn [compile Vector.fold_left M_init' Vector.tl Vector.caseS].
    {
      eexists_UpToC f. [f]:refine (fun '(sim,v) => _). 
      {
        cbn. intros sim v.
        hstep. hsteps_cbn;cbn. exact (MK_isVoid_multi_SpecT 5). cbn;cleanupParamTM. 2:reflexivity.
        hsteps_cbn. reflexivity.
        cleanupParamTM.
        apply EntailsI. intros t H. eapply tspec_ext. eassumption. easy.
        intros i. clear - i.
        repeat (destruct (fin_destruct_S i) as [(i'&->) | ->];[rename i' into i;cbn| ]);try (intros H;exact H).
      }
      unfold f. etransitivity. 
      {eapply upToC_le with (F:= (fun '(_,_) => _ ));intros []. unfold WriteValue_steps. rewrite !size_le_sizeP. unfold sizeP;rewrite !sizeP_size. reflexivity. }
      smpl_upToC_solve.
    }
    {
      eexists_UpToC f. [f]:refine (fun '(sim,v) => _).
      { 
        cbn. intros sim v.
        hstep.
        3:reflexivity. now apply (projT2 IHren). 
        cbn. intros _. hstep. { cbn. rewrite Vector_nth_R,nth_map'. cbn. eapply (projT2 (M_init_one_Spec H_disj _ _)). }
        cbn;fold Nat.add;rewrite Nat.eqb_refl;cbn. intros _.
        apply EntailsI. intros t H. eapply tspec_ext. eassumption. easy.
        intros i. clear - i. 
        repeat (destruct (fin_destruct_S i) as [(i'&->) | ->];[rename i' into i;cbn| ]);try (intros H;exact H).
        rewrite nth_tabulate. destruct (Fin.eqb _ _) eqn:H'. 2:tauto.
        cbn. eapply Fin.eqb_eq in H' as ->. rewrite Vector_nth_R,nth_map'. cbn. tauto.
      }
      unfold f. etransitivity. 
      {
        eapply upToC_le with (F:= (fun '(_,_) => _ ));intros [].
        do 2 rewrite (correct__leUpToC (correct__UpToC _)). reflexivity.
      }
      assert (Hnth : forall n h,(fun '(_, x) => | x[@h] |) <=c
          (fun '(sim, v) =>
          L_facts.size sim + sumn (Vector.to_list (n:=n) (Vector.map (length (A:=bool)) v)) +
          1)).
          {
          clear. intros. eapply upToC_le;intros [? ?].
          clear. revert h t0. induction n;intros i v. easy. depelim v. depelim i.
            now cbn;nia.
            cbn. rewrite IHn. unfold Vector.to_list. nia.
          }
      smpl_upToC.
      all:try smpl_upToC_solve. now apply Hnth.
      -clear - Hnth. induction n.
       +depelim ren;cbn. smpl_upToC_solve.
       +depelim ren;cbn.
        etransitivity.   
        *eapply upToC_le with (F:= (fun '(_,_) => _ ));intros []. unfold select in IHn.  rewrite (correct__leUpToC (IHn ren) (_,_)). reflexivity.
        *smpl_upToC. all:try smpl_upToC_solve.
         etransitivity.
         {
           eapply upToC_le with (F:= (fun '(_,_) => _ ));intros [? ?].
           change (encBoolsL t0[@h]) with (Extract.enc t0[@h]).
           rewrite (correct__leUpToC size_L_enc_bools). reflexivity.
         }
           smpl_upToC. apply Hnth. smpl_upToC_solve.
    }
  Qed.

  Program Definition startRen := Vectors.tabulate (n:=k) (fun i => Fin.of_nat_lt (n:=k) (p:=k - 1 -proj1_sig (Fin.to_nat i)) _).
  Next Obligation.
  destruct Fin.to_nat;cbn. nia.
  Defined. (* because definition *)

  Lemma startRen_spec A (v:Vector.t A _): select startRen v = Vector.rev v.
  Proof.
    unfold select.
    apply eq_nth_iff'. intros i. rewrite nth_map'.
    unfold startRen.
    unshelve erewrite nth_tabulate, vector_nth_rev. 1:abstract (inv i;nia).
    f_equal.  eapply Fin.of_nat_ext.
  Qed.  

  
  Import CasePair Code.CaseList.

  



  Definition M_init sim : pTM (Σ) ^+ unit ((6 + m)+ k) :=
    M_init' sim startRen.

    
  Theorem M_init_SpecT:
  { f : UpToC (fun '(sim,v) => L_facts.size sim + sumn (Vector.to_list (Vector.map (length (A:=bool)) v)) + 1)
    & forall sim (v:Vector.t (list bool) k),
  TripleT ≃≃([],Vector.const (Custom (eq niltape)) (6+m) ++ Vector.map (fun bs => Custom (eq (encBoolsTM s b bs))) v)
    (f (sim,v)) (M_init sim)
    (fun _ => ≃≃([],
      ([|Custom (eq niltape);
        Contains retr_pro (compile (Vector.fold_left (fun s l_i => L.app s (encBoolsL l_i)) sim v));
         Void;Void;Void;Void|]
         ++Vector.const (Custom (eq niltape)) m) ++ Vector.map (fun bs => Custom (eq (encBoolsTM s b bs))) v))}.
  Proof using H_disj.
    eexists_UpToC f. [f]:refine (fun '(sim,v) => _).
    intros. 
    unfold M_init.
    eapply ConsequenceT. eapply (projT2 (M_init'_SpecT _)). reflexivity. 2:unfold f;reflexivity.
    cbn. intros _.
    rewrite vector_fold_left_right with (v:=v), <- (startRen_spec v).
    apply EntailsI. intros t H. eapply tspec_ext. eassumption. easy.
    intros i. clear - i. 
    repeat (destruct (fin_destruct_S i) as [(i'&->) | ->];[rename i' into i;cbn| ]);try (intros H;exact H).
    unfold f;cbn beta.
    etransitivity.
    {
       eapply upToC_le with (F:= fun '(x,y)=>_);intros []. cbn. 
      setoid_rewrite (correct__leUpToC (correct__UpToC _)). reflexivity.
    }
    smpl_upToC_solve.
  Qed.


End mk_init.

From Undecidability Require Import Enc_to_Boollist.

Section conv_output.

  Variable Σ : finType.
  Variable s b : Σ^+.
  Variable (retr_pro : Retract sigPro Σ).
  Variable (retr_list : Retract (sigList bool) Σ).

    

  Definition M_out : pTM (Σ) ^+ unit 4 :=
    EncToBoollist.M _ _ @ [|Fin0;Fin2;Fin3|];;
    Boollist2encBoolsTM.M s b _ @ [|Fin2;Fin1;Fin3|].

  
  Theorem M_out_SpecT :
    { f : UpToC (fun bs => length bs + 1) & forall bs,
    TripleT ≃≃([],[|Contains _ (compile (encBoolsL bs));Custom (eq niltape);Void;Void|])
      (f bs) M_out
      (fun _ => ≃≃([],
        ([|Custom (fun _ => True); Custom (eq (encBoolsTM s b bs)); Void;Void|])))}.
  Proof.
    eexists_UpToC f. [f]:refine (fun bs => _).
    intro bs.
    unfold M_out. hsteps_cbn;cbn.
    -eapply (projT2 (@EncToBoollist.SpecT _ _ _)).
    -eapply (projT2 (Boollist2encBoolsTM.SpecT _ _ _)).
    - cbn. rewrite rev_involutive. tspec_ext. easy.
    -unfold f.  setoid_rewrite (correct__leUpToC (correct__UpToC _)). rewrite rev_length. reflexivity.
    -unfold f. smpl_upToC_solve.
  Qed.

End conv_output.

From Undecidability.TM.L.HeapInterpreter Require UnfoldClosBounds.

Section main.

  Variable k : nat.
  Variable (R : Vector.t (list bool) k -> (list bool) -> Prop).

  Variable s : term.

  Hypothesis Hscl : closed s.

  Variable Hs1 : (forall v, forall m : list bool,
   L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encBoolsL n)) s v) (encBoolsL m)
   -> R v m).

  Variable Hs2 : (forall v, forall o : term,
                     L.eval (Vector.fold_left (n := k) (fun (s0 : term) (n : list bool) => L.app s0 (encBoolsL n)) s v) o ->
                     exists m : list bool, o = encBoolsL m).

  Definition n_main := 14.

  Definition Σ : Type := sigList bool + EvalL.Σintern.

  Definition retr_bools : Retract (sigList bool) Σ := (Retract_inl _ _).
  Definition retr_intern : Retract EvalL.Σintern Σ := (Retract_inr _ _).

  Definition retr_closs : Retract (sigList sigHClos) Σ
  := ComposeRetract retr_intern _.
  Definition retr_clos : Retract sigHClos Σ := ComposeRetract retr_closs _.
  Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos _.

  Definition sym_s : Σ^+ := inr (inl (sigList_X true)).
  Definition sym_b : Σ^+ := inr (inl (sigList_X false)).

  (*
    auxiliary tapes:

    0    : T

   *)

  Notation aux n := (Fin.L k (Fin.R 1 n)).

  Definition garb : Σ^+ := inl UNKNOWN.

  Definition M_main : pTM (Σ ^+)  unit (1 + n_main + k):=
        M_init sym_s retr_pro retr_bools (1 + n_main - 6) k s ;;
        MK_isVoid_multi _ @ [|aux Fin5;aux Fin6;aux Fin7;aux Fin8;aux Fin9;aux Fin10;aux Fin11;aux Fin12;aux Fin13 |] ;;
        EvalL.M retr_intern retr_pro @ [| aux Fin0 ; aux Fin1 ; aux Fin2; aux Fin5 ; aux Fin6 ; aux Fin7 ; aux Fin8 ; aux Fin9 ; aux Fin10 ; aux Fin11 ; aux Fin12 |] ;;
        M_out sym_s sym_b retr_pro retr_bools @ [|aux Fin0;Fin.L k Fin0;aux Fin7;aux Fin8|].

  Lemma syms_diff : sym_s <> sym_b. Proof. cbv. congruence. Qed.
  
  Theorem M_main_Spec v:
    Triple ≃≃([],Vector.const (Custom (eq niltape)) (S n_main) ++ Vector.map (fun bs => Custom (eq (encBoolsTM sym_s sym_b bs))) v)
       M_main
      (fun _ t => exists m, t ≃≃ ([R v m]%list,
        (Custom (eq (encBoolsTM sym_s sym_b m)):::Vector.const (Custom (fun _ => True)) _))).
  Proof  using Hscl Hs1 Hs2.
    unfold M_main.
    hstep. { eapply TripleT_Triple,(projT2 (M_init_SpecT syms_diff _ _ _ _)). }
    cbn. intros _.
    start_TM.
    hstep. {hsteps_cbn;cbn. eapply TripleT_Triple. exact (MK_isVoid_multi_SpecT 9). }
    cbn;cleanupParamTM. intros _.
    hstep. {eapply LiftTapes_Spec_ex. now smpl_dupfree. cbn. refine (EvalL.Spec _ _ _). now eapply closed_compiler_helper. }
    cbn;cleanupParamTM.
    intros _. eapply Triple_exists_pre. intros s'.
    change (fun x => ?f x) with f.
    hintros Heval%eval_iff. specialize (Hs2 Heval) as (res&->). 
    unfold_abbrev.
    eapply Triple_exists_con. eexists res. 
    hstep. { eapply Consequence_pre. eapply TripleT_Triple. refine (projT2 (M_out_SpecT _ _ _ _) res). cbn. reflexivity. }
    cbn;cleanupParamTM. intros _.
    apply Hs1 in Heval.
    eapply EntailsI. intros tin [[] Hin]%tspecE.
    eapply tspecI;cbn. easy.
    intros i. specialize (Hin i). destruct_fin i;try exact Logic.I;cbn in *.
    now simpl_vector. eassumption.
  Qed.
End main.

Import UpToCNary.



Polymorphic Lemma upToC_mul_descend_nary (domain : list Type) (f g f' g': Rarrow domain nat):
  Uncurry f <=c Uncurry f'
  -> Uncurry g <=c Uncurry g'
  -> Fun' (fun x => App f x * App g x)
    <=c Fun' (fun x => App f' x * App g' x).
Proof.
  prove_nary upToC_mul_descend. 
Qed.

Theorem M_main_SpecT k s (Hscl : closed s):
  { f : UpToC (fun '(i,m_r,m_v) => (i+1)*(i+m_v+1)*((m_v+1)*(i+1) + m_r)) & 
  forall i v res,
    (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encBoolsL n)) s v) ⇓(i) (encBoolsL res)  ->
    TripleT ≃≃([],Vector.const (Custom (eq niltape)) (S n_main) ++ Vector.map (fun bs => Custom (eq (encBoolsTM sym_s sym_b bs))) v)
    (f (i,length res,sumn (Vector.to_list (Vector.map (length (A:=bool)) v)))) (M_main k s)
      (fun _ => ≃≃([],Custom (eq (encBoolsTM sym_s sym_b res)):::Vector.const (Custom (fun _ => True)) (13+S k)))}.
Proof.
  eexists_UpToC f. [f]:refine (fun '(i,m_r,m_v) => _). 
  intros ? ? ? Red. unfold M_main.
  eapply ConsequenceT_pre. 2:reflexivity.
  { 
  hstep. { eapply (projT2 (M_init_SpecT syms_diff _ _ _ _)). }
  2:{ set (f' := f__UpToC _). pose (H' := correct__UpToC _ :f' <=c _). rewrite (correct__leUpToC H'). subst f' H'; cbn beta;reflexivity. }
  cbn. intros _.
  start_TM.
  hstep. {hsteps_cbn;cbn. exact (MK_isVoid_multi_SpecT 9). } 2:reflexivity.
  cbn;cleanupParamTM. intros _.
  hstep. { eapply LiftTapes_SpecT. now smpl_dupfree. cbn. unshelve apply EvalL.SpecT. 3:now eapply closed_compiler_helper. 3:easy. }
  cbn;cleanupParamTM.
  intros _.
  hstep. now refine (projT2 (M_out_SpecT _ _ _ _) res). 
  cbn;cleanupParamTM. intros _. 
  eapply EntailsI. intros tin [[] Hin]%tspecE.
  eapply tspecI;cbn. easy.
  intros j. specialize (Hin j). destruct_fin j;try exact Logic.I;cbn in *.
  now simpl_vector. eassumption. cbn beta.
  set (l:= EvalL.steps _ _).
  pose (Hl:= proj2_sig UnfoldClosBounds.EvalL_steps_nice' _ _ _ _ _ : l <= _ ). 
  rewrite Hl.   setoid_rewrite (correct__leUpToC (correct__UpToC _)) at 1. reflexivity.
  } 
  set (f' := L_facts.size
      (Vector.fold_left _ _ _)). pose (H':= correct__leUpToC (size_fold_app k) (s,v) : f' <= _).
      cbn in H'. setoid_rewrite H'. clear f' H'.
  rewrite (LargestVar_fold s v) at 1.
  change (encBoolsL) with (Extract.enc (X:=list bool)).
  rewrite (correct__leUpToC size_L_enc_bools res).

  unfold f;cbn beta iota.
  set (m_s:= L_facts.size s). set (m_v:= sumn (Vector.to_list (Vector.map (length (A:=bool)) v))). 
  set (m_r := length res).
  reflexivity.
  unfold f. cbn - ["+" "*"]. clear.
  assert ( (fun _ => 1) <=c (fun '(i, m_r,m_v) => (i + 1) * (i + m_v+1) * ((m_v + 1) * (i + 1) + m_r))) by smpl_upToC_solve.
  smpl_upToC.
  1,3:now smpl_upToC_solve.
  eapply leUpToC_proper_eq with (x:=fun '(i, m_r,m_v) => _) (x0:=fun '(i, m_r,m_v) => _).
  { intros [[]]. rewrite <- !Nat.mul_assoc. reflexivity. }
  { intros [[]]. rewrite <- !Nat.mul_assoc. reflexivity. }
  nary simple apply upToC_mul_descend_nary. reflexivity.
  nary simple apply upToC_mul_descend_nary. now smpl_upToC_solve.
  smpl_upToC.
  2,3:smpl_upToC_solve.
  transitivity ((fun '(t', x) => let '(t'0, x0) := t' in (0*x0)+(x + 1) * (t'0 + 1))).
  1,2:cbn.
  nary simple apply upToC_mul_descend_nary; now smpl_upToC_solve.
  smpl_upToC_solve.
Qed.

Theorem compiler_correct {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) :
  L_bool_computable_closed R -> TM_bool_computable_hoare' R.
Proof.
  intros H. 
  destruct H as [sim [cs Hsim]].
  hnf. 
  eexists _, _, sym_s, sym_b. split. eapply syms_diff. exists (M_main k sim).
  intros v. split.
  - eapply M_main_Spec. easy. all:firstorder.
  - intros. edestruct eval_evalIn. now apply eval_iff,Hsim.
    eexists. eapply (projT2 (M_main_SpecT _ cs)). easy.
Qed.
