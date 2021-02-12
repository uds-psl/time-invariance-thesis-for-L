From Undecidability Require Import TM.PrettyBounds.PrettyBounds.
From Undecidability Require Import TM.PrettyBounds.BaseCode.
From Undecidability Require Import LM_heap_def TM.PrettyBounds.MaxList.

From Undecidability.TM.L Require Import Alphabets CaseCom.
From Undecidability.L.AbstractMachines Require Import SizeAnalysisStep .

From Undecidability Require Import UpToC UpToCNary.



(** ** Sizes for (atomic) commands *)

Lemma size_ACom_singleton (t : ACom) :
  size [ACom2Com t] = 4.
Proof. destruct t; cbn; cbv; reflexivity. Qed.

Lemma size_ACom_singleton' (t : ACom) :
  size [t] = 3.
Proof. destruct t; cbn; cbv; reflexivity. Qed.

Lemma size_ACom (t : ACom) :
  size t = 1.
Proof. unfold size. destruct t; cbn; reflexivity. Qed.

Lemma size_ACom' (t : ACom) :
  size (ACom2Com t) = 2.
Proof. unfold size. destruct t; cbn; reflexivity. Qed.

Lemma size_Var (n : nat) :
  size (varT n) = 2 + n.
Proof. unfold size. cbn. simpl_list. rewrite repeat_length. cbn. lia. Qed.

Lemma size_nat' (n : nat) :
  size (varT n) = 1 + size n.
Proof. unfold size. cbn. simpl_list. rewrite repeat_length. cbn. lia. Qed.

Lemma Encode_Com_hasSize_ge1 (t : Tok) :
  1 <= size t.
Proof. unfold size. destruct t; auto. unfold Encode_Heap. cbn. simpl_list. all: cbn; lia. Qed.

Lemma size_Com_singleton (t : Tok) :
  size [t] = 2 + size t.
Proof. unfold size. destruct t; cbn; try lia. simpl_list. rewrite repeat_length. cbn. lia. Qed.

Lemma Encode_Pro_hasSize_ge1 (P : Pro) :
  1 <= size P.
Proof. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. Qed.

Lemma Encode_Pro_hasSize_ge_length (P : Pro) :
  length P <= Encode_list_size _ P.
Proof.
  induction P.
  - cbn. lia.
  - cbn. rewrite IHP. lia.
Qed.

Lemma Encode_Heap_hasSize_ge_length (H : Heap) :
  length H <= Encode_list_size _ H.
Proof.
  induction H.
  - cbn. lia.
  - cbn. rewrite IHlist. lia.
Qed.


Lemma sizeT_ge_1 t:
  1 <= sizeT t.
Proof.
  destruct t;cbn. all:nia.
Qed.

Lemma size_sizeT_le t:
  size t <= 2* sizeT t.
Proof.
  destruct t.
  1:rewrite size_Var.
  all:cbv - [plus mult]. all:nia.
Qed.

Lemma size_le_sizeP P:
  size P <= 3 * sizeP P.
Proof.
  induction P as [ | t P].
  {now cbv. }
  setoid_rewrite encodeList_size_cons. rewrite IHP.
  unfold sizeP;cbn. rewrite size_sizeT_le.
  specialize (sizeT_ge_1 t). nia.
Qed.

Lemma sizeT_le_size t:
  sizeT t <= size t.
Proof.
  destruct t.
  1:rewrite size_Var.
  all:cbv - [plus mult]. all:nia.
Qed.

Lemma sizeP_le_size P:
  sizeP P <= size P.
Proof.
  induction P as [ | t P].
  {now cbv. }
  setoid_rewrite BaseCode.encodeList_size_cons. rewrite <- IHP.
  unfold sizeP;cbn. rewrite sizeT_le_size. nia.
Qed.

(*
Lemma sizeH_le H:
  size H <= 
Proof.
  induction P as [ | t P].
  {now cbv. }
  setoid_rewrite encodeList_size_cons. rewrite IHP.
  unfold sizeP;cbn. rewrite size_sizeT_le.
  specialize (sizeT_ge_1 t). nia.
Qed.
 *)

Lemma size_list (sig X : Type) (cX : codable sig X) (xs : list X):
  size xs = length xs + sumn (map size xs) + 1.
Proof.
  induction xs. now rewrite encodeList_size_nil.
  rewrite encodeList_size_cons. cbn [length map sumn]. nia.
Qed.

Lemma size_list_le_bound (sig X : Type) (cX : codable sig X) (xs : list X) c:
  (forall x, x el xs -> size x <= c)
  -> size xs <= length xs * (c+1) + 1.
Proof.
  intros H. rewrite size_list. rewrite sumn_le_bound.
  2:{ intros ?. rewrite in_map_iff. intros (?&<-&?). eauto. }
  rewrite map_length. nia.
Qed.


Lemma Encode_Clos_hasSize (g : HClos) :
  size g = fst g + Encode_list_size _ (snd g) + 1.
Proof.
  destruct g as (a,P); cbn.
  setoid_rewrite Encode_pair_hasSize; unfold Encode_pair_size.
  setoid_rewrite Encode_nat_hasSize.
  setoid_rewrite Encode_list_hasSize.
  lia.
Qed.

Lemma Encode_Clos_hasSize' (g : HClos) :
  size g = size (fst g) + Encode_list_size _ (snd g).
Proof.
  destruct g as (a,P); cbn.
  setoid_rewrite Encode_pair_hasSize; unfold Encode_pair_size.
  setoid_rewrite Encode_nat_hasSize.
  setoid_rewrite Encode_list_hasSize.
  lia.
Qed.

Lemma Encode_Clos_hasSize_ge1 (g : HClos) :
  1 <= size g.
Proof. rewrite Encode_Clos_hasSize. lia. Qed.

Lemma Encode_HEntr_hasSize_ge1 (e : HEntr) :
  1 <= size e.
Proof. setoid_rewrite Encode_option_hasSize. apply Encode_option_hasSize_ge1. Qed.

Lemma Encode_Heap_hasSize_ge1 (H : Heap) :
  1 <= size H.
Proof. setoid_rewrite Encode_list_hasSize. apply Encode_list_hasSize_ge1. Qed.



Lemma size_HClos_le (g : HClos):
  size g = fst g + size (snd g) + 1.
Proof.
  rewrite Encode_Clos_hasSize. destruct g as [a P];cbn.
  replace (Encode_list_size _ P) with (size P). nia. apply Encode_list_hasSize.
Qed.
