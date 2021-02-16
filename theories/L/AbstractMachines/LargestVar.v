From Undecidability.L Require Import Util.Subterm.
From Undecidability.L.Datatypes Require Import LProd LNat LTerm LBool List_enc.

Fixpoint largestVar (s:term) : nat :=
  match s with
    var n => n
  | app s t => max (largestVar s) (largestVar t)
  | lam s => largestVar s
  end.

Lemma subterm_largestVar s s' :
subterm s s' -> largestVar s <= largestVar s'.
Proof.
  induction 1;cbn;Lia.nia.
Qed.

Lemma largestVar_size s :
  largestVar s <= size s.
Proof.
  induction s;cbn;Lia.lia.
Qed.

Lemma largestVar_prod X Y `{Rx : encodable X} {Ry : encodable Y} (w:X*Y):
  largestVar (enc w) = max (largestVar (enc (fst w))) (largestVar (enc (snd w))).
Proof.
  destruct w.
  unfold enc. destruct Rx,Ry. cbn.  reflexivity.
Qed.
Lemma largestVar_nat (n:nat):
  largestVar (enc n) <= 1.
Proof.
  unfold enc,encodable_nat_enc.
  induction n;cbn in *. all:Lia.lia.
Qed.
Lemma largestVar_term (s:term):
  largestVar (enc s) <= 2.
Proof.
  unfold enc,encodable_term_enc.
  induction s;cbn -[max] in *.
  1:rewrite largestVar_nat.
  all:try Lia.lia.
Qed.

Lemma largestVar_bool (b:bool):
  largestVar (enc b) <= 1.
Proof.
  destruct b;cbv. all:easy.
Qed.

Lemma largestVar_list X {R:encodable X} (xs:list X):
  largestVar (enc xs) <= max (list_max (map (fun x => largestVar (enc x)) xs)) 1.
Proof.
  unfold enc,encodable_list_enc.
  induction xs. now cbv.
  cbn.
  rewrite IHxs. unfold enc,list_max. nia.
Qed.

Lemma largestVar_bools (bs:list bool):
  largestVar (enc bs) <= 1.
Proof.
  rewrite largestVar_list.
  specialize list_max_le with (n:=1) as [_ H]. rewrite H. easy.
  eapply Forall_forall. intros ? (?&<-&?)%in_map_iff. eapply largestVar_bool.
Qed.
