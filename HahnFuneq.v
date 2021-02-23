Require Import HahnBase HahnRelationsBasic.
Require Import Setoid.
Set Implicit Arguments.

Section FunEq.

  Variable A B : Type.
  Variable f : A -> B.

  Definition funeq (r : relation A) := forall a b (H: r a b), f a = f b.

  Lemma funeq_union r t (H1: funeq r) (H2: funeq t) : funeq (r ∪ t).
  Proof. firstorder. Qed.

  Lemma funeq_inter_l r t (H1: funeq r) : funeq (r ∩ t).
  Proof. firstorder. Qed.

  Lemma funeq_inter_r r t (H1: funeq t) : funeq (r ∩ t).
  Proof. firstorder. Qed.

  Lemma funeq_seq r t (H1: funeq r) (H2: funeq t) : funeq (r ⨾ t).
  Proof. eby red; ins; destruct H; desc; etransitivity; [apply H1 | apply H2]. Qed.

  Lemma funeq_ct r (H: funeq r) : funeq r⁺.
  Proof. eby red; ins; induction H0; eauto; etransitivity. Qed.

  Lemma funeq_cr r (H: funeq r) : funeq r^?.
  Proof. red; ins; red in H0; desf; subst; auto. Qed.

  Lemma funeq_rt r (H: funeq r) : funeq r＊.
  Proof. eby red; ins; induction H0; eauto; etransitivity. Qed.

  Lemma funeq_restr r (H: funeq r) dom : funeq (restr_rel dom r).
  Proof. firstorder. Qed.

  Lemma funeq_restr_eq r (H: funeq r) C (dom : A -> C) : funeq (restr_eq_rel dom r).
  Proof. firstorder. Qed.

  Lemma funeq_restr_eq_rel r : funeq (restr_eq_rel f r).
  Proof. firstorder. Qed.

  Lemma funeq_eqv_rel dom : funeq ⦗dom⦘.
  Proof. by red; ins; red in H; desc; subst. Qed.

  Lemma funeq_transp r (H: funeq r) : funeq r⁻¹.
  Proof. firstorder. Qed.

  Lemma funeq_minus r t (H: funeq r) : funeq (r \ t).
  Proof. firstorder. Qed.

  Lemma funeq_irreflexive r t (H: funeq r)
    (IRR: irreflexive (restr_eq_rel f t ⨾ r)) : irreflexive (t ⨾ r).
  Proof.
    unfold funeq, irreflexive, seq, restr_eq_rel in *.
    ins; desf; eauto 8 using eq_sym.
  Qed.

End FunEq.

Global Hint Unfold funeq : unfolderDb.
Global Hint Resolve funeq_union funeq_inter_l funeq_inter_r : hahn.
Global Hint Resolve funeq_seq funeq_ct funeq_cr funeq_rt : hahn.
Global Hint Resolve funeq_restr funeq_restr_eq funeq_restr_eq_rel : hahn.
Global Hint Resolve funeq_eqv_rel funeq_transp funeq_minus : hahn.

Add Parametric Morphism A B f : (@funeq A B f) with signature
  inclusion --> Basics.impl as funeq_mori.
Proof.
  unfold inclusion, funeq, Basics.impl; eauto.
Qed.

Add Parametric Morphism A B f : (@funeq A B f) with signature
  same_relation ==> iff as funeq_more.
Proof.
   unfold same_relation; split; desc; [rewrite H0|rewrite H]; eauto.
Qed.
