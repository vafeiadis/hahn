Require Import HahnBase HahnRelationsBasic.
Require Import Classical Setoid.
Set Implicit Arguments.

Section FunEq.

Variable A B : Type.
Variable f : A -> B.

Definition funeq (r : relation A) := forall a b (H: r a b), f a = f b.

Lemma funeq_union r t (H1: funeq r) (H2: funeq t) : funeq (r ∪ t).
Proof. unfold funeq, union in *; ins; desf; eauto. Qed.

Lemma funeq_seq r t (H1: funeq r) (H2: funeq t) : funeq (r ⨾ t).
Proof. eby red; ins; destruct H; desc; etransitivity; [apply H1 | apply H2]. Qed.

Lemma funeq_ct r (H: funeq r) : funeq r⁺.
Proof. eby red; ins; induction H0; eauto; etransitivity. Qed.

Lemma funeq_cr r (H: funeq r) : funeq r^?.
Proof. red; ins; red in H0; desf; subst; auto. Qed.

Lemma funeq_rt r (H: funeq r) : funeq r^*.
Proof. eby red; ins; induction H0; eauto; etransitivity. Qed.

Lemma funeq_restr r (H: funeq r) dom : funeq (restr_rel dom r).
Proof. unfold funeq, restr_rel in *; ins; desf; eauto. Qed.

Lemma funeq_restr_eq r (H: funeq r) C (dom : A -> C) : funeq (restr_eq_rel dom r).
Proof. unfold funeq, restr_eq_rel in *; ins; desf; eauto. Qed.

Lemma funeq_restr_eq_rel r : funeq (restr_eq_rel f r).
Proof. by red; ins; red in H; desc; subst. Qed.

Lemma funeq_eqv_rel dom : funeq ⦗dom⦘.
Proof. by red; ins; red in H; desc; subst. Qed.

Lemma funeq_transp r (H: funeq r) : funeq r⁻¹.
Proof. unfold funeq, transp in *; ins; symmetry; eauto. Qed.

Lemma funeq_minus r t (H: funeq r) : funeq (r \ t).
Proof. unfold funeq, minus_rel in *; ins; desf; eauto. Qed.

Lemma funeq_irreflexive r t (H: funeq r)
  (IRR: irreflexive (restr_eq_rel f t ⨾ r)) : irreflexive (t ⨾ r).
Proof.
  unfold funeq, irreflexive, seq, restr_eq_rel in *.
  ins; desf; eauto 8 using eq_sym.
Qed.

End FunEq.

Hint Resolve
 funeq_union funeq_seq funeq_ct funeq_cr funeq_rt
 funeq_restr funeq_restr_eq funeq_restr_eq_rel
 funeq_eqv_rel funeq_transp funeq_minus : rel.

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
