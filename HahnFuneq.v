Require Import HahnBase HahnRelationsBasic.
Require Import Classical Setoid.
Set Implicit Arguments.

Section FunEq.

Variable A B : Type.
Variable f : A -> B.

Definition funeq (R : relation A) := forall a b (H: R a b), f a = f b.

Lemma funeq_union R T (H1: funeq R) (H2: funeq T) : funeq (R ∪ T).
Proof. unfold funeq, union in *; ins; desf; eauto. Qed.

Lemma funeq_seq R T (H1: funeq R) (H2: funeq T) : funeq (R ;; T).
Proof. eby red; ins; destruct H; desc; etransitivity; [apply H1 | apply H2]. Qed.

Lemma funeq_ct R (H: funeq R) : funeq R^+.
Proof. eby red; ins; induction H0; eauto; etransitivity. Qed.

Lemma funeq_cr R (H: funeq R) : funeq R^?.
Proof. red; ins; red in H0; desf; subst; auto. Qed.

Lemma funeq_rt R (H: funeq R) : funeq R^*.
Proof. eby red; ins; induction H0; eauto; etransitivity. Qed.

Lemma funeq_restr R (H: funeq R) dom : funeq (restr_rel dom R).
Proof. unfold funeq, restr_rel in *; ins; desf; eauto. Qed.

Lemma funeq_restr_eq R (H: funeq R) C (dom : A -> C) : funeq (restr_eq_rel dom R).
Proof. unfold funeq, restr_eq_rel in *; ins; desf; eauto. Qed.

Lemma funeq_restr_eq_rel R : funeq (restr_eq_rel f R).
Proof. by red; ins; red in H; desc; subst. Qed.

Lemma funeq_eqv_rel dom : funeq <| dom |>.
Proof. by red; ins; red in H; desc; subst. Qed.

Lemma funeq_transp R (H: funeq R) : funeq R^{-1}.
Proof. unfold funeq, transp in *; ins; symmetry; eauto. Qed.

Lemma funeq_minus R T (H: funeq R) : funeq (R \ T).
Proof. unfold funeq, minus_rel in *; ins; desf; eauto. Qed.

Lemma funeq_irreflexive R T (H: funeq R)
  (IRR: irreflexive (restr_eq_rel f T ;; R)) : irreflexive (T ;; R).
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
