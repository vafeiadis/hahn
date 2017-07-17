Require Import HahnBase HahnSets HahnRelationsBasic.
Require Import Classical Setoid.
Set Implicit Arguments.

(** * Calculating the (co)domain of a relation *)

Section Domains.

Variable A : Type.

Section Definitions.
  Variable r : relation A.
  Variable d : A -> Prop.

  Definition doma := forall x y (REL: r x y), d x.
  Definition domb := forall x y (REL: r x y), d y.
End Definitions.

Section Lemmas.

  Variables r r' : relation A.
  Variable B : Type.
  Variables f : A -> B.
  Variables d d' : A -> Prop.

  Lemma eqv_doma : doma ⦗d⦘ d.
  Proof. unfold doma, eqv_rel; ins; desf. Qed.

  Lemma eqv_domb : domb ⦗d⦘ d.
  Proof. unfold domb, eqv_rel; ins; desf. Qed.

  Lemma seq_eqv_doma : doma r d -> doma (⦗d'⦘ ⨾ r) d.
  Proof. unfold doma, eqv_rel, seq; ins; desf; eauto. Qed.

  Lemma seq_eqv_domb : domb r d -> domb (r ⨾ ⦗d'⦘) d.
  Proof. unfold domb, eqv_rel, seq; ins; desf; eauto. Qed.

  Lemma restr_eq_rel_doma : doma r d -> doma (restr_eq_rel f r) d.
  Proof. unfold doma, restr_eq_rel; ins; desf; eauto. Qed.

  Lemma restr_eq_rel_domb : domb r d -> domb (restr_eq_rel f r) d.
  Proof. unfold domb, restr_eq_rel; ins; desf; eauto. Qed.

  Lemma seq_doma : doma r d -> doma (r ⨾ r') d.
  Proof. unfold doma, seq; ins; desf; eauto. Qed.

  Lemma seq_domb : domb r' d -> domb (r ⨾ r') d.
  Proof. unfold domb, seq; ins; desf; eauto. Qed.

  Lemma union_doma : doma r d -> doma r' d -> doma (r ∪ r') d.
  Proof. unfold doma, union; ins; desf; eauto. Qed.

  Lemma union_domb : domb r d -> domb r' d -> domb (r ∪ r') d.
  Proof. unfold domb, union; ins; desf; eauto. Qed.

  Lemma ct_doma : doma r d -> doma r⁺ d.
  Proof. induction 2; eauto. Qed.

  Lemma ct_domb : domb r d -> domb r⁺ d.
  Proof. induction 2; eauto. Qed.

  Lemma seq_r_doma : doma r d -> doma r' d -> doma (r^? ⨾ r') d.
  Proof. unfold clos_refl, seq; red; ins; desf; eauto. Qed.

  Lemma seq_r_domb : domb r d -> domb r' d -> domb (r ⨾ r'^?) d.
  Proof. unfold clos_refl, seq; red; ins; desf; eauto. Qed.

  Lemma minus_doma :doma r d -> doma (r \ r') d.
  Proof. unfold doma, minus_rel; ins; desf; eauto. Qed.

  Lemma minus_domb :domb r d -> domb (r \ r') d.
  Proof. unfold domb, minus_rel; ins; desf; eauto. Qed.

  Lemma dom_union x : dom_rel (r ∪ r') x <-> dom_rel r x \/ dom_rel r' x.
  Proof. unfold dom_rel, union; split; ins; desf; eauto. Qed.

  Lemma codom_union x : codom_rel (r ∪ r') x <-> codom_rel r x \/ codom_rel r' x.
  Proof. unfold codom_rel, union; split; ins; desf; eauto. Qed.

  Lemma dom_eqv x : dom_rel ⦗d⦘ x <-> d x.
  Proof. unfold dom_rel, eqv_rel; split; ins; desf; eauto. Qed.

  Lemma codom_eqv x : codom_rel ⦗d⦘ x <-> d x.
  Proof. unfold codom_rel, eqv_rel; split; ins; desf; eauto. Qed.

  Lemma dom_eqv1 x : dom_rel (⦗d⦘ ⨾ r) x <-> d x /\ dom_rel r x.
  Proof. unfold dom_rel, seq, eqv_rel; split; ins; desf; eauto. Qed.

  Lemma codom_eqv1 x : codom_rel (r ⨾ ⦗d⦘) x <-> codom_rel r x /\ d x.
  Proof. unfold codom_rel, seq, eqv_rel; split; ins; desf; eauto. Qed.

  Lemma transp_doma : domb r d -> doma (transp r) d.
  Proof. unfold doma, domb, transp; eauto. Qed.

  Lemma transp_domb : doma r d -> domb (transp r) d.
  Proof. unfold doma, domb, transp; eauto. Qed.

  Lemma doma_implies : (forall a, d a -> d' a) -> doma r d -> doma r d'.
  Proof. unfold doma; eauto. Qed.

  Lemma domb_implies : (forall a, d a -> d' a) -> domb r d -> domb r d'.
  Proof. unfold domb; eauto. Qed.

  Lemma doma_fold :
    (doma r d) -> (forall a, d a -> d' a) -> ⦗d'⦘ ⨾ r ≡ r.
  Proof. unfold eqv_rel, seq; split; red; ins; desf; eauto 6. Qed.

  Lemma domb_fold :
    (domb r d) -> (forall a, d a -> d' a) -> r ⨾ ⦗d'⦘ ≡ r.
  Proof. unfold eqv_rel, seq; split; red; ins; desf; eauto 6. Qed.
  
  Lemma doma_helper : r ⊆ ⦗d⦘ ⨾ r <-> doma r d.
  Proof.
    split; unfold doma, inclusion, seq, eqv_rel; ins; desf.
      by apply H in REL; desf.
      by eexists; splits; eauto.
  Qed.

  Lemma domb_helper : r ⊆ r ⨾ ⦗d⦘ <-> domb r d.
  Proof. 
    split; unfold domb, inclusion, seq, eqv_rel; ins; desf. 
      by apply H in REL; desf.
      by eexists; splits; eauto.
  Qed.
  
  Lemma domab_helper : 
    r ⊆ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ <-> doma r d /\ domb r d'.
  Proof.
    split; ins; splits; unfold doma, domb, inclusion, eqv_rel, seq in *; 
    ins; desf; try specialize (H _ _ REL); try specialize (H1 _ _ H0);
    desf; splits; eexists; splits; eauto.
  Qed.

End Lemmas.

End Domains.

Hint Resolve
  eqv_doma seq_eqv_doma restr_eq_rel_doma seq_doma union_doma ct_doma seq_r_doma
  eqv_domb seq_eqv_domb restr_eq_rel_domb seq_domb union_domb ct_domb seq_r_domb
  transp_doma transp_domb
: rel.

Add Parametric Morphism A : (@doma A) with signature
  inclusion --> set_subset ==> Basics.impl as doma_mori.
Proof.
  unfold inclusion, doma, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@domb A) with signature
  inclusion --> set_subset ==> Basics.impl as domb_mori.
Proof.
  unfold inclusion, domb, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@doma A) with signature
  same_relation ==> set_equiv ==> iff as doma_more.
Proof.
  unfold same_relation; ins; rewrite set_equivE in *; 
    desc; split; eapply doma_mori; eauto.
Qed.

Add Parametric Morphism A : (@domb A) with signature
  same_relation ==> set_equiv ==> iff as domb_more.
Proof.
  unfold same_relation; ins; rewrite set_equivE in *; 
    desc; split; eapply domb_mori; eauto.
Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
  inclusion ==> set_subset as dom_rel_mori.
Proof.
  firstorder.
Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
  inclusion ==> set_subset as codom_rel_mori.
Proof.
  firstorder.
Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
  same_relation ==> set_equiv as dom_rel_more.
Proof.
  firstorder.
Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
  same_relation ==> set_equiv as codom_rel_more.
Proof.
  firstorder. 
Qed.

Hint Rewrite dom_union codom_union dom_eqv codom_eqv dom_eqv1 codom_eqv1 : rel_dom.
