(******************************************************************************)
(** * Equational properties of relations *)
(******************************************************************************)

Require Import Classical NPeano Omega Permutation List Setoid.
Require Import HahnBase HahnList HahnRelationsBasic HahnSets.

Set Implicit Arguments.

(******************************************************************************)
(** Set up setoid rewriting *)
(******************************************************************************)

(** First, for inclusion. *)

Add Parametric Relation (A : Type) : (relation A) (@inclusion A)
 reflexivity proved by (@inclusion_refl _)
 transitivity proved by (@inclusion_trans _)
 as inclusion_rel.

Add Parametric Morphism A : (@inclusion A) with signature
  inclusion --> inclusion ++> Basics.impl as inclusion_mori.
Proof.
  unfold inclusion, Basics.impl; ins; eauto.
Qed.

Add Parametric Morphism A : (@union A) with signature
  inclusion ==> inclusion ==> inclusion as union_mori.
Proof.
  unfold inclusion, union; intuition; eauto.
Qed.

Add Parametric Morphism A : (@inter_rel A) with signature
  inclusion ==> inclusion ==> inclusion as inter_rel_mori.
Proof.
  unfold inclusion, inter_rel; intuition; eauto.
Qed.

Add Parametric Morphism A : (@minus_rel A) with signature
  inclusion ++> inclusion --> inclusion as minus_rel_mori.
Proof.
  unfold inclusion, minus_rel; intuition; eauto.
Qed.

Add Parametric Morphism A : (@seq A) with signature
  inclusion ==> inclusion ==> inclusion as seq_mori.
Proof.
  unfold inclusion, seq; intuition; desf; eauto.
Qed.

Add Parametric Morphism A : (@irreflexive A) with signature
  inclusion --> Basics.impl as irreflexive_mori.
Proof.
  unfold inclusion, irreflexive, Basics.impl; intuition; desf; eauto.
Qed.

Add Parametric Morphism A : (@clos_trans A) with signature
  inclusion ==> inclusion as clos_trans_mori.
Proof.
  unfold inclusion; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism A : (@clos_refl_trans A) with signature
  inclusion ==> inclusion as clos_refl_trans_mori.
Proof.
  unfold inclusion; eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism A : (@clos_refl A) with signature
  inclusion ==> inclusion as clos_refl_mori.
Proof.
  unfold inclusion, clos_refl; intuition; eauto.
Qed.

Add Parametric Morphism A P : (@restr_rel A P) with signature
  inclusion ==> inclusion as restr_rel_mori.
Proof.
  unfold inclusion, restr_rel; intuition; eauto.
Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature
  eq ==> inclusion ==> inclusion as restr_eq_rel_mori.
Proof.
  unfold inclusion, restr_eq_rel; intuition; eauto.
Qed.

Add Parametric Morphism A : (@acyclic A) with signature
  inclusion --> Basics.impl as acyclic_mori.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism A : (@is_total A) with signature
  set_subset --> inclusion ++> Basics.impl as is_total_mori.
Proof.
  unfold inclusion, is_total, Basics.impl; ins; desf.
  eapply H1 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism A : (@transp A) with signature
  inclusion ==> inclusion as transp_mori.
Proof.
  unfold inclusion, transp; eauto.
Qed.

Add Parametric Morphism A : (@functional A) with signature
  inclusion --> Basics.impl as functional_mori.
Proof.
  unfold same_relation, inclusion, functional; ins; desf; red; ins; eauto.
Qed.

Add Parametric Morphism A : (@eqv_rel A) with signature
  set_subset ==> inclusion as eqv_rel_mori.
Proof.
  unfold inclusion, set_subset, eqv_rel; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@pow_rel X) with signature
  inclusion ==> eq ==> inclusion as pow_rel_mori.
Proof.
  ins. induction y0 as [| y' IH].
    by simpl; eauto with rel.
    by simpl; rewrite IH, H.
Qed.

Add Parametric Morphism A : (@well_founded A) with signature
  inclusion --> Basics.impl as well_founded_mori.
Proof.
  repeat red; ins; induction (H0 a); econs; eauto.
Qed.

Add Parametric Morphism A : (@cross_rel A) with signature
  set_subset ==> set_subset ==> inclusion as cross_mori.
Proof.
  unfold inclusion, cross_rel, set_subset; ins; desf; eauto.
Qed.

(** Second, for equivalence. *)

Lemma same_relation_exp A (r r' : relation A) (EQ: r ≡ r') :
  forall x y, r x y <-> r' x y.
Proof. split; apply EQ. Qed.

Lemma same_relation_refl A : reflexive (@same_relation A).
Proof. split; ins. Qed.

Lemma same_relation_sym A : symmetric (@same_relation A).
Proof. unfold same_relation; split; ins; desf. Qed.

Lemma same_relation_trans A : transitive (@same_relation A).
Proof. unfold same_relation; split; ins; desf; red; eauto. Qed.

Add Parametric Relation (A : Type) : (relation A) (@same_relation A)
 reflexivity proved by (@same_relation_refl A)
 symmetry proved by (@same_relation_sym A)
 transitivity proved by (@same_relation_trans A)
 as same_rel.

Add Parametric Morphism A : (@inclusion A) with signature
  same_relation ==> same_relation ==> iff as inclusion_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@union A) with signature
  same_relation ==> same_relation ==> same_relation as union_more.
Proof.
  unfold same_relation, union; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@inter_rel A) with signature
  same_relation ==> same_relation ==> same_relation as inter_rel_more.
Proof.
  unfold same_relation, inter_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@minus_rel A) with signature
  same_relation ==> same_relation ==> same_relation as minus_rel_more.
Proof.
  unfold same_relation, minus_rel; ins; desf; split; red; intuition.
Qed.

Add Parametric Morphism A : (@seq A) with signature
  same_relation ==> same_relation ==> same_relation as seq_more.
Proof.
  unfold same_relation, seq; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@immediate A) with signature
  same_relation ==> same_relation as immediate_more.
Proof.
  ins; rewrite !immediateE; rewrite H; eauto.
Qed.

Add Parametric Morphism A : (@eqv_dom_rel A) with signature
  (@Permutation _) ==> same_relation as eqv_dom_rel_more.
Proof.
  by unfold same_relation, eqv_dom_rel; ins; desf; split; red; ins; desf;
     rewrite H in *.
Qed.

Add Parametric Morphism A P : (@restr_rel A P) with signature
  same_relation ==> same_relation as restr_rel_more.
Proof.
  unfold same_relation, restr_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature
  eq ==> same_relation ==> same_relation as restr_eq_rel_more.
Proof.
  unfold same_relation, restr_eq_rel; intuition; eauto using restr_eq_rel_mori.
Qed.

Add Parametric Morphism A : (@clos_trans A) with signature
  same_relation ==> same_relation as clos_trans_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism A : (@clos_refl_trans A) with signature
  same_relation ==> same_relation as clos_relf_trans_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf;
  eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism A : (@clos_refl A) with signature
  same_relation ==> same_relation as clos_relf_more.
Proof.
  unfold same_relation, clos_refl; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@irreflexive A) with signature
  same_relation ==> iff as irreflexive_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@acyclic A) with signature
  same_relation ==> iff as acyclic_more.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism A : (@transitive A) with signature
  same_relation ==> iff as transitive_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@is_total A) with signature
  @set_equiv _ ==> same_relation ==> iff as is_total_more.
Proof.
  unfold is_total, same_relation, inclusion, set_equiv; split. 
  intros H1 a Ha b Hb NEQ; desf.
  by cut(x0 a b \/ x0 b a); [ins; desf; eauto| apply H1; firstorder].
  intros H1 a Ha b Hb NEQ; desf.
  by cut(y0 a b \/ y0 b a); [ins; desf; eauto| apply H1; firstorder].
Qed.

Add Parametric Morphism A : (@transp A) with signature
  same_relation ==> same_relation as transp_more.
Proof.
  unfold same_relation, transp; ins; desf; eauto; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@functional A) with signature
  same_relation ==> Basics.impl as functional_more.
Proof.
  unfold same_relation, inclusion, functional; ins; desf; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@eqv_rel A) with signature
  @set_equiv _ ==> same_relation as eqv_rel_more.
Proof.
  unfold same_relation, inclusion, set_equiv, eqv_rel; firstorder.
Qed.

Add Parametric Morphism X : (@pow_rel X) with signature
same_relation ==> eq ==> same_relation as pow_rel_more.
Proof.
  ins. induction y0 as [| y' IH].
    by simpl; eauto with rel.
    by simpl; rewrite IH, H.
Qed.

Add Parametric Morphism A : (@well_founded A) with signature
  same_relation ==> iff as well_founded_more.
Proof.
  unfold same_relation; split; eapply well_founded_mori; desf.
Qed.

Add Parametric Morphism A : (@cross_rel A) with signature
  set_equiv ==> set_equiv ==> same_relation as cross_more.
Proof.
  unfold same_relation, set_equiv; ins; desf; eauto using cross_mori.
Qed.

(******************************************************************************)
(** Basic properties of sequential composition and relational union *)
(******************************************************************************)

Section PropertiesSeqUnion.

  Variables B A : Type.
  Implicit Type r : relation A.
  Implicit Type rr : B -> relation A.

  Lemma seqA r1 r2 r3 : (r1 ⨾ r2) ⨾ r3 ≡ r1 ⨾ (r2 ⨾ r3).
  Proof.
    unfold seq; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_false_l r : ∅₂ ⨾ r ≡ ∅₂.
  Proof.
    split; unfold seq, inclusion; ins; desf.
  Qed.

  Lemma seq_false_r r : r ⨾ ∅₂ ≡ ∅₂.
  Proof.
    split; unfold seq, inclusion; ins; desf.
  Qed.

  Lemma seq_id_l r :  ⦗fun _ => True⦘ ⨾ r ≡ r.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_id_r r : r ⨾ ⦗fun _ => True⦘ ≡ r.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto.
  Qed.

  Lemma unionA r1 r2 r3 : (r1 ∪ r2) ∪ r3 ≡ r1 ∪ (r2 ∪ r3).
  Proof.
    unfold seq, union; split; red; ins; desf; eauto.
  Qed.

  Lemma unionC r1 r2 : r1 ∪ r2 ≡ r2 ∪ r1.
  Proof.
    unfold seq, union; split; red; ins; desf; eauto.
  Qed.

  Lemma unionAC r r' r'' : r ∪ (r' ∪ r'') ≡ r' ∪ (r ∪ r'').
  Proof.
    rewrite <- !unionA, (unionC r r'); vauto.
  Qed.

  Lemma unionK r : r ∪ r ≡ r.
  Proof.
    split; eauto with rel.
  Qed.

  Lemma union_false_r r : r ∪ ∅₂ ≡ r.
  Proof.
    split; unfold union, inclusion; ins; desf; eauto.
  Qed.

  Lemma union_false_l r : ∅₂ ∪ r ≡ r.
  Proof.
    by rewrite unionC, union_false_r.
  Qed.

  Lemma seq_union_l r1 r2 r : (r1 ∪ r2) ⨾ r ≡ (r1 ⨾ r) ∪ (r2 ⨾ r).
  Proof.
    unfold seq, union; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_union_r r r1 r2 : r ⨾ (r1 ∪ r2) ≡ (r ⨾ r1) ∪ (r ⨾ r2).
  Proof.
    unfold seq, union; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_Union_l P rr r : Union P rr ⨾ r ≡ Union P (fun n => rr n ⨾ r).
  Proof.
    unfold seq, Union; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_Union_r r P rr : r ⨾ Union P rr ≡ Union P (fun n => r ⨾ rr n).
  Proof.
    unfold seq, Union; split; red; ins; desf; eauto.
  Qed.

  Lemma minus_union_l r1 r2 r :
    (r1 ∪ r2) \ r ≡ (r1 \ r) ∪ (r2 \ r).
  Proof.
    unfold minus_rel, union; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_eqvK (dom : A -> Prop) : ⦗dom⦘ ⨾ ⦗dom⦘ ≡ ⦗dom⦘.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_eqvK_l (dom1 dom2 : A -> Prop) (IMP: forall x, dom2 x -> dom1 x) :
    ⦗dom1⦘ ⨾ ⦗dom2⦘ ≡ ⦗dom2⦘.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto 8.
  Qed.

  Lemma seq_eqvK_r (dom1 dom2 : A -> Prop) (IMP: forall x, dom1 x -> dom2 x) :
    ⦗dom1⦘ ⨾ ⦗dom2⦘ ≡ ⦗dom1⦘.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto 8.
  Qed.

  Lemma seq_eqvC (doma domb : A -> Prop) :
    ⦗doma⦘ ⨾ ⦗domb⦘ ≡ ⦗domb⦘ ⨾ ⦗doma⦘.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto 8.
  Qed.

  Lemma seq_eqv (doma domb : A -> Prop) :
    ⦗doma⦘ ⨾ ⦗domb⦘ ≡ ⦗fun x => doma x /\ domb x⦘.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto 8.
  Qed.

  Lemma union_absorb_l r r' (SUB: r ⊆ r') : r ∪ r' ≡ r'.
  Proof.
    split; auto with rel.
  Qed.

  Lemma union_absorb_r r r' (SUB: r ⊆ r') : r' ∪ r ≡ r'.
  Proof.
    split; auto with rel.
  Qed.

  Lemma id_union (s s': A -> Prop) : ⦗s ∪₁ s'⦘ ≡ ⦗s⦘ ∪ ⦗s'⦘.
  Proof.
    red; splits; unfold set_union, eqv_rel, union, inclusion; ins; desf; auto.
  Qed.

End PropertiesSeqUnion.

Hint Rewrite seq_false_l seq_false_r union_false_l union_false_r unionK : rel.
Hint Rewrite seq_id_l seq_id_r seq_eqvK : rel.

Hint Rewrite seq_Union_l seq_Union_r seq_union_l seq_union_r : rel_full.

(******************************************************************************)
(** Basic properties of relational intersection *)
(******************************************************************************)

Section PropertiesInter.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma interA r1 r2 r3 : (r1 ∩ r2) ∩ r3 ≡ r1 ∩ (r2 ∩ r3).
  Proof.
    firstorder.
  Qed.

  Lemma interC r1 r2 : r1 ∩ r2 ≡ r2 ∩ r1.
  Proof.
    firstorder.
  Qed.

  Lemma interAC r r' r'' : r ∩ (r' ∩ r'') ≡ r' ∩ (r ∩ r'').
  Proof.
    firstorder.
  Qed.

  Lemma interK r : r ∩ r ≡ r.
  Proof.
    firstorder.
  Qed.

  Lemma inter_false_r r : r ∩ ∅₂ ≡ ∅₂.
  Proof.
    firstorder.
  Qed.

  Lemma inter_false_l r : ∅₂ ∩ r ≡ ∅₂.
  Proof.
    firstorder.
  Qed.

  Lemma inter_union_r r r1 r2 : r ∩ (r1 ∪ r2) ≡ (r ∩ r1) ∪ (r ∩ r2).
  Proof.
    firstorder.
  Qed.

  Lemma inter_union_l r r1 r2 : (r1 ∪ r2) ∩ r ≡ (r1 ∩ r) ∪ (r2 ∩ r).
  Proof.
    firstorder.
  Qed.

  Lemma inter_absorb_l r r' (SUB: r ⊆ r') : r' ∩ r ≡ r.
  Proof.
    firstorder.
  Qed.

  Lemma inter_absorb_r r r' (SUB: r ⊆ r') : r ∩ r' ≡ r.
  Proof.
    firstorder.
  Qed.

  Lemma inter_trans (r r' i : relation A) (T: transitive i) :
  (r ∩ i) ⨾ (r' ∩ i) ⊆ (r ⨾ r') ∩ i.
  Proof.
    firstorder.
  Qed.

  Lemma inter_inclusion (r i : relation A) : r ∩ i ⊆ r.
  Proof.
    firstorder.
  Qed.

End PropertiesInter.

Hint Rewrite inter_false_l inter_false_r interK : rel.

(******************************************************************************)
(** Properties of relational difference *)
(******************************************************************************)

Section PropertiesMinus.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma minus_false_r r : r \ ∅₂ ≡ r.
  Proof.
    firstorder.
  Qed.

  Lemma minus_false_l r : ∅₂ \ r ≡ ∅₂.
  Proof.
    firstorder.
  Qed.

  Lemma minusK r : r \ r ≡ ∅₂.
  Proof.
    unfold minus_rel; split; red; intuition.
  Qed.

  Lemma minus_absorb r r' (SUB: r ⊆ r') : r \ r' ≡ ∅₂.
  Proof.
    firstorder.
  Qed.

End PropertiesMinus.

Hint Rewrite minus_false_l minus_false_r minusK : rel.

(******************************************************************************)
(** Basic properties of reflexive and transitive closures *)
(******************************************************************************)

Section PropertiesClos.

  Variable A : Type.
  Implicit Types r : relation A.

  Lemma rtE r : r ＊ ≡ ⦗fun _ => True⦘ ∪ r⁺.
  Proof.
    unfold eqv_rel, union, same_relation, inclusion.
    split; ins; rewrite clos_refl_transE in *; tauto.
  Qed.

  Lemma crE r : r ^? ≡ ⦗fun _ => True⦘ ∪ r.
  Proof.
    unfold eqv_rel, union, same_relation, inclusion, clos_refl.
    split; ins; tauto.
  Qed.

  Lemma rtEE r : r ＊ ≡ ⋃ n, r ^^ n.
  Proof.
    split; ins; desc.
      unfold eqv_rel, Union, same_relation, inclusion; ins.
      induction H using clos_refl_trans_ind_left; desc.
        by exists 0.
      by exists (S a); vauto.
    apply inclusion_Union_l; ins.
    induction x; ins; [|rewrite IHx];
      unfold eqv_rel, seq; red; ins; desf; vauto.
  Qed.

  Lemma ct_begin r : r⁺ ≡ r ⨾ r ＊.
  Proof.
    unfold seq; split; red; ins; desf; rewrite t_step_rt in *; eauto.
  Qed.

  Lemma ct_end r : r⁺ ≡ r ＊ ⨾ r.
  Proof.
    unfold seq; split; red; ins; desf; rewrite t_rt_step in *; eauto.
  Qed.

  Lemma ctEE r : r⁺ ≡ ⋃ n, r ^^ (S n).
  Proof.
    by rewrite ct_end, rtEE, seq_Union_l.
  Qed.

  Lemma rt_begin r :
    r ＊ ≡ ⦗fun _ => True⦘ ∪ r ⨾ r ＊.
  Proof.
    rewrite <- ct_begin, <- rtE; vauto.
  Qed.

  Lemma rt_end r :
    r ＊ ≡ ⦗fun _ => True⦘ ∪ r ＊ ⨾ r.
  Proof.
    rewrite <- ct_end, <- rtE; vauto.
  Qed.

  Lemma ct_of_trans r (T: transitive r) : r⁺ ≡ r.
  Proof.
    split; eauto with rel.
  Qed.

  Lemma rt_of_trans r (T: transitive r) : r ＊ ≡ r ^?.
  Proof.
    rewrite rtE, crE, ct_of_trans; vauto.
  Qed.

  Lemma cr_ct r : r ^? ⨾ r⁺ ≡ r⁺.
  Proof.
    unfold seq, clos_refl; split; red; ins; desf; eauto using t_trans, t_step.
  Qed.

  Lemma cr_rt r : r ^? ⨾ r ＊ ≡ r ＊.
  Proof.
    unfold seq, clos_refl; split; red; ins; desf; eauto using rt_trans, rt_step.
  Qed.

  Lemma ct_rt r : r⁺ ⨾ r ＊ ≡ r⁺.
  Proof.
    unfold seq; split; red; ins; desf; eauto using t_rt_trans, rt_refl.
  Qed.

  Lemma ct_ct r : r⁺ ⨾ r⁺ ⊆ r⁺.
  Proof.
    unfold seq; red; ins; desf; eauto using t_trans.
  Qed.

  Lemma ct_cr r : r⁺ ⨾ r ^? ≡ r⁺.
  Proof.
    unfold seq, clos_refl; split; red; ins; desf; eauto using t_trans, t_step.
  Qed.

  Lemma rt_rt r : r ＊ ⨾ r ＊ ≡ r ＊.
  Proof.
    unfold seq; split; red; ins; desf; eauto using rt_trans, rt_refl.
  Qed.

  Lemma rt_ct r : r ＊ ⨾ r⁺ ≡ r⁺.
  Proof.
    unfold seq; split; red; ins; desf; eauto using rt_t_trans, rt_refl.
  Qed.

  Lemma rt_cr r : r ＊ ⨾ r ^? ≡ r ＊.
  Proof.
    unfold seq, clos_refl; split; red; ins; desf; eauto using rt_trans, rt_step.
  Qed.

  Lemma cr_of_ct r : (r⁺) ^? ≡ r ＊.
  Proof.
    by rewrite rt_begin, ct_begin, crE.
  Qed.

  Lemma cr_of_cr r : (r ^?) ^? ≡ r ^?.
  Proof.
    by rewrite !crE, <- unionA, unionK.
  Qed.

  Lemma cr_of_rt r : (r ＊) ^? ≡ r ＊.
  Proof.
    by rewrite rtE, <- crE, cr_of_cr.
  Qed.

  Lemma ct_of_ct r: (r⁺)⁺ ≡ r⁺.
  Proof.
    split; eauto with rel.
  Qed.

  Lemma ct_of_union_ct_l r r' : (r⁺ ∪ r')⁺ ≡ (r ∪ r')⁺.
  Proof.
    split; eauto 8 with rel.
  Qed.

  Lemma ct_of_union_ct_r r r' : (r ∪ r'⁺)⁺ ≡ (r ∪ r')⁺.
  Proof.
    split; eauto 8 with rel.
  Qed.

  Lemma ct_of_cr r: (r ^?)⁺ ≡ r ＊.
  Proof.
    split; eauto with rel.
    apply inclusion_rt_ind_left; vauto.
    rewrite ct_begin at 2; eauto with rel.
  Qed.

  Lemma ct_of_rt r: (r ＊)⁺ ≡ r ＊.
  Proof.
    split; eauto with rel.
  Qed.

  Lemma rt_of_ct r : (r⁺) ＊ ≡ r ＊.
  Proof.
    split; eauto using inclusion_rt_rt2 with rel.
  Qed.

  Lemma rt_of_cr r : (r ^?) ＊ ≡ r ＊.
  Proof.
    split; eauto using inclusion_rt_rt2 with rel.
  Qed.

  Lemma rt_of_rt r : (r ＊) ＊ ≡ r ＊.
  Proof.
    split; eauto using inclusion_rt_rt2 with rel.
  Qed.

  Lemma cr_union_l r r' : (r ∪ r') ^? ≡ r ^? ∪ r'.
  Proof.
    by rewrite !crE, unionA.
  Qed.

  Lemma cr_union_r r r' : (r ∪ r') ^? ≡ r ∪ r' ^?.
  Proof.
    by rewrite unionC, cr_union_l, unionC.
  Qed.

  Lemma seq_rtE_r r r' : r ⨾ r' ＊ ≡ r ∪ (r ⨾ r') ⨾ r' ＊.
  Proof.
    by rewrite rt_begin at 1; rewrite ?seq_union_r, ?seq_id_r, ?seqA.
  Qed.

  Lemma seq_rtE_l r r' : r' ＊ ⨾ r ≡ r ∪ (r' ＊ ⨾ r' ⨾ r).
  Proof.
    by rewrite rt_end at 1; rewrite ?seq_union_l, ?seq_id_l, ?seqA.
  Qed.

  Lemma ct_step r : r ⊆ r⁺.
  Proof.
    firstorder.
  Qed.

  Lemma rt_unit r : r＊ ⨾ r ⊆ r＊.
  Proof.
    rewrite <- ct_end; apply inclusion_t_rt.
  Qed.

  Lemma ct_unit r : r⁺ ⨾ r ⊆ r⁺.
  Proof.
    unfold seq, inclusion; ins; desf; vauto.
  Qed.

  Lemma trailing_refl r r' e : r ⊆ r' -> r ⊆ r' ⨾ e^?.
  Proof.
    firstorder.
  Qed.

End PropertiesClos.

Hint Rewrite cr_of_ct cr_of_cr cr_of_rt
  ct_of_ct ct_of_cr ct_of_rt
  rt_of_ct rt_of_cr rt_of_rt : rel.

Definition good_ctx A (P: relation A -> relation A) :=
  << MON: Morphisms.Proper (inclusion ==> inclusion) P >> /\
  << CUN: forall (rr : nat -> relation A), P (⋃ n, rr n) ⊆ ⋃ n, P (rr n) >>. 

Section good_ctx_lemmas.

  Variables A : Type.
  Implicit Types P Q : relation A -> relation A.
  Implicit Types r : relation A.

  Lemma good_ctx_id : good_ctx (fun x : relation A => x).
  Proof.
    split; unnw; ins; vauto.
  Qed.

  Lemma good_ctx_const r : good_ctx (fun x : relation A => r).
  Proof.
    split; unnw; ins; repeat red; ins; vauto.
  Qed.

  Lemma good_ctx_seq_l P (GP : good_ctx P) r :
    good_ctx (fun x => P x ⨾ r).
  Proof.
    cdes GP; split; unnw; ins; [by do 2 red; ins; rewrite H|].
    by rewrite CUN, seq_Union_l.
  Qed.

  Lemma good_ctx_seq_r P (GP : good_ctx P) r :
    good_ctx (fun x => r ⨾ P x).
  Proof.
    cdes GP; split; unnw; ins; [by do 2 red; ins; rewrite H|].
    by rewrite CUN, seq_Union_r.
  Qed.

  Lemma good_ctx_union P (GP : good_ctx P) Q (GQ : good_ctx Q) :
    good_ctx (fun x => P x ∪ Q x).
  Proof.
    cdes GP; cdes GQ; split; unnw; ins; [by do 2 red; ins; rewrite H|].
    rewrite CUN, CUN0; firstorder.
  Qed.

  Lemma good_ctx_compose P (GP : good_ctx P) Q (GQ : good_ctx Q) :
    good_ctx (fun x => P (Q x)).
  Proof.
    cdes GP; cdes GQ; split; unnw; ins; [by do 2 red; ins; rewrite H|].
    rewrite CUN0, CUN; apply inclusion_Union_l; vauto.
  Qed.

  Lemma seq_pow_l r n : r ^^ n ⨾ r ≡ r ⨾ r ^^ n.
  Proof.
    induction n; ins; autorewrite with rel; try done.
    by rewrite IHn at 1; rewrite seqA.
  Qed.

  Lemma rt_ind_left P (G: good_ctx P) r r' :
    P ⦗fun _ => True⦘ ⊆ r' ->
    (forall k, P k ⊆ r' -> P (r ⨾ k) ⊆ r') ->
    P r＊ ⊆ r'.
  Proof.
    ins; cdes G; rewrite (proj1 (rtEE _)).
    etransitivity; [eapply CUN|apply inclusion_Union_l]; ins.
    induction x; ins; rewrite (proj1 (seq_pow_l _ _)); eauto.
  Qed.

  Lemma rt_ind_right P (G: good_ctx P) r r' :
    P ⦗fun _ => True⦘ ⊆ r' ->
    (forall k, P k ⊆ r' -> P (k ⨾ r) ⊆ r') ->
    P r＊ ⊆ r'.
  Proof.
    ins; cdes G; rewrite (proj1 (rtEE _)).
    etransitivity; [eapply CUN|apply inclusion_Union_l]; ins.
    induction x; ins; eauto.
  Qed.

  Lemma ct_ind_left P (G: good_ctx P) r r' :
    P r ⊆ r' -> (forall k, P k ⊆ r' -> P (r ⨾ k) ⊆ r') -> P ( r⁺ ) ⊆ r'.
  Proof.
    ins; cdes G; rewrite (proj1 (ct_end _)).
    apply rt_ind_left with (P := fun x => P (x ⨾ r)); ins;
      eauto using good_ctx_compose, good_ctx_seq_l, good_ctx_id.
      by rewrite (proj1 (seq_id_l _)).
    by rewrite (proj1 (seqA _ _ _)); eauto.
  Qed.

  Lemma ct_ind_right P (G: good_ctx P) r r' :
    P r ⊆ r' -> (forall k, P k ⊆ r' -> P (k ⨾ r) ⊆ r') -> P ( r⁺ ) ⊆ r'.
  Proof.
    ins; cdes G; rewrite (proj1 (ctEE _)).
    etransitivity; [eapply CUN|apply inclusion_Union_l]; ins.
    induction x; ins; eauto.
    by rewrite (proj1 (seq_id_l _)).
  Qed.

  Lemma ct_ind_left_helper P (G: good_ctx P) x r (EQ: x = r⁺) r' :
    P r ⊆ r' -> (forall k, P k ⊆ r' -> P (r ⨾ k) ⊆ r') -> P x ⊆ r'.
  Proof.
    by subst; apply ct_ind_left.
  Qed.

End good_ctx_lemmas.

Hint Resolve good_ctx_id good_ctx_const good_ctx_seq_l
  good_ctx_seq_r good_ctx_union good_ctx_compose : rel.

Section ExtraPropertiesClos.

  Variable A : Type.
  Implicit Types r : relation A.

  Lemma ct_seq_swap r r' :
    (r ⨾ r')⁺ ⨾ r ≡ r ⨾ (r' ⨾ r)⁺.
  Proof.
    split.
     { apply ct_ind_left with (P := fun x => x ⨾ _); auto with rel;
       ins; rewrite seqA; eauto with rel.
       rewrite ct_begin, H, ?seqA; eauto with rel. }
     apply ct_ind_right with (P := fun x => _ ⨾ x); auto with rel;
     ins; rewrite <- seqA; eauto with rel.
     rewrite ct_end, H, <- ?seqA; eauto with rel.
  Qed.

  Lemma rt_seq_swap r r' :
    (r ⨾ r') ＊ ⨾ r ≡ r ⨾ (r' ⨾ r) ＊.
  Proof.
    by rewrite !rtE; autorewrite with rel rel_full; rewrite ct_seq_swap.
  Qed.

  Lemma ct_rotl r r' :
    (r ⨾ r')⁺ ≡ r ⨾ (r' ⨾ r) ＊ ⨾ r'.
  Proof.
    by rewrite rt_seq_swap, ct_begin, seqA.
  Qed.

  Lemma crt_double r :
    r ＊ ≡ r ^? ⨾ (r ⨾ r) ＊.
  Proof.
    split; [|by eauto 7 using inclusion_seq_trans, inclusion_rt_rt2 with rel].
    apply inclusion_rt_ind_left; eauto with rel.
    rewrite !crE; autorewrite with rel rel_full.
    rewrite <- seqA, <- ct_begin; eauto with rel.
  Qed.

End ExtraPropertiesClos.

(******************************************************************************)
(** Properties of [eqv_rel] *)
(******************************************************************************)

Lemma seq_eqv_r A (r : relation A) dom :
  r ⨾ ⦗dom⦘ ≡ (fun x y => r x y /\ dom y).
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma seq_eqv_l A (r : relation A) dom :
  ⦗dom⦘ ⨾ r ≡ (fun x y => dom x /\ r x y).
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_l A (r : relation A) dom :
  ⦗dom⦘ ⨾ r ⊆ r.
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_r A (r : relation A) dom :
  r ⨾ ⦗dom⦘ ⊆ r.
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma seq_eqv_lr A (r : relation A) dom1 dom2 :
  ⦗dom1⦘ ⨾ r ⨾ ⦗dom2⦘ ≡ (fun x y : A => dom1 x /\ r x y /\ dom2 y).
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto 10.
Qed.

(******************************************************************************)
(** Properties of restrictions *)
(******************************************************************************)

Lemma same_relation_restr A (f : A -> Prop) r r' :
   (forall x (CONDx: f x) y (CONDy: f y), r x y <-> r' x y) ->
   (restr_rel f r ≡ restr_rel f r').
Proof.
  unfold restr_rel; split; red; ins; desf; rewrite H in *; eauto.
Qed.

Lemma restr_union A (f : A -> Prop) r r' :
  restr_rel f (r ∪ r') ≡ restr_rel f r ∪ restr_rel f r'.
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
Qed.

Lemma union_restr A (f : A -> Prop) r r' :
  restr_rel f r ∪ restr_rel f r' ≡ restr_rel f (r ∪ r').
Proof.
  symmetry; apply restr_union.
Qed.

Lemma restr_eq_union:
  forall (A : Type) (r r' : relation A) (B : Type) (f : A -> B),
  restr_eq_rel f (r ∪ r') ≡
  restr_eq_rel f r ∪ restr_eq_rel f r'.
Proof.
  unfold restr_eq_rel, union, same_relation, inclusion; intuition.
Qed.

Lemma restr_eq_elim :
  forall A (r : relation A) B (f: A -> B)
         (R: forall x y, r x y -> f x = f y),
   restr_eq_rel f r ≡ r.
Proof.
  unfold restr_eq_rel; split; red; ins; intuition.
Qed.

Lemma restr_eq_seq_eqv_rel A (r : relation A) (B : Type) (f : A -> B) dom :
  restr_eq_rel f (r⨾ ⦗dom⦘) ≡ restr_eq_rel f r⨾ ⦗dom⦘.
Proof.
  ins; rewrite !seq_eqv_r; unfold restr_eq_rel.
  split; red; ins; desf.
Qed.


(******************************************************************************)
(** Lemmas about [transp] *)
(******************************************************************************)

Section TranspProperties.

  Variable A : Type.
  Implicit Type r : relation A.
  Implicit Type dom : A -> Prop.

  Lemma transp_inv r : r⁻¹ ⁻¹ ≡ r.
  Proof.
    unfold transp; split; red; intuition.
  Qed.

  Lemma transp_eqv_rel dom : ⦗dom⦘⁻¹ ≡ ⦗dom⦘.
  Proof.
    unfold eqv_rel, transp; split; red; ins; desf.
  Qed.

  Lemma transp_union r1 r2 : (r1 ∪ r2)⁻¹ ≡ r1⁻¹ ∪ r2⁻¹.
  Proof.
    unfold transp, union; split; red; intuition.
  Qed.

  Lemma transp_seq r1 r2 : (r1 ⨾ r2)⁻¹ ≡ r2⁻¹ ⨾ r1⁻¹.
  Proof.
    unfold transp, seq; split; red; ins; desf; eauto.
  Qed.

  Lemma transp_inter r1 r2 : (r1 ∩ r2)⁻¹ ≡ r1⁻¹ ∩ r2⁻¹.
  Proof.
    unfold transp, inter_rel; split; red; intuition.
  Qed.

  Lemma transp_minus r1 r2 : (r1 \ r2)⁻¹ ≡ r1⁻¹ \ r2⁻¹.
  Proof.
    unfold transp, minus_rel; split; red; intuition.
  Qed.

  Lemma transp_rt r : (r＊) ⁻¹ ≡ (r⁻¹)＊.
  Proof.
    unfold transp, seq; split; red; ins; induction H; vauto.
  Qed.

  Lemma transp_ct r : (r⁺)⁻¹ ≡ (r⁻¹)⁺.
  Proof.
    unfold transp, seq; split; red; ins; induction H; vauto.
  Qed.

  Lemma transp_cr r : (r^?)⁻¹ ≡ (r⁻¹)^?.
  Proof.
    unfold transp, clos_refl; split; red; intuition.
  Qed.

  Lemma transitive_transp r : transitive r -> transitive (r⁻¹).
  Proof.
    unfold transp, transitive; eauto.
  Qed.

  Lemma inclusion_transpE r r' : r⁻¹ ⊆ r'⁻¹ -> r ⊆ r'.
  Proof.
    by unfold transp, inclusion; intuition.
  Qed.

  Lemma same_relation_transpE r r' : transp r ≡ transp r' -> r ≡ r'.
  Proof. 
    by unfold transp, same_relation, inclusion; intuition.
  Qed.

End TranspProperties.

Hint Rewrite transp_inv transp_eqv_rel: rel.
Hint Rewrite transp_inv transp_eqv_rel transp_union transp_seq 
  transp_inter transp_minus transp_rt transp_ct transp_cr : rel_transp.

Ltac rel_transp := 
  first [apply inclusion_transpE | apply same_relation_transpE ];
    autorewrite with rel_transp.

(******************************************************************************)
(** Properties of [pow_rel] *)
(******************************************************************************)
Lemma pow_t A n (r: relation A) : transitive r -> r ⨾ r^^n ⊆ r.
Proof.
  ins; induction n; simpl.
    by rewrite seq_id_r.
    by rewrite <- seqA, IHn; unfold inclusion, seq; ins; desf; eauto.
Qed.

Lemma pow_seq A n (r: relation A): r^^n ⨾ r ≡ r^^(S n).
Proof. by simpl. Qed.

Lemma pow_nm A (n m : nat) (r : relation A) : r^^n ⨾ r^^m ≡ r^^(n + m).
Proof.
  induction m; simpl.
    by rewrite <- plus_n_O; rewrite seq_id_r.
    by rewrite <- seqA, IHm, pow_seq, plus_n_Sm.
Qed.

Lemma pow_unit A (r : relation A) : r^^1 ≡ r.
Proof. by simpl; rewrite seq_id_l. Qed.

Lemma pow_inclusion (n : nat ) A (r r' : relation A): r ≡ r' -> r^^n ≡ r'^^n.
Proof. by ins; rewrite H. Qed.

Lemma pow_rt (n : nat) A (r: relation A) : r^^n ⊆ r＊.
Proof.
  induction n; simpl; eauto with rel.
  rewrite IHn.
  assert (r ⊆ r＊) by eauto with rel.
  rewrite H at 2.
  by rewrite rt_rt.
Qed.

(* Hint Resolve pow_t pow_rt : rel.
Hint Rewrite pow_seq pow_nm pow_unit pow_inclusion : rel. *)

(******************************************************************************)
(** Properties of cross product *)
(******************************************************************************)

Section PropertiesCross.

  Variable A : Type.
  Implicit Type s : A -> Prop.

  Lemma cross_false_r s : s × ∅ ≡ ∅₂.
  Proof.
    firstorder.
  Qed.

  Lemma cross_false_l s : ∅ × s ≡ ∅₂.
  Proof.
    firstorder.
  Qed.

End PropertiesCross.

Hint Rewrite cross_false_l cross_false_r : rel.

(******************************************************************************)
(** Misc properties *)
(******************************************************************************)

Lemma acyclic_mon A (r r' : relation A) :
  acyclic r -> r' ⊆ r -> acyclic r'.
Proof.
  eby repeat red; ins; eapply H, clos_trans_mon.
Qed.

Lemma acyclic_seqC A (r r' : relation A) :
  acyclic (r ⨾ r') <-> acyclic (r' ⨾ r).
Proof.
  by unfold acyclic; rewrite ct_rotl, irreflexive_seqC, !seqA, <- ct_end.
Qed.


Lemma clos_trans_imm :
  forall A (r : relation A) (I: irreflexive r)
         (T: transitive r) L (ND: NoDup L) a b
         (D: forall c, r a c -> r c b -> In c L)
         (REL: r a b),
    (immediate r)⁺ a b.
Proof.
  intros until 3; induction ND; ins; vauto.
  destruct (classic (r a x /\ r x b)) as [|N]; desf;
    [apply t_trans with x|]; eapply IHND; ins;
  forward (by eapply (D c); eauto) as K; desf; exfalso; eauto.
Qed.

Lemma ct_imm1 :
  forall A (r : relation A) (I: irreflexive r) (T: transitive r)
       acts (FIN : dom_rel r ⊆₁ (fun x => In x acts)),
    r ≡ (immediate r)⁺.
Proof.
  split; cycle 1.
    by rewrite immediateE, inclusion_minus_rel; auto with rel.
  assert (M: forall x y, r x y -> In x (undup acts)).
    by ins; eapply in_undup_iff, FIN; vauto.
  red; ins; eapply clos_trans_imm; eauto.
Qed.

Lemma ct_imm2 :
  forall A (r : relation A) (I: irreflexive r) (T: transitive r)
       acts (FIN : codom_rel r ⊆₁ (fun x => In x acts)),
    r ≡ (immediate r)⁺.
Proof.
  split; cycle 1.
    by rewrite immediateE, inclusion_minus_rel; auto with rel.
  assert (M: forall x y, r x y -> In y (undup acts)).
    by ins; eapply in_undup_iff, FIN; vauto.
  red; ins; eapply clos_trans_imm; eauto.
Qed.


Lemma immediate_clos_trans_elim A (r : relation A) a b :
  immediate (r⁺) a b ->
  r a b /\ (forall c, r⁺ a c -> r⁺ c b -> False).
Proof.
  unfold immediate; ins; desf; split; ins.
  apply t_step_rt in H; desf.
  apply clos_refl_transE in H1; desf; exfalso; eauto using t_step.
Qed.

Lemma clos_trans_immediate1 A (r : relation A) (T: transitive r) a b :
  (immediate r)⁺ a b -> r a b.
Proof.
  unfold immediate; induction 1; desf; eauto.
Qed.

Lemma clos_trans_immediate2 A (r : relation A)
      (T: transitive r) (IRR: irreflexive r) dom
      (D: forall a b (r: r a b), In b dom) a b :
  r a b ->
  (immediate r)⁺ a b.
Proof.
  assert (D': forall c, r a c -> r c b -> In c dom).
    by ins; apply D in H; desf.
  clear D; revert a b D'.
  remember (length dom) as n; revert dom Heqn; induction n.
    by destruct dom; ins; vauto.
  ins; destruct (classic (exists c, r a c /\ r c b)); desf.
  2: by eapply t_step; split; ins; eauto.
  forward (by eapply D'; eauto) as K; apply in_split in K; desf.
  rewrite app_length in *; ins; rewrite <- plus_n_Sm, <- app_length in *; desf.
  apply t_trans with c; eapply IHn with (dom := l1 ++ l2); ins;
  forward (by eapply (D' c0); eauto);
  rewrite !in_app_iff; ins; desf; eauto; exfalso; eauto.
Qed.

Lemma clos_trans_imm2 :
  forall A (r : relation A) (I: irreflexive r)
         (T: transitive r) L a b
         (D: forall c, r a c -> r c b -> In c L)
         (REL: r a b),
    (immediate r)⁺ a b.
Proof.
  ins; eapply clos_trans_imm with (L := undup L); ins;
  try rewrite in_undup_iff; eauto using nodup_undup.
Qed.


Lemma total_immediate_unique:
  forall A (r: A -> A -> Prop) (P: A -> Prop)
         (Tot: is_total P r)
         a b c (pa: P a) (pb: P b) (pc: P c)
         (iac: immediate r a c)
         (ibc: immediate r b c),
    a = b.
Proof.
  ins; destruct (classic (a = b)) as [|N]; eauto.
  exfalso; unfold immediate in *; desf.
  eapply Tot in N; eauto; desf; eauto.
Qed.

Lemma acyclic_case_split A (r : relation A) f :
  acyclic r <->
  acyclic (restr_rel f r) /\ (forall x (NEG: ~ f x) (CYC: r⁺ x x), False).
Proof.
  unfold restr_rel; repeat split; repeat red; ins; desc; eauto.
    by eapply H, clos_trans_mon; eauto; instantiate; ins; desf.
  destruct (classic (f x)) as [K|K]; eauto.
  assert (M: (fun a b => r a b /\ f a /\ f b) ＊ x x) by vauto.
  generalize K; revert H0 M K; generalize x at 2 3 5; ins.
  apply clos_trans_tn1 in H0; induction H0; eauto 6 using rt_t_trans, t_step.
  destruct (classic (f y)); eauto 6 using clos_refl_trans.
  eapply H1; eauto.
  eapply t_rt_trans, rt_trans; eauto using t_step, clos_trans_in_rt, clos_tn1_trans.
  by eapply clos_refl_trans_mon; eauto; instantiate; ins; desf.
Qed.

Lemma seqA2 A (r r' r'' : relation A) x y :
  ((r⨾ r')⨾ r'') x y <-> (r⨾ r'⨾ r'') x y.
Proof.
  unfold seq; split; ins; desf; eauto 8.
Qed.

Lemma inclusion_t_r_t A (r r' r'': relation A) :
  r ⊆ r'' ->
  r' ⊆ r'' ＊ ->
  r⁺ ⨾ r' ⊆ r''⁺.
Proof.
  by ins; rewrite H, H0, ct_rt.
Qed.

Lemma inclusion_r_t_t A (r r' r'': relation A) :
  r ⊆ r'' ＊ ->
  r' ⊆ r'' ->
  r ⨾ r'⁺ ⊆ r''⁺.
Proof.
  by ins; rewrite H, H0, rt_ct.
Qed.

Lemma inclusion_step2_ct A (r r' r'': relation A) :
  r ⊆ r'' ->
  r' ⊆ r'' ->
  r ⨾ r' ⊆ r''⁺.
Proof.
  ins; rewrite H, H0, <- ct_ct; eauto with rel.
Qed.

Lemma inclusion_ct_seq_eqv_l A dom (r : relation A) :
  (⦗dom⦘ ⨾ r)⁺ ⊆ ⦗dom⦘ ⨾ r⁺.
Proof.
  by rewrite ct_begin, seqA, inclusion_seq_eqv_l with (r:=r), <- ct_begin.
Qed.

Lemma inclusion_ct_seq_eqv_r A dom (r : relation A) :
  (r ⨾ ⦗dom⦘)⁺ ⊆ r⁺ ⨾ ⦗dom⦘.
Proof.
  by rewrite ct_end, inclusion_seq_eqv_r at 1; rewrite <- seqA, <- ct_end.
Qed.

Lemma minus_eqv_rel_helper A (R T: relation A) d1 d2:
  ⦗d1⦘ ⨾ (R \ T) ⨾ ⦗d2⦘ ≡ (⦗d1⦘ ⨾ R ⨾ ⦗d2⦘) \ T.
Proof.
  red; split; unfold inclusion, eqv_rel, minus_rel, seq; ins; desf; firstorder.
Qed.

Lemma fun_seq_minus_helper A (R S T: relation A)
  (FUN: functional R):
  R ⨾ (S \ T) ≡ (R ⨾ S) \ (R ⨾ T).
Proof.
  red; unfold minus_rel, seq, inclusion, transp, eqv_rel in *;
  splits; ins; desf; firstorder.
  intro; desf.
  assert (z=z0); try by subst.
  eapply FUN; eauto.
Qed.

Lemma inter_irrefl_equiv A (r r' : relation A) :
  r ∩ r' ≡ ∅₂ <-> irreflexive (r' ⨾ r⁻¹).
Proof.
  firstorder.
Qed.

Lemma tot_ex X (mo : relation X) dom (TOT: is_total dom mo) a b
  (INa: dom a) (INb: dom b)
  (NMO: ~ mo a b) (NEQ: a <> b) : mo b a.
Proof. eapply TOT in NEQ; desf; eauto. Qed.
