(******************************************************************************)
(** * Equational properties of relations *)
(******************************************************************************)

Require Import Program.Basics Arith micromega.Lia Permutation List Setoid.
Require Import HahnBase HahnList HahnRelationsBasic HahnSets.

Set Implicit Arguments.

Local Open Scope program_scope.

(******************************************************************************)
(** Set up setoid rewriting *)
(******************************************************************************)

Global Hint Unfold Basics.impl : unfolderDb.
Local Ltac u := autounfold with unfolderDb in *; splits; ins; desf;
                try solve [intuition; desf; eauto].

(** First, for inclusion. *)

Add Parametric Relation (A : Type) : (relation A) (@inclusion A)
 reflexivity proved by (@inclusion_refl _)
 transitivity proved by (@inclusion_trans _)
 as inclusion_rel.

Add Parametric Morphism A : (@inclusion A) with signature
  inclusion --> inclusion ++> Basics.impl as inclusion_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@union A) with signature
  inclusion ==> inclusion ==> inclusion as union_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@inter_rel A) with signature
  inclusion ==> inclusion ==> inclusion as inter_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@minus_rel A) with signature
  inclusion ++> inclusion --> inclusion as minus_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@seq A) with signature
  inclusion ==> inclusion ==> inclusion as seq_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@irreflexive A) with signature
  inclusion --> Basics.impl as irreflexive_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@clos_refl A) with signature
  inclusion ==> inclusion as clos_refl_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@clos_trans A) with signature
  inclusion ==> inclusion as clos_trans_mori.
Proof. u; eauto using clos_trans_mon. Qed.

Add Parametric Morphism A : (@clos_refl_trans A) with signature
  inclusion ==> inclusion as clos_refl_trans_mori.
Proof. u; eauto using clos_refl_trans_mon. Qed.

Add Parametric Morphism A : (@clos_sym A) with signature
  inclusion ==> inclusion as clos_sym_mori.
Proof. unfold clos_sym. u. Qed.

Add Parametric Morphism A : (@clos_refl_sym A) with signature
  inclusion ==> inclusion as clos_refl_sym_mori.
Proof. unfold clos_refl_sym. u. Qed.

Add Parametric Morphism A : (@restr_rel A) with signature
  set_subset ==> inclusion ==> inclusion as restr_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature
  eq ==> inclusion ==> inclusion as restr_eq_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A B : (@map_rel A B) with signature 
    eq ==> inclusion ==> inclusion as map_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@acyclic A) with signature
  inclusion --> Basics.impl as acyclic_mori.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism A : (@is_total A) with signature
  set_subset --> inclusion ++> Basics.impl as is_total_mori.
Proof. u; ins; desf; eapply H1 in NEQ; desf; eauto. Qed.

Add Parametric Morphism A : (@transp A) with signature
  inclusion ==> inclusion as transp_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@functional A) with signature
  inclusion --> Basics.impl as functional_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@eqv_rel A) with signature
  set_subset ==> inclusion as eqv_rel_mori.
Proof. u. Qed.

Add Parametric Morphism X : (@pow_rel X) with signature
  inclusion ==> eq ==> inclusion as pow_rel_mori.
Proof.
  ins. induction y0 as [| y' IH].
    by simpl; eauto with hahn.
    by simpl; rewrite IH, H.
Qed.

Add Parametric Morphism A : (@well_founded A) with signature
  inclusion --> Basics.impl as well_founded_mori.
Proof.
  repeat red; ins; induction (H0 a); econs; eauto.
Qed.

Add Parametric Morphism A : (@cross_rel A) with signature
  set_subset ==> set_subset ==> inclusion as cross_mori.
Proof. u. Qed.

Add Parametric Morphism A B : (@bunion A B) with signature
  set_subset ==> eq ==> inclusion as bunion_mori.
Proof. u. Qed.

Add Parametric Morphism A B : (@collect_rel A B) with signature 
  eq ==> inclusion ==> inclusion as collect_rel_mori.
Proof. u; eauto 8. Qed.

(** Second, for equivalence. *)

Lemma same_relation_exp A (r r' : relation A) (EQ: r ≡ r') :
  forall x y, r x y <-> r' x y.
Proof. split; apply EQ. Qed.

Lemma same_relation_refl A : reflexive (@same_relation A).
Proof. u. Qed.

Lemma same_relation_sym A : symmetric (@same_relation A).
Proof. u. Qed.

Lemma same_relation_trans A : transitive (@same_relation A).
Proof. u. Qed.

Add Parametric Relation (A : Type) : (relation A) (@same_relation A)
 reflexivity proved by (@same_relation_refl A)
 symmetry proved by (@same_relation_sym A)
 transitivity proved by (@same_relation_trans A)
 as same_rel.

Add Parametric Morphism A : (@inclusion A) with signature
  same_relation ==> same_relation ==> iff as inclusion_more.
Proof. u. Qed.

Add Parametric Morphism A : (@union A) with signature
  same_relation ==> same_relation ==> same_relation as union_more.
Proof. u. Qed.

Add Parametric Morphism A : (@inter_rel A) with signature
  same_relation ==> same_relation ==> same_relation as inter_rel_more.
Proof. u. Qed.

Add Parametric Morphism A : (@minus_rel A) with signature
  same_relation ==> same_relation ==> same_relation as minus_rel_more.
Proof. u. Qed.

Add Parametric Morphism A : (@seq A) with signature
  same_relation ==> same_relation ==> same_relation as seq_more.
Proof. u. Qed.

Add Parametric Morphism A : (@immediate A) with signature
  same_relation ==> same_relation as immediate_more.
Proof. u. Qed.

Add Parametric Morphism A : (@eqv_dom_rel A) with signature
  (@Permutation _) ==> same_relation as eqv_dom_rel_more.
Proof. by u; rewrite H in *. Qed.

Add Parametric Morphism A : (@restr_rel A) with signature
  set_equiv ==> same_relation ==> same_relation as restr_rel_more.
Proof. u. Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature
  eq ==> same_relation ==> same_relation as restr_eq_rel_more.
Proof. u. Qed.

Add Parametric Morphism A B : (@map_rel A B) with signature 
    eq ==> same_relation ==> same_relation as map_rel_more.
Proof. u. Qed.

Add Parametric Morphism A : (@clos_refl A) with signature
  same_relation ==> same_relation as clos_relf_more.
Proof. u. Qed.

Add Parametric Morphism A : (@clos_trans A) with signature
  same_relation ==> same_relation as clos_trans_more.
Proof. u; eauto using clos_trans_mon. Qed.

Add Parametric Morphism A : (@clos_refl_trans A) with signature
  same_relation ==> same_relation as clos_refl_trans_more.
Proof. u; eauto using clos_refl_trans_mon. Qed.

Add Parametric Morphism A : (@clos_sym A) with signature
  same_relation  ==> same_relation as clos_sym_more.
Proof. unfold clos_sym. u. Qed.

Add Parametric Morphism A : (@clos_refl_sym A) with signature
  same_relation  ==> same_relation as clos_refl_sym_more.
Proof. unfold clos_refl_sym. u. Qed.

Add Parametric Morphism A : (@irreflexive A) with signature
  same_relation ==> iff as irreflexive_more.
Proof. u. Qed.

Add Parametric Morphism A : (@acyclic A) with signature
  same_relation ==> iff as acyclic_more.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism A : (@symmetric A) with signature
  same_relation ==> iff as symmetric_more.
Proof. u. Qed.

Add Parametric Morphism A : (@transitive A) with signature
  same_relation ==> iff as transitive_more.
Proof. u. Qed.

Add Parametric Morphism A : (@is_total A) with signature
  @set_equiv _ ==> same_relation ==> iff as is_total_more.
Proof.
  u; split; ins; desf; apply H3 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism A : (@transp A) with signature
  same_relation ==> same_relation as transp_more.
Proof. u. Qed.

Add Parametric Morphism A : (@functional A) with signature
  same_relation ==> Basics.impl as functional_more.
Proof. u. Qed.

Add Parametric Morphism A : (@eqv_rel A) with signature
  @set_equiv _ ==> same_relation as eqv_rel_more.
Proof. u. Qed.

Add Parametric Morphism X : (@pow_rel X) with signature
same_relation ==> eq ==> same_relation as pow_rel_more.
Proof.
  by ins; induction y0 as [| y' IH]; ins; rewrite IH, H.
Qed.

Add Parametric Morphism A : (@well_founded A) with signature
  same_relation ==> iff as well_founded_more.
Proof.
  unfold same_relation; split; eapply well_founded_mori; desf.
Qed.

Add Parametric Morphism A : (@cross_rel A) with signature
  set_equiv ==> set_equiv ==> same_relation as cross_more.
Proof. u. Qed.

Add Parametric Morphism A B : (@bunion A B) with signature
  set_equiv ==> eq ==> same_relation as bunion_more.
Proof. u. Qed.

Add Parametric Morphism A B : (@collect_rel A B) with signature 
  eq ==> same_relation ==> same_relation as collect_rel_more.
Proof. u; eauto 8. Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
  inclusion ==> set_subset as dom_rel_mori.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
  inclusion ==> set_subset as codom_rel_mori.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
  same_relation ==> set_equiv as dom_rel_more.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
  same_relation ==> set_equiv as codom_rel_more.
Proof. firstorder. Qed.

(******************************************************************************)
(** Basic properties of sequential composition and relational union *)
(******************************************************************************)

Section PropertiesSeqUnion.

  Variables B A : Type.
  Implicit Type r : relation A.
  Implicit Type rr : B -> relation A.
  Local Ltac uu := autounfold with unfolderDb in *; 
            try solve [intuition; ins; desf; eauto; firstorder].

  Lemma seqA r1 r2 r3 : (r1 ⨾ r2) ⨾ r3 ≡ r1 ⨾ (r2 ⨾ r3).
  Proof. uu. Qed.

  Lemma seq_false_l r : ∅₂ ⨾ r ≡ ∅₂.
  Proof. uu. Qed.

  Lemma seq_false_r r : r ⨾ ∅₂ ≡ ∅₂.
  Proof. uu. Qed.

  Lemma seq_id_l r :  ⦗fun _ => True⦘ ⨾ r ≡ r.
  Proof. uu. Qed.

  Lemma seq_id_r r : r ⨾ ⦗fun _ => True⦘ ≡ r.
  Proof. uu. Qed.

  Lemma unionA r1 r2 r3 : (r1 ∪ r2) ∪ r3 ≡ r1 ∪ (r2 ∪ r3).
  Proof. uu. Qed.

  Lemma unionC r1 r2 : r1 ∪ r2 ≡ r2 ∪ r1.
  Proof. uu. Qed.

  Lemma unionAC r r' r'' : r ∪ (r' ∪ r'') ≡ r' ∪ (r ∪ r'').
  Proof. uu. Qed.

  Lemma unionK r : r ∪ r ≡ r.
  Proof. uu. Qed.

  Lemma union_false_r r : r ∪ ∅₂ ≡ r.
  Proof. uu. Qed.

  Lemma union_false_l r : ∅₂ ∪ r ≡ r.
  Proof. uu. Qed.

  Lemma seq_union_l r1 r2 r : (r1 ∪ r2) ⨾ r ≡ (r1 ⨾ r) ∪ (r2 ⨾ r).
  Proof. uu. Qed.

  Lemma seq_union_r r r1 r2 : r ⨾ (r1 ∪ r2) ≡ (r ⨾ r1) ∪ (r ⨾ r2).
  Proof. uu. Qed.

  Lemma seq_bunion_l P rr r : bunion P rr ⨾ r ≡ (⋃n ∈ P, rr n ⨾ r). 
  Proof. uu. Qed.

  Lemma seq_bunion_r r P rr : r ⨾ bunion P rr ≡ (⋃n ∈ P, r ⨾ rr n). 
  Proof. uu. Qed.

  Lemma minus_union_l r1 r2 r : (r1 ∪ r2) \ r ≡ (r1 \ r) ∪ (r2 \ r).
  Proof. uu. Qed.

  Lemma seq_eqvK (dom : A -> Prop) : ⦗dom⦘ ⨾ ⦗dom⦘ ≡ ⦗dom⦘.
  Proof. uu. Qed.

  Lemma seq_eqvK_l (dom1 dom2 : A -> Prop) (IMP: forall x, dom2 x -> dom1 x) :
    ⦗dom1⦘ ⨾ ⦗dom2⦘ ≡ ⦗dom2⦘.
  Proof. uu. Qed.

  Lemma seq_eqvK_r (dom1 dom2 : A -> Prop) (IMP: forall x, dom1 x -> dom2 x) :
    ⦗dom1⦘ ⨾ ⦗dom2⦘ ≡ ⦗dom1⦘.
  Proof. uu. Qed.

  Lemma seq_eqvC (doma domb : A -> Prop) :
    ⦗doma⦘ ⨾ ⦗domb⦘ ≡ ⦗domb⦘ ⨾ ⦗doma⦘.
  Proof. uu. Qed.

  Lemma seq_eqv (doma domb : A -> Prop) :
    ⦗doma⦘ ⨾ ⦗domb⦘ ≡ ⦗fun x => doma x /\ domb x⦘.
  Proof. uu. Qed.

  Lemma union_absorb_l r r' (SUB: r ⊆ r') : r ∪ r' ≡ r'.
  Proof. uu. Qed.

  Lemma union_absorb_r r r' (SUB: r ⊆ r') : r' ∪ r ≡ r'.
  Proof. uu. Qed.

  Lemma id_union (s s': A -> Prop) : ⦗s ∪₁ s'⦘ ≡ ⦗s⦘ ∪ ⦗s'⦘.
  Proof. uu. Qed.

End PropertiesSeqUnion.

#[export] 
Hint Rewrite seq_false_l seq_false_r union_false_l union_false_r unionK
             seq_id_l seq_id_r seq_eqvK : hahn.

#[export] 
Hint Rewrite seq_bunion_l seq_bunion_r seq_union_l seq_union_r : hahn_full.

(******************************************************************************)
(** Properties of big union *)
(******************************************************************************)

Section PropertiesBigUnion.

  Variables B A : Type.
  Implicit Type r : relation A.
  Implicit Type rr : B -> relation A.
  Local Ltac uu := autounfold with unfolderDb in *; 
            try solve [intuition; ins; desf; eauto; firstorder].

  Lemma bunion_empty rr : bunion ∅ rr ≡ ∅₂.
  Proof. uu. Qed.
  
  Lemma bunion_eq a rr : bunion (eq a) rr ≡ rr a.
  Proof. u; splits; ins; desf; eauto. Qed. 

  Lemma bunion_union_l s s' rr :
    bunion (s ∪₁ s') rr ≡ bunion s rr ∪ bunion s' rr.
  Proof. uu. Qed. 

  Lemma bunion_union_r s rr rr' :
    bunion s (fun x => rr x ∪ rr' x) ≡ bunion s rr ∪ bunion s rr'.
  Proof. uu. Qed. 

  Lemma bunion_inter_compat_l s r rr :
    bunion s (fun x => r ∩ rr x) ≡ r ∩ bunion s rr.
  Proof. uu; split; ins; desf; eauto 8. Qed. 

  Lemma bunion_inter_compat_r s r rr :
    bunion s (fun x => rr x ∩ r) ≡ bunion s rr ∩ r.
  Proof. uu; split; ins; desf; eauto 8. Qed. 

  Lemma bunion_minus_compat_r s r rr :
    bunion s (fun x => rr x \ r) ≡ bunion s rr \ r.
  Proof. uu; split; ins; desf; eauto 8. Qed. 

End PropertiesBigUnion.


(******************************************************************************)
(** Basic properties of relational intersection *)
(******************************************************************************)

Section PropertiesInter.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma interA r1 r2 r3 : (r1 ∩ r2) ∩ r3 ≡ r1 ∩ (r2 ∩ r3).
  Proof. u. Qed.

  Lemma interC r1 r2 : r1 ∩ r2 ≡ r2 ∩ r1.
  Proof. u. Qed.

  Lemma interAC r r' r'' : r ∩ (r' ∩ r'') ≡ r' ∩ (r ∩ r'').
  Proof. u. Qed.

  Lemma interK r : r ∩ r ≡ r.
  Proof. u. Qed.

  Lemma inter_false_r r : r ∩ ∅₂ ≡ ∅₂.
  Proof. u. Qed.

  Lemma inter_false_l r : ∅₂ ∩ r ≡ ∅₂.
  Proof. u. Qed.

  Lemma inter_union_r r r1 r2 : r ∩ (r1 ∪ r2) ≡ (r ∩ r1) ∪ (r ∩ r2).
  Proof. u. Qed.

  Lemma inter_union_l r r1 r2 : (r1 ∪ r2) ∩ r ≡ (r1 ∩ r) ∪ (r2 ∩ r).
  Proof. u. Qed.

  Lemma inter_absorb_l r r' (SUB: r ⊆ r') : r' ∩ r ≡ r.
  Proof. u. Qed.

  Lemma inter_absorb_r r r' (SUB: r ⊆ r') : r ∩ r' ≡ r.
  Proof. u. Qed.

  Lemma inter_trans (r r' i : relation A) (T: transitive i) :
    (r ∩ i) ⨾ (r' ∩ i) ⊆ (r ⨾ r') ∩ i.
  Proof. u. Qed.

  Lemma inter_inclusion (r i : relation A) : r ∩ i ⊆ r.
  Proof. u. Qed.

  Lemma id_inter (s s' : A -> Prop) : ⦗s ∩₁ s'⦘ ≡ ⦗s⦘ ⨾ ⦗s'⦘.
  Proof. u. Qed.

  Lemma inter_restr_absorb_l (s : A -> Prop) r r' :
    restr_rel s r ∩ restr_rel s r' ≡ r ∩ restr_rel s r'.
  Proof. u. Qed.

  Lemma inter_restr_absorb_r (s : A -> Prop) r r' :
    restr_rel s r ∩ restr_rel s r' ≡ restr_rel s r ∩ r'.
  Proof. u. Qed.

End PropertiesInter.

#[export] 
Hint Rewrite inter_false_l inter_false_r interK : hahn.

(******************************************************************************)
(** Properties of relational difference *)
(******************************************************************************)

Section PropertiesMinus.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma minus_false_r r : r \ ∅₂ ≡ r.
  Proof. u. Qed.

  Lemma minus_false_l r : ∅₂ \ r ≡ ∅₂.
  Proof. u. Qed.

  Lemma minusK r : r \ r ≡ ∅₂.
  Proof. u. Qed.

  Lemma minus_absorb r r' (SUB: r ⊆ r') : r \ r' ≡ ∅₂.
  Proof. u. Qed.

End PropertiesMinus.

#[export] 
Hint Rewrite minus_false_l minus_false_r minusK : hahn.

(******************************************************************************)
(** Basic properties of reflexive/symmetric/transitive closures *)
(******************************************************************************)

Section PropertiesClos.

  Variable A : Type.
  Implicit Types r : relation A.

  Lemma crE r : r ^? ≡ ⦗fun _ => True⦘ ∪ r.
  Proof. u. Qed.

  Lemma rtE r : r ＊ ≡ ⦗fun _ => True⦘ ∪ r⁺.
  Proof.
    u; rewrite clos_refl_transE in *; tauto.
  Qed.

  Lemma rtEE r : r＊ ≡ ⋃n, r ^^ n.
  Proof.
    split; ins; desc.
      u. 
      induction H using clos_refl_trans_ind_left; desc.
        by exists 0.
      by exists (S a); vauto.
    apply inclusion_bunion_l; ins.
    induction x; ins; [|rewrite IHx];
      unfold eqv_rel, seq; red; ins; desf; vauto.
  Qed.

  Lemma csE r : r^⋈ ≡ r ∪ r⁻¹.
  Proof. u. Qed.

  Lemma crsE r : r^⋈? ≡ ⦗fun _ => True⦘ ∪ r ∪ r⁻¹.
  Proof. unfold clos_refl_sym. u. Qed.

  Lemma crsEE r : r^⋈? ≡ ⦗fun _ => True⦘ ∪ r^⋈.
  Proof. rewrite crsE, csE. u. Qed.

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
    by rewrite ct_end, rtEE, seq_bunion_l.
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
    split; eauto with hahn.
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
    split; eauto with hahn.
  Qed.

  Lemma ct_of_union_ct_l r r' : (r⁺ ∪ r')⁺ ≡ (r ∪ r')⁺.
  Proof.
    split; eauto 8 with hahn.
  Qed.

  Lemma ct_of_union_ct_r r r' : (r ∪ r'⁺)⁺ ≡ (r ∪ r')⁺.
  Proof.
    split; eauto 8 with hahn.
  Qed.

  Lemma ct_of_cr r: (r ^?)⁺ ≡ r ＊.
  Proof.
    split; eauto with hahn.
    apply inclusion_rt_ind_left; vauto.
    rewrite ct_begin at 2; eauto with hahn.
  Qed.

  Lemma ct_of_rt r: (r ＊)⁺ ≡ r ＊.
  Proof.
    split; eauto with hahn.
  Qed.

  Lemma rt_of_ct r : (r⁺) ＊ ≡ r ＊.
  Proof.
    split; eauto using inclusion_rt_rt2 with hahn.
  Qed.

  Lemma rt_of_cr r : (r ^?) ＊ ≡ r ＊.
  Proof.
    split; eauto using inclusion_rt_rt2 with hahn.
  Qed.

  Lemma rt_of_rt r : (r ＊) ＊ ≡ r ＊.
  Proof.
    split; eauto using inclusion_rt_rt2 with hahn.
  Qed.

  Lemma cr_union_l r r' : (r ∪ r') ^? ≡ r ^? ∪ r'.
  Proof.
    by rewrite !crE, unionA.
  Qed.

  Lemma cr_union_r r r' : (r ∪ r') ^? ≡ r ∪ r' ^?.
  Proof.
    by rewrite unionC, cr_union_l, unionC.
  Qed.

  Lemma cs_union r r' : (r ∪ r')^⋈  ≡ r^⋈ ∪ r'^⋈.
  Proof. rewrite !csE. u. Qed.

  Lemma crs_union r r' : (r ∪ r')^⋈? ≡ r^⋈? ∪ r'^⋈?.
  Proof. rewrite !crsE. u. Qed.

  Lemma cs_inter r r' : (r ∩ r')^⋈ ⊆ r^⋈ ∩ r'^⋈.
  Proof. rewrite !csE. u. Qed.

  Lemma crs_inter r r' : (r ∩ r')^⋈? ⊆ r^⋈? ∩ r'^⋈?.
  Proof. rewrite !crsE. u. Qed.

  Lemma cs_cross (s s' : A -> Prop) : (s × s')^⋈ ≡ s × s' ∪ s' × s.
  Proof. rewrite !csE. u. Qed.

  Lemma crs_cross (s s' : A -> Prop) : (s × s')^⋈? ≡ ⦗fun _ => True⦘ ∪ s × s' ∪ s' × s.
  Proof. rewrite !crsE. u. Qed.

  Lemma cs_restr (s : A -> Prop) r : (restr_rel s r)^⋈ ≡ restr_rel s r^⋈.
  Proof. rewrite !csE. u. Qed.

  Lemma crs_restr (s : A -> Prop) r : (restr_rel s r)^⋈? ≡ ⦗fun _ => True⦘ ∪ restr_rel s r^⋈.
  Proof. rewrite !csE, !crsE. u. Qed.

  Lemma restr_of_crs (s : A -> Prop) r : restr_rel s r^⋈? ≡ ⦗s⦘ ∪ restr_rel s r^⋈.
  Proof. rewrite !csE, !crsE. u. Qed.

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
    vauto.
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

  Lemma cr_seq (r r' : relation A) : r^? ⨾ r' ≡ r' ∪ r ⨾ r'.
  Proof. split; autounfold with unfolderDb; ins; desf; eauto. Qed.

  Lemma cr_helper (r r' : relation A) d (H: r ⨾ ⦗d⦘ ⊆ ⦗d⦘ ⨾ r') : r^? ⨾ ⦗d⦘ ⊆ ⦗d⦘ ⨾ r'^? .
  Proof.
    rewrite crE.
    autounfold with unfolderDb in *; ins; desf; eauto.
    edestruct H; eauto. desf. eauto.
  Qed.
End PropertiesClos.

#[export] 
Hint Rewrite cr_of_ct cr_of_cr cr_of_rt
  ct_of_ct ct_of_cr ct_of_rt
  rt_of_ct rt_of_cr rt_of_rt : hahn.

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
    by rewrite CUN, seq_bunion_l.
  Qed.

  Lemma good_ctx_seq_r P (GP : good_ctx P) r :
    good_ctx (fun x => r ⨾ P x).
  Proof.
    cdes GP; split; unnw; ins; [by do 2 red; ins; rewrite H|].
    by rewrite CUN, seq_bunion_r.
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
    rewrite CUN0, CUN; apply inclusion_bunion_l; vauto.
  Qed.

  Lemma seq_pow_l r n : r ^^ n ⨾ r ≡ r ⨾ r ^^ n.
  Proof.
    induction n; ins; autorewrite with hahn; try done.
    by rewrite IHn at 1; rewrite seqA.
  Qed.

  Lemma rt_ind_left P (G: good_ctx P) r r' :
    P ⦗fun _ => True⦘ ⊆ r' ->
    (forall k, P k ⊆ r' -> P (r ⨾ k) ⊆ r') ->
    P r＊ ⊆ r'.
  Proof.
    ins; cdes G; rewrite (proj1 (rtEE _)).
    etransitivity; [eapply CUN|apply inclusion_bunion_l]; ins.
    induction x; ins; rewrite (proj1 (seq_pow_l _ _)); eauto.
  Qed.

  Lemma rt_ind_right P (G: good_ctx P) r r' :
    P ⦗fun _ => True⦘ ⊆ r' ->
    (forall k, P k ⊆ r' -> P (k ⨾ r) ⊆ r') ->
    P r＊ ⊆ r'.
  Proof.
    ins; cdes G; rewrite (proj1 (rtEE _)).
    etransitivity; [eapply CUN|apply inclusion_bunion_l]; ins.
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
    etransitivity; [eapply CUN|apply inclusion_bunion_l]; ins.
    induction x; ins; eauto.
    by rewrite (proj1 (seq_id_l _)).
  Qed.

  Lemma ct_ind_left_helper P (G: good_ctx P) x r (EQ: x = r⁺) r' :
    P r ⊆ r' -> (forall k, P k ⊆ r' -> P (r ⨾ k) ⊆ r') -> P x ⊆ r'.
  Proof.
    by subst; apply ct_ind_left.
  Qed.

End good_ctx_lemmas.

Global Hint Resolve good_ctx_id good_ctx_const good_ctx_seq_l
  good_ctx_seq_r good_ctx_union good_ctx_compose : hahn.

Section ExtraPropertiesClos.

  Variable A : Type.
  Implicit Types r : relation A.

  Lemma ct_seq_swap r r' :
    (r ⨾ r')⁺ ⨾ r ≡ r ⨾ (r' ⨾ r)⁺.
  Proof.
    split.
    { apply ct_ind_left with (P := fun x => x ⨾ _); auto with hahn;
        ins; rewrite seqA; eauto with hahn.
      rewrite ct_begin, H, ?seqA; eauto with hahn. }
    apply ct_ind_right with (P := fun x => _ ⨾ x); auto with hahn;
      ins; rewrite <- seqA; eauto with hahn.
    rewrite ct_end, H, <- ?seqA; eauto with hahn.
  Qed.

  Lemma rt_seq_swap r r' :
    (r ⨾ r') ＊ ⨾ r ≡ r ⨾ (r' ⨾ r) ＊.
  Proof.
    by rewrite !rtE; autorewrite with hahn hahn_full; rewrite ct_seq_swap.
  Qed.

  Lemma ct_rotl r r' :
    (r ⨾ r')⁺ ≡ r ⨾ (r' ⨾ r) ＊ ⨾ r'.
  Proof.
    by rewrite rt_seq_swap, ct_begin, seqA.
  Qed.

  Lemma crt_double r :
    r ＊ ≡ r ^? ⨾ (r ⨾ r) ＊.
  Proof.
    split; [|by eauto 7 using inclusion_seq_trans, inclusion_rt_rt2 with hahn].
    apply inclusion_rt_ind_left; eauto with hahn.
    rewrite !crE; autorewrite with hahn hahn_full.
    rewrite <- seqA, <- ct_begin; eauto with hahn.
  Qed.

End ExtraPropertiesClos.

(******************************************************************************)
(** Properties of [eqv_rel] *)
(******************************************************************************)

Lemma eqv_empty A : ⦗@set_empty A⦘ ≡ ∅₂.
Proof.
  autounfold with unfolderDb; intuition; desf; eauto.
Qed.
  
Lemma seq_eqv_r A (r : relation A) dom :
  r ⨾ ⦗dom⦘ ≡ (fun x y => r x y /\ dom y).
Proof.
  autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma seq_eqv_l A (r : relation A) dom :
  ⦗dom⦘ ⨾ r ≡ (fun x y => dom x /\ r x y).
Proof.
  autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_l A (r : relation A) dom :
  ⦗dom⦘ ⨾ r ⊆ r.
Proof.
  autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_r A (r : relation A) dom :
  r ⨾ ⦗dom⦘ ⊆ r.
Proof.
  autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma seq_eqv_lr A (r : relation A) dom1 dom2 :
  ⦗dom1⦘ ⨾ r ⨾ ⦗dom2⦘ ≡ (fun x y : A => dom1 x /\ r x y /\ dom2 y).
Proof.
  autounfold with unfolderDb; intuition; desf; eauto 10.
Qed.

Lemma seq_eqv_inter_ll A S (r r' : relation A) :
  (⦗S⦘ ⨾ r) ∩ r' ≡ ⦗S⦘ ⨾ r ∩ r'.
Proof. autounfold with unfolderDb; intuition; desf; eauto. Qed.

Lemma seq_eqv_inter_lr A S (r r' : relation A) :
  (r ⨾ ⦗S⦘) ∩ r' ≡ r ∩ r' ⨾ ⦗S⦘.
Proof. autounfold with unfolderDb; intuition; desf; eauto. Qed.

Lemma seq_eqv_minus_lr A (s : A -> Prop) (r r' : relation A) :
  (r ⨾ ⦗s⦘) \ r' ≡ (r \ r') ⨾ ⦗s⦘.
Proof. autounfold with unfolderDb; intuition; desf; eauto. Qed.

Lemma seq_eqv_minus_ll A (s : A -> Prop) (r r' : relation A) :
  (⦗s⦘ ⨾ r) \ r' ≡ ⦗s⦘ ⨾ (r \ r').
Proof. autounfold with unfolderDb; intuition; desf; eauto. Qed.

#[export] 
Hint Rewrite eqv_empty : hahn.

(******************************************************************************)
(** Properties of restrictions *)
(******************************************************************************)

Lemma same_relation_restr A (f : A -> Prop) r r' :
   (forall x (CONDx: f x) y (CONDy: f y), r x y <-> r' x y) ->
   (restr_rel f r ≡ restr_rel f r').
Proof. u; firstorder. Qed.

Lemma restr_restr A (d d' : A -> Prop) r :
  restr_rel d (restr_rel d' r) ≡ restr_rel (d' ∩₁ d) r. 
Proof. u. Qed.

Lemma restrC A (d d': A -> Prop) r :
  restr_rel d (restr_rel d' r) ≡ restr_rel d' (restr_rel d r). 
Proof. u. Qed.

Lemma restr_relE A (d : A -> Prop) r :
  restr_rel d r ≡ <| d |> ;; r ;; <| d |>. 
Proof. rewrite seq_eqv_lr; u. Qed. 

Lemma restr_relEE A (d : A -> Prop) r : restr_rel d r ≡ r ∩ d × d.
Proof. u. Qed.

Lemma restr_union A (f : A -> Prop) r r' :
  restr_rel f (r ∪ r') ≡ restr_rel f r ∪ restr_rel f r'.
Proof. u. Qed.

Lemma restr_inter A (f : A -> Prop) r r' :
  restr_rel f (r ∩ r') ≡ restr_rel f r ∩ restr_rel f r'.
Proof. u. Qed.

Lemma restr_seq A (f : A -> Prop) r r' :
  restr_rel f r ⨾ restr_rel f r' ⊆ restr_rel f (r ⨾ r').
Proof. u. Qed.

Lemma restr_minus A (f : A -> Prop) r r' :
  restr_rel f (r \ r') ≡ restr_rel f r \ restr_rel f r'.
Proof. u. Qed.

Lemma restr_minus_alt A (f : A -> Prop) r r' :
  restr_rel f (r \ r') ≡ restr_rel f r \ r'.
Proof. u. Qed.

Lemma restr_transp A (f : A -> Prop) r :
  restr_rel f r⁻¹ ≡ (restr_rel f r)⁻¹.
Proof. u. Qed.

Lemma restr_eqv A (s s' : A -> Prop) :
  restr_rel s ⦗s'⦘ ≡ ⦗s ∩₁ s'⦘.
Proof. u. Qed.

Lemma restr_bunion A B (f : B -> Prop) (s: A -> Prop) rr :
  restr_rel f (⋃x ∈ s, rr x) ≡ ⋃x ∈ s, restr_rel f (rr x).
Proof. u. Qed.

Lemma restr_ct A (d: A -> Prop) r :
  (restr_rel d r)⁺ ⊆ restr_rel d r⁺.
Proof. u; induction H; desf; eauto using clos_trans. Qed.

Lemma restr_seq_eqv_l A (f : A -> Prop) d r :
  restr_rel f (⦗d⦘ ⨾ r) ≡ ⦗d⦘ ⨾ restr_rel f r.
Proof. u; eauto 6. Qed.

Lemma restr_seq_eqv_r A (f : A -> Prop) r d :
  restr_rel f (r ⨾ ⦗d⦘) ≡ restr_rel f r ⨾ ⦗d⦘.
Proof. u; eauto 6. Qed.

Lemma restr_set_union A (s s' : A -> Prop) r :
  restr_rel (s ∪₁ s') r ≡
    restr_rel s r ∪ restr_rel s' r ∪ ⦗s⦘ ⨾ r ⨾ ⦗s'⦘ ∪ ⦗s'⦘ ⨾ r ⨾ ⦗s⦘.
Proof. u; eauto 10. Qed.

Lemma restr_set_inter A (s s' : A -> Prop) r :
  restr_rel (s ∩₁ s') r ≡ restr_rel s r ∩ restr_rel s' r.
Proof. u. Qed.

Lemma restr_eq_union A r r' B (f : A -> B) :
  restr_eq_rel f (r ∪ r') ≡ restr_eq_rel f r ∪ restr_eq_rel f r'.
Proof. u. Qed.

Lemma restr_eq_bunion A (s : A -> Prop) B (rr: A -> relation B) C (f : B -> C) :
  restr_eq_rel f (⋃x ∈ s, rr x) ≡ ⋃x ∈ s, restr_eq_rel f (rr x).
Proof. u. Qed.

Lemma restr_eq_elim A (r : relation A) B (f: A -> B) 
      (R: forall x y, r x y -> f x = f y) :
   restr_eq_rel f r ≡ r.
Proof. u. Qed.

Lemma restr_eq_seq_eqv_l A (r : relation A) B (f : A -> B) dom :
  restr_eq_rel f (⦗dom⦘⨾ r) ≡ ⦗dom⦘⨾ restr_eq_rel f r.
Proof. u. Qed.

Lemma restr_eq_seq_eqv_r A (r : relation A) B (f : A -> B) dom :
  restr_eq_rel f (r⨾ ⦗dom⦘) ≡ restr_eq_rel f r⨾ ⦗dom⦘.
Proof. u. Qed.

Lemma restr_full {A} (r : relation A) :
  restr_rel (fun _ : A => True) r ≡ r.
Proof. u. Qed.

(******************************************************************************)
(** Lemmas about [transp] *)
(******************************************************************************)

Section TranspProperties.

  Variable A : Type.
  Implicit Type r : relation A.
  Implicit Type d : A -> Prop.

  Lemma transp_inv r : r⁻¹ ⁻¹ ≡ r.
  Proof. u. Qed.

  Lemma transp_eqv_rel d : ⦗d⦘⁻¹ ≡ ⦗d⦘.
  Proof. u. Qed.

  Lemma transp_cross d d' : (d × d')⁻¹ ≡ (d' × d).
  Proof. u. Qed.

  Lemma transp_union r1 r2 : (r1 ∪ r2)⁻¹ ≡ r1⁻¹ ∪ r2⁻¹.
  Proof. u. Qed.

  Lemma transp_seq r1 r2 : (r1 ⨾ r2)⁻¹ ≡ r2⁻¹ ⨾ r1⁻¹.
  Proof. u. Qed.

  Lemma transp_inter r1 r2 : (r1 ∩ r2)⁻¹ ≡ r1⁻¹ ∩ r2⁻¹.
  Proof. u. Qed.

  Lemma transp_minus r1 r2 : (r1 \ r2)⁻¹ ≡ r1⁻¹ \ r2⁻¹.
  Proof. u. Qed.

  Lemma transp_rt r : (r＊) ⁻¹ ≡ (r⁻¹)＊.
  Proof. u; induction H; vauto. Qed.

  Lemma transp_ct r : (r⁺)⁻¹ ≡ (r⁻¹)⁺.
  Proof. u; induction H; vauto. Qed.

  Lemma transp_cr r : (r^?)⁻¹ ≡ (r⁻¹)^?.
  Proof. u. Qed.

  Lemma transitive_transp r : transitive r -> transitive (r⁻¹).
  Proof. u. Qed.

  Lemma inclusion_transpE r r' : r⁻¹ ⊆ r'⁻¹ -> r ⊆ r'.
  Proof. u. Qed.

  Lemma same_relation_transpE r r' : transp r ≡ transp r' -> r ≡ r'.
  Proof. u. Qed.

End TranspProperties.

#[export] 
Hint Rewrite transp_inv transp_cross transp_eqv_rel : hahn.
#[export] 
Hint Rewrite transp_inv transp_cross transp_eqv_rel transp_union transp_seq 
  transp_inter transp_minus transp_rt transp_ct transp_cr : rel_transp.

Ltac rel_transp := 
  first [apply inclusion_transpE | apply same_relation_transpE ];
    autorewrite with rel_transp.

(******************************************************************************)
(** Properties of [map_rel] *)
(******************************************************************************)

Section PropertiesMapRel.

  Variable A B C : Type.
  Implicit Type f : A -> B.
  Implicit Type d : B -> Prop.

  Lemma map_rel_compose (f : A -> B) (g : B -> C) r :
    (g ∘ f) ↓ r ≡ f ↓ (g ↓ r).
  Proof.
    unfold compose.
    repeat autounfold with unfolderDb.
    ins; splits; ins; splits; desf; eauto 10.
  Qed.

  Lemma map_rel_false f :
    f ↓ ∅₂ ≡ ∅₂.
  Proof. u. Qed.

  Lemma map_rel_cross f d d' :
    f ↓ (d × d') ≡ (f ↓₁ d) × (f ↓₁ d').
  Proof. u. Qed.

  Lemma map_rel_union f r r' :
    f ↓ (r ∪ r') ≡ f ↓ r ∪ f ↓ r'.
  Proof. u. Qed.

  Lemma map_rel_inter f r r' :
    f ↓ (r ∩ r') ≡ f ↓ r ∩ f ↓ r'.
  Proof. u. Qed.

  Lemma map_rel_minus f r r' :
    f ↓ (r \ r') ≡ f ↓ r \ f ↓ r'.
  Proof. u. Qed.

  Lemma map_rel_restr f d r :
    f ↓ (restr_rel d r) ≡ restr_rel (f ↓₁ d) (f ↓ r).
  Proof. u. Qed.

  Lemma map_rel_transp f r :
    f ↓ r⁻¹ ≡ (f ↓ r)⁻¹.
  Proof. u; eauto 8. Qed.

  Lemma map_rel_eqv f d :
    ⦗ f ↓₁ d ⦘ ⊆ f ↓ ⦗ d ⦘.
  Proof. u; eauto 8. Qed.

  Lemma map_rel_seq f r r' :
    (f ↓ r) ⨾ (f ↓ r') ⊆ f ↓ (r ⨾ r').
  Proof. u; eauto. Qed.

  Lemma map_rel_cr f r :
    (f ↓ r)^? ⊆ f ↓ r^?.
  Proof. u; eauto 8. Qed.

  Lemma map_rel_ct f r :
    (f ↓ r)⁺ ⊆ f ↓ r⁺.
  Proof. 
    u. induction H.
    { apply ct_step. eauto. }
    apply ct_ct. eexists. eauto. 
  Qed.

  Lemma map_rel_crt f r :
    (f ↓ r)＊ ⊆ f ↓ r＊.
  Proof.
    by rewrite 
         <- !cr_of_ct,
         <- map_rel_cr,
         <- map_rel_ct.
  Qed.

  Lemma map_rel_irr f r (Irr : irreflexive r):
    irreflexive (f ↓ r).
  Proof. u. Qed.

  Lemma map_rel_acyclic f r (ACYC : acyclic r):
    acyclic (f ↓ r).
  Proof.
    unfold acyclic in *.
    erewrite map_rel_ct.
    by eapply map_rel_irr.
  Qed.

End PropertiesMapRel.

(******************************************************************************)
(** Properties of [pow_rel] *)
(******************************************************************************)

Lemma powE A (r : relation A) n a b :
  (r ^^ n) a b <->
  exists f,
    f 0 = a /\ f n = b /\
    forall i, i < n -> r (f i) (f (S i)).
Proof.
  split.
    generalize b; induction n; ins; unfold seq, eqv_rel in *; desf.
      exists (fun x => b0); splits; ins; lia.
    specialize (IHn _ H); desf.
    exists (fun x => if eq_op x (S n) then b0 else f x); ins; desf; desf.
    splits; ins; desf; ins; desf; try lia; eauto.
    apply IHn1; lia.
  ins; desf; induction n; ins; exists (f n); split; eauto.
Qed.

Lemma pow_0 A (r : relation A) : r^^0 ≡ ⦗fun _ : A => True⦘.
Proof. done. Qed.

Lemma pow_1 A (r : relation A) : r^^1 ≡ r.
Proof. by simpl; rewrite seq_id_l. Qed.

Lemma pow_S_end A (r : relation A) n : r^^(S n) ≡ r^^n ⨾ r.
Proof. done. Qed.

Lemma pow_S_begin A (r : relation A) n : r^^(S n) ≡ r ⨾ r^^n.
Proof.
  induction n; ins; rewrite ?seq_id_l, ?seq_id_r; ins.
  by rewrite IHn at 1; rewrite seqA.
Qed.

Lemma pow_add A (r : relation A) m n : r^^(m + n) ≡ r^^m ⨾ r^^n.
Proof.
  induction m; ins; rewrite ?seq_id_l, ?seq_id_r; ins.
  by rewrite IHm, !seqA, <- pow_S_begin.
Qed.

Lemma pow_seq A n (r: relation A): r^^n ⨾ r ≡ r^^(S n).
Proof. done. Qed.

Lemma pow_nm A (n m : nat) (r : relation A) : r^^n ⨾ r^^m ≡ r^^(n + m).
Proof. symmetry; apply pow_add. Qed.

Lemma pow_rt (n : nat) A (r: relation A) : r^^n ⊆ r＊.
Proof.
  induction n; simpl; auto with hahn.
  rewrite IHn, <- ct_end; auto with hahn.
Qed.

Lemma pow_ct (n : nat) A (r: relation A) (NZ : n <> 0) : r^^n ⊆ r⁺.
Proof.
  by destruct n; ins; rewrite pow_rt, ct_end.
Qed.

Lemma pow_of_transitive (n : nat) A (r: relation A) :
  n <> 0 -> transitive r -> r^^n ⊆ r.
Proof.
  by ins; rewrite pow_ct, ct_of_trans.
Qed.

Lemma pow_of_transitive_cr (n : nat) A (r: relation A) :
  transitive r -> r^^n ⊆ r^?.
Proof.
  by ins; rewrite pow_rt, rt_of_trans.
Qed.

#[export] 
Hint Rewrite pow_1 pow_0 : hahn.
Global Hint Resolve pow_rt : hahn.

(******************************************************************************)
(** Properties of cross product *)
(******************************************************************************)

Section PropertiesCross.

  Variable A : Type.
  Implicit Type s : A -> Prop.

  Lemma cross_false_r s : s × ∅ ≡ ∅₂.
  Proof. u. Qed.

  Lemma cross_false_l s : ∅ × s ≡ ∅₂.
  Proof. u. Qed.

  Lemma cross_union_l s s' s'' : (s ∪₁ s') × s'' ≡ s × s'' ∪ s' × s''.
  Proof. u. Qed.

  Lemma cross_union_r s s' s'' : s × (s' ∪₁ s'') ≡ s × s' ∪ s × s''.
  Proof. u. Qed.

  Lemma cross_inter_l s s' s'' : (s ∩₁ s') × s'' ≡ ⦗s⦘ ⨾ s' × s''.
  Proof. u. Qed.

  Lemma cross_inter_r s s' s'' : s × (s' ∩₁ s'') ≡ s × s' ⨾ ⦗s''⦘.
  Proof. u. Qed.

  Lemma ct_of_cross s s' : (s × s')⁺ ≡ s × s'.
  Proof. u; induction H; desf; eauto. Qed.

  Lemma cross_minus_compl_l s s' s'' : s × s' \ (set_compl s) × s'' ≡ s × s'.
  Proof. u. Qed.

  Lemma cross_minus_compl_r s s' s'' : s × s' \ s'' × (set_compl s') ≡ s × s'.
  Proof. u. Qed.

End PropertiesCross.

#[export] 
Hint Rewrite cross_false_l cross_false_r : hahn.

(******************************************************************************)
(** Properties of [collect_rel] *)
(******************************************************************************)

Section PropertiesCollectRel.

  Variable A B C : Type.
  Implicit Type f : A -> B.
  Implicit Type s : A -> Prop.

  Lemma collect_rel_compose (f : A -> B) (g : B -> C) r :
    (g ∘ f) ↑ r ≡ g ↑ (f ↑ r).
  Proof.
    unfold compose.
    repeat autounfold with unfolderDb.
    ins; splits; ins; splits; desf; eauto 10.
  Qed.

  Lemma collect_rel_empty f : f ↑ ∅₂ ≡ ∅₂.
  Proof. u. Qed.

  Lemma collect_rel_singl f x y : f ↑ singl_rel x y ≡ singl_rel (f x) (f y).
  Proof. u; eauto 8. Qed.

  Lemma collect_rel_cross f s s' :
    f ↑ (s × s') ≡ (f ↑₁ s) × (f ↑₁ s').
  Proof. u; eauto 8. Qed.

  Lemma collect_rel_union f r r' :
    f ↑ (r ∪ r') ≡ f ↑ r ∪ f ↑ r'.
  Proof. u; eauto 8. Qed.

  Lemma collect_rel_inter f r r' :
    f ↑ (r ∩ r') ⊆ (f ↑ r) ∩ (f ↑ r').
  Proof. u; eauto 8. Qed.

  Lemma collect_rel_bunion f (s : C -> Prop) rr :
    f ↑ (⋃x ∈ s, rr x) ≡ ⋃x ∈ s, f ↑ (rr x).
  Proof. u; eauto 8. Qed.

  Lemma collect_rel_minus f r r' :
    f ↑ r \ f ↑ r' ⊆ f ↑ (r \ r').
  Proof. u; eauto 20. Qed.

  Lemma collect_rel_transp f r :
    f ↑ r⁻¹ ≡ (f ↑ r)⁻¹.
  Proof. u; eauto 8. Qed.

  Lemma collect_rel_eqv f s :
    f ↑ ⦗ s ⦘ ≡ ⦗ f ↑₁ s ⦘.
  Proof. u; eauto 8. Qed.

  Lemma collect_rel_seq f r r' :
    f ↑ (r ⨾ r') ⊆ (f ↑ r) ⨾ (f ↑ r').
  Proof. u; eauto 20. Qed.

  Lemma collect_rel_cr f r :
    f ↑ r^? ⊆  (f ↑ r)^?.
  Proof. u; eauto 8. Qed.

  Lemma collect_rel_ct f r :
    f ↑ r⁺ ⊆ (f ↑ r)⁺.
  Proof. 
    u. induction H.
    { apply ct_step. eauto. }
    apply ct_ct. eexists. eauto. 
  Qed.

  Lemma collect_rel_crt f r :
    f ↑ r＊ ⊆ (f ↑ r)＊.
  Proof.
      by rewrite 
         <- !cr_of_ct,
         <- collect_rel_ct,
         <- collect_rel_cr.
  Qed.

  Lemma collect_rel_irr f r (Irr : irreflexive (f ↑ r)):
    irreflexive r.
  Proof. u. eapply Irr. eauto. Qed.

  Lemma collect_rel_acyclic f r (ACYC : acyclic (f ↑ r)):
    acyclic r.
  Proof.
    unfold acyclic in *.
    eapply collect_rel_irr.
    eby erewrite collect_rel_ct.
  Qed.

End PropertiesCollectRel.

#[export] 
Hint Rewrite collect_rel_empty collect_rel_cross
             collect_rel_union collect_rel_bunion : hahn.

(******************************************************************************)
(** ** Properties of symmetry *)
(******************************************************************************)

Section PropertiesSymmetry.

  Variable A : Type.
  Implicit Type r : relation A.
  Implicit Type s : A -> Prop.

  Lemma symmetricE r : symmetric r <-> r ⊆ r⁻¹.
  Proof. u. Qed.

  Lemma symmetricEE r : symmetric r <-> r ≡ r⁻¹.
  Proof. u. Qed.

  Lemma cr_sym r : symmetric r -> symmetric r^?.
  Proof. u. Qed.

  Lemma cs_sym r : symmetric r^⋈.
  Proof. rewrite csE. u. Qed.

  Lemma crs_sym r : symmetric r^⋈?.
  Proof. rewrite crsE. u. Qed.

  Lemma eqv_sym s : symmetric ⦗s⦘.
  Proof. u. Qed.

  Lemma union_sym r r' : symmetric r -> symmetric r' -> symmetric (r ∪ r').
  Proof. u. Qed.

  Lemma inter_sym r r' : symmetric r -> symmetric r' -> symmetric (r ∩ r').
  Proof. u. Qed.

  Lemma minus_sym r r' : symmetric r -> symmetric r' -> symmetric (r \ r').
  Proof. u. Qed.

  Lemma transp_sym r : symmetric r -> symmetric r⁻¹.
  Proof. u. Qed.

  Lemma restr_sym s r : symmetric r -> symmetric (restr_rel s r).
  Proof. u. Qed.

End PropertiesSymmetry.

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

Lemma restr_seq_compl_l A d (r : relation A) : restr_rel d (⦗set_compl d⦘ ;; r) ≡ ∅₂.
Proof. u. Qed.

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
    by rewrite immediateE, inclusion_minus_rel; auto with hahn.
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
    by rewrite immediateE, inclusion_minus_rel; auto with hahn.
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
    by eapply H, clos_trans_mon; eauto; ins; desf.
  destruct (classic (f x)) as [K|K]; eauto.
  assert (M: (fun a b => r a b /\ f a /\ f b) ＊ x x) by vauto.
  generalize K; revert H0 M K; generalize x at 2 3 5; ins.
  apply clos_trans_tn1 in H0; induction H0; eauto 6 using rt_t_trans, t_step.
  destruct (classic (f y)); eauto 6 using clos_refl_trans.
  eapply H1; eauto.
  eapply t_rt_trans, rt_trans; eauto using t_step, clos_trans_in_rt, clos_tn1_trans.
  by eapply clos_refl_trans_mon; eauto; ins; desf.
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
  ins; rewrite H, H0, <- ct_ct; eauto with hahn.
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

Lemma seq_minus_transitive A (r r1 r2 : relation A)
      (TR : transitive r) :
  r1 ⨾ r2 \ r ⊆ (r1 \ r) ⨾  r2 ∪ (r1 ∩ r) ⨾  (r2 \ r).
Proof.
  autounfold with unfolderDb; ins; desf.
  destruct (classic (r x z)); [|eauto].
  right; eexists; splits; try edone; intro; eauto.
Qed.

Lemma add_dom_l A (r: relation A) (s s': A -> Prop)
      (IN: r ⨾ ⦗s⦘ ⊆ ⦗s'⦘ ⨾ r) :
  r ⨾ ⦗s⦘ ≡ ⦗s'⦘ ⨾ r ⨾ ⦗s⦘.
Proof.
  split.
  all: autounfold with unfolderDb in *; ins; desf; eauto.
  edestruct IN; eauto. desf.
  eexists; splits; eauto.
Qed.

Lemma add_dom_r A (r: relation A) (s s': A -> Prop)
      (IN: ⦗s'⦘ ⨾ r ⊆ r ⨾ ⦗s⦘) :
  ⦗s'⦘ ⨾ r ≡ ⦗s'⦘ ⨾ r ⨾ ⦗s⦘.
Proof.
  split.
  all: autounfold with unfolderDb in *; ins; desf; eauto.
  edestruct IN; eauto.
Qed.

Tactic Notation "rotate" int_or_var(i) := do i (
 rewrite <- ?seqA; (apply irreflexive_seqC || apply acyclic_seqC); rewrite ?seqA).
Tactic Notation "rotate" := rotate 1.
