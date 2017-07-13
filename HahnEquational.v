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

Add Parametric Relation (X : Type) : (relation X) (@inclusion X)
 reflexivity proved by (@inclusion_refl _)
 transitivity proved by (@inclusion_trans _)
 as inclusion_rel.

Add Parametric Morphism X : (@inclusion X) with signature
  inclusion --> inclusion ++> Basics.impl as inclusion_mori.
Proof.
  unfold inclusion, Basics.impl; ins; eauto.
Qed.

Add Parametric Morphism X : (@union X) with signature
  inclusion ==> inclusion ==> inclusion as union_mori.
Proof.
  unfold inclusion, union; intuition; eauto.
Qed.

Add Parametric Morphism X : (@inter_rel X) with signature
  inclusion ==> inclusion ==> inclusion as inter_rel_mori.
Proof.
  unfold inclusion, inter_rel; intuition; eauto.
Qed.

Add Parametric Morphism X : (@minus_rel X) with signature
  inclusion ++> inclusion --> inclusion as minus_rel_mori.
Proof.
  unfold inclusion, minus_rel; intuition; eauto.
Qed.

Add Parametric Morphism X : (@seq X) with signature
  inclusion ==> inclusion ==> inclusion as seq_mori.
Proof.
  unfold inclusion, seq; intuition; desf; eauto.
Qed.

Add Parametric Morphism X : (@irreflexive X) with signature
  inclusion --> Basics.impl as irreflexive_mori.
Proof.
  unfold inclusion, irreflexive, Basics.impl; intuition; desf; eauto.
Qed.

Add Parametric Morphism X : (@clos_trans X) with signature
  inclusion ==> inclusion as clos_trans_mori.
Proof.
  unfold inclusion; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl_trans X) with signature
  inclusion ==> inclusion as clos_refl_trans_mori.
Proof.
  unfold inclusion; eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl X) with signature
  inclusion ==> inclusion as clos_refl_mori.
Proof.
  unfold inclusion, clos_refl; intuition; eauto.
Qed.

Add Parametric Morphism X P : (@restr_rel X P) with signature
  inclusion ==> inclusion as restr_rel_mori.
Proof.
  unfold inclusion, restr_rel; intuition; eauto.
Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature
  eq ==> inclusion ==> inclusion as restr_eq_rel_mori.
Proof.
  unfold inclusion, restr_eq_rel; intuition; eauto.
Qed.

Add Parametric Morphism X : (@acyclic X) with signature
  inclusion --> Basics.impl as acyclic_mori.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism X : (@is_total X) with signature
  eq ==> inclusion ==> Basics.impl as is_total_mori.
Proof.
  unfold inclusion, is_total, Basics.impl; ins; desf.
  eapply H0 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism X : (@transp X) with signature
  inclusion ==> inclusion as transp_mori.
Proof.
  unfold inclusion, transp; eauto.
Qed.

Add Parametric Morphism X : (@eqv_rel X) with signature
  @set_subset _ ==> inclusion as eqv_rel_mori.
Proof.
  unfold inclusion, set_subset, eqv_rel; ins; desf; eauto.
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

Add Parametric Relation (X : Type) : (relation X) (@same_relation X)
 reflexivity proved by (@same_relation_refl X)
 symmetry proved by (@same_relation_sym X)
 transitivity proved by (@same_relation_trans X)
 as same_rel.

Add Parametric Morphism X : (@inclusion X) with signature
  same_relation ==> same_relation ==> iff as inclusion_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@union X) with signature
  same_relation ==> same_relation ==> same_relation as union_more.
Proof.
  unfold same_relation, union; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@inter_rel X) with signature
  same_relation ==> same_relation ==> same_relation as inter_rel_more.
Proof.
  unfold same_relation, inter_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@minus_rel X) with signature
  same_relation ==> same_relation ==> same_relation as minus_rel_more.
Proof.
  unfold same_relation, minus_rel; ins; desf; split; red; intuition.
Qed.

Add Parametric Morphism X : (@seq X) with signature
  same_relation ==> same_relation ==> same_relation as seq_more.
Proof.
  unfold same_relation, seq; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@immediate X) with signature
  same_relation ==> same_relation as immediate_more.
Proof.
  ins; rewrite !immediateE; rewrite H; eauto.
Qed.

Add Parametric Morphism X : (@eqv_dom_rel X) with signature
  (@Permutation _) ==> same_relation as eqv_dom_rel_more.
Proof.
  by unfold same_relation, eqv_dom_rel; ins; desf; split; red; ins; desf;
     rewrite H in *.
Qed.

Add Parametric Morphism X P : (@restr_rel X P) with signature
  same_relation ==> same_relation as restr_rel_more.
Proof.
  unfold same_relation, restr_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature
  eq ==> same_relation ==> same_relation as restr_eq_rel_more.
Proof.
  unfold same_relation, restr_eq_rel; intuition; eauto using restr_eq_rel_mori.
Qed.

Add Parametric Morphism X : (@clos_trans X) with signature
  same_relation ==> same_relation as clos_trans_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl_trans X) with signature
  same_relation ==> same_relation as clos_relf_trans_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf;
  eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl X) with signature
  same_relation ==> same_relation as clos_relf_more.
Proof.
  unfold same_relation, clos_refl; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@irreflexive X) with signature
  same_relation ==> iff as irreflexive_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@acyclic X) with signature
  same_relation ==> iff as acyclic_more.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism X : (@transitive X) with signature
  same_relation ==> iff as transitive_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@is_total X) with signature
  eq ==> same_relation ==> iff as is_total_more.
Proof.
  unfold is_total, same_relation; split; ins; eapply H0 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism X : (@transp X) with signature
  same_relation ==> same_relation as transp_more.
Proof.
  unfold same_relation, transp; ins; desf; eauto; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@functional X) with signature
  same_relation ==> Basics.impl as functional_more.
Proof.
  unfold same_relation, inclusion, functional; ins; desf; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@eqv_rel X) with signature
  @set_equiv _ ==> same_relation as eqv_rel_more.
Proof.
  unfold same_relation, inclusion, set_equiv, eqv_rel; firstorder. 
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

  Lemma seq_Union_l rr r : Union rr ⨾ r ≡ Union (fun n => rr n ⨾ r).
  Proof.
    unfold seq, Union; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_Union_r r rr : r ⨾ Union rr ≡ Union (fun n => r ⨾ rr n).
  Proof.
    unfold seq, Union; split; red; ins; desf; eauto.
  Qed.

  Lemma minus_union_l r1 r2 r :
    (r1 ∪ r2) \ r ≡ minus_rel r1 r ∪ minus_rel r2 r.
  Proof.
    unfold minus_rel, union; split; red; ins; desf; eauto.
  Qed.

  Lemma minusK r : r \ r ≡ ∅₂.
  Proof.
    unfold minus_rel; split; red; intuition.
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

End PropertiesSeqUnion.

Hint Rewrite seq_false_l seq_false_r union_false_l union_false_r unionK : rel.
Hint Rewrite seq_id_l seq_id_r seq_eqvK : rel.

Hint Rewrite seq_Union_l seq_Union_r seq_union_l seq_union_r : rel_full.




(******************************************************************************)
(** Basic properties of reflexive and transitive closures *)
(******************************************************************************)

Section PropertiesClos.

  Variable A : Type.
  Implicit Types r : relation A.

  Lemma rtE r : r ^* ≡ ⦗fun _ => True⦘ ∪ r⁺.
  Proof.
    unfold eqv_rel, union, same_relation, inclusion.
    split; ins; rewrite clos_refl_transE in *; tauto.
  Qed.

  Lemma crE r : r ^? ≡ ⦗fun _ => True⦘ ∪ r.
  Proof.
    unfold eqv_rel, union, same_relation, inclusion, clos_refl.
    split; ins; tauto.
  Qed.

  Lemma rtEE r : r ^* ≡ Union (fun n => r ^^ n).
  Proof.
    split; ins; desc.
      unfold eqv_rel, Union, same_relation, inclusion; ins.
      induction H using clos_refl_trans_ind_left; desc.
        by exists 0.
      by exists (S a); vauto.
    apply inclusion_Union_l.
    induction n; ins; [|rewrite IHn];
      unfold eqv_rel, seq; red; ins; desf; vauto.
  Qed.

  Lemma ct_begin r : r⁺ ≡ r ⨾ r ^*.
  Proof.
    unfold seq; split; red; ins; desf; rewrite t_step_rt in *; eauto.
  Qed.

  Lemma ct_end r : r⁺ ≡ r ^* ⨾ r.
  Proof.
    unfold seq; split; red; ins; desf; rewrite t_rt_step in *; eauto.
  Qed.

  Lemma ctEE r : r⁺ ≡ Union (fun n => r ^^ (S n)).
  Proof.
    by rewrite ct_end, rtEE, seq_Union_l.
  Qed.

  Lemma rt_begin r :
    r ^* ≡ ⦗fun _ => True⦘ ∪ r ⨾ r ^*.
  Proof.
    rewrite <- ct_begin, <- rtE; vauto.
  Qed.

  Lemma rt_end r :
    r ^* ≡ ⦗fun _ => True⦘ ∪ r ^* ⨾ r.
  Proof.
    rewrite <- ct_end, <- rtE; vauto.
  Qed.

  Lemma ct_of_trans r (T: transitive r) : r⁺ ≡ r.
  Proof.
    split; eauto with rel.
  Qed.

  Lemma rt_of_trans r (T: transitive r) : r ^* ≡ r ^?.
  Proof.
    rewrite rtE, crE, ct_of_trans; vauto.
  Qed.

  Lemma cr_ct r : r ^? ⨾ r⁺ ≡ r⁺.
  Proof.
    unfold seq, clos_refl; split; red; ins; desf; eauto using t_trans, t_step.
  Qed.

  Lemma cr_rt r : r ^? ⨾ r ^* ≡ r ^*.
  Proof.
    unfold seq, clos_refl; split; red; ins; desf; eauto using rt_trans, rt_step.
  Qed.

  Lemma ct_rt r : r⁺ ⨾ r ^* ≡ r⁺.
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

  Lemma rt_rt r : r ^* ⨾ r ^* ≡ r ^*.
  Proof.
    unfold seq; split; red; ins; desf; eauto using rt_trans, rt_refl.
  Qed.

  Lemma rt_ct r : r ^* ⨾ r⁺ ≡ r⁺.
  Proof.
    unfold seq; split; red; ins; desf; eauto using rt_t_trans, rt_refl.
  Qed.

  Lemma rt_cr r : r ^* ⨾ r ^? ≡ r ^*.
  Proof.
    unfold seq, clos_refl; split; red; ins; desf; eauto using rt_trans, rt_step.
  Qed.

  Lemma cr_of_ct r : (r⁺) ^? ≡ r ^*.
  Proof.
    by rewrite rt_begin, ct_begin, crE.
  Qed.

  Lemma cr_of_cr r : (r ^?) ^? ≡ r ^?.
  Proof.
    by rewrite !crE, <- unionA, unionK.
  Qed.

  Lemma cr_of_rt r : (r ^*) ^? ≡ r ^*.
  Proof.
    by rewrite rtE, <- crE, cr_of_cr.
  Qed.

  Lemma ct_of_ct r: (r⁺)⁺ ≡ r⁺.
  Proof.
    split; eauto with rel.
  Qed.

  Lemma ct_of_cr r: (r ^?)⁺ ≡ r ^*.
  Proof.
    split; eauto with rel.
    apply inclusion_rt_ind_left; vauto.
    rewrite ct_begin at 2; eauto with rel.
  Qed.

  Lemma ct_of_rt r: (r ^*)⁺ ≡ r ^*.
  Proof.
    split; eauto with rel.
  Qed.

  Lemma rt_of_ct r : (r⁺) ^* ≡ r ^*.
  Proof.
    split; eauto using inclusion_rt_rt2 with rel.
  Qed.

  Lemma rt_of_cr r : (r ^?) ^* ≡ r ^*.
  Proof.
    split; eauto using inclusion_rt_rt2 with rel.
  Qed.

  Lemma rt_of_rt r : (r ^*) ^* ≡ r ^*.
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

  Lemma seq_rtE_r r r' : r ⨾ r' ^* ≡ r ∪ (r ⨾ r') ⨾ r' ^*.
  Proof.
    by rewrite rt_begin at 1; rewrite ?seq_union_r, ?seq_id_r, ?seqA.
  Qed.

  Lemma seq_rtE_l r r' : r' ^* ⨾ r ≡ r ∪ (r' ^* ⨾ r' ⨾ r).
  Proof.
    by rewrite rt_end at 1; rewrite ?seq_union_l, ?seq_id_l, ?seqA.
  Qed.

End PropertiesClos.

Hint Rewrite cr_of_ct cr_of_cr cr_of_rt
  ct_of_ct ct_of_cr ct_of_rt
  rt_of_ct rt_of_cr rt_of_rt : rel.

Definition good_ctx A (P: relation A -> relation A) :=
  << MON: Morphisms.Proper (inclusion ==> inclusion) P >> /\
  << CUN: forall (rr : nat -> relation A), P (Union rr) ⊆ Union (fun n => P (rr n)) >>.

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
    rewrite CUN, CUN0; apply inclusion_union_l; apply inclusion_Union_l; vauto.
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
    P ( r ^* ) ⊆ r'.
  Proof.
    ins; cdes G; rewrite (proj1 (rtEE _)).
    etransitivity; [eapply CUN|apply inclusion_Union_l]; ins.
    induction n; ins; rewrite (proj1 (seq_pow_l _ _)); eauto.
  Qed.

  Lemma rt_ind_right P (G: good_ctx P) r r' :
    P ⦗fun _ => True⦘ ⊆ r' ->
    (forall k, P k ⊆ r' -> P (k ⨾ r) ⊆ r') ->
    P ( r ^* ) ⊆ r'.
  Proof.
    ins; cdes G; rewrite (proj1 (rtEE _)).
    etransitivity; [eapply CUN|apply inclusion_Union_l]; ins.
    induction n; ins; eauto.
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
    induction n; ins; eauto.
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
    (r ⨾ r') ^* ⨾ r ≡ r ⨾ (r' ⨾ r) ^*.
  Proof.
    by rewrite !rtE; autorewrite with rel rel_full; rewrite ct_seq_swap.
  Qed.

  Lemma ct_rotl r r' :
    (r ⨾ r')⁺ ≡ r ⨾ (r' ⨾ r) ^* ⨾ r'.
  Proof.
    by rewrite rt_seq_swap, ct_begin, seqA.
  Qed.

  Lemma crt_double r :
    r ^* ≡ r ^? ⨾ (r ⨾ r) ^*.
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


(******************************************************************************)
(** Properties of restrictions *)
(******************************************************************************)

Lemma same_relation_restr X (f : X -> Prop) r r' :
   (forall x (CONDx: f x) y (CONDy: f y), r x y <-> r' x y) ->
   (restr_rel f r ≡ restr_rel f r').
Proof.
  unfold restr_rel; split; red; ins; desf; rewrite H in *; eauto.
Qed.

Lemma restr_union X (f : X -> Prop) r r' :
  restr_rel f (r ∪ r') ≡ restr_rel f r ∪ restr_rel f r'.
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
Qed.

Lemma union_restr X (f : X -> Prop) r r' :
  restr_rel f r ∪ restr_rel f r' ≡ restr_rel f (r ∪ r').
Proof.
  symmetry; apply restr_union.
Qed.

Lemma ct_restr X (f : X -> Prop) r (UC: upward_closed r f) :
  (restr_rel f r)⁺ ≡ restr_rel f (r⁺).
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
    split; [|by apply clos_trans_restrD in H].
    by eapply clos_trans_mon; eauto; unfold restr_rel; ins; desf.
  clear H0; apply clos_trans_tn1 in H.
  induction H; eauto 10 using clos_trans.
Qed.

Lemma restr_eq_union:
  forall (X : Type) (r r' : relation X) (B : Type) (f : X -> B),
  restr_eq_rel f (r ∪ r') ≡
  restr_eq_rel f r ∪ restr_eq_rel f r'.
Proof.
  unfold restr_eq_rel, union, same_relation, inclusion; intuition.
Qed.

Lemma restr_eq_elim :
  forall X (r : relation X) B (f: X -> B)
         (R: forall x y, r x y -> f x = f y),
   restr_eq_rel f r ≡ r.
Proof.
  unfold restr_eq_rel; split; red; ins; intuition.
Qed.

Lemma restr_eq_seq_eqv_rel X (r : relation X) (B : Type) (f : X -> B) dom :
  restr_eq_rel f (r⨾ ⦗dom⦘) ≡ restr_eq_rel f r⨾ ⦗dom⦘.
Proof.
  ins; rewrite !seq_eqv_r; unfold restr_eq_rel.
  split; red; ins; desf.
Qed.


(******************************************************************************)
(** Lemmas about [transp] *)
(******************************************************************************)

Lemma transp_inv  X (r : relation X) :
  r⁻¹ ⁻¹ ≡ r.
Proof.
  unfold transp; split; red; intuition.
Qed.

Lemma transp_eqv_rel  X (dom: X -> Prop) : 
  transp ⦗dom⦘ ≡ ⦗dom⦘.
Proof.
  unfold eqv_rel, transp; split; red; ins; desf.
Qed.

Lemma transp_union  X (r1 r2 : relation X) :
  (r1 ∪ r2)⁻¹ ≡ r1⁻¹ ∪ r2⁻¹.
Proof.
  unfold transp, union; split; red; intuition.
Qed.

Lemma transp_seq  X (r1 r2 : relation X) :
  (r1 ⨾ r2)⁻¹ ≡ r2⁻¹ ⨾ r1⁻¹.
Proof.
  unfold transp, seq; split; red; ins; desf; eauto.
Qed.

Lemma transp_inter  X (r1 r2 : relation X) :
  (r1 ∩ r2)⁻¹ ≡ r1⁻¹ ∩ r2⁻¹.
Proof.
  unfold transp, inter_rel; split; red; intuition.
Qed.

Lemma transp_minus  X (r1 r2 : relation X) :
  (r1 \ r2)⁻¹ ≡ r1⁻¹ \ r2⁻¹.
Proof.
  unfold transp, minus_rel; split; red; intuition.
Qed.

Lemma transp_rt  X (r : relation X) :
  (r ^*) ⁻¹ ≡ (r⁻¹) ^*.
Proof.
  unfold transp, seq; split; red; ins; induction H; vauto.
Qed.

Lemma transp_ct  X (r : relation X) :
  (r⁺)⁻¹ ≡ (r⁻¹)⁺.
Proof.
  unfold transp, seq; split; red; ins; induction H; vauto.
Qed.

Lemma transp_cr  X (r : relation X) :
  (r^?)⁻¹ ≡ (r⁻¹)^?.
Proof.
  unfold transp, clos_refl; split; red; intuition.
Qed.

Lemma transitive_transp X (r : relation X) :
  transitive r -> transitive (r⁻¹).
Proof.
  unfold transp, transitive; eauto.
Qed.

Lemma inclusion_transpE A (r r': relation A) :
  r⁻¹ ⊆ r'⁻¹ -> r ⊆ r'.
Proof.
  by unfold transp, inclusion; intuition.
Qed.

Hint Rewrite transp_inv transp_eqv_rel: rel.


(** Misc properties *)
(******************************************************************************)


Lemma acyclic_mon X (r r' : relation X) :
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
  forall X (R : relation X) (I: irreflexive R)
         (T: transitive R) L (ND: NoDup L) a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    (immediate R)⁺ a b.
Proof.
  intros until 3; induction ND; ins; vauto.
  destruct (classic (R a x /\ R x b)) as [|N]; desf;
    [apply t_trans with x|]; eapply IHND; ins;
  forward (by eapply (D c); eauto) as K; desf; exfalso; eauto.
Qed.

Lemma ct_imm1 :
  forall X (R : relation X) (I: irreflexive R) (T: transitive R)
       acts (FIN : dom_rel R ⊆₁ (fun x => In x acts)),
    R ≡ (immediate R)⁺.
Proof.
  split; cycle 1.
    by rewrite immediateE, inclusion_minus_rel; auto with rel.
  assert (M: forall x y, R x y -> In x (undup acts)).
    by ins; eapply in_undup_iff, FIN; vauto.
  red; ins; eapply clos_trans_imm; eauto.
Qed.

Lemma ct_imm2 :
  forall X (R : relation X) (I: irreflexive R) (T: transitive R)
       acts (FIN : codom_rel R ⊆₁ (fun x => In x acts)),
    R ≡ (immediate R)⁺.
Proof.
  split; cycle 1.
    by rewrite immediateE, inclusion_minus_rel; auto with rel.
  assert (M: forall x y, R x y -> In y (undup acts)).
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
      (D: forall a b (R: r a b), In b dom) a b :
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
  forward (by eapply D'; eauto) as X; apply in_split in X; desf.
  rewrite app_length in *; ins; rewrite <- plus_n_Sm, <- app_length in *; desf.
  apply t_trans with c; eapply IHn with (dom := l1 ++ l2); ins;
  forward (by eapply (D' c0); eauto);
  rewrite !in_app_iff; ins; desf; eauto; exfalso; eauto.
Qed.

Lemma clos_trans_imm2 :
  forall X (R : relation X) (I: irreflexive R)
         (T: transitive R) L a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    (immediate R)⁺ a b.
Proof.
  ins; eapply clos_trans_imm with (L := undup L); ins;
  try rewrite in_undup_iff; eauto using nodup_undup.
Qed.


Lemma total_immediate_unique:
  forall X (r: X -> X -> Prop) (P: X -> Prop)
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

Lemma acyclic_case_split A (R : relation A) f :
  acyclic R <->
  acyclic (restr_rel f R) /\ (forall x (NEG: ~ f x) (CYC: R⁺ x x), False).
Proof.
  unfold restr_rel; repeat split; repeat red; ins; desc; eauto.
    by eapply H, clos_trans_mon; eauto; instantiate; ins; desf.
  destruct (classic (f x)) as [X|X]; eauto.
  assert (M: (fun a b => R a b /\ f a /\ f b) ^* x x) by vauto.
  generalize X; revert H0 M X; generalize x at 2 3 5; ins.
  apply clos_trans_tn1 in H0; induction H0; eauto 6 using rt_t_trans, t_step.
  destruct (classic (f y)); eauto 6 using clos_refl_trans.
  eapply H1; eauto.
  eapply t_rt_trans, rt_trans; eauto using t_step, clos_trans_in_rt, clos_tn1_trans.
  by eapply clos_refl_trans_mon; eauto; instantiate; ins; desf.
Qed.

Lemma seqA2 X (r r' r'' : relation X) x y :
  ((r⨾ r')⨾ r'') x y <-> (r⨾ r'⨾ r'') x y.
Proof.
  unfold seq; split; ins; desf; eauto 8.
Qed.

Lemma inclusion_t_r_t A (r r' r'': relation A) :
  r ⊆ r'' ->
  r' ⊆ r'' ^* ->
  r⁺ ⨾ r' ⊆ r''⁺.
Proof.
  by ins; rewrite H, H0, ct_rt.
Qed.

Lemma inclusion_r_t_t A (r r' r'': relation A) :
  r ⊆ r'' ^* ->
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

Lemma clos_trans_union_ct A (r r' : relation A) :
  (r⁺ ∪ r')⁺ ≡ (r ∪ r')⁺.
Proof.
  split; eauto 8 with rel.
Qed.

Lemma inclusion_ct_seq_eqv_l A dom (r : relation A) :
  (⦗dom⦘ ⨾ r)⁺ ⊆ ⦗dom⦘ ⨾ r⁺.
Proof.
  by rewrite ct_begin, seqA, inclusion_seq_eqv_l with (r:=r), <- ct_begin.
Qed.


