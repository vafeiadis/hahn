Require Import HahnBase HahnSets HahnRelationsBasic HahnEquational.
Require Import HahnRewrite.
Require Import Setoid.
Set Implicit Arguments.

(** * Calculating the (co)domain of a relation *)

Section Domains.

Variable A B : Type.

Section Definitions.
  Variable r : relation A.
  Variable d : A -> Prop.
  Variables f g : A -> B.

  Definition doma := forall x y (REL: r x y), d x.
  Definition domb := forall x y (REL: r x y), d y.
  Definition eq_dom := forall x (DX: d x), f x = g x. 

  Definition dom_cond d := (fun e => dom_rel (r ⨾ ⦗ eq e ⦘) ⊆₁ d).
End Definitions.

Section Lemmas.

  Variables r r' : relation A.
  Variables f g : A -> B.
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

  Lemma minus_doma : doma r d -> doma (r \ r') d.
  Proof. unfold doma, minus_rel; ins; desf; eauto. Qed.

  Lemma minus_domb : domb r d -> domb (r \ r') d.
  Proof. unfold domb, minus_rel; ins; desf; eauto. Qed.

  Lemma doma_inter_r : doma r (d ∩₁ d') <-> doma r d /\ doma r d'.
  Proof. firstorder.  Qed.

  Lemma domb_inter_r : domb r (d ∩₁ d') <-> domb r d /\ domb r d'.
  Proof. firstorder.  Qed.

  Lemma restr_doma : doma (restr_rel d r) d.
  Proof. firstorder. Qed. 

  Lemma restr_domb : domb (restr_rel d r) d.
  Proof. firstorder. Qed. 

  Lemma restr_doma_mon : doma r d -> doma (restr_rel d' r) d.
  Proof. firstorder. Qed. 

  Lemma restr_domb_mon : domb r d -> domb (restr_rel d' r) d.
  Proof. firstorder. Qed. 

  Lemma dom_empty : dom_rel (A:=A) ∅₂ ≡₁ ∅.
  Proof. unfolder; split; ins; desf. Qed. 

  Lemma codom_empty : codom_rel (A:=A) ∅₂ ≡₁ ∅.
  Proof. unfolder; split; ins; desf. Qed. 

  Lemma codom_seq : codom_rel (r ⨾ r') ⊆₁ codom_rel r'.
  Proof. unfold codom_rel, seq, set_subset.
         ins; desf; eauto. Qed.

  Lemma dom_union : dom_rel (r ∪ r') ≡₁ dom_rel r ∪₁ dom_rel r'.
  Proof. unfold dom_rel, union, set_union, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma codom_union : codom_rel (r ∪ r') ≡₁ codom_rel r ∪₁ codom_rel r'.
  Proof. unfold codom_rel, union, set_union, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma dom_eqv : dom_rel ⦗d⦘ ≡₁ d.
  Proof. unfold dom_rel, eqv_rel, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma codom_eqv : codom_rel ⦗d⦘ ≡₁ d.
  Proof. unfold codom_rel, eqv_rel, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma dom_eqv1 : dom_rel (⦗d⦘ ⨾ r) ≡₁ d ∩₁ dom_rel r.
  Proof. unfold dom_rel, eqv_rel, seq, set_inter, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma codom_eqv1 : codom_rel (r ⨾ ⦗d⦘) ≡₁ codom_rel r ∩₁ d.
  Proof. unfold codom_rel, eqv_rel, seq, set_inter, set_equiv, set_subset.
         split; ins; desf; eauto. Qed.

  Lemma dom_cross (N: ~ d' ≡₁ ∅): dom_rel (d × d') ≡₁ d.
  Proof. apply set_nonemptyE in N; unfold dom_rel, cross_rel, set_equiv, set_subset; 
         split; ins; desf; eauto. Qed.

  Lemma codom_cross (N: ~ d ≡₁ ∅): codom_rel (d × d') ≡₁ d'.
  Proof. apply set_nonemptyE in N; unfold codom_rel, cross_rel, set_equiv, set_subset; 
         split; ins; desf; eauto. Qed.

  Lemma transp_doma : domb r d -> doma (transp r) d.
  Proof. unfold doma, domb, transp; eauto. Qed.

  Lemma transp_domb : doma r d -> domb (transp r) d.
  Proof. unfold doma, domb, transp; eauto. Qed.

  Lemma cross_doma : doma (d × d') d.
  Proof. unfold doma, cross_rel; ins; desf. Qed.

  Lemma cross_domb : domb (d × d') d'.
  Proof. unfold domb, cross_rel; ins; desf. Qed.

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

  Lemma doma_rewrite : doma r d -> r ⊆ ⦗d⦘ ⨾ r. 
  Proof. firstorder. Qed.

  Lemma domb_rewrite : domb r d -> r ⊆ r ⨾ ⦗d⦘. 
  Proof. firstorder. Qed.

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

  Lemma domab_helper2 : 
    r ⊆ d × d' <-> doma r d /\ domb r d'.
  Proof.
    unfold doma, domb, cross_rel, inclusion; intuition; firstorder. 
  Qed.

  Lemma dom_to_doma : r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ -> doma r d.
  Proof.
    intro H; unfold doma; ins.
    hahn_rewrite H in REL; revert REL; basic_solver.
  Qed.

  Lemma dom_to_domb : r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ -> domb r d'.
  Proof.
    intro H; unfold domb; ins.
    hahn_rewrite H in REL; revert REL; basic_solver.
  Qed.

  Lemma dom_l : r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ -> r ≡ ⦗d⦘ ⨾ r.
  Proof.
    unfolder; firstorder.
  Qed.

  Lemma dom_r : r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ -> r ≡ r ⨾ ⦗d'⦘.
  Proof.
    unfolder; firstorder.
  Qed.

  Lemma dom_helper_1 : r ⊆ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘ <-> r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘.
  Proof.
    unfolder; firstorder.
  Qed.

  Lemma dom_helper_2 : r ⊆ ⦗d⦘ ⨾ (fun _ _ => True) ⨾ ⦗d'⦘ <-> r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘.
  Proof.
    unfolder; firstorder.
  Qed.

  Lemma dom_helper_3 : r ⊆ d × d' <-> r ≡ ⦗d⦘ ⨾ r ⨾ ⦗d'⦘.
  Proof.
    unfolder; firstorder.
  Qed.

  Lemma step_dom 
        (E: r ⊆ (⦗d⦘ ∪ ⦗d'⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗d'⦘))
        dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
        de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗d'⦘)
        ed (ED: ed = ⦗d'⦘ ⨾ r ⨾ ⦗d⦘)
        ee (EE: ee = ⦗d'⦘ ⨾ r ⨾ ⦗d'⦘) :
    r ⊆ dd ∪ de ∪ ed ∪ ee.
  Proof.
    rewrite E; subst; basic_solver 8.
  Qed.

  Lemma path_dom
        (E1: r ⊆ (⦗d⦘ ∪ ⦗d'⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗d'⦘))
        (E2: ⦗d⦘ ⨾ ⦗d'⦘ ⊆ ∅₂)
        dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
        de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗d'⦘)
        ed (ED: ed = ⦗d'⦘ ⨾ r ⨾ ⦗d⦘)
        ee (EE: ee = ⦗d'⦘ ⨾ r ⨾ ⦗d'⦘) : 
    r⁺ ⊆ (dd⁺ ∪ (dd＊ ⨾ de ⨾ ee＊ ⨾ ed)⁺ ⨾ dd＊ ) ∪
       (ee⁺ ∪ (ee＊ ⨾ ed ⨾ dd＊ ⨾ de)⁺ ⨾ ee＊ ) ∪
       (ee＊ ⨾ ed ⨾ dd＊ ⨾ de)＊ ⨾ ee＊ ⨾ ed ⨾ dd＊ ∪
       (dd＊ ⨾ de ⨾ ee＊ ⨾ ed)＊ ⨾ dd＊ ⨾ de ⨾ ee＊.
  Proof. 
    apply inclusion_t_ind_right.
    { rewrite step_dom at 1; try eassumption.
      repeat apply inclusion_union_l; rewrite ?seqA.
      1,4: sin_rewrite !ct_end.
      all: try (repeat (apply inclusion_union_r; constructor); basic_solver 14). }
    rewrite step_dom at 1; try eassumption.
     relsf.
    assert (E2': ⦗d'⦘ ⨾ ⦗d⦘ ⊆ (fun _ _ : A => False)).
    { by rewrite seq_eqvC in E2. }

    assert (X17: ed ⨾ ed ⊆ ∅₂).
    { rewrite ?DD, ?ED, ?DE, ?EE; generalize E2; basic_solver. }
    assert (X18: ed ⨾ ee ⊆ ∅₂).
    { rewrite ?DD, ?ED, ?DE, ?EE; generalize E2; basic_solver. }
    assert (X19: de ⨾ dd ⊆ ∅₂).
    { rewrite ?DD, ?ED, ?DE, ?EE; generalize E2; basic_solver. }
    assert (X20: de ⨾ de ⊆ ∅₂).
    { by rewrite ?DD, ?ED, ?DE, ?EE; generalize E2; basic_solver. }
    assert (X1: dd ＊ ⨾ ed ⊆ ed).
    { by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X2: dd ＊ ⨾ dd ⊆ dd＊ ).
    {  by rewrite rt_end at 2; relsf. }
    assert (X3: dd ＊ ⨾ ee ⊆ ee).
    {  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X4: ee ＊ ⨾ de ⊆ de).
    {  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X5: ee ＊ ⨾ ee ⊆ ee＊ ).
    {  by rewrite rt_end at 2; relsf. }
    assert (X6: ee ＊ ⨾ dd ⊆ dd).
    {  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
         try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X7: dd ⁺ ⨾ dd ⊆ dd⁺).
    { by rewrite ct_end at 2; rewrite inclusion_t_rt. }
    assert (X8: dd ⁺ ⨾ ed ⊆ ∅₂).
    { by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X9: dd ⁺ ⨾ ee ⊆ ∅₂).
    { by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X10: (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed) ⁺ ⨾ ed ⊆ ∅₂).
    { by rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X11: (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed) ⁺ ⨾ ee ⊆ ∅₂).
    { by rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA;
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X12: ee ⁺ ⨾ dd ⊆ ∅₂).
    { by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X13: ee ⁺ ⨾ de ⊆ ∅₂).
    { by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X14: ee ⁺ ⨾ ee ⊆ ee⁺).
    { by rewrite ct_end at 2; rewrite inclusion_t_rt. }
    assert (X15: (ee ＊ ⨾ ed ⨾ dd ＊ ⨾ de) ⁺ ⨾ dd ⊆ ∅₂).
    { by rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }
    assert (X16: (ee ＊ ⨾ ed ⨾ dd ＊ ⨾ de) ⁺ ⨾ de ⊆ ∅₂).
    { by rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
        try sin_rewrite E2; try sin_rewrite E2'; relsf. }

    repeat apply inclusion_union_l; rewrite ?seqA.
    all: rewrite ?X1, ?X2, ?X3, ?X4, ?X5, ?X6, ?X7, ?X8, ?X9, ?X10,
         ?X11, ?X12, ?X13, ?X14, ?X15, ?X16, ?X17, ?X18, ?X19, ?X20.
    all: rels.
    all: try (repeat (apply inclusion_union_r; constructor); basic_solver 5).
    all: try (repeat (apply inclusion_union_r; constructor); basic_solver 20).
  Qed.

  Lemma path_dom_same
        (E1: r ⊆ (⦗d⦘ ∪ ⦗d'⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗d'⦘))
        (E2: ⦗d⦘ ⨾ ⦗d'⦘ ⊆ ∅₂)
        dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
        de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗d'⦘)
        ed (ED: ed = ⦗d'⦘ ⨾ r ⨾ ⦗d⦘)
        ee (EE: ee = ⦗d'⦘ ⨾ r ⨾ ⦗d'⦘) : 
    ⦗d⦘ ⨾ r⁺ ⨾ ⦗d⦘ ⊆ dd⁺ ∪ (dd＊ ⨾ de ⨾ ee＊ ⨾ ed)⁺ ⨾ dd＊.
  Proof.
    rewrite path_dom; try edone.
    relsf; repeat apply inclusion_union_l; rewrite ?seqA.
    all: try by rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; relsf.
    { by rewrite ct_begin, EE, ?seqA; sin_rewrite E2; relsf. }
    { rewrite ct_begin at 1; rewrite EE at 1; rewrite ED at 1;
        rewrite rtE at 1; relsf.
      rewrite ?seqA. 
      repeat apply inclusion_union_l; rewrite ?seqA.
      { by sin_rewrite E2; relsf. }
      rewrite ct_begin, EE, ?seqA; sin_rewrite E2; relsf. }
    { rewrite rtE at 1; relsf.
      rewrite rtE at 1; relsf.
      repeat apply inclusion_union_l; rewrite ?seqA.
      { rewrite ED, ?seqA; sin_rewrite E2; relsf. }
      { rewrite ct_begin, EE, ?seqA; sin_rewrite E2; relsf. }
      rewrite ct_begin at 1; rewrite ?seqA.
      rewrite rtE at 1; relsf.
      rewrite ED, ?seqA; sin_rewrite E2; relsf.
      rewrite ct_begin, EE, ?seqA; sin_rewrite E2; relsf. }
    rewrite ?seqA.
    arewrite (⦗d⦘ ⨾ (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed) ＊ ⨾ dd ＊ ⊆ fun _ _ => True).
    rewrite rtE at 1; relsf.
    rewrite DE, ?seqA.
    arewrite (⦗d'⦘ ⨾ ⦗d⦘ ⊆ (fun _ _ : A => False)).
    {  by rewrite seq_eqvC in E2. }
    relsf.
    rewrite ct_end at 1; rewrite ?seqA.
    rewrite EE, ?seqA.
    arewrite (⦗d'⦘ ⨾ ⦗d⦘ ⊆ (fun _ _ : A => False)).
    {  by rewrite seq_eqvC in E2. }
    relsf.
  Qed.

  Lemma irr_dom
        (E1: r ⊆ (⦗d⦘ ∪ ⦗d'⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗d'⦘))
        (E2: ⦗d⦘ ⨾ ⦗d'⦘ ⊆ ∅₂)
        (IRRd: irreflexive (⦗d⦘ ⨾ r ⨾ ⦗d⦘)) 
        (IRRe: irreflexive (⦗d'⦘ ⨾ r ⨾ ⦗d'⦘)) :
    irreflexive r.
  Proof.
    rewrite step_dom; try edone.
    repeat rewrite irreflexive_union; splits; try done; 
      generalize E2; basic_solver 8.
  Qed.

  Lemma eq_dom_union :
    eq_dom (d ∪₁ d') f g <-> eq_dom d f g /\ eq_dom d' f g.
  Proof. 
    split.
    { ins. unfold eq_dom in *. 
      splits; ins; apply (H x); basic_solver. }
    intros [Hs Hs'].
    unfold eq_dom in *. ins. 
    unfold set_union in DX. 
    desf; basic_solver.
  Qed.  

  Lemma eq_dom_full_eq (EQD : eq_dom (fun _ => True) f g) :
    f = g.
  Proof. apply functional_extensionality. ins. by apply EQD. Qed.

  Lemma dom_cond_elim : r ⨾ ⦗dom_cond r d⦘ ⊆ ⦗d⦘ ⨾ r.
  Proof.
    unfold dom_cond; basic_solver 12.
  Qed.

  Lemma dom_cond_elim1 (IN: r ⊆ r') :
    r ⨾ ⦗dom_cond r' d⦘ ⊆ ⦗d⦘ ⨾ r.
  Proof. unfold dom_cond; basic_solver 21. Qed.

  Lemma dom_cond_elim2 :
    d' ∩₁ dom_cond r d ⊆₁ dom_cond (⦗ d' ⦘ ⨾ r) d.
  Proof. unfold dom_cond. basic_solver 12. Qed.

  Lemma dom_cond_union :
    dom_cond (r ∪ r') d ≡₁ dom_cond r d ∩₁ dom_cond r' d.
  Proof. unfold dom_cond; split; basic_solver 21. Qed.

  Lemma dom_cond_in :
    r ⨾ ⦗d'⦘ ⊆ ⦗d⦘ ⨾ r' -> d' ⊆₁ dom_cond r d.
  Proof.
    unfold dom_cond; unfolder; ins; desf.
   splits; eauto; eapply H; eauto.
  Qed.
End Lemmas.

Lemma doma_eqv (d : A -> Prop) (r : relation A): doma (⦗d⦘ ⨾ r) d.
Proof. apply doma_helper. basic_solver. Qed.

Lemma domb_eqv (d : A -> Prop) (r : relation A): domb (r ⨾ ⦗d⦘) d.
Proof. apply domb_helper. basic_solver. Qed.

Lemma acyc_dom (r: relation A) d e
      (E1: r ⊆ (⦗d⦘ ∪ ⦗e⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗e⦘))
      (E2: ⦗d⦘ ⨾ ⦗e⦘ ⊆ ∅₂)
      dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
      de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗e⦘)
      ed (ED: ed = ⦗e⦘ ⨾ r ⨾ ⦗d⦘)
      ee (EE: ee = ⦗e⦘ ⨾ r ⨾ ⦗e⦘) 
      (ACYCd: acyclic dd) 
      (ACYCe: acyclic ee) 
      (ACYCed: acyclic (ed ⨾ dd＊ ⨾ de ⨾ ee＊)) :
  acyclic r.
Proof.
  red.
  eapply irr_dom; try edone.
  { arewrite (⦗d⦘ ∪ ⦗e⦘ ≡ ⦗fun x => d x \/ e x⦘) by basic_solver.
    apply domab_helper; split.
    apply ct_doma; eapply domab_helper with (d':= fun x => d x \/ e x).
    rewrite E1 at 1; basic_solver.
    apply ct_domb; eapply domab_helper with (d := fun x => d x \/ e x).
    rewrite E1 at 1; basic_solver. }
  sin_rewrite path_dom_same; try edone.
  { repeat rewrite irreflexive_union; splits; try done.
    rewrite irreflexive_seqC.
    arewrite( dd＊ ⨾ (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed) ⁺ ⊆ (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed) ⁺).
    {  by rewrite ct_begin; rewrite !seqA; rels. }
    assert (acyclic (dd ＊ ⨾ de ⨾ ee ＊ ⨾ ed)); try done. (*?*)
    rewrite acyclic_seqC; rewrite !seqA. 
    rewrite acyclic_seqC; rewrite !seqA. 
    rewrite acyclic_seqC; rewrite !seqA. 
    done. }
  rewrite unionC in E1.
  sin_rewrite path_dom_same; try edone; try by rewrite seq_eqvC.
  repeat rewrite irreflexive_union; splits; try done.
  rewrite irreflexive_seqC.
  arewrite( ee＊ ⨾ (ee ＊ ⨾ ed ⨾ dd ＊ ⨾ de) ⁺  ⊆ (ee ＊ ⨾ ed ⨾ dd ＊ ⨾ de) ⁺).
  { by rewrite ct_begin; rewrite !seqA; rels. }
  assert (acyclic(ee ＊ ⨾ ed ⨾ dd ＊ ⨾ de)); try done. (*?*)
  rewrite acyclic_seqC; rewrite !seqA. 
  done.
Qed.

End Domains.

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

Add Parametric Morphism A : (@dom_cond A) with signature
  inclusion --> set_subset ==> set_subset as dom_cond_mori.
Proof.
  ins. unfold dom_cond.
  red; ins.
    by rewrite H, <- H0.
Qed.

Add Parametric Morphism A : (@dom_cond A) with signature
  same_relation ==> set_equiv ==> set_equiv as dom_cond_more.
Proof.
  unfold dom_cond; unfolder; ins; splits; ins; desf; eauto 10.
Qed.

Hint Unfold doma domb eq_dom dom_cond : unfolderDb.

Hint Resolve eqv_doma seq_eqv_doma restr_eq_rel_doma : hahn. 
Hint Resolve seq_doma union_doma ct_doma seq_r_doma : hahn.
Hint Resolve transp_doma cross_doma restr_doma restr_doma_mon : hahn.
Hint Resolve eqv_domb seq_eqv_domb restr_eq_rel_domb : hahn.
Hint Resolve seq_domb union_domb ct_domb seq_r_domb : hahn.
Hint Resolve transp_domb cross_domb restr_domb restr_domb_mon : hahn.

Hint Rewrite dom_empty codom_empty dom_union codom_union : hahn.
Hint Rewrite dom_eqv codom_eqv dom_eqv1 codom_eqv1 : hahn.
Hint Rewrite dom_cross codom_cross : hahn_full.
