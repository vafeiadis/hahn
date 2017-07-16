(******************************************************************************)
(** * Maximal elements of relations *)
(******************************************************************************)

Require Import HahnBase HahnList HahnSets HahnRelationsBasic HahnEquational HahnRewrite.
Require Import Classical NPeano Omega Setoid.

Set Implicit Arguments.


Definition max_elt A (r: relation A) (a : A) :=
  forall b (REL: r a b), False.

Definition wmax_elt A (r: relation A) (a : A) :=
  forall b (REL: r a b), a = b.


Section BasicProperties.

Variable A : Type.
Variables r r' r'' : relation A.
Variable a : A.

Lemma set_subset_max_elt (S: r' ⊆ r) : max_elt r ⊆₁ max_elt r'.
Proof. unfold max_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_subset_wmax_elt (S: r' ⊆ r) : wmax_elt r ⊆₁ wmax_elt r'.
Proof. unfold wmax_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_max_elt (S: r ≡ r') : max_elt r ≡₁ max_elt r'.
Proof. unfold max_elt, same_relation, set_equiv in *; intuition; eauto. Qed.

Lemma set_equiv_wmax_elt (S: r ≡ r') : wmax_elt r ≡₁ wmax_elt r'.
Proof. unfold wmax_elt, same_relation, set_equiv in *; intuition; eauto. Qed.

Lemma max_elt_weaken : max_elt r a -> wmax_elt r a.
Proof.
  red; ins; exfalso; eauto.
Qed.

Lemma max_elt_union : max_elt r a -> max_elt r' a -> max_elt (r +++ r') a.
Proof.
  unfold union; red; ins; desf; eauto.
Qed.

Lemma wmax_elt_union : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r +++ r') a.
Proof.
  unfold union; red; ins; desf; eauto.
Qed.

Lemma max_elt_t : max_elt r a -> max_elt (r⁺) a.
Proof.
  red; ins; apply clos_trans_t1n in REL; induction REL; eauto.
Qed.

Lemma wmax_elt_rt : wmax_elt r a -> wmax_elt (r＊) a.
Proof.
  red; ins; apply clos_rt_rtn1 in REL; induction REL; desf; eauto.
Qed.

Lemma wmax_elt_t : wmax_elt r a -> wmax_elt (r⁺) a.
Proof.
  by red; ins; eapply wmax_elt_rt, inclusion_t_rt.
Qed.

Lemma wmax_elt_eqv (f: A -> Prop) : wmax_elt (eqv_rel f) a.
Proof.
  unfold eqv_rel; red; ins; desf.
Qed.

Lemma wmax_elt_restr_eq B (f: A -> B) :
  wmax_elt r a -> wmax_elt (restr_eq_rel f r) a.
Proof.
  unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma max_elt_restr_eq B (f: A -> B) :
  max_elt r a -> max_elt (restr_eq_rel f r) a.
Proof.
  unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma wmax_elt_r :
  wmax_elt r a -> wmax_elt (r^?) a.
Proof.
  unfold clos_refl; red; ins; desf; eauto.
Qed.

Lemma max_elt_seq1 : max_elt r a -> max_elt (r ⨾ r') a.
Proof.
  unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma wmax_elt_seq2 : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r ⨾ r') a.
Proof.
  unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma wmax_elt_seq1 : max_elt r a -> wmax_elt (r ⨾ r') a.
Proof.
  unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma max_elt_seq2 : wmax_elt r a -> max_elt r' a -> max_elt (r ⨾ r') a.
Proof.
  unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

End BasicProperties.

Hint Immediate max_elt_weaken : rel.
Hint Resolve wmax_elt_union max_elt_union : rel.
Hint Resolve wmax_elt_t wmax_elt_r wmax_elt_rt max_elt_t : rel.
Hint Resolve max_elt_restr_eq wmax_elt_restr_eq : rel.
Hint Resolve max_elt_seq1 max_elt_seq2 wmax_elt_seq1 wmax_elt_seq2 : rel.

Section MoreProperties.

Variable A : Type.
Implicit Type r : relation A.

Lemma seq_max r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r' ≡ ∅₂.
Proof.
  unfold seq; split; red; ins; desf.
  apply COD in H; desf; eauto.
Qed.

Lemma seq_max_t r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ⁺ ≡ ∅₂.
Proof.
  eauto using seq_max with rel.
Qed.

Lemma seq_max_rt r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r'＊ ≡ r.
Proof.
  rewrite rtE; relsf; rewrite seq_max_t; relsf.
Qed.

Lemma seq_max_r r r' b
      (MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
  r ⨾ r'^? ≡ r.
Proof.
  rewrite crE; relsf; rewrite seq_max; relsf.
Qed.

Lemma seq_eq_max r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r ≡ ∅₂.
Proof.
  eapply seq_max; unfold eqv_rel; ins; desf; eauto.
Qed.

Lemma seq_eq_max_t r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r⁺ ≡ ∅₂.
Proof.
  eauto using seq_eq_max with rel.
Qed.

Lemma seq_eq_max_rt r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r＊ ≡ ⦗eq b⦘.
Proof.
  rewrite rtE; relsf; rewrite seq_eq_max_t; relsf.
Qed.

Lemma seq_eq_max_r r b (MAX: max_elt r b) :
  ⦗eq b⦘ ⨾ r^? ≡ ⦗eq b⦘.
Proof.
  rewrite crE; relsf; rewrite seq_eq_max; relsf.
Qed.

Lemma seq_singl_max r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r ≡ ∅₂.
Proof.
  unfold singl_rel, seq; split; red; ins; desf; eauto.
Qed.

Lemma seq_singl_max_t r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r⁺ ≡ ∅₂.
Proof.
  eauto using seq_singl_max with rel.
Qed.

Lemma seq_singl_max_rt r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r＊ ≡ singl_rel a b.
Proof.
  rewrite rtE; relsf; rewrite seq_singl_max_t; relsf.
Qed.

Lemma seq_singl_max_r r a b (MAX: max_elt r b) :
  singl_rel a b ⨾ r^? ≡ singl_rel a b.
Proof.
  rewrite crE; relsf; rewrite seq_singl_max; relsf.
Qed.

Lemma seq_eqv_max r : 
  ⦗max_elt r⦘ ⨾ r ≡ (∅₂).
Proof.
  basic_solver.
Qed.

Lemma seq_eqv_max_t r :
  ⦗max_elt r⦘ ⨾ r⁺ ≡ (∅₂).
Proof.
  rewrite ct_begin; seq_rewrite seq_eqv_max; basic_solver.
Qed.

Lemma seq_eqv_max_rt r :
  ⦗max_elt r⦘ ⨾ r＊ ≡ ⦗max_elt r⦘.
Proof.
  rewrite rtE; relsf; rewrite seq_eqv_max_t; relsf.
Qed.

Lemma seq_eqv_max_r r :
  ⦗max_elt r⦘ ⨾ r^? ≡ ⦗max_elt r⦘.
Proof.
  rewrite crE; relsf; rewrite seq_eqv_max; relsf.
Qed.

Lemma transp_seq_eqv_max r : 
  r⁻¹ ⨾ ⦗max_elt r⦘ ≡ (∅₂).
Proof.
  basic_solver.
Qed.

Lemma transp_seq_eqv_max_t r :
  (r⁻¹)⁺ ⨾ ⦗max_elt r⦘ ≡ (∅₂).
Proof.
  rewrite ct_end, !seqA; seq_rewrite transp_seq_eqv_max; basic_solver.
Qed.

Lemma transp_seq_eqv_max_rt r :
  (r⁻¹)＊ ⨾ ⦗max_elt r⦘  ≡ ⦗max_elt r⦘.
Proof.
  rewrite rtE; relsf; rewrite transp_seq_eqv_max_t; relsf.
Qed.

Lemma transp_seq_eqv_max_r r :
  (r⁻¹)^? ⨾ ⦗max_elt r⦘ ≡ ⦗max_elt r⦘.
Proof.
  rewrite crE; relsf; rewrite transp_seq_eqv_max; relsf.
Qed.

Lemma seq_wmax r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
    r⨾ r' ⊆ r.
Proof.
  unfold seq; red; ins; desf; eauto.
  specialize (COD _ _ H); desf; apply MAX in H0; desf.
Qed.

Lemma seq_wmax_t r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ⁺ ⊆ r.
Proof.
  eauto using seq_wmax with rel.
Qed.

Lemma seq_wmax_rt r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ＊ ≡ r.
Proof.
  rewrite rtE; split; relsf; rewrite seq_wmax_t; relsf.
Qed.

Lemma seq_wmax_r r r' b
      (MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
  r⨾ r' ^? ≡ r.
Proof.
  rewrite crE; split; relsf; rewrite seq_wmax; relsf.
Qed.

Lemma seq_eq_wmax r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ⊆ ⦗eq b⦘.
Proof.
  eapply seq_wmax; unfold eqv_rel; ins; desf.
Qed.

Lemma seq_eq_wmax_t r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ⁺ ⊆ ⦗eq b⦘.
Proof.
  eauto using seq_eq_wmax with rel.
Qed.

Lemma seq_eq_wmax_rt r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ＊ ≡ ⦗eq b⦘.
Proof.
  rewrite rtE; split; relsf; rewrite seq_eq_wmax_t; relsf.
Qed.

Lemma seq_eq_wmax_r r b (MAX: wmax_elt r b) :
  ⦗eq b⦘⨾ r ^? ≡ ⦗eq b⦘.
Proof.
  rewrite crE; split; relsf; rewrite seq_eq_wmax; relsf.
Qed.

Lemma seq_singl_wmax r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ⊆ singl_rel a b.
Proof.
  unfold singl_rel, seq; red; ins; desf; eauto.
  apply MAX in H0; desf.
Qed.

Lemma seq_singl_wmax_t r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ⁺ ⊆ singl_rel a b.
Proof.
  eauto using seq_singl_wmax with rel.
Qed.

Lemma seq_singl_wmax_rt r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ＊ ≡ singl_rel a b.
Proof.
  rewrite rtE; split; relsf; rewrite seq_singl_wmax_t; relsf.
Qed.

Lemma seq_singl_wmax_r r a b (MAX: wmax_elt r b) :
  singl_rel a b⨾ r ^? ≡ singl_rel a b.
Proof.
  rewrite crE; split; relsf; rewrite seq_singl_wmax; relsf.
Qed.

End MoreProperties.

Require Import Morphisms.

Instance max_elt_Proper A : Proper (_ ==> _) _ := set_subset_max_elt (A:=A).
Instance wmax_elt_Proper A : Proper (_ ==> _) _ := set_subset_wmax_elt (A:=A).
Instance max_elt_Propere A : Proper (_ ==> _) _ := set_equiv_max_elt (A:=A).
Instance wmax_elt_Propere A : Proper (_ ==> _) _ := set_equiv_wmax_elt (A:=A).
