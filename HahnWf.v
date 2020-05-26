(******************************************************************************)
(** * Well-founded and finitely supported relations *)
(******************************************************************************)

Require Import Setoid Morphisms Wf_nat Omega.
Require Import HahnBase HahnList HahnSets HahnRelationsBasic HahnEquational HahnRewrite.

Set Implicit Arguments.

(** A relation is finitely supported iff every element has a finite number of
    predecessors. *)

Definition fsupp A (r: relation A) :=
  forall y, exists findom, forall x (REL: r x y), In x findom.

(** A relation is n-total iff any set of n+1 elements must contain two related
    elements. This generalization of totality useful for bounding the length
    of cycles. *)

Definition n_total A (r : relation A) (n : nat) :=
  forall l (LLEN: n < length l) (ND: NoDup l),
  exists a b, a <> b /\ In a l /\ In b l /\ r a b.

(** A relation has only finite antichains iff there is no infinite set of pairwise
    unrelated elements. *)

Definition has_finite_antichains A (r : relation A) :=
  exists n, n_total r n.

Hint Unfold fsupp ltof n_total has_finite_antichains : unfolderDb.

Lemma has_finite_antichainsI A (r : relation A) n :
  n_total r n -> has_finite_antichains r.
Proof. vauto. Qed.

Hint Immediate has_finite_antichainsI : hahn.

Add Parametric Morphism A : (@fsupp A) with signature
  inclusion --> Basics.impl as fsupp_mori.
Proof.
  unfolder; ins; desf; specialize (H0 y0); desf; eauto.
Qed.

Add Parametric Morphism A : (@fsupp A) with signature
  same_relation ==> iff as fsupp_more.
Proof.
  by split; [rewrite (proj2 H)|rewrite (proj1 H)].
Qed.

Add Parametric Morphism A : (@n_total A) with signature
  inclusion ==> le ==> Basics.impl as n_total_mori.
Proof.
  unfolder; ins.
  apply H1 in ND; try omega; desf; repeat eexists; eauto.
Qed.

Add Parametric Morphism A : (@n_total A) with signature
  same_relation ==> eq ==> iff as n_total_more.
Proof.
  by split; [rewrite (proj1 H)|rewrite (proj2 H)].
Qed.

Add Parametric Morphism A : (@has_finite_antichains A) with signature
  inclusion ==> Basics.impl as has_finite_antichains_mori.
Proof.
  unfold Basics.impl, has_finite_antichains; ins; desc.
  by exists n; rewrite <- H.
Qed.

Add Parametric Morphism A : (@has_finite_antichains A) with signature
  same_relation ==> iff as has_finite_antichains_more.
Proof.
  by split; [rewrite (proj1 H)|rewrite (proj2 H)].
Qed.

(** Bounded paths because of n-totality. *)

Lemma pow_bounded_n_total A (r : relation A) n
      (TOT: n_total r n)
      (IRR: irreflexive (⋃i <= 2 * n, r ^^ (S i)))  :
  r ^^ (S (2 * n)) ⊆ (⋃i < 2 * n, r ^^ (S i)).
Proof.
  intros a b R; apply powE in R; desf.
  assert (I: forall i j (L: i < j < S (2 * n)), r ^+ (f i) (f j)).
  {
    clear - R1; intros; desc.
    revert L0.
    rewrite (le_plus_minus _ _ L); generalize (j - S i) as k.
    revert R1; generalize (2 * n + 1) as m; ins.
    induction k; rewrite ?Nat.add_0_r; vauto.
      apply t_step, R1; omega.
    eapply t_trans, t_step; [apply IHk; omega|].
    rewrite Nat.add_succ_r; apply R1; omega.
  }
  tertium_non_datur (exists i j, i < j <= n /\ f (2 * i) = f (2 * j)) as [C|C];
    desc.
  {
    exists (2 * i + (2 * n - 2 * j)); split; try omega.
    rewrite <- Nat.add_succ_r.
    hahn_rewrite pow_add; exists (f (2 * i)); splits.
      apply powE; exists f; splits; ins; eapply R1; omega.
    rewrite C0; apply powE; exists (fun n => f (2 * j + n)).
    splits; try (f_equal; omega).
    intros; rewrite Nat.add_succ_r; apply R1; omega.
  }
  forward eapply (TOT (map (fun x => f (2 * x)) (List.seq 0 (S n)))).
    by rewrite length_map, length_seq; ins.
  {
    apply nodup_map; auto using nodup_seq; red; intros.
    rewrite in_seq0_iff in *.
    destruct (lt_eq_lt_dec x y) as [[L|]|L]; desf; eapply C.
    eexists x, y; splits; ins; omega.
    eexists y, x; splits; ins; omega.
  }
  intros; desf; rewrite in_map_iff in *; desc; rewrite in_seq0_iff in *; desf.
  assert (K: r ^^ (S (2 * x0 + (2 * n + 1 - 2 * x))) (f 0) (f (S (2 * n)))).
  {
    assert (K: r ^^ (2 * x0) (f 0) (f (2 * x0))).
      apply powE; exists f; splits; ins; eapply R1; omega.
    assert (L: r ^^ (2 * n + 1 - 2 * x) (f (2 * x)) (f (S (2 * n)))).
    { apply powE; exists (fun n => f (2 * x + n)); rewrite ?Nat.add_0_r.
      rewrite le_plus_minus_r; splits; intros; try done; try omega.
      f_equal; omega.
      rewrite Nat.add_succ_r; apply R1; omega. }
    rewrite <- Nat.add_succ_l, <- Nat.add_1_r.
    do 2 hahn_rewrite pow_add; unfold seq; repeat eexists; eauto.
  }
  destruct (lt_eq_lt_dec x0 x) as [[]|]; desf.
  - eexists; split; try exact K; omega.
  - edestruct IRR.
    exists (2 * x0 - 2 * x); split; try omega.
    eexists; split; [apply powE|edone].
    exists (fun n => f (n + 2 * x)); splits; intros;
      try (f_equal; omega); apply R1; omega.
Qed.

Lemma ct_bounded_n_total A (r : relation A) (ACYC: acyclic r)
      n (TOT: n_total r n) :
  r⁺ ≡ ⋃ i < 2 * n, pow_rel r (S i).
Proof.
  split.
  2: apply inclusion_bunion_l; ins.
  2: by rewrite ct_end, pow_rt.
  apply inclusion_t_ind_right.
  { exists 0; split; [|by apply pow_1].
    destruct n; try omega.
    forward eapply (TOT (x :: nil)); ins; desf. }
  relsf.
  apply inclusion_bunion_l; intros.
  rewrite <- Nat.le_succ_l in H.
  rewrite pow_seq.
  destruct (eqP (S x) (2 * n)) as [->|].
    apply pow_bounded_n_total; eauto.
    by apply irreflexive_bunion; intros; rewrite pow_ct.
  by apply inclusion_bunion_r with (S x); try omega.
Qed.

Lemma rt_bounded_n_total A (r : relation A) (ACYC: acyclic r)
      n (TOT: n_total r n) :
  r＊ ≡ ⋃ i <= 2 * n, pow_rel r i.
Proof.
  split; auto using inclusion_bunion_l, pow_rt.
  rewrite rtE, ct_bounded_n_total; eauto.
  repeat (apply inclusion_union_l || apply inclusion_bunion_l; intros).
    apply inclusion_bunion_r with 0; ins; omega.
  apply inclusion_bunion_r with (S x); ins.
Qed.


(** Properties of well-founded relations. *)

Section well_founded.

  Variable A : Type.
  Implicit Types r : relation A.

  Lemma wf_impl_no_inf_seq r (WF: well_founded r) x :
    ~ exists a, a 0 = x /\ forall n, r (a (S n)) (a n).
  Proof.
    specialize (WF x); induction WF.
    intro CONTRA; desf.
    specialize (CONTRA0 0)  as C.
    apply H0 in C; destruct C.
    exists (fun n => a (S n)); ins.
  Qed.

  Lemma wf_impl_min_elt r (WF: well_founded r) B (NONEMPTY: ~ B ≡₁ ∅) :
    exists b, B b /\ forall b', B b' -> ~ r b' b.
  Proof.
    apply set_nonemptyE in NONEMPTY; desc.
    apply NNPP; intro C.
    induction x using (well_founded_ind WF).
    destruct C; eexists; split; try edone; red; ins; eauto.
  Qed.

  Lemma wf_mon r1 r2 (INCL: r1 ⊆ r2) (WF: well_founded r2) : well_founded r1.
  Proof.
    unfold well_founded in *; ins;
    induction (WF a); econstructor; eauto.
  Qed.

  Lemma wf_imm_succ r (WF: well_founded r) a b (REL: r a b) :
    exists c, immediate r a c.
  Proof.
    revert a REL; induction b using (well_founded_ind WF); ins.
    tertium_non_datur (immediate r a b) as [?|NIM]; eauto.
  Qed.

  Lemma wf_restr r (WF: well_founded r) cond : well_founded (restr_rel cond r).
  Proof.
    red; ins; induction a using (well_founded_induction WF).
    constructor; ins; unfolder in H0; desf; eauto.
  Qed.

End well_founded.

Hint Resolve wf_restr : hahn.

(** Properties of finitely supported relations. *)

Section finite_support.

  Variable A : Type.
  Implicit Types r : relation A.

  Theorem fsupp_well_founded r (FS: fsupp r)
          (IRR: irreflexive r) (TRANS: transitive r) :
    well_founded r.
  Proof.
    intros a; specialize (FS a); desf; revert a FS.
    induction findom
      using (well_founded_induction (well_founded_ltof _ (@length _))).
    unfold ltof in *.
    constructor; intros y Rya.
    assert (IN := FS _ Rya).
    apply In_split in IN; desf.
    eapply H with (y0 := l1 ++ l2); ins.
      by rewrite !app_length; simpl; omega.
    assert (Rxa: r x a) by eauto.
    generalize (FS _ Rxa); rewrite !in_app_iff; ins; desf; eauto.
    exfalso; eauto.
  Qed.

  Lemma fsupp_imm_t r (FS: fsupp r)
          (IRR: irreflexive r) (TRANS: transitive r) :
    r ≡ (immediate r)⁺.
  Proof.
    split; [|by eauto with hahn].
    red; ins.
    specialize (FS y); desf.
    assert (M: forall n, r x n -> r n y -> In n findom) by eauto.
    clear FS; revert x y H M.
    induction findom
      using (well_founded_induction (well_founded_ltof _ (@length _))).
    unfold ltof in *.
    ins.
    tertium_non_datur (immediate r x y) as [|NIMM]; vauto.
    assert (N := M _ NIMM NIMM0); apply In_split in N; desf.
    apply t_trans with (y := n); eapply H with (y := l1 ++ l2); ins.
    1,3: by rewrite !app_length; simpl; omega.
    - apply M in H1; eauto; rewrite !in_app_iff in *; ins; desf; eauto.
      exfalso; eauto.
    - apply M in H2; eauto; rewrite !in_app_iff in *; ins; desf; eauto.
      exfalso; eauto.
  Qed.

  Lemma fsupp_mon r r' (SUBS: r ⊆ r') (FS: fsupp r') : fsupp r.
  Proof.
    unfolder in *; ins; specialize (FS y); des; eauto.
  Qed.

  Lemma fsupp_empty : fsupp (A:=A) ∅₂.
  Proof.
    exists nil; ins.
  Qed.

  Lemma fsupp_eqv (d : A -> Prop) : fsupp ⦗d⦘.
  Proof.
    unfolder; ins; exists (y :: nil); ins; desf; eauto.
  Qed.

  Lemma fsupp_cross (s s': A -> Prop) (F: set_finite s) : fsupp (s × s').
  Proof.
    unfolder in *; ins; desf; eexists; ins; desf; eauto.
  Qed.

  Lemma fsupp_union_iff r1 r2 : fsupp (r1 ∪ r2) <-> fsupp r1 /\ fsupp r2.
  Proof.
    unfolder in *; intuition;
      repeat match goal with [ H : _, y : A |- _ ] => specialize (H y) end;
      desf; first [exists (findom ++ findom0) | exists findom];
      ins; desf; eauto using in_or_app.
  Qed.

  Lemma fsupp_union r1 r2 (FS1: fsupp r1) (FS2: fsupp r2) : fsupp (r1 ∪ r2).
  Proof.
    by apply fsupp_union_iff.
  Qed.

  Lemma fsupp_bunion B s (rr : B -> relation A)
        (FIN: set_finite s) (FS: forall x (IN: s x), fsupp (rr x)) :
    fsupp (bunion s rr).
  Proof.
    unfold fsupp, seq; ins; desf.
    apply set_finite_bunion; ins.
    apply FS; done.
  Qed.

  Lemma fsupp_inter_l r r' : fsupp r -> fsupp (r ∩ r').
  Proof.
    unfolder; ins; desf.
    specialize (H y); desf; eauto; exists findom; ins; desf; eauto.
  Qed.

  Lemma fsupp_inter_r r r' : fsupp r' -> fsupp (r ∩ r').
  Proof.
    unfolder; ins; desf.
    specialize (H y); desf; eauto; exists findom; ins; desf; eauto.
  Qed.

  Lemma fsupp_minus r r' : fsupp r -> fsupp (r \ r').
  Proof.
    unfolder; ins; desf.
    specialize (H y); desf; eauto; exists findom; ins; desf; eauto.
  Qed.

  Lemma fsupp_list r (FS: fsupp r) l :
    exists findom, forall x y (REL: r x y) (IN: In y l), In x findom.
  Proof.
    induction l; ins; desf.
      by exists nil; ins.
    specialize (FS a); desf.
    exists (findom ++ findom0); ins; desf; eauto using in_or_app.
  Qed.

  Lemma fsupp_seq r1 r2 (FS1: fsupp r1) (FS2: fsupp r2) : fsupp (r1 ⨾ r2).
  Proof.
    unfold fsupp, seq; desf; ins; desf.
    specialize (FS2 y); desf.
    apply fsupp_list with (l:=findom) in FS1; desf.
    exists findom0; ins; desf; eauto.
  Qed.

  Lemma fsupp_seq_eqv_l r d (FS: fsupp r) : fsupp (⦗d⦘ ⨾ r).
  Proof.
    unfold fsupp, seq, eqv_rel; desf; ins; desf.
    specialize (FS y); desf; exists findom; ins; desf; eauto.
  Qed.

  Lemma fsupp_seq_eqv_r r d (FS: fsupp r) : fsupp (r ⨾ ⦗d⦘).
  Proof.
    unfold fsupp, seq, eqv_rel; desf; ins; desf.
    specialize (FS y); desf; exists findom; ins; desf; eauto.
  Qed.

  Lemma fsupp_restr r (FS: fsupp r) cond : fsupp (restr_rel cond r).
  Proof.
    firstorder.
  Qed.

  Lemma functional_inv_fsupp r (F: functional r⁻¹) : fsupp r.
  Proof.
    unfolder; ins.
    tertium_non_datur (exists x, r x y); ins; desf.
    - exists (x :: nil); ins; eauto.
    - exists nil; ins; eauto.
  Qed.

  Lemma fsupp_cr r : fsupp r -> fsupp r^?.
  Proof.
    rewrite crE; ins; eauto using fsupp_eqv, fsupp_union.
  Qed.

  Lemma fsupp_pow r n : fsupp r -> fsupp (r ^^ n).
  Proof.
    ins; induction n; ins; eauto using fsupp_eqv, fsupp_union, fsupp_seq.
  Qed.

  Lemma fsupp_ct r (ACYC: acyclic r) (TOT: has_finite_antichains r) :
    fsupp r -> fsupp r⁺.
  Proof.
    destruct TOT; intros; rewrite ct_bounded_n_total;
      eauto using fsupp_bunion, fsupp_pow with hahn.
  Qed.

  Lemma fsupp_ct_rt r : fsupp r⁺ -> fsupp r＊.
  Proof.
    rewrite rtE; eauto using fsupp_union, fsupp_eqv.
  Qed.

  Lemma fsupp_rt r (ACYC: acyclic r) (TOT: has_finite_antichains r) :
    fsupp r -> fsupp r＊.
  Proof.
    eauto using fsupp_ct_rt, fsupp_ct.
  Qed.

End finite_support.

Hint Resolve fsupp_empty fsupp_eqv fsupp_cross : hahn.
Hint Resolve fsupp_union fsupp_bunion fsupp_seq : hahn.
Hint Resolve fsupp_inter_l fsupp_inter_r fsupp_minus : hahn.
Hint Resolve fsupp_restr : hahn.
Hint Resolve fsupp_cr fsupp_pow fsupp_ct fsupp_ct_rt : hahn.
Hint Immediate functional_inv_fsupp : hahn.
