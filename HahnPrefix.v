(******************************************************************************)
(** * Prefix finiteness *)
(******************************************************************************)

Require Import NPeano Omega Setoid.
Require Import HahnBase HahnList HahnSets HahnRelationsBasic.
Require Import HahnEquational HahnRewrite.

Set Implicit Arguments.

(** A generalization of totality useful for bounding the length of cycles. *)

Definition n_total A (r : relation A) (n : nat) :=
  forall l (LLEN: n < length l) (ND: NoDup l),
  exists a b, a <> b /\ In a l /\ In b l /\ r a b.

Definition has_finite_antichain A (r : relation A) :=
  exists n, n_total r n.

Add Parametric Morphism A : (@n_total A) with signature
  inclusion ==> le ==> Basics.impl as n_total_mori.
Proof.
  repeat red; unfold inclusion; intros.
  apply H1 in ND; try omega; desf; repeat eexists; eauto.
Qed.

Add Parametric Morphism A : (@n_total A) with signature
  same_relation ==> eq ==> iff as n_total_more.
Proof.
  unfold same_relation; ins; desf; split; desf; ins;
  [rewrite <- H | rewrite <- H0]; ins.
Qed.

Add Parametric Morphism A : (@has_finite_antichain A) with signature
  inclusion ==> Basics.impl as has_finite_antichain_mori.
Proof.
  unfold Basics.impl, has_finite_antichain; ins; desc.
  by exists n; rewrite <- H.
Qed.

Add Parametric Morphism A : (@has_finite_antichain A) with signature
  same_relation ==> iff as has_finite_antichain_more.
Proof.
  unfold same_relation; ins; desf; split; desf; ins;
  [rewrite <- H | rewrite <- H0]; ins.
Qed.

Lemma has_finite_antichainI A (r : relation A) n :
  n_total r n -> has_finite_antichain r.
Proof. vauto. Qed.

Hint Immediate has_finite_antichainI : hahn.

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


(** Prefix finiteness *)

Definition prefix_finite A (r : relation A) :=
  forall x,  set_finite (fun a => r a x).

Add Parametric Morphism A : (@prefix_finite A) with signature
  inclusion --> Basics.impl as prefix_finite_mori.
Proof.
  unfold inclusion; intros; intros F a; destruct (F a) as [d ?].
  exists d; ins; eauto.
Qed.

Add Parametric Morphism A : (@prefix_finite A) with signature
  same_relation ==> iff as prefix_finite_more.
Proof.
  by unfold same_relation; split; desf; ins; [rewrite H0|rewrite H].
Qed.

Lemma prefix_finite_eqv A (s : A -> Prop) : prefix_finite ⦗s⦘.
Proof.
  intro x; exists (x :: nil); unfold eqv_rel; ins; desf; vauto.
Qed.

Lemma prefix_finite_union A (r r': relation A) :
  prefix_finite r ->
  prefix_finite r' ->
  prefix_finite (r ∪ r').
Proof.
  unfold prefix_finite, union, set_finite; ins; desf.
  specialize (H x); specialize (H0 x); desf.
  exists (findom ++ findom0); ins; desf; eauto using in_or_app.
Qed.

Lemma prefix_finite_bunion A (s : A -> Prop) B (rr : A -> relation B) :
  set_finite s ->
  (forall x, s x -> prefix_finite (rr x)) ->
  prefix_finite (⋃x ∈ s, rr x).
Proof.
  unfold prefix_finite, seq; ins; desf.
  apply set_finite_bunion; ins; eauto.
Qed.

Lemma prefix_finite_seq A (r r': relation A) :
  prefix_finite r ->
  prefix_finite r' ->
  prefix_finite (r ;; r').
Proof.
  unfold prefix_finite, seq; ins; desf.
  specialize (H0 x).
  forward eapply (proj2 (set_finite_bunion (B:=A) H0 (fun a b => r b a))) as X; ins.
  clear - X; unfold set_bunion in *.
  unfold set_finite in *; desf; exists findom; ins; desf; eauto.
Qed.

Lemma prefix_finite_inter_l A (r r': relation A) :
  prefix_finite r ->
  prefix_finite (r ∩ r').
Proof.
  unfold prefix_finite, inter_rel, set_finite; ins; desf.
  specialize (H x); desf; exists findom; ins; desf; eauto.
Qed.

Lemma prefix_finite_inter_r A (r r': relation A) :
  prefix_finite r' ->
  prefix_finite (r ∩ r').
Proof.
  unfold prefix_finite, inter_rel, set_finite; ins; desf.
  specialize (H x); desf; exists findom; ins; desf; eauto.
Qed.

Lemma prefix_finite_minus A (r r': relation A) :
  prefix_finite r ->
  prefix_finite (r \ r').
Proof.
  unfold prefix_finite, minus_rel, set_finite; ins; desf.
  specialize (H x); desf; exists findom; ins; desf; eauto.
Qed.

Hint Resolve
     prefix_finite_eqv
     prefix_finite_union
     prefix_finite_bunion
     prefix_finite_inter_l
     prefix_finite_inter_r
     prefix_finite_seq 
     prefix_finite_minus : hahn.

Lemma prefix_finite_cr A (r : relation A) :
  prefix_finite r -> prefix_finite r^?.
Proof.
  rewrite crE; ins; eauto with hahn.
Qed.

Lemma prefix_finite_pow A (r : relation A) n :
  prefix_finite r -> prefix_finite (r ^^ n).
Proof.
  intros; induction n; ins; auto with hahn.
Qed.

Hint Resolve prefix_finite_cr prefix_finite_pow : hahn.

Lemma prefix_finite_ct A (r : relation A)
      (ACYC: acyclic r)
      (TOT: has_finite_antichain r)
      (PF: prefix_finite r) :
  prefix_finite r⁺.
Proof.
  destruct TOT; intros; rewrite ct_bounded_n_total; eauto with hahn.
Qed.

Lemma prefix_finite_rt A (r : relation A)
      (ACYC: acyclic r)
      (TOT: has_finite_antichain r)
      (PF: prefix_finite r) :
  prefix_finite r＊.
Proof.
  destruct TOT; intros; rewrite rt_bounded_n_total; eauto with hahn.
Qed.

Hint Resolve prefix_finite_ct prefix_finite_rt : hahn.

