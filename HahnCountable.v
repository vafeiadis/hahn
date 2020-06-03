(******************************************************************************)
(** * Countable sets *)
(******************************************************************************)

Require Import NPeano Omega Setoid IndefiniteDescription ClassicalChoice.
Require Import HahnBase HahnList HahnEquational HahnRewrite.
Require Import HahnRelationsBasic HahnSets HahnNatExtra.
Require Import HahnListBefore HahnWf HahnSorted HahnTotalExt.

Set Implicit Arguments.

Fixpoint findP A (cond : A -> Prop) (l : list A) :=
  match l with
  | nil => 0
  | h :: t =>
    if excluded_middle_informative (cond h) then 0 else S (findP cond t)
  end.

Lemma findP_spec A (cond : A -> Prop) (l : list A)
      n (IN: In n l) (COND: cond n) d :
  cond (nth (findP cond l) l d) /\
  forall j, j < findP cond l -> ~ cond (nth j l d).
Proof.
  induction l; ins; desf; splits; ins; desf; try omega; intuition.
  eauto using lt_S_n.
Qed.

Lemma exists_min (cond : nat -> Prop) (H: exists n, cond n) :
  exists n, cond n /\ forall j, j < n -> ~ cond j.
Proof.
  desc; assert (IN: In n (List.seq 0 (S n))).
    by apply in_seq; omega.
  assert (L: findP cond (List.seq 0 (S n)) < S n).
  {
    rewrite <- (seq_length (S n) 0) at 2.
    revert IN; generalize (List.seq 0 (S n)).
    induction l; ins; desf; intuition.
  }

  forward eapply findP_spec with (cond := cond) (l := List.seq 0 (S n)) (d := 0)
    as X; desc; eauto.
  rewrite seq_nth in *; ins.

  eexists; split; eauto; ins; specialize_full X0; eauto.
  rewrite seq_nth in *; ins; omega.
Qed.

Definition fcompose A B C (f : B -> C) (g: A -> B) x :=
  f (g x).

Fixpoint fexp A (f : A -> A) n :=
  match n with
    0 => (fun x => x)
  | S n => fcompose f (fexp f n)
  end.

Lemma fcompose_id_l A B (f: A -> B) :
  fcompose (fun x => x) f = f.
Proof. done. Qed.

Lemma fcompose_id_r A B (f: A -> B) :
  fcompose f (fun x => x) = f.
Proof. done. Qed.

Lemma fcompose_assoc A B C D (f: C -> D) (g : B -> C) (h : A -> B) :
  fcompose (fcompose f g) h = fcompose f (fcompose g h).
Proof. done. Qed.

Lemma fexpS A (f : A -> A) n x :
  fexp f n (f x) = f (fexp f n x).
Proof.
  by revert x; induction n; ins; unfold fcompose; rewrite IHn.
Qed.

Lemma fexp_plus A (f : A -> A) n m :
  fexp f (n + m) = fcompose (fexp f n) (fexp f m).
Proof.
  by induction n; ins; rewrite IHn.
Qed.

Lemma lt_funI f (ONE: forall x, x < f x) i j (LT: i < j) d :
  fexp f i d < fexp f j d.
Proof.
  revert i LT; induction j; ins; try omega.
  destruct (eqP i j); desf; eauto.
  eapply lt_trans, ONE; apply IHj; omega.
Qed.

Definition lt_size A i (s : A -> Prop) :=
  exists dom, NoDup dom /\ (forall x, In x dom -> s x) /\ i < length dom.

Lemma lt_size_inhabited A (s : A -> Prop) i (LT : lt_size i s) : inhabited A.
Proof.
  destruct LT as [[]]; ins; desf; omega.
Qed.

Lemma lt_size_infinite A (s : A -> Prop) (INF : ~ set_finite s) i : lt_size i s.
Proof.
  assert (C: forall l, exists x, s x /\ ~ In x l).
  { ins; apply NNPP; intro X.
    apply INF; exists l; ins; apply NNPP; eauto. }
  apply choice in C; desc.
  set (go := fix go n := match n with
                       | 0 => f nil :: nil
                       | S n => f (go n) :: go n
                      end).
  exists (go i); splits; induction i; ins; desf; eauto;
    try apply C; try omega.
  apply nodup_cons; split; ins; apply C.
Qed.


Section countable.

  Variable A : Type.

  Definition enumerates (f : nat -> A) (s : A -> Prop) :=
     << RNG: forall i, s (f i) >> /\
     << INJ: forall i j (EQ: f i = f j), i = j >> /\
     << SUR: forall a (IN: s a), exists i, f i = a >>
   \/ exists n,
         << RNG: forall i (LTi: i < n), s (f i) >> /\
         << INJ: forall i (LTi: i < n) j (LTj: j < n) (EQ: f i = f j), i = j >> /\
         << SUR: forall a (IN: s a), exists i, i < n /\ f i = a >>.

  Definition countable (s : A -> Prop) :=
     ~ inhabited A \/ exists nu, enumerates nu s.

  Lemma enumeratesE f s :
    enumerates f s <->
    << RNG: forall i (LTi: lt_size i s), s (f i) >> /\
    << INJ: forall i (LTi: lt_size i s) j (LTj: lt_size j s) (EQ: f i = f j),
        i = j >> /\
    << SUR: forall a (IN: s a), exists i, lt_size i s /\ f i = a >>.
  Proof.
    unfold enumerates; split; ins; desf.
    { splits; ins; eauto.
      eapply SUR in IN; desc; exists i; split; ins.
      exists (map f (List.seq 0 (S i))); splits; ins;
        try rewrite length_map, length_seq; ins; desf.
        apply nodup_map; eauto using nodup_seq.
        rewrite in_map_iff in *; desf. }
    { assert (LTI: forall i, lt_size i s -> i < n).
      { ins; red in H; desc.
        replace n with (length (map f (List.seq 0 n))).
        2: by rewrite length_map, length_seq.
        eapply Nat.lt_le_trans; eauto.
        ins; apply NoDup_incl_length; ins.
        red; ins; apply H0, SUR in H2; desf.
          by apply in_map, in_seq0_iff. }
      splits; ins; eauto.
      apply SUR in IN; desf; exists i; split; ins.
      exists (map f (List.seq 0 n)); splits; ins;
        try rewrite length_map, length_seq; ins; desf.
      apply nodup_map; eauto using nodup_seq.
      red; ins; rewrite in_seq0_iff in *; eauto.
      ins; rewrite in_map_iff in *; desf; rewrite in_seq0_iff in *; eauto.
    }
    destruct (classic (set_finite s)) as [[dom X]|INF].
    { right; exists (length (undup (filterP s dom))).
      assert (LTI: forall i, lt_size i s -> i < length (undup (filterP s dom))).
      { ins; red in H; desc.
        eapply Nat.lt_le_trans; eauto.
        apply NoDup_incl_length; ins.
        red; ins; apply H0 in H2; desf.
        apply in_undup_iff, in_filterP_iff; eauto. }
      assert (LTI': forall i, i < length (undup (filterP s dom)) -> lt_size i s).
      { exists (undup (filterP s dom)); splits; ins.
        apply in_undup_iff, in_filterP_iff in H0; desf. }
      splits; ins; eauto; apply SUR in IN; desf; eauto. }
    {  left; splits; ins; eauto using lt_size_infinite.
       eapply SUR in IN; desf; eauto. }
  Qed.

  Lemma finite_countable s (F: set_finite s) : countable s.
  Proof.
    destruct F as [l H]; red.
    destruct (classic (inhabited A)) as [[a]|]; auto.
    right; exists (fun i => nth i (undup (filterP s l)) a).
    right; exists (length (undup (filterP s l))); splits; unnw; ins.
    - apply nth_In with (d:=a) in LTi.
      rewrite in_undup_iff, in_filterP_iff in LTi; desf.
    - eapply NoDup_nth; eauto.
    - apply In_nth, in_undup_iff, in_filterP_iff; eauto.
  Qed.

  Lemma surjection_countable (f : nat -> A) (s : A -> Prop)
      (SUR: forall a (IN: s a), exists i, f i = a) :
    countable s.
  Proof.
    tertium_non_datur (set_finite s); eauto using finite_countable.
    assert (N: forall i, exists k, i < k /\ s (f k) /\ ~ In (f k) (mk_list (S i) f) /\
                                   forall j, j < k -> s (f j) ->
                                             In (f j) (mk_list (S i) f)).
    {
      assert (M: forall i, exists a, s a /\ forall j, j <= i -> f j <> a).
      { ins; apply NNPP; intro X; apply H.
        exists (mk_list (S i) f); intros; apply in_mk_list_iff.
        eapply not_ex_all_not with (n:=x) in X; clarify_not; eauto with arith. }
      intros; specialize (M i); desc.
      specialize_full SUR; eauto; desf.
      destruct (le_lt_dec i0 i); [by edestruct M0; eauto|].
      revert M M0; rewrite (le_plus_minus (S i) i0); auto with arith.
      generalize (i0 - S i) as n; intros.
      exists (S i + findP (fun x => s x /\ ~ In x (mk_list (S i) f))
                          (mk_list (S n) (fun x => (f (S i + x))))).
      forward eapply findP_spec
        with (cond := fun x => s x /\ ~ In x (mk_list (S i) f)) (d := f 0)
             (l := mk_list (S n) (fun x => (f (S i + x)))) as K; desc; eauto.
        by apply in_mk_list_iff; eauto.
          split; try done; rewrite in_mk_list_iff; intro X; desf.
          by symmetry in X0; eapply M0 in X0; eauto with arith.

        rewrite nth_mk_list in *; desf.
          by rewrite in_mk_list_iff in *;
             destruct K1; eauto with arith.
        splits; auto with arith; intros; rewrite in_mk_list_iff.
        destruct (le_lt_dec j i).
          by exists j; auto with arith.
        specialize (K0 (j - S i)).
        rewrite nth_mk_list in K0; desf; [omega|].
        rewrite le_plus_minus_r, in_mk_list_iff in K0; auto with arith.
        apply NNPP; intro; eapply K0; desf; omega. }

    apply choice in N; destruct N as [g N].
    right.
    assert (MID: forall i, exists k, fexp g k 0 <= i < fexp g (S k) 0).
    {
      induction i; ins; unfold fcompose in *; desf.
      - exists 0; split; ins; apply N.
      - destruct (eqP (g (fexp g k 0)) (S i)) as [EQ|NEQ];
          [exists (S k) |exists k; omega].
        split; ins; unfold fcompose; rewrite EQ; ins; apply N.
    }

    tertium_non_datur (s (f 0)).
    {

      exists (fun x => f (fexp g x 0)); left; splits; ins.
      by destruct i; ins; apply N.
      { destruct (lt_eq_lt_dec i j) as [[LT|]|LT]; ins.
        1-2: apply lt_funI with (f:=g) (d:=0) in LT; try (by intros; apply N).
        1-2: exfalso.
        - destruct j; ins; unfold fcompose in *; try omega.
          eapply N with (x := fexp g j 0); rewrite <- EQ.
          apply N; ins; rewrite EQ; apply N.
        - destruct i; ins; unfold fcompose in *; try omega.
          eapply N with (x := fexp g i 0); rewrite EQ.
          apply N; ins; rewrite <- EQ; apply N. }
      forward eapply exists_min with (cond := fun k => f k = a) as X;
        desf; auto.
      specialize (MID n); desc.
      rewrite Nat.le_lteq in *; desf; eauto.
      apply N in MID0; ins.
      apply in_mk_list_iff with (n := S _) in MID0.
      exfalso; desc; symmetry in MID1; eapply X0 in MID1; ins; omega.
    }
    {
      exists (fun x => f (g (fexp g x 0))); left; splits; ins.
      by apply N.
      { destruct (lt_eq_lt_dec i j) as [[LT|]|LT]; ins.
        1-2: apply lt_funI with (f:=g) (d:=g 0) in LT; try (by intros; apply N).
        1-2: rewrite !fexpS in *; exfalso.
        1: eapply N with (x := fexp g j 0); rewrite <- EQ.
        2: eapply N with (x := fexp g i 0); rewrite EQ.
        1-2: apply N; ins; apply N. }
      forward eapply exists_min with (cond := fun k => f k = a) as X;
        desf; auto.
      specialize (MID n); desc.
      rewrite Nat.le_lteq in *; desf; eauto.
        2: by destruct k; ins; exists k; ins.
      apply N in MID0; ins.
      apply in_mk_list_iff with (n := S _) in MID0.
      exfalso; desc; symmetry in MID1; eapply X0 in MID1; ins; omega.
    }
  Qed.

  Lemma enumerates_surjection (s : A -> Prop) nu (E : enumerates nu s) :
    forall a (IN: s a), exists i, nu i = a.
  Proof.
    unfold enumerates in *; desf; ins.
    specialize_full SUR; eauto; desf; eauto.
  Qed.

  Lemma countable_subset s s' :
    countable s' -> s ⊆₁ s' -> countable s.
  Proof.
    unfold countable at 1; ins; desf; vauto.
    pose proof (enumerates_surjection H).
    eapply surjection_countable with (f := nu); eauto.
  Qed.

  Lemma countable_union s s' :
    countable s -> countable s' -> countable (s ∪₁ s').
  Proof.
    unfold countable at 1 2; ins; desf; vauto.
    eapply surjection_countable with
        (f := fun x => if Nat.odd x then nu (Nat.div2 x) else nu0 (Nat.div2 x)).
    unfold set_union; ins; desf;
    eapply enumerates_surjection in IN; eauto; desf.
    exists (2 * i); rewrite Nat.odd_mul, Nat.odd_2, Nat.div2_double; ins.
    exists (S (2 * i)); rewrite Nat.odd_add_mul_2 with (n := 1),
                                Nat.div2_succ_double; ins.
  Qed.

End countable.

Lemma countable_bunion A (s : A -> Prop) B (ss : A -> B -> Prop)
      (K : countable s)
      (L : forall a, countable (ss a)) :
  countable (⋃₁x ∈ s, ss x).
Proof.
  tertium_non_datur (inhabited B) as [Ib|NIb]; vauto.
  unfold countable in K, L; desf; vauto.
    destruct Ib as [b]; eapply surjection_countable with (f := fun _ => b).
    unfold set_bunion; ins; desf; destruct K; vauto.
  assert (C: exists f : A -> nat -> B, forall a, enumerates (f a) (ss a)).
  { apply choice with (R := fun x y => enumerates y (ss x)).
    intros x; specialize (L x); desf; eauto. }
  clear L; desc.
  assert (D := fun x => enumerates_surjection (C x)); clear C.
  specialize (enumerates_surjection K); clear K; intro K.
  apply surjection_countable with
      (f := fun n => f (nu (nat_fst n)) (nat_snd n)).
  unfold set_bunion; ins; desc.
  apply K in IN; desf.
  apply D in IN0; desf.
  by eexists (nat_tup _ _); rewrite nat_fst_tup, nat_snd_tup.
Qed.

Add Parametric Morphism A : (@countable A) with signature
  set_subset --> Basics.impl as countable_mori.
Proof.
  red; ins; eauto using countable_subset.
Qed.

Add Parametric Morphism A : (@countable A) with signature
  set_equiv ==> iff as countable_more.
Proof.
  by unfold set_equiv; split; desf; [rewrite H0|rewrite H].
Qed.


Section prefixes.

  Variable A : Type.
  Variable r : relation A.
  Variable PO : strict_partial_order r.
  Variable F : fsupp r.

  Definition prefixes (a : A) : list A :=
    isort (proj1_sig (constructive_indefinite_description
                        _ (partial_order_included_in_total_order PO)))
          (undup (filterP (fun x => r x a)
                          (proj1_sig (constructive_indefinite_description
                                        _ (F a))))).

  Lemma in_prefixes a b : In a (prefixes b) <-> r a b.
  Proof.
    unfold prefixes; rewrite in_isort_iff, in_undup_iff; in_simp; intuition.
    destruct (constructive_indefinite_description _ (F b)); ins; eauto.
  Qed.

  Lemma sorted_prefixes a :
    exists t, ⟪ INCL: r ⊆ t ⟫
       /\ ⟪ TOT : strict_total_order (fun _ => True) t ⟫
       /\ ⟪ SORT: StronglySorted t (prefixes a) ⟫.
  Proof.
    unfold prefixes.
    destruct (constructive_indefinite_description
                _ (partial_order_included_in_total_order PO)) as [t [INCL TOT]]; ins.
    exists t; splits; auto using StronglySorted_isort.
  Qed.

  Lemma nodup_prefixes a : NoDup (prefixes a).
  Proof.
    assert (X := sorted_prefixes a); ins; desf.
    eapply NoDup_StronglySorted; try apply TOT; auto.
  Qed.

  Lemma prefixes_r n a b :
    list_before (prefixes n) a b -> r b a -> False.
  Proof.
    assert (X := sorted_prefixes n);
      unfold list_before; ins; desf.
    rewrite H1 in *.
    apply StronglySorted_app_r, StronglySorted_inv, proj2 in SORT.
    rewrite Forall_app, Forall_cons in SORT; desc.
    apply INCL in H0; eapply TOT; eapply TOT; eauto.
  Qed.

End prefixes.

Section enum_ext.

  Variable A : Type.
  Variable s : A -> Prop.
  Variable f : nat -> A.
  Variable r : relation A.
  Variable PO : strict_partial_order r.
  Variable F : fsupp r.

  Fixpoint prefix_of_nat n :=
    let prev := match n with
                  0 => nil
                | S n => prefix_of_nat n
                end in
    prev ++ filterP (fun x => ~ In x prev /\ s x) (prefixes PO F (f n) ++ f n :: nil).

  Lemma prefix_of_nat_prefix i j (LEQ : i <= j) :
    exists l, prefix_of_nat j = prefix_of_nat i ++ l.
  Proof.
    apply le_plus_minus in LEQ; rewrite LEQ; generalize (j - i) as n.
    clear; intro n; rewrite Nat.add_comm; induction n; ins; desf; eauto using app_nil_end.
    by rewrite IHn; eexists; rewrite <- app_assoc.
  Qed.

  Lemma in_prefix_of_nat_iff a n :
    In a (prefix_of_nat n) <-> exists i, i <= n /\ r^? a (f i) /\ s a.
  Proof.
    unfold clos_refl; induction n; ins; in_simp;
      repeat (rewrite ?in_app_iff, ?in_prefixes; ins; in_simp).
      intuition; desf; eauto; try (destruct i; ins; desf; eauto; omega).
    rewrite IHn; clear IHn; intuition; desf; try solve [exists i; splits; auto]; eauto.
    all: destruct (eqP i (S n)); [desf|assert (i <= n) by omega]; eauto 8.
    all: classical_right; splits; ins; eauto.
  Qed.

  Lemma in_prefix_of_nat i j (LEQ: i <= j) (S : s (f i)) : In (f i) (prefix_of_nat j).
  Proof.
    apply prefix_of_nat_prefix in LEQ; desf.
    rewrite LEQ; apply in_or_app; left.
    destruct i; ins; rewrite filterP_app; ins; desf;
      rewrite ?in_app_iff in *; ins; desf; tauto.
  Qed.


  Lemma in_prefix_of_nat_in x n : In x (prefix_of_nat n) -> s x.
  Proof.
    induction n; ins; rewrite ?in_app_iff in *; in_simp.
    rewrite in_app_iff in *; desf; eauto.
  Qed.

  Lemma nodup_prefix_of_nat n : NoDup (prefix_of_nat n).
  Proof.
    destruct PO;
    induction n; ins.
    all: repeat first [apply conj | apply nodup_filterP | rewrite nodup_app |
                       rewrite nodup_cons | apply nodup_prefixes ]; ins.
    all: red; ins; in_simp; desf; rewrite in_prefixes in *; eauto.
  Qed.

  Lemma length_prefix_of_nat n (INJ : forall i j, i < j <= n -> f i <> f j)
    (SET : forall i, i <= n -> s (f i)) :
    n < length (prefix_of_nat n).
  Proof.
    assert (exists l, Permutation (prefix_of_nat n) (map f (List.seq 0 (S n)) ++ l)).
    2: desc; rewrite H, length_app, length_map, length_seq; omega.
    generalize (prefix_of_nat n), (fun i => @in_prefix_of_nat i n).
    induction n; ins.
      by forward apply (H 0); ins; eauto; apply in_split_perm.
      forward apply (H (S n)); ins; eauto.
    forward apply IHn as X; intros; eauto.
      apply INJ; omega.
    desf.
    rewrite X, in_app_iff, in_map_iff in H0; desf.
    rewrite in_seq0_iff in *; eapply INJ in H0; try omega.
    apply in_split_perm in H0; desf.
    by exists l'; rewrite X, H0, <- (Nat.add_1_r (S n)), seq_app, map_app, <- app_assoc.
  Qed.

  Lemma list_app_eq_simpl (l l0 l' l0' : list A) :
    l ++ l' = l0 ++ l0' ->
    length l <= length l0 -> exists lr, l0 = l ++ lr /\ l' = lr ++ l0'.
  Proof.
    revert l0; induction l; ins; eauto.
    destruct l0; ins; desf; try omega.
    eapply IHl in H; desf; eauto; omega.
  Qed.

  Lemma list_app_eq_simpl2 (a : A) (l l0 l' l0' : list A) :
    l ++ a :: l' = l0 ++ l0' ->
    length l < length l0 -> exists lr, l0 = l ++ a :: lr /\ l' = lr ++ l0'.
  Proof.
    change (l ++ a :: l') with (l ++ (a :: nil) ++ l'); intros.
    rewrite app_assoc in H; apply list_app_eq_simpl in H; desf.
      by exists lr; rewrite <- app_assoc.
    rewrite length_app; ins; omega.
  Qed.

  Lemma prefix_nat_r n a b
        (P: list_before (prefix_of_nat n) a b)
        (R: r b a) : False.
  Proof.
    destruct PO as [IRR T].
    induction n; ins; rewrite filterP_app in *; ins; desf;
      rewrite ?app_nil_r; desf.
    all: repeat (rewrite list_before_app in *; desf;
                 try (eby eapply list_before_nil);
                 try (eby eapply list_before_singl); ins; desf); in_simp;
      try rewrite in_prefixes in *; eauto.
    all: try (rewrite ?in_app_iff in *; ins; desf; in_simp).
    all: try rewrite in_prefixes in *; eauto.
    all: try rewrite in_prefix_of_nat_iff in *; unfold clos_refl in *; desf; eauto 10.
    all: try (match goal with H: _ |- _ => eapply list_before_filterP_inv in H;
                                           [|by apply nodup_prefixes]
              end); eauto using prefixes_r.
  Qed.

  Lemma wlog_lt (Q : nat -> nat -> Prop) :
    (forall x, Q x x) -> (forall x y, x < y -> Q x y) -> (forall x y, y < x -> (forall x y, x < y -> Q x y) -> Q x y) -> forall x y, Q x y.
  Proof. ins; destruct (lt_eq_lt_dec x y) as [[]|]; desf; eauto. Qed.

  Lemma enum_ext (E: enumerates f s) :
    exists f, enumerates f s  /\
              forall i j (Li : lt_size i s) (Lj: lt_size j s)
                     (R: r (f i) (f j)), i < j.
  Proof.
    exists (fun n => nth n (prefix_of_nat n) (f 0)); split.
    { red in E; des; [left|right]; splits; try exists n; splits.
      { ins; destruct (nth_in_or_default i (prefix_of_nat i) (f 0)) as [X|X];
        [apply in_prefix_of_nat_in in X| rewrite X]; eauto. }
      { ins.
        revert EQ.
        apply wlog_lt with (x := i) (y := j); ins; [|by symmetry; eauto].
        assert (L: y < length (prefix_of_nat y)).
        { apply length_prefix_of_nat; eauto.
          red; intros; eapply INJ in H1; desf; omega. }
        assert (Lx: x < length (prefix_of_nat x)).
        { apply length_prefix_of_nat; eauto.
          red; intros; eapply INJ in H1; desf; omega. }
        forward apply prefix_of_nat_prefix with (i := x) (j := y) as X; desc; try omega.
        forward apply nodup_prefix_of_nat with (n:=y) as Y; try done.
        rewrite NoDup_nth with (d := f 0) in Y; apply Y; eauto; try omega.
        rewrite X at 1; rewrite nth_app; desf; omega. }
      { ins; apply SUR in IN; desf.
        forward apply in_prefix_of_nat with (i := i) (j := i) as X; ins.
        apply in_split in X; desf.
        exists (length l1).
        destruct (le_lt_dec i (length l1)) as [Y|Y].
          apply prefix_of_nat_prefix in Y; desc.
          rewrite Y, X, appA, nth_app; desf; try omega.
          rewrite Nat.sub_diag; done.
        forward apply (@prefix_of_nat_prefix (length l1) i) as Z; desc; try omega.
        forward apply length_prefix_of_nat with (n := length l1); eauto.
          red; intros; apply INJ in H0; desf; omega.
        rewrite Z in X; symmetry in X; ins.
        apply list_app_eq_simpl2 in X; desc; try omega.
        rewrite X, nth_app, Nat.sub_diag; ins; desf; omega. }
      { ins; destruct (nth_in_or_default i (prefix_of_nat i) (f 0)) as [X|X];
          [apply in_prefix_of_nat_in in X| rewrite X]; eauto.
        apply RNG; omega.
      }
      { ins.
        revert LTi LTj EQ.
        apply wlog_lt with (x := i) (y := j); ins; [|by symmetry; eauto].
        assert (L: y < length (prefix_of_nat y)).
        { apply length_prefix_of_nat; [|intros; apply RNG; omega].
          red; intros; eapply INJ in H1; desf; omega. }
        assert (Lx: x < length (prefix_of_nat x)).
        { apply length_prefix_of_nat; [|intros; apply RNG; omega].
          red; intros; eapply INJ in H1; desf; omega. }
        forward apply prefix_of_nat_prefix with (i := x) (j := y) as X; desc; try omega.
        forward apply nodup_prefix_of_nat with (n:=y) as Y; try done.
        rewrite NoDup_nth with (d := f 0) in Y; apply Y; eauto; try omega.
        rewrite X at 1; rewrite nth_app; desf; omega. }
      { ins; apply SUR in IN; desf.
        forward apply in_prefix_of_nat with (i := i) (j := i) as X; ins; eauto.
        apply in_split in X; desf.
        exists (length l1).
        destruct (le_lt_dec i (length l1)) as [Y|Y].
          apply prefix_of_nat_prefix in Y; desc.
          rewrite Y, X, appA, nth_app; desf; try omega.
          rewrite Nat.sub_diag; splits; ins.
          assert (length (prefix_of_nat i) <= n).
          { generalize (nodup_prefix_of_nat i),
              (fun x => in_prefix_of_nat_in x i).
            generalize (prefix_of_nat i); clear -SUR; ins.
            assert (X: forall x, In x l -> In x (map f (List.seq 0 n))).
              by intros; apply H0, SUR in H1; desf; apply in_map, in_seq0_iff.
            clear SUR H0.
            eapply NoDup_incl_length in X; ins.
            by rewrite length_map, length_seq in *. }
          rewrite X, length_app in *; ins; omega.
        forward apply (@prefix_of_nat_prefix (length l1) i) as Z; desc; try omega.
        forward apply length_prefix_of_nat with (n := length l1).
          red; intros; apply INJ in H0; desf; omega.
          intros; apply RNG; omega.
        rewrite Z in X; symmetry in X; ins.
        apply list_app_eq_simpl2 in X; desc; try omega.
        rewrite X, nth_app, Nat.sub_diag; splits; ins; desf; omega. }
    }
    intros.
    destruct (lt_eq_lt_dec j i) as [[]|]; ins; desf; exfalso; [|eby eapply PO].
    forward eapply prefix_of_nat_prefix with (i:=j) (j:=i) as X; try omega; desc.
    red in E; desf.
      forward eapply length_prefix_of_nat with (n := i) as LEN; try red; ins; desc; eauto.
        eapply INJ in H0; desf; omega.
      forward eapply length_prefix_of_nat with (n := j) as LENj; try red; ins; desc; eauto.
        eapply INJ in H0; desf; omega.
      forward apply list_before_nth with (l := prefix_of_nat i) (i := j) (j := i) (d := f 0);
        splits; ins; eauto using nodup_prefix_of_nat.
      rewrite X in H at 2; rewrite app_nth1 in H; eauto using prefix_nat_r.

    assert (Lin : i < n). {
      clear - SUR Li. red in Li; desc.
      eapply lt_le_trans; eauto.
      replace n with (length (map f (List.seq 0 n)))
                     by now (rewrite length_map, length_seq).
      apply NoDup_incl_length; try red; ins.
      by apply Li0, SUR in H; desf; apply in_map, in_seq0_iff.
    }
    forward eapply length_prefix_of_nat with (n := i) as LEN; try red; ins; desc; eauto.
      eapply INJ in H0; desf; omega.
      eapply RNG; omega.
    forward eapply length_prefix_of_nat with (n := j) as LENj; try red; ins; desc; eauto.
      eapply INJ in H0; desf; omega.
      eapply RNG; omega.
    forward apply list_before_nth with (l := prefix_of_nat i) (i := j) (j := i) (d := f 0);
        splits; ins; eauto using nodup_prefix_of_nat.
    rewrite X in H at 2; rewrite app_nth1 in H; eauto using prefix_nat_r.
  Qed.

End enum_ext.

Lemma countable_ext A (s : A -> Prop) (C: countable s)
      (r : relation A) (PO : strict_partial_order r) (F : fsupp r) :
  ~ inhabited A \/
  exists f,
    enumerates f s  /\
    forall i j (Li : lt_size i s) (Lj: lt_size j s)
           (R: r (f i) (f j)), i < j.
Proof.
  destruct C; desf; eauto using enum_ext.
Qed.
