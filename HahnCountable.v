(******************************************************************************)
(** * Countable sets *)
(******************************************************************************)

Require Import NPeano Omega Setoid ClassicalChoice.
Require Import HahnBase HahnList HahnEquational HahnRewrite.
Require Import HahnSets HahnNatExtra.

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


Fixpoint find_nthP A (cond : A -> Prop) (n : nat) (l : list A) :=
  match l with
  | nil => 0
  | h :: t =>
    if excluded_middle_informative (cond h) then
      match n with
      | 0 => 0
      | S n => S (find_nthP cond n t)
      end else S (find_nthP cond n t)
  end.

(*
Lemma find_nthP_spec A (cond : A -> Prop) (l l' : list A) n
      (ND: NoDup l') (LEN: n <= length l')
      (INCL: forall n, In n l' -> In n l)
      (COND: forall n, In n l' -> cond n) d :
  cond (nth (find_nthP cond n l) l d) /\
  length (undup (filterP s (mk_list n f)))
  forall j, j < findP cond l -> ~ cond (nth j l d).
Proof.
  subst; revert dependent l'.
  induction l; ins; desf; splits; ins; desf; try omega; intuition.
  eauto using lt_S_n.
Qed.
*)

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
