Require Import NPeano Arith micromega.Lia Setoid HahnBase.

Lemma div2_add_double n m :
  Nat.div2 (2 * n + m) = n + Nat.div2 m.
Proof.
  induction n; ins.
  rewrite Nat.add_0_r in *.
  rewrite (Nat.add_comm n); ins; f_equal; ins.
Qed.

Lemma add_eq_zero n m : n + m = 0 <-> n = 0 /\ m = 0. 
Proof. lia. Qed.

(*****************************************************************************)
(** Sum of arithmetic series *)
(*****************************************************************************)

Definition arith_sum n := Nat.div2 (n * S n). 

Lemma arith_sum_0 : arith_sum 0 = 0.
Proof. done. Qed.

Lemma arith_sum_S n : arith_sum (S n) = arith_sum n + S n.
Proof.
  unfold arith_sum.
  replace (S n * (S (S n))) with (2 * (S n) + n * (S n)).
    rewrite div2_add_double; lia.
  rewrite (Nat.mul_comm _ (S (S n))); simpl; lia.
Qed.  
    
Lemma arith_sum_double n : arith_sum n * 2 = n * S n.
Proof.
  induction n; try done.
  rewrite arith_sum_S, (Nat.mul_comm _ (S (S n))); simpl; lia.
Qed.

Lemma arith_sum_le_mono n m (L : n <= m) : arith_sum n <= arith_sum m.
Proof.
  apply le_plus_minus in L; rewrite L; clear L; generalize (m - n) as k; ins.
  rewrite Nat.add_comm; induction k; ins.
  rewrite arith_sum_S; lia.
Qed.

Lemma arith_sum_lt n m (L : n < m) : arith_sum n + n < arith_sum m.
Proof.
  apply le_plus_minus in L; rewrite L; clear L; generalize (m - S n) as k; intros.
  replace (S n + k) with (S (n + k)) by done.
  rewrite arith_sum_S.
  forward apply (arith_sum_le_mono n (n + k)); lia.
Qed.

Lemma arith_sum_lt_mono n m (L : n < m) : arith_sum n < arith_sum m.
Proof.
  forward apply (arith_sum_lt n m); lia.
Qed.

Lemma arith_sum_inj n m (EQ: arith_sum n = arith_sum m) :
  n = m.
Proof.
  destruct (lt_eq_lt_dec n m) as [[A|A]|A]; desf; try lia.
  all: apply arith_sum_lt in A; lia.
Qed.

Lemma arith_sum_inj_gen n n' (Ln: n' <= n) m m' (Lm: m' <= m)
      (EQ: arith_sum n + n' = arith_sum m + m') :
  n = m /\ n' = m'.
Proof.
  destruct (lt_eq_lt_dec n m) as [[A|A]|A]; desf; try lia.
  all: apply arith_sum_lt in A; lia.
Qed.

(** [find_max f n] returns the maximum number below [n] that satisfies [f]. *)

Fixpoint find_max (f: nat -> bool) (n : nat) :=
  match n with
  | 0 => 0
  | S m => if f n then n else find_max f m
  end.

Lemma find_max_sat (f : nat -> bool) n (F: f 0) : f (find_max f n).
Proof.
  induction n; ins; desf.
Qed.  

Lemma find_max_sat2 (f : nat -> bool) n (F: f 0) (G: f (S n) = false) :
  f (find_max f n) /\ f (S (find_max f n)) = false.
Proof.
  induction n; ins; desf; eauto.
Qed.  

(** [invert_nat_fun f n] returns the maximum [x <= n] such that [f x <= n]. *)

Definition invert_nat_fun (f : nat -> nat) (y : nat) :=
  find_max (fun x => f x <=? y) y.

Lemma invert_nat_fun_sat f y (F : f 0 <= y) :
  f (invert_nat_fun f y) <= y.
Proof.
  apply Nat.leb_le, find_max_sat with (f := fun x => f x <=? y) .
  apply Nat.leb_le; done.
Qed.  

Lemma invert_nat_fun_sat2 f y (F : f 0 <= y < f (S y)) :
  f (invert_nat_fun f y) <= y < f (S (invert_nat_fun f y)).
Proof.
  rewrite <- Nat.leb_le in *.
  rewrite <- Nat.ltb_lt in *; desc.
  rewrite Nat.ltb_antisym, Bool.negb_true_iff in *.
  apply find_max_sat2 with (f := fun x => f x <=? y); ins.
Qed.  

(*****************************************************************************)
(** Bijection between [Nat * Nat] and [Nat] *)
(*****************************************************************************)

Definition nat_tup (n1 n2 : nat) :=
  arith_sum (n1 + n2) + n1.

Definition nat_fst (n : nat) : nat :=
  let p := invert_nat_fun arith_sum n in
  n - arith_sum p.

Definition nat_snd (n : nat) : nat :=
  let p := invert_nat_fun arith_sum n in
  p - (n - arith_sum p).

Lemma nat_tup_inj n1 n2 m1 m2
      (EQ: nat_tup n1 n2 = nat_tup m1 m2) : 
  n1 = m1 /\ n2 = m2.
Proof.
  eapply arith_sum_inj_gen in EQ; lia.
Qed.

Lemma nat_tup_eta n :
  nat_tup (nat_fst n) (nat_snd n) = n.
Proof.
  forward eapply invert_nat_fun_sat2
    with (f := arith_sum) (y := n) as X.
    rewrite arith_sum_0, arith_sum_S; ins; lia.
  rewrite arith_sum_S in *; unfold nat_tup.
  replace (nat_fst n + nat_snd n)
    with (invert_nat_fun arith_sum n).
  all: unfold nat_fst, nat_snd; lia.
Qed.

Lemma nat_fst_tup n m : nat_fst (nat_tup n m) = n.
Proof.
  apply (nat_tup_inj _ _ _ _ (nat_tup_eta _)).
Qed.
  
Lemma nat_snd_tup n m : nat_snd (nat_tup n m) = m.
Proof.
  apply (nat_tup_inj _ _ _ _ (nat_tup_eta _)).
Qed.
