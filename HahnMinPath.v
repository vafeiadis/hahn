(******************************************************************************)
(** * Minimal paths and cycles *)
(******************************************************************************)

Require Import NPeano Omega.
Require Import HahnBase HahnList HahnRelationsBasic HahnRewrite.

Set Implicit Arguments.

Lemma mod_S_expand i n (NZ : n <> 0) : 
  (S i mod n) = if eq_op n 1 then 0 else if eq_op (S (i mod n)) n then 0 else S (i mod n).
Proof.
  desf; desf;
    rewrite Nat.add_mod with (a := 1); try done;
    rewrite (Nat.mod_small 1); try omega.
    by simpl; rewrite Heq0, Nat.mod_same.
  assert (UB := Nat.mod_upper_bound i n).
  rewrite (Nat.mod_small (1 + i mod n)); omega.
Qed.

Lemma mod_SS_expand i n : 
  (S i mod S n) = if eq_op n 0 then 0 else if eq_op (i mod (S n)) n then 0 else S (i mod (S n)).
Proof.
  by rewrite mod_S_expand; desf.
Qed.

Lemma eqmod_add_idemp_l n i j k :
  (k + i) mod n = (k + j) mod n <-> i mod n = j mod n.
Proof.
  destruct (eqP n 0); desf.
  rewrite !(Nat.add_mod k); try done.
  split; [intro L|by intros ->].
  rewrite !(Nat.add_mod_idemp_r) in L; try done.
  apply f_equal with (f := fun x => ((n - k mod n) + x) mod n) in L.
  rewrite !Nat.add_mod_idemp_r, !Nat.add_assoc, !Nat.sub_add in L; 
    eauto using Nat.mod_upper_bound, Nat.lt_le_incl. 
  do 2 (rewrite Nat.add_mod, Nat.mod_same, Nat.add_0_l, Nat.mod_mod in L; try done).
Qed.

Lemma eqmod_add_idemp_r n i j k :
  (i + k) mod n = (j + k) mod n <-> i mod n = j mod n.
Proof.
  by rewrite <- !(Nat.add_comm k); apply eqmod_add_idemp_l.
Qed.

Lemma eqmod_S n i j :
  S i mod n = S j mod n <-> i mod n = j mod n.
Proof.
  apply eqmod_add_idemp_l with (k := 1).
Qed.

Lemma get_first_nat (P : nat -> Prop) :
  (exists m, P m /\ forall k, P k -> m <= k) \/ forall k, ~ P k.
Proof.
  apply NNPP; intro X; apply not_or_and in X; desf.
  apply not_all_not_ex in X0; desf; destruct X. 
  revert P X0; induction n; ins.
    by exists 0; split; ins; desf; auto with arith. 
  destruct (classic (P 0)).
    by exists 0; split; ins; desf; auto with arith. 
  specialize (IHn (fun n => P (S n)) X0); desf.
  eexists (S m); split; ins; eauto.
  destruct k; try done; eauto using le_n_S.
Qed.

Lemma get_max_bounded_nat (P : nat -> Prop) x n (LE: x <= n) (SAT: P x) :
  exists m, m <= n /\ P m /\ forall k, k <= n -> P k -> k <= m.
Proof.
  destruct get_first_nat with (P := fun x => P (n - x)); desf.
  exists (n - m); repeat split; ins; eauto; try omega. 
  replace k with (n - (n - k)) in H2; [apply H0 in H2|]; omega.
  destruct (H (n - x)).
  replace (n - (n - x)) with x; eauto; omega.
Qed.

Lemma path_minimize :
  forall X (r : relation X) a b
    (PATH: r⁺ a b),
    exists f n, 
      << START: f 0 = a >> /\ 
      << END: f (S n) = b >> /\
      << STEP: forall i (LT: i <= n), r (f i) (f (S i)) >> /\
      << MIN: forall i (LTi: i <= n) j (LTj: i < j <= S n), 
                r (f i) (f j) -> j = S i >> .
Proof.
  ins; apply clos_trans_tn1 in PATH; induction PATH; desf; unnw.
    exists (fun x => match x with 0 => a | S _ => y end), 0; intuition; try omega. 
      by apply NPeano.Nat.le_0_r in LT; desf.

  destruct (get_first_nat (fun x => x <= n /\ r (f x) z)) as [(m & M)|M]; desc.
  { exists (fun x => if Compare_dec.le_dec x m then f x else z), m;
    repeat split; ins; desf; try omega.
      by eapply STEP; omega.
    by assert (i = m) by omega; desf. 
    by eapply MIN; eauto; omega.
    assert (j = S m) by omega; desf.
    specialize (M0 i); specialize_full M0; try split; ins; omega. }
  { exists (fun x => if Compare_dec.le_dec x (S n) then f x else z), (S n);
    repeat split; ins; desf; try omega.
      by eapply STEP; omega.
    assert (i = S n) by omega; desf. 
    eapply MIN; eauto; try omega.
    destruct (eqP i (S n)); desf; try omega.
    destruct (M i); split; ins; omega. }
Qed.

Structure min_cycle_mod X (r : relation X) (f : nat -> X) (n : nat) : Prop := 
  { mp_nonzero : n <> 0
  ; mp_modulo : forall x, f x = f (x mod n) 
  ; mp_step : forall i, r (f i) (f (S i)) 
  ; mp_min  : forall i j, r (f i) (f j) -> j mod n = (S i) mod n }.

Lemma min_cycle_nodup X (r : relation X) f n (MC : min_cycle_mod r f n) 
      i j (EQ: f i = f j) : i mod n = j mod n.
Proof.
  apply eqmod_S.
  by erewrite <- (mp_min MC); [|rewrite EQ; apply (mp_step MC)]. 
Qed.  

Lemma min_cycle_step X (r : relation X) f n (MC : min_cycle_mod r f n) 
      i j : r (f i) (f j) <-> j mod n = S i mod n.
Proof.
  destruct MC as [NZ MOD STEP MIN]; split; ins; eauto.
  by rewrite (MOD i), (MOD j), H, <- !MOD; auto.
Qed.

Lemma min_cycle_wlog X (r : relation X) f n (MC : min_cycle_mod r f n) 
      i (P : X -> Prop) (PROP: P (f i)) : 
  exists f, << MC : min_cycle_mod r f n >> /\ << PROP : P (f 0) >>.
Proof.
  exists (fun x => f (x + i)); unnw; repeat split; ins; try apply MC.
    by rewrite !(mp_modulo MC (_ + i)), Nat.add_mod_idemp_l; try apply MC.
  eby rewrite (min_cycle_step MC) in *; eapply eqmod_add_idemp_r.
Qed.


Lemma acyclic_minimize1 X (r : relation X) :
  acyclic r <->
  ~ exists f n, 
      << ENDS: f 0 = f (S n) >> /\ 
      << STEP: forall i (LT: i <= n), r (f i) (f (S i)) >> /\
      << MIN: forall i (LTi: i <= n) j (LTj: j <= S n), 
                r (f i) (f j) -> j = S i \/ i = n /\ j = 0 >>.
Proof.
  split; repeat red; ins; desf.
  { destruct (H (f 0)).
    rewrite ENDS at 2; clear - STEP.
    induction n; vauto.
      by apply t_step, STEP.
    by eapply t_trans, t_step; eauto. }
  apply path_minimize in H0; desf.
  destruct H; unnw.
  destruct (get_first_nat (fun x => x <= n /\ exists mm, mm <= x /\ 
                                                         r (f x) (f mm))) 
    as [(m & M & M'')|M]; desc.
  assert (M' : forall k k', k' <= k -> k <= n -> r (f k) (f k') -> m <= k).
    by ins; apply M''; eauto.
  clear M''.
  { 
    forward eapply get_max_bounded_nat 
    with (P := fun x => r (f m) (f x)) (x := mm) (n := m) as [kk K]; ins; desc.
    clear mm M0 M1; rename kk into mm.
    exists (fun x => if eq_op x (S (m - mm)) then (f mm) else (f (x + mm))), (m - mm); 
      repeat split; ins; desf; desf; try omega.
    by rewrite NPeano.Nat.sub_add.
    eapply STEP; omega.
    left; apply M' in H; omega.  
    destruct (eqP j 0); desf; ins.
      right; apply M' in H; omega.
    left; apply MIN in H; try split; try omega. 
    apply NNPP; intro K'.
    assert (Z:=H); apply M' in Z; try omega.
    assert (i = m - mm) by omega; subst.
    rewrite Nat.sub_add in *; ins; apply K1 in H; omega.
  }
  { exists f, n;
    repeat split; ins; desf; try omega. 
    destruct (le_lt_dec j i); [edestruct M|]; eauto.
 }
Qed.



Lemma acyclic_no_min_cycle X (r : relation X) :
  acyclic r <-> ~ exists f n, min_cycle_mod r f n. 
Proof.
  rewrite acyclic_minimize1; split; intros A B; destruct A; desc.
  { destruct B as [NZ MOD STEP MIN]; destruct n; try done. 
    exists f, n; unnw; repeat split; intros; try done; eauto.
    by rewrite (MOD (S n)), Nat.mod_same.
    apply MIN in H.
    destruct (eqP i n), (eqP j (S n)); subst; auto;
      rewrite ?Nat.mod_same, ?Nat.mod_small in H; omega. 
  }
  exists (fun x => f (x mod (S n))), (S n); split; intros; try done.
  - by rewrite Nat.mod_mod.
  - assert (UB := Nat.mod_upper_bound i (S n)).
    exploit (STEP (i mod S n)); try omega.
    rewrite mod_SS_expand; desf; desf. 
      by rewrite !Nat.mod_1_r, ENDS.
    by rewrite Heq0, ENDS.
  - assert (UBi := Nat.mod_upper_bound i (S n)).
    assert (UBj := Nat.mod_upper_bound j (S n)).
    apply MIN in H; try omega.
    rewrite mod_SS_expand; desf; desf; omega.
Qed.


Lemma acyclic_minimize X (r : relation X) :
  acyclic r <->
  ~ exists f n, 
      << ENDS: f 0 = f (S n) >> /\ 
      << STEP: forall i (LT: i <= n), r (f i) (f (S i)) >> /\
      << MIN: forall i (LTi: i <= n) j (LTj: j <= S n), 
                r (f i) (f j) -> j = S i \/ i = n /\ j = 0 >> /\
      << NODUP: forall i (LTi: i <= S n) j (LTj: j <= S n), 
                  f i = f j -> 
                  i = j \/ i = 0 /\ j = S n \/ 
                           i = S n /\ j = 0 >>.
Proof.
  rewrite acyclic_minimize1. 
  split; intros A B; destruct A; desc; unnw; eauto. 
  exists f, n; repeat split; ins; eauto.
  destruct (lt_dec i j).
    destruct j; [exfalso; omega|]; ins; auto. 
    specialize (STEP j); specialize_full STEP; try omega.
    rewrite <- H in STEP; eapply MIN in STEP; try omega.
  destruct (lt_dec j i); try omega.
  destruct i; [exfalso; omega|]; ins; auto. 
  specialize (STEP i); specialize_full STEP; try omega.
  rewrite H in STEP; eapply MIN in STEP; try omega.
Qed.

(** Minimum cycle lemma *)

Lemma min_cycle X (r r' : relation X) (dom : X -> Prop)
    (TOT: is_total dom r') 
    (T : transitive r')
    (INCL: r' ⊆ r⁺)
    (INV: irreflexive (r ⨾ r')) :
    acyclic r <->
    acyclic (restr_rel (fun x => ~ dom x) r) /\
    (forall x (CYC: r x x) (D: dom x), False) /\
    (forall c1 b1 (R: r c1 b1) b2 
       (S : r'^? b1 b2) c2 
       (R': r b2 c2) (S': clos_refl_trans (restr_rel (fun x => ~ dom x) r) c2 c1)
       (D1 : dom b1) (D2: dom b2) (ND1: ~ dom c1) (ND2: ~ dom c2), False).
Proof.
  split; intros A; repeat split; ins; desc; eauto.
    by intros x P; eapply A, clos_trans_mon; eauto; unfold restr_rel; ins; desf.
    by eauto using t_step.
    eapply (A c1), t_trans, rt_t_trans, t_rt_trans; eauto using t_step;
      try (by eapply clos_refl_trans_mon; eauto; unfold restr_rel; ins; desf).
    by red in S; desf; eauto using clos_refl_trans, clos_trans_in_rt.
  assert (INCL': forall a b (R: r a b) (D: dom a) (D': dom b), r' a b).
    by unfold seq in *; ins; destruct (classic (a = b)) as [|N]; 
       [|eapply TOT in N]; desf; exfalso; eauto.
  intros x P.

  assert (J: clos_refl_trans (restr_rel (fun x : X => ~ dom x) r) x x \/
             r' x x /\ dom x /\ dom x \/
          dom x /\ (exists m n k, r'^? x m /\ r m n /\
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) r) n k 
            /\ r^? k x 
            /\ dom m /\ ~ dom n /\ ~ dom k) \/
          (exists k m,
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) r) x k /\
            r k m /\ r'^? m x /\
            ~ dom k /\ dom m /\ dom x) \/
          (exists k m m' n,
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) r) x k /\
            r k m /\ r'^? m m' /\ r m' n /\
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) r) n x /\
            ~ dom k /\ dom m /\ dom m' /\ ~ dom n)).
    by vauto.
  revert P J; generalize x at 1 4 6 8 11 13 14 16.
  unfold restr_rel in *; ins; apply clos_trans_tn1 in P; induction P; eauto.
  { rename x0 into x; desf; eauto.
    destruct (classic (dom x)); rewrite clos_refl_transE in *; desf; eauto using clos_trans. 
      by destruct (clos_trans_restrD J); desf. 
    by destruct (clos_trans_restrD J); eapply A, t_trans, t_step; vauto. 
    by eapply INV; vauto.

    unfold clos_refl in J3; desf.
      by eapply A1 with (c1 := x) (b2 := m); eauto using rt_trans, rt_step.
    destruct (classic (dom x)).
      by eapply A1 with (c1 := k) (b2 := m); eauto; 
         unfold clos_refl in *; desf; eauto.
    by eapply A1 with (c1 := x) (b2 := m); eauto using rt_trans, rt_step.

    destruct (classic (dom y)).
      by rewrite clos_refl_transE in J; desf; 
         destruct (clos_trans_restrD J); desf.
    by eapply A1 with (c1 := k) (b2 := x); eauto 8 using rt_trans, rt_step.

    destruct (classic (dom x)).
      by rewrite clos_refl_transE in J3; desf; destruct (clos_trans_restrD J3); desf. 
    destruct (classic (dom y)).
      by rewrite clos_refl_transE in J; desf; destruct (clos_trans_restrD J); desf. 
    by eapply A1 with (c1 := k) (b2 := m'); eauto 8 using rt_trans, rt_step.
  }
  eapply clos_tn1_trans in P; desf.
  {
    destruct (classic (dom y)).
      rewrite clos_refl_transE in J; desf.
        destruct (classic (dom x0)).
          by eapply IHP; right; left; eauto using t_step.
        eapply IHP; do 2 right; left; split; ins.
        by eexists y,x0,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
      destruct (clos_trans_restrD J).
      apply IHP; right; right; left; split; ins.
      by eexists y,z,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
    rewrite clos_refl_transE in J; desf.
      destruct (classic (dom x0)).
        eapply IHP; do 3 right; left.
        by eexists y,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
      by eapply IHP; left; vauto.
    by destruct (clos_trans_restrD J); eapply IHP; left; 
       eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
  }
  {
    destruct (classic (dom y)).
      by apply IHP; eauto 8 using clos_trans.
    apply IHP; do 3 right; left; eexists y, z; 
    repeat eexists; vauto; eauto using clos_trans_in_rt. 
  }
  { destruct (classic (dom y)).
      by eapply IHP; do 2 right; left; split; ins; eexists m; repeat eexists; 
         eauto; red in J0; red; desf; eauto. 
    destruct (classic (dom x0)).
    
    destruct (classic (m = x0)) as [|NEQ]; subst.
      by eapply IHP; do 3 right; left; eexists y,z; repeat eexists; vauto. 
    eapply TOT in NEQ; desf.
      by eapply IHP; do 3 right; left; eexists y,z; repeat eexists; vauto;
         eauto; red; red in J0; desf; eauto. 
    by red in J3; desf; eapply A1 with (c1 := k) (b2 := m); 
       eauto 8 using rt_trans, rt_step, clos_trans_in_rt.

    by eapply IHP; do 4 right; eexists y,z; repeat eexists; vauto; 
       unfold clos_refl in *; desf; vauto.
  }

  { destruct (classic (dom z)).
      by rewrite clos_refl_transE in J; desf; 
         destruct (clos_trans_restrD J); desf.
    destruct (classic (y = m)) as [|NEQ]; desf.
      by unfold clos_refl in *; desf; eauto.
    destruct (classic (dom y)).
      eapply TOT in NEQ; desf.
        by unfold clos_refl in *; desf; 
           apply IHP; right; left; eauto using t_rt_trans, t_step.
      by eapply A1 with (c1 := k) (b2 := y); 
         eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
    by eapply IHP; do 3 right; left; eexists k, m; repeat eexists; vauto.
  }

    destruct (classic (dom x0)).
      by rewrite clos_refl_transE in J3; desf; destruct (clos_trans_restrD J3); desf. 
    destruct (classic (dom z)).
      by rewrite clos_refl_transE in J; desf; destruct (clos_trans_restrD J); desf. 
    destruct (classic (y = m)) as [|NEQ]; desf.
      by eapply IHP; do 2 right; left; split; ins; eexists m', n; repeat eexists; vauto.
    destruct (classic (dom y)).
      eapply TOT in NEQ; desf.
        by unfold clos_refl in *; desf; eapply IHP; do 2 right; left; split; ins; 
           eexists m', n; repeat eexists; vauto;
           eauto using rt_trans, clos_trans_in_rt.
      by eapply A1 with (c1 := k) (b2 := y); 
         eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
    by eapply IHP; do 4 right; eexists k,m,m'; repeat eexists; vauto.
Qed.

Lemma min_cycle1 X (r r' : relation X) (d : X -> Prop)
    nd (ND: nd = fun x => ~ d x)
    (TOT: is_total d r')
    (T : transitive r')
    (INCL: r' ⊆ r⁺)
    (INV: irreflexive (r ⨾ r')) :
    acyclic r <->
    acyclic (⦗nd⦘ ⨾ r ⨾ ⦗nd⦘) /\
    irreflexive (⦗d⦘ ⨾ r ⨾ ⦗d⦘) /\
    irreflexive (⦗nd⦘ ⨾ r ⨾ ⦗d⦘ ⨾ r'^? ⨾ ⦗d⦘ ⨾
                 r ⨾ ⦗nd⦘ ⨾ (⦗nd⦘ ⨾ r ⨾ ⦗nd⦘)＊).
Proof.
  assert (AA: restr_rel nd r ≡ ⦗nd⦘⨾ r⨾ ⦗nd⦘).
    by red; unfold seq, eqv_rel, restr_rel, inclusion in *; split; ins; desf; eauto 10.
  forward (eapply min_cycle; eauto) as N; subst; rewrite N, <- !AA; clear.
  unfold irreflexive, seq, eqv_rel;
  split; ins; desf; splits; ins; desf; eauto.
    by eapply H0; eauto 10.
  by apply (H1 c1); repeat eexists; eauto.
Qed.

