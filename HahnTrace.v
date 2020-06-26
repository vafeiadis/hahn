(******************************************************************************)
(** * Lemmas about traces (finite or infinite sequences) *)
(******************************************************************************)

Require Import HahnBase HahnList HahnSets HahnRelationsBasic.
Require Import HahnOmega HahnWf.
Require Import Omega IndefiniteDescription.

Set Implicit Arguments.

Lemma set_infinite_natE (s : nat -> Prop) (INF: ~ set_finite s) n :
  exists m, s m /\ length (filterP s (List.seq 0 m)) = n.
Proof.
  assert (IMP: forall findom, exists x, s x /\ ~ In x findom).
  { unfold set_finite in *; apply NNPP; intro X; clarify_not.
    eapply INF; eexists; ins; apply NNPP; intro Y; eauto. }
  apply functional_choice in IMP; destruct IMP as [nin IMP].
  assert (exists m, s m /\ n <= length (filterP s (List.seq 0 m))).
  { induction n; desf.
    1: exists (nin nil); split; [apply IMP | omega].
    exists (nin (List.seq 0 (S m))); split; [apply IMP|].
    rewrite seq_split0 with (a := m).
    rewrite filterP_app, length_app; ins; desf; ins; omega.
    specialize (IMP (List.seq 0 (S m))); desf.
    rewrite in_seq0_iff in IMP0; omega. }
  desf; rewrite Nat.le_lteq in *; desf; eauto.
  clear - H0; induction m; ins.
  replace (List.seq 0 0) with (@nil nat) in H0; ins; omega.
  replace (S m) with (m + 1) in H0; try omega.
  rewrite seq_add, filterP_app, length_app in H0; ins.
  replace (List.seq m 1) with (m :: nil) in H0; ins; desf; ins.
  1: rewrite Nat.add_1_r, Nat.lt_succ_r, Nat.le_lteq in *; desf; eauto.
  rewrite Nat.add_0_r in *; eauto.
Qed.

(** Prepend a finite list to an infinite sequence *)

Definition trace_prepend A (l : list A) (fl : nat -> A) n :=
  if Nat.ltb n (length l) then nth n l (fl 0)
  else fl (n - length l).


(******************************************************************************)
(** Lemmas about [trace_prepend] *)
(******************************************************************************)

Lemma trace_prepend_fst A (l: list A) fl n (LT : n < length l) :
  trace_prepend l fl n = nth n l (fl 0).
Proof.
  unfold trace_prepend; desf; f_equal; omega.
Qed.

Lemma trace_prepend_fst0 A (l: list A) fl x :
  trace_prepend (x :: l) fl 0 = x.
Proof.
  ins.
Qed.

Lemma trace_prepend_snd A (l: list A) fl n :
  trace_prepend l fl (length l + n) = fl n.
Proof.
  unfold trace_prepend; desf; f_equal; omega.
Qed.

Lemma trace_prepend_snd0 A (l: list A) fl :
  trace_prepend l fl (length l) = fl 0.
Proof.
  unfold trace_prepend; desf; f_equal; omega.
Qed.

Lemma trace_prepend_app A (l l' : list A) fl :
  trace_prepend (l ++ l') fl = trace_prepend l (trace_prepend l' fl).
Proof.
  unfold trace_prepend; extensionality n.
  rewrite length_app, nth_app; desf; try omega.
  all: first [apply nth_indep | f_equal]; omega.
Qed.

Hint Rewrite
     filterP_app
     length_app
     trace_prepend_fst0
     trace_prepend_snd
     trace_prepend_snd0
     trace_prepend_app : trace_prepends.

Lemma map_trace_prepend_geq A (l: list A) fl n (LT: length l <= n) :
  map (trace_prepend l fl) (List.seq 0 n) =
    l ++ map fl (List.seq 0 (n - length l)).
Proof.
  unfold trace_prepend.
  rewrite seq_split with (x := length l); ins.
  rewrite map_app.
  rewrite map_nth_seq with (d := fl 0); [|by ins; desf].
  rewrite map_seq_shift with (g := fl) (b := 0); ins.
  desf; try f_equal; omega.
Qed.

Lemma map_trace_prepend_lt A (l: list A) fl n (LT: n < length l) :
  exists l' a l'',
    l = l' ++ a :: l'' /\ length l' = n /\
    map (trace_prepend l fl) (List.seq 0 n) = l'.
Proof.
  unfold trace_prepend.
  destruct (Nat.le_exists_sub n (length l)) as (p & X & _);
    try omega.
      rewrite Nat.add_comm in X.
  apply length_eq_add in X; desf.
  rewrite length_app in *; destruct l''; ins; try omega.
  repeat eexists.
  eapply map_nth_seq with (d := fl 0); ins; desf; try omega.
  rewrite nth_app; desf; try omega.
Qed.


Lemma set_finite_prepend A (l : list A) (fl : nat -> A) (f : A -> Prop) :
  set_finite (set_map (trace_prepend l fl) f) <-> set_finite (set_map fl f).
Proof.
  unfold trace_prepend, set_finite, set_map.
  split; ins; desf.
  { exists (map (fun x => x - length l) findom); intro y; ins.
    rewrite in_map_iff.
    specialize (H (y + length l)); desf; eauto; try omega.
    exists (y + length l); rewrite Nat.add_sub in *; eauto. }
  { exists (List.seq 0 (length l) ++ map (fun x => x + length l) findom);
    intro y; ins.
    rewrite in_app_iff, in_seq0_iff, in_map_iff; desf; eauto.
    apply H in IN.
    right; eexists; split; eauto; omega.
  }
Qed.

(******************************************************************************)
(** Finite or infinite traces of [A] elements. *)
(******************************************************************************)

Inductive trace (A : Type) : Type :=
| trace_fin (l : list A)
| trace_inf (fl : nat -> A).

Definition trace_finite A (t : trace A) :=
  exists l, t = trace_fin l.

(** [trace_app] concatenates two traces *)

Definition trace_app A (t t' : trace A) :=
  match t, t' with
  | trace_fin l, trace_fin l' => trace_fin (l ++ l')
  | trace_fin l, trace_inf f =>
    trace_inf (trace_prepend l f)
  | trace_inf f, _ => trace_inf f
  end.

(** [trace_map f t] applies [f] to all the elements of [t] *)

Definition trace_map A B (f : A -> B) (t : trace A) : trace B :=
  match t with
  | trace_fin l => trace_fin (map f l)
  | trace_inf fl => trace_inf (fun x => f (fl x))
  end.

(** Returns the length of a trace *)

Definition trace_length A (t : trace A) : nat_omega :=
  match t with
  | trace_fin l => NOnum (length l)
  | trace_inf fl => NOinfinity
  end.

(** [trace_elems t] returns true iff [a] is an element of the trace [t] *)

Definition trace_elems A (t : trace A) :=
  match t with
  | trace_fin l => (fun a => In a l)
  | trace_inf fl => (fun a => exists n, a = fl n)
  end.

(** [trace_nth n t d] returns the [n]th element of trace [t]
   or the default element [d], if [n] exceeds the trace's length. *)

Definition trace_nth (n : nat) A (t : trace A) (d : A) : A :=
  match t with
  | trace_fin l => nth n l d
  | trace_inf fl => fl n
  end.

(** [trace_filter f t] returns the sub-trace of [t] whose elements
satisfy the predicate [f]. *)

Definition trace_filter A (f : A -> Prop) (t : trace A) : trace A :=
  match t with
  | trace_fin l => trace_fin (filterP f l)
  | trace_inf fl =>
    let s := excluded_middle_informative (set_finite (set_map fl f)) in
    match s with
    | left FIN =>
        let B := set_finite_nat_bounded FIN in
        let n := proj1_sig (constructive_indefinite_description _ B) in
        trace_fin (filterP f (map fl (List.seq 0 (S n))))
    | right INF =>
        trace_inf
          (fun n =>
           let H := set_infinite_natE INF n in
           let H0 := constructive_indefinite_description _ H in
           fl (proj1_sig H0))
    end
  end.

(** Is a trace a prefix of another trace? *)

Definition trace_prefix A (t t' : trace A) :=
  match t, t' with
  | trace_fin l, trace_fin l' => exists l'', l' = l ++ l''
  | trace_fin l, trace_inf f => forall i (LLEN: i < length l) d, f i = nth i l d
  | trace_inf f, trace_fin _ => False
  | trace_inf f, trace_inf f' => forall x, f x = f' x
  end.

(** Is the trace duplicate-free? *)

Definition trace_nodup A (t: trace A) :=
  forall i j (LTi: i < j) (LTj: NOmega.lt_nat_l j (trace_length t)) d,
    trace_nth i t d <> trace_nth j t d.

(** Is [e] before [e'] in the duplicate-free trace [t]? *)

Definition trace_order A (t: trace A) e e' :=
  trace_nodup t /\
  (exists i j, i < j /\ NOmega.lt_nat_l j (trace_length t)
              /\ trace_nth i t e = e /\ trace_nth j t e = e').


(******************************************************************************)
(** Basic lemmas *)
(******************************************************************************)

Lemma trace_nth_indep (n : nat) A (t : trace A)
      (LT : NOmega.lt_nat_l n (trace_length t)) (d d' : A) :
  trace_nth n t d = trace_nth n t d'.
Proof.
  destruct t; ins; desf; auto using nth_indep.
Qed.

Lemma trace_nth_in A (t : trace A) n
      (LT : NOmega.lt_nat_l n (trace_length t)) d :
  trace_elems t (trace_nth n t d).
Proof.
  destruct t; ins; desf; eauto using nth_In.
Qed.

Hint Resolve trace_nth_in : hahn.

Lemma trace_in_nth A (t : trace A) a (IN : trace_elems t a) d :
  exists n, NOmega.lt_nat_l n (trace_length t) /\
            trace_nth n t d = a.
Proof.
  destruct t; ins; desf; eauto using In_nth.
Qed.

Lemma trace_elems_nth A (t : trace A) d :
  trace_elems t
   ≡₁ (⋃₁ n ∈ (fun n => NOmega.lt_nat_l n (trace_length t)),
       eq (trace_nth n t d)).
Proof.
  repeat autounfold with unfolderDb; intuition; desf;
    eauto using trace_in_nth with hahn.
Qed.

Lemma trace_length_app A (t t' : trace A) :
  trace_length (trace_app t t') =
  NOmega.add (trace_length t) (trace_length t').
Proof.
  destruct t, t'; ins; auto using length_app.
Qed.

(** Lemmas about concatenation of traces *)

Lemma trace_in_app A (a : A) (t t' : trace A) :
  trace_elems (trace_app t t') a <->
  trace_elems t a \/ trace_length t <> NOinfinity /\ trace_elems t' a.
Proof.
  split; destruct t, t'; ins; unfold trace_prepend in *;
    desf; rewrite ?in_app_iff in *; desf;
    eauto using nth_In; vauto.
  all: try solve [right; split; ins; eauto].
  apply In_nth with (d := fl 0) in H; desf; exists n; desf; ins.
  exists (n + length l); desf; try f_equal; omega.
Qed.

Lemma trace_elems_app A (t t' : trace A) :
  trace_elems (trace_app t t') ≡₁
    trace_elems t ∪₁ ifP trace_finite t then trace_elems t' else ∅.
Proof.
  unfold set_union, trace_finite; split; intro x;
    rewrite trace_in_app; ins; desf; desf; ins; eauto.
  destruct t; ins; destruct n; eauto.
  right; ins.
Qed.

Lemma trace_nth_app (n : nat) A (t t' : trace A) (d : A) :
  trace_nth n (trace_app t t') d =
  ifP NOmega.lt_nat_l n (trace_length t) then trace_nth n t d
  else trace_nth (NOmega.sub_nat_l n (trace_length t)) t' d.
Proof.
  destruct t, t'; ins; unfold trace_prepend in *;
    desf; try rewrite app_nth; desf;
      auto using nth_indep; omega.
Qed.

Lemma trace_appA A (t t' t'' : trace A) :
  trace_app (trace_app t t') t'' = trace_app t (trace_app t' t'').
Proof.
  unfold trace_app; ins; desf; try by rewrite appA.
  all: f_equal; extensionality x; desf.
  by rewrite trace_prepend_app.
Qed.

Lemma trace_app_assoc A (t t' t'' : trace A) :
  trace_app t (trace_app t' t'') = trace_app (trace_app t t') t''.
Proof.
  symmetry; apply trace_appA.
Qed.

(** Lemmas about [trace_map] *)

Lemma trace_length_map A B (f : A -> B) (t : trace A) :
  trace_length (trace_map f t) = trace_length t.
Proof.
  destruct t; ins; eauto using length_map.
Qed.

Lemma trace_in_map A (a : A) B (f : B -> A) (t : trace B) :
  trace_elems (trace_map f t) a <-> exists x, trace_elems t x /\ f x = a.
Proof.
  destruct t; ins; try rewrite in_map_iff; split; ins; desf; eauto.
Qed.

Lemma trace_elems_map A B (f : B -> A) (t : trace B) :
  trace_elems (trace_map f t) ≡₁ set_collect f (trace_elems t).
Proof.
  unfold set_collect; split; intro x; destruct t; ins; desf;
    try rewrite in_map_iff in *; desf; eauto.
Qed.

Lemma trace_nth_map (n : nat) A B (f : B -> A) (t : trace B) d :
  trace_nth n (trace_map f t) (f d) = f (trace_nth n t d).
Proof.
  destruct t; ins; apply map_nth.
Qed.

(** Lemmas about [trace_filter] *)

Lemma trace_in_filter A (a : A) (f : A -> Prop) (t : trace A) :
  trace_elems (trace_filter f t) a <-> trace_elems t a /\ f a.
Proof.
  destruct t; ins; desf; ins; rewrite ?in_filterP_iff, ?in_map_iff; ins.
  all: split; ins; desf; splits; eauto.
  all: try (eexists; try split; ins).
  all: destruct (constructive_indefinite_description); ins; desf.
  { in_simp; apply l in H0; omega. }
  revert a0.
  instantiate (1 := length (filterP (fl ↓₁ f) (List.seq 0 n0))).
  destruct (lt_eq_lt_dec x n0) as [[LT|]|LT]; desf.
  unfold set_map.
  all: rewrite (seq_split0 LT), filterP_app, length_app;
    ins; desf; ins; omega.
Qed.

Lemma trace_elems_filter A (f : A -> Prop) (t : trace A) :
  trace_elems (trace_filter f t) ≡₁ trace_elems t ∩₁ f.
Proof.
  repeat autounfold with unfolderDb; split; ins.
  all: rewrite trace_in_filter in *; desf.
Qed.

Lemma trace_filter_app A (f : A -> Prop) (t t' : trace A)
      (IMP: trace_length (trace_filter f t) <> NOinfinity ->
            trace_length t <> NOinfinity) :
  trace_filter f (trace_app t t') =
  trace_app (trace_filter f t)
            (trace_filter f t').
Proof.
  destruct t; ins; desf; ins; desf.
  all: try solve [destruct IMP; ins]; clear IMP.
  all: repeat destruct (constructive_indefinite_description); ins; desf.
  all: try solve [exfalso; rewrite set_finite_prepend in *; ins].
    by rewrite filterP_app in *.
  { unfold set_map in *.
    destruct (le_lt_dec (length l) (S x)).
    - rewrite map_trace_prepend_geq; ins.
      unfold trace_prepend in *.
      rewrite filterP_app.
      do 2 f_equal.
      eapply filterP_map_seq_eq; simpl; eauto.
      ins; forward apply (l0 (length l + i)); desf; try omega.
        by rewrite minus_plus.
      ins; eapply l1 in H; omega.
    - eapply map_trace_prepend_lt with (fl := fl) in l2; desf.
      rewrite l4, filterP_app, appA; clear l4.
      f_equal.
      symmetry; rewrite app_eq_prefix, app_eq_nil, ?filterP_eq_nil.
      remember (a :: l'') as l; clear a l'' Heql.
      split; ins.
      apply in_split in IN; desf.
        forward apply (l0 (length l' + length l2)); try omega.
        by autorewrite with trace_prepends.
      in_simp.
      forward apply (l0 (length l' + (length l + x2))); try omega.
      by autorewrite with trace_prepends.
  }
  { f_equal; extensionality y; ins.
    destruct (constructive_indefinite_description); ins; desf.
    erewrite <- length_map, <- filterP_map.
    destruct (le_lt_dec (length l) x) as [LE|LT].
    { rewrite map_trace_prepend_geq; ins.
      autorewrite with trace_prepends.
      rewrite filterP_map, length_map.
      destruct (constructive_indefinite_description); ins; desf.
      unfold set_map, trace_prepend in *; desf; try omega.
      destruct (lt_eq_lt_dec (x - length l) x0) as [[LT|]|LT]; desf;
      apply seq_split0 in LT; rewrite LT in *;
        exfalso; revert a1; rewrite ?map_app, ?filterP_app, ?length_app;
          ins; desf; ins; omega. }
    eapply map_trace_prepend_lt with (fl := fl) in LT; desf.
    rewrite filterP_app, LT1; red in a.
    autorewrite with trace_prepends in *; ins; desf.
  }
Qed.

Lemma trace_lt_length_filter A n t
      (LT : NOmega.lt_nat_l n (trace_length t))
      (f : A -> Prop) d (F : f (trace_nth n t d)) :
  NOmega.lt_nat_l
    (length
       (filterP f
          (map (fun i => trace_nth i t d) (List.seq 0 n))))
    (trace_length (trace_filter f t)).
Proof.
  destruct t; ins; desf; ins.
  erewrite <- map_nth_seq
    with (a := 0) (l := l)
         (f := fun i => nth i l d) at 1; auto using app_nth1.
  rewrite (seq_split0 LT), map_app, filterP_app, length_app; ins; desf; ins;
    try omega.
  destruct (IndefiniteDescription.constructive_indefinite_description);
    ins; desf.
  specialize (l _ F).
  rewrite seqS, (seq_split0 l); ins.
  rewrite !map_app, !filterP_app, !length_app; ins; desf; ins; desf.
  all: rewrite <- !Nat.add_assoc; apply Nat.lt_add_pos_r; omega.
Qed.


Lemma trace_nth_filter A (f : A -> Prop) (t : trace A) i d
      (LT : NOmega.lt_nat_l i (trace_length (trace_filter f t))) :
  exists n, NOmega.lt_nat_l n (trace_length t)
            /\ trace_nth i (trace_filter f t) d = trace_nth n t d
            /\ i = length (filterP f (map (fun i => trace_nth i t d)
                                          (List.seq 0 n))).
Proof.
  destruct t; ins; desf; ins.
  { apply nth_filterP; ins. }
  {
    destruct (IndefiniteDescription.constructive_indefinite_description);
      ins; desf.
    apply nth_filterP with (d := d) in LT; desf.
    rewrite map_length, seq_length in *; ins.
    exists n; splits; try rewrite map_length, seq_length; ins.
    rewrite LT0, nth_indep with (d' := fl 0); ins.
    rewrite map_nth, seq_nth; ins.
    rewrite map_length, seq_length; ins.
    do 2 f_equal; apply map_ext_in; ins; in_simp.
    rewrite nth_indep with (d' := fl 0); ins.
    rewrite map_nth, seq_nth; ins; omega.
    rewrite map_length, seq_length; ins; omega.
  }
  destruct set_infinite_natE with (n := i) as (m & F & NF).
  exists m; desf.
  destruct (IndefiniteDescription.constructive_indefinite_description);
    ins; desf.
  rewrite filterP_map, length_map; splits; ins.
  clear LT; destruct (lt_eq_lt_dec x m) as [[LT|]|LT]; desf.
  all: rewrite (seq_split0 LT), filterP_app, length_app in *; ins; desf;
    ins; omega.
Qed.

Lemma trace_nth_filter' A (f : A -> Prop) (t : trace A) n d
      (LT : NOmega.lt_nat_l n (trace_length t)) (F: f (trace_nth n t d)):
  trace_nth (length (filterP f (map (fun i => trace_nth i t d)
                              (List.seq 0 n))))
      (trace_filter f t) d = trace_nth n t d.
Proof.
  destruct t; ins; desf; ins; eauto using nth_filterP'.
  {
    destruct (IndefiniteDescription.constructive_indefinite_description);
      ins; desf.
    clear LT; assert (LT := l _ F); ins.
    rewrite seqS, (seq_split0 LT), appA, map_app, filterP_app.
    rewrite app_nth2, Nat.sub_diag; ins; desf.
  }
  destruct (IndefiniteDescription.constructive_indefinite_description); ins.
  destruct a as [F' LEQ].
  rewrite filterP_map, length_map in *.
  change (fun i => fl i) with fl in *.
  clear LT; destruct (lt_eq_lt_dec x n) as [[LT|]|LT]; desf.
  all: rewrite (seq_split0 LT), filterP_app, length_app in *; ins; desf;
    ins; omega.
Qed.


(** Lemmas about [trace_prefix] *)

Lemma trace_prefix_app A (t t' : trace A) :
  trace_prefix t (trace_app t t').
Proof.
  destruct t, t'; ins; unfold trace_prepend;
    desf; eauto using nth_indep; done.
Qed.

Lemma trace_prefixE A (t t' : trace A) :
  trace_prefix t t' <-> exists t'', t' = trace_app t t''.
Proof.
  split; ins; desf; eauto using trace_prefix_app.
  destruct t, t'; ins; desf; desf.
  - by eexists (trace_fin _).
  - exists (trace_inf (fun x => fl (x + length l))).
    unfold trace_prepend; f_equal; extensionality y; desf; eauto.
    f_equal; omega.
  - exists (trace_fin nil); f_equal; extensionality x; eauto.
Qed.

Lemma trace_prefix_refl A (t : trace A) :
  trace_prefix t t.
Proof.
  destruct t; ins; eauto using app_nil_end.
Qed.

Lemma trace_prefix_trans A (t t' t'' : trace A) :
  trace_prefix t t' ->
  trace_prefix t' t'' ->
  trace_prefix t t''.
Proof.
  destruct t, t', t''; ins; desf; try rewrite <- H0; eauto.
    by rewrite appA; vauto.
  forward apply H0 with (i := i) (d := d);
    rewrite ?length_app, ?nth_app;
    ins; desf; omega.
Qed.

(** No duplicates *)

Lemma trace_nodup_filter A (f : A -> Prop) (t : trace A) :
  trace_nodup t -> trace_nodup (trace_filter f t).
Proof.
  unfold trace_nodup; ins; desf.
  red; intros.
  forward eapply trace_nth_filter with (i := i) (d := d)
    as (n & LTn & N); eauto with hahn.
  forward eapply trace_nth_filter with (i := j) (d := d)
    as (m & LTm & M); eauto with hahn.
  desf.
  destruct (lt_eq_lt_dec n m) as [[LT|]|LT]; desf; try omega;
  eapply H with (d := d) in LT; congruence.
Qed.

Lemma trace_nodup_mapE A B (f : A -> B) (t : trace A) :
  trace_nodup (trace_map f t) -> trace_nodup t.
Proof.
  unfold trace_nodup; ins; desf.
  intro; eapply H; try rewrite trace_length_map; eauto.
  rewrite !trace_nth_map; eauto using f_equal.
Qed.

Lemma trace_nodup_inj A (t: trace A)
      (ND: trace_nodup t)
      i (LTi : NOmega.lt_nat_l i (trace_length t))
      j (LTj : NOmega.lt_nat_l j (trace_length t)) d d'
      (EQ: trace_nth i t d = trace_nth j t d') :
  i = j.
Proof.
  rewrite trace_nth_indep with (d := d) (d' := d') in EQ; ins.
  destruct (lt_eq_lt_dec i j) as [[LT|]|LT]; ins.
  all: exfalso; eapply ND; eauto.
Qed.

Lemma trace_nodup_filter_inj A (f : A -> Prop) t
      (ND : trace_nodup (trace_filter f t))
      n (Ln : NOmega.lt_nat_l n (trace_length t))
      m (Lm : NOmega.lt_nat_l m (trace_length t))
      d (EQ : trace_nth n t d = trace_nth m t d)
      (EXT : f (trace_nth n t d)) :
  n = m.
Proof.
  assert (Em: f (trace_nth m t d)) by congruence.
  rewrite <- trace_nth_filter'
    with (n := m) (f := f) in EQ; ins.
  rewrite <- trace_nth_filter'
    with (n := n) (f := f) in EQ; ins; desf.
  eapply trace_nodup_inj in EQ; ins;
    try eapply trace_lt_length_filter; eauto.
  destruct (lt_eq_lt_dec n m) as [[LT|]|LT]; desf.
  all: rewrite (seq_split0 LT) in *.
  all: rewrite map_app, filterP_app, length_app in *;
      ins; desf; ins; omega.
Qed.


(** Lemmas about [trace_order] *)

Lemma trace_order_in1 A (t : trace A) a b :
  trace_order t a b -> trace_elems t a.
Proof.
  unfold trace_order; destruct t; ins; desf; ins; eauto.
  rewrite <- H2; apply nth_In; omega.
Qed.

Lemma trace_order_in2 A (t : trace A) a b :
  trace_order t a b -> trace_elems t b.
Proof.
  unfold trace_order; destruct t; ins; desf; ins; eauto.
  rewrite <- H2; apply nth_In; omega.
Qed.

Hint Immediate trace_order_in1 trace_order_in2 : hahn.

Lemma trace_order_total A (t : trace A) (ND : trace_nodup t) :
  is_total (trace_elems t) (trace_order t).
Proof.
  red; ins.
  apply trace_in_nth with (d := a) in IWa; desf.
  apply trace_in_nth with (d := a) in IWb; desf.
  destruct (lt_eq_lt_dec n n0) as [[LT|]|LT]; desf; try congruence.
  left; repeat eexists; eauto.
  right; repeat eexists; eauto using trace_nth_indep.
  rewrite trace_nth_indep with (d' := a); ins.
Qed.

Lemma trace_order_trans A (t : trace A) x y z :
  trace_order t x y ->
  trace_order t y z ->
  trace_order t x z.
Proof.
  unfold trace_order; splits; ins; desf.
  rewrite trace_nth_indep with (d' := x) in *; ins; eauto.
  2: destruct (trace_length t); ins; omega.
  exists i0, j; splits; eauto.
  destruct (le_lt_dec j0 i) as [|LT]; try omega.
  exfalso; eapply H0; try apply LT; eauto.
Qed.

Lemma trace_order_irrefl A (t : trace A) x
      (ORD: trace_order t x x) : False.
Proof.
  unfold trace_order in *; ins; desf.
  eapply ORD with (d := x); eauto; congruence.
Qed.

Lemma fsupp_trace_order A (t : trace A) :
  fsupp (trace_order t).
Proof.
  intro y.
  tertium_non_datur (trace_elems t y).
  2: exists nil; ins; eauto with hahn.
  apply trace_in_nth with (d := y) in H; desc.
  exists (map (fun i => trace_nth i t y) (List.seq 0 n)).
  unfold trace_order; ins; desf.
  ins; in_simp.
  rewrite trace_nth_indep with (d' := x) in H0; ins.
  apply trace_nodup_inj in H0; ins; desf.
  exists i; rewrite trace_nth_indep with (d' := x);
    splits; ins; in_simp; eauto with hahn.
Qed.

Lemma trace_order_nth_nth A (t : trace A)
      n (LTn : NOmega.lt_nat_l n (trace_length t)) d
      m (LTm : NOmega.lt_nat_l m (trace_length t)) d' :
  trace_order t (trace_nth n t d) (trace_nth m t d') <->
  trace_nodup t /\ n < m.
Proof.
  unfold trace_order; split; ins; desf; splits; ins.
    apply trace_nodup_inj in H2; ins; desf.
    apply trace_nodup_inj in H3; ins; desf.
    destruct (trace_length t); ins; omega.
  exists n, m; splits; ins; auto using trace_nth_indep.
Qed.


Lemma exists_max (cond : nat -> Prop) n :
  (forall m (LT : m < n), ~ cond m)
  \/ exists m, m < n /\ cond m /\ forall j, m < j -> j < n -> ~ cond j.
Proof.
  induction n; [left; ins; omega|].
  tertium_non_datur (cond n).
    right; exists n; splits; ins; omega.
  desf; [left | right].
  ins; rewrite Nat.lt_succ_r, Nat.le_lteq in *; desf; eauto.
  exists m; splits; ins; eauto.
  rewrite Nat.lt_succ_r, Nat.le_lteq in *; desf; eauto.
Qed.


(** Labelled transition system (LTS) *)

Record LTS (State Label : Type) : Type :=
  { LTS_init : State -> Prop ;
    LTS_final : State -> Prop ;
    LTS_step : State -> Label -> State -> Prop }.

Section LTS_traces.

  Variable State : Type.
  Variable Label : Type.
  Variable lts : LTS State Label.

  (** Traces generated by a labelled transition system *)

  Definition LTS_trace (t : trace Label) :=
    match t with
    | trace_fin l =>
      exists fl', LTS_init lts (fl' 0) /\
                  forall i (LLEN : i < length l) d,
                    LTS_step lts (fl' i) (nth i l d) (fl' (S i))
    | trace_inf fl =>
      exists fl', LTS_init lts (fl' 0) /\
                  forall i, LTS_step lts (fl' i) (fl i) (fl' (S i))
    end.

  Definition LTS_complete_trace (t : trace Label) :=
    match t with
    | trace_fin l =>
      exists fl', LTS_init lts (fl' 0) /\
                  LTS_final lts (fl' 0) /\
                  forall i (LLEN : i < length l) d,
                    LTS_step lts (fl' i) (nth i l d) (fl' (S i))
    | trace_inf fl =>
      exists fl', LTS_init lts (fl' 0) /\
                  forall i, LTS_step lts (fl' i) (fl i) (fl' (S i))
    end.

  Lemma LTS_complete_trace_weaken t :
    LTS_complete_trace t -> LTS_trace t.
  Proof.
    destruct t; ins; desf; eauto.
  Qed.

  Lemma LTS_trace_prefix_closed t t' :
    LTS_trace t' -> trace_prefix t t' -> LTS_trace t.
  Proof.
    destruct t, t'; ins; desf; exists fl'; splits; ins.
    all: specialize (H1 i); rewrite ?length_app in *.
    all: specialize_full H1; try omega.
    all: try rewrite nth_app in *; desf; eauto; try omega.
    rewrite <- H0; ins.
    rewrite H0; ins.
  Qed.

  Lemma LTS_traceE t (T : LTS_trace t) :
    exists fl',
      LTS_init lts (fl' 0) /\
      (forall i (LTi : NOmega.lt_nat_l i (trace_length t)) d,
          LTS_step lts (fl' i) (trace_nth i t d) (fl' (S i))).
  Proof.
    destruct t; ins; desf.
    exists fl'; split; ins.
  Qed.

End LTS_traces.


Hint Resolve fsupp_trace_order : hahn.

