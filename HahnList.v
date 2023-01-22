(******************************************************************************)
(** * Lemmas about lists and permutations *)
(******************************************************************************)

Require Import HahnBase HahnSets.
Require Import Arith Lia Setoid Morphisms Sorted.
Require Import IndefiniteDescription.
Require Export List Permutation.

Set Implicit Arguments.

(** This file contains a number of basic definitions and lemmas about lists
    that are missing from the standard library, and a few properties of
    classical logic. *)

(** Very basic lemmas *)
(******************************************************************************)

Definition appA := app_ass.
Definition length_nil A : length (@nil A) = 0 := eq_refl.
Definition length_cons A (a: A) l : length (a :: l) = S (length l) := eq_refl.
Definition length_app := app_length.
Definition length_rev := rev_length.
Definition length_map := map_length.
Definition length_combine := combine_length.
Definition length_prod := prod_length.
Definition length_firstn := firstn_length.
Definition length_seq := seq_length.
Definition length_repeat := repeat_length.

Hint Rewrite length_nil length_cons length_app length_rev length_map : calc_length.
Hint Rewrite length_combine length_prod length_firstn length_seq  : calc_length.
Hint Rewrite length_repeat : calc_length.

Lemma in_cons_iff A (a b : A) l : In b (a :: l) <-> a = b \/ In b l.
Proof. done. Qed.

Lemma in_app_l A (a : A) l l' : In a l -> In a (l ++ l').
Proof. eauto using in_or_app. Qed.

Lemma in_app_r A (a : A) l l' : In a l' -> In a (l ++ l').
Proof. eauto using in_or_app. Qed.

Global Hint Resolve in_app_l in_app_r in_cons in_eq : hahn.

Lemma In_split2 :
  forall A (x: A) l (IN: In x l),
  exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1.
Proof.
  induction l; ins; desf; [by eexists nil; ins; eauto|].
  destruct (classic (a = x)); desf; [by eexists nil; ins; eauto|].
  apply IHl in IN; desf; eexists (_ :: _); repeat eexists; ins; intro; desf.
Qed.

Lemma app_nth A n l l' (d : A) :
  nth n (l ++ l') d =
  if le_lt_dec (length l) n then nth (n - length l) l' d else nth n l d.
Proof.
  desf; eauto using app_nth1, app_nth2.
Qed.

Definition nth_app := app_nth.

Lemma app_comm_cons' A (a : A) l l' :
  l ++ a :: l' = (l ++ a :: nil) ++ l'.
Proof.
  by rewrite <- app_assoc.
Qed.

Lemma destruct_end A (l : list A) :
  l = nil \/ exists l' a, l = l' ++ a :: nil.
Proof.
  induction l; ins; desf; eauto.
  - right; exists nil; ins; eauto.
  - right; eexists (_ :: _); ins; eauto.
Qed.

Lemma rev_induction A (P : list A -> Prop) :
  P nil -> (forall a l, P l -> P (l ++ a :: nil)) -> forall l, P l.
Proof.
  ins; rewrite <- rev_involutive.
  induction (rev l); ins; eauto.
Qed.


(* Destructing equalities between lists *)
(******************************************************************************)

Lemma snoc_eq_snoc A (a a' : A) l l' :
  l ++ a :: nil = l' ++ a' :: nil <-> l = l' /\ a = a'.
Proof.
  by split; ins; desf; apply app_inj_tail.
Qed.

Lemma app_eq_nil A (l1 l2 : list A) :
  l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof.
  destruct l1; split; ins; desf.
Qed.

Lemma app_eq_cons A (l1 l2 : list A) a l :
  l1 ++ l2 = a :: l <->
  (l1 = nil /\ l2 = a :: l) \/ (exists l1', l1 = a :: l1' /\ l1' ++ l2 = l).
Proof.
  split; ins; desf.
  destruct l1; ins; desf; eauto.
Qed.

Lemma app_eq_singleton A (l1 l2 : list A) a :
  l1 ++ l2 = a :: nil <->
  (l1 = nil /\ l2 = a :: nil) \/ (l1 = a :: nil /\ l2 = nil).
Proof.
  rewrite app_eq_cons; split; ins; desf; eauto.
  rewrite app_eq_nil in *; desf; eauto.
Qed.

Lemma app_eq_snoc A (l1 l2 : list A) a l :
  l1 ++ l2 = l ++ a :: nil <->
  (l1 = l ++ a :: nil /\ l2 = nil) \/ (exists l2', l2 = l2' ++ a :: nil /\ l1 ++ l2' = l).
Proof.
  split; ins; desf; rewrite ?app_nil_r, ?app_assoc; ins; eauto.
  destruct (destruct_end l2); desf; rewrite ?app_nil_r in *; desf; eauto.
  rewrite app_assoc, snoc_eq_snoc in *; desf; eauto.
Qed.

Lemma app_eq_prefix A (l : list A) l' :
  l ++ l' = l <-> l' = nil.
Proof.
  split; ins; desf; auto using app_nil_r.
  induction l; ins; desf; eauto.
Qed.

Lemma app_eq_suffix A (l : list A) l' :
  l ++ l' = l' <-> l = nil.
Proof.
  split; ins; desf; revert H.
  induction l' using rev_induction; rewrite ?app_nil_r; ins.
  rewrite app_assoc, snoc_eq_snoc in *; desf; eauto.
Qed.

Lemma app_cons_eq_nil A (l1 l2 : list A) a :
  l1 ++ a :: l2 = nil <-> False.
Proof.
  destruct l1; ins; desf.
Qed.

Lemma app_cons_eq_cons A (l1 l2 : list A) a a' l :
  l1 ++ a :: l2 = a' :: l <->
  (l1 = nil /\ a = a' /\ l2 = l) \/ (exists l1', l1 = a' :: l1' /\ l1' ++ a :: l2 = l).
Proof.
  rewrite app_eq_cons; split; ins; desf; eauto.
Qed.

Lemma app_cons_eq_singleton A (l1 l2 : list A) a a' :
  l1 ++ a :: l2 = a' :: nil <-> l1 = nil /\ a = a' /\ l2 = nil.
Proof.
  rewrite app_eq_singleton; split; ins; desf; eauto.
Qed.

Lemma app_cons_eq_snoc A (l1 l2 : list A) a a' l :
  l1 ++ a :: l2 = l ++ a' :: nil <->
  (l1 = l /\ a = a' /\ l2 = nil) \/ (exists l2', l2 = l2' ++ a' :: nil /\ l1 ++ a :: l2' = l).
Proof.
  split; ins; desf; [|by rewrite <- app_assoc].
  rewrite app_eq_snoc in H; ins; desf.
  symmetry in H; rewrite app_cons_eq_cons in H; desf; eauto using app_nil_end.
Qed.

Lemma snoc_eq_nil A (l : list A) a :
  l ++ a :: nil = nil <-> False.
Proof.
  apply app_cons_eq_nil.
Qed.

Lemma snoc_eq_cons A (l : list A) a a' l' :
  l ++ a :: nil = a' :: l' <->
  (l = nil /\ a = a' /\ l' = nil) \/ (exists l1', l = a' :: l1' /\ l1' ++ a :: nil = l').
Proof.
  rewrite app_cons_eq_cons; split; ins; desf; eauto.
Qed.

Lemma snoc_eq_singleton A (l : list A) a a' :
  l ++ a :: nil = a' :: nil <-> l = nil /\ a = a'.
Proof.
  rewrite app_cons_eq_singleton; split; ins; desf; eauto.
Qed.

Lemma snoc_eq_app A (l1 l2 : list A) a l :
  l ++ a :: nil = l1 ++ l2 <->
  (l ++ a :: nil = l1 /\ l2 = nil) \/ (exists l2', l2' ++ a :: nil = l2 /\ l = l1 ++ l2').
Proof.
  split; ins; desf; rewrite ?app_nil_r, ?app_assoc; ins; eauto.
  destruct (destruct_end l2); desf; rewrite ?app_nil_r in *; desf; eauto.
  rewrite app_assoc, snoc_eq_snoc in *; desf; eauto.
Qed.

Lemma length_eq_add A (l : list A) m n :
  length l = m + n <->
  exists l' l'', l = l' ++ l'' /\ length l' = m /\ length l'' = n.
Proof.
  split; ins; desf; eauto using length_app.
  revert m H; induction l; ins.
  destruct m; ins; desf; exists nil, nil; ins.
  destruct m; [eexists nil, _; ins|].
  forward apply (IHl m) as X; ins; desf.
  eexists (_ :: _), _; ins.
Qed.


(** List map *)
(******************************************************************************)

Lemma map_eq_nil A B (f : A -> B) l :
  map f l = nil <-> l = nil.
Proof.
  destruct l; ins; desf; eauto.
Qed.

Lemma map_eq_cons A B (f : A -> B) l y ys :
  map f l = y :: ys <->
  exists x l', l = x :: l' /\ y = f x /\ map f l' = ys.
Proof.
  split; ins; desf.
  destruct l; ins; desf; eauto.
Qed.

Lemma map_eq_singleton A B (f : A -> B) l y :
  map f l = y :: nil <->
  exists x, l = x :: nil /\ y = f x.
Proof.
  split; ins; desf.
  destruct l as [|?[|??]]; ins; desf; eauto.
Qed.

Lemma map_eq_app A B (f : A -> B) l l1' l2' :
  map f l = l1' ++ l2' <->
  exists l1 l2, l = l1 ++ l2 /\ map f l1 = l1' /\ map f l2 = l2'.
Proof.
  split; ins; desf; auto using map_app.
  revert dependent l1'; induction l; destruct l1'; ins; desf.
  - exists nil, nil; ins.
  - eexists nil, (_ :: _); ins.
  - apply IHl in H; desf; eexists (_ :: _), _; ins.
Qed.

Lemma map_eq_snoc A B (f : A -> B) l y ys :
  map f l = ys ++ y :: nil <->
  exists x l', l = l' ++ x :: nil /\ y = f x /\ map f l' = ys.
Proof.
  rewrite map_eq_app; split; ins; desf; eauto.
  rewrite map_eq_singleton in *; desf; eauto.
Qed.

Lemma map_eq_app_inv A B (f : A -> B) l l1 l2 :
  map f l = l1 ++ l2 ->
  exists l1' l2', l = l1' ++ l2' /\ map f l1' = l1 /\ map f l2' = l2.
Proof.
  apply map_eq_app.
Qed.

Lemma list_app_eq_app A (l l' l0 l0' : list A) :
  l ++ l' = l0 ++ l0' ->
  (exists lr, l ++ lr = l0 /\ l' = lr ++ l0') \/
  (exists lr, l = l0 ++ lr /\ lr ++ l' = l0').
Proof.
  revert l0; induction l; ins; eauto.
  destruct l0; ins; desf; eauto.
  apply IHl in H; desf; eauto.
Qed.

(** List filtering *)
(******************************************************************************)

Lemma in_filter_iff A l f (x : A) : In x (filter f l) <-> In x l /\ f x.
Proof.
  induction l; ins; try tauto.
  des_if; ins; rewrite IHl; split; ins; desf; eauto.
Qed.

Lemma filter_app A f (l l' : list A) :
  filter f (l ++ l') = filter f l ++ filter f l'.
Proof.
  induction l; ins; desf; ins; congruence.
Qed.

Lemma Permutation_filter A (l l' : list A) (P: Permutation l l') f :
  Permutation (filter f l) (filter f l').
Proof.
  induction P; ins; desf; vauto.
Qed.

Add Parametric Morphism A : (@filter A) with
  signature eq ==> (@Permutation A) ==> (@Permutation A)
      as filter_mor.
Proof.
  by ins; apply Permutation_filter.
Qed.

Lemma length_filter A f (l : list A) :
  length (filter f l) <= length l.
Proof.
  induction l; ins; desf; ins; lia.
Qed.

(** List filtering with a [Prop]-predicate *)
(******************************************************************************)

Fixpoint filterP A (f: A -> Prop) l :=
  match l with
    | nil => nil
    | x :: l => if excluded_middle_informative (f x) then
                  x :: filterP f l
                else filterP f l
  end.

Lemma in_filterP_iff A (x : A) f l :
  In x (filterP f l) <-> In x l /\ f x.
Proof.
  induction l; ins; desf; ins; try (rewrite IHn; clear IHn);
  intuition; desf; eauto.
Qed.

Lemma filterP_app A f (l l' : list A) :
  filterP f (l ++ l') = filterP f l ++ filterP f l'.
Proof.
  induction l; ins; desf; ins; congruence.
Qed.

Lemma filterP_map A (d : A -> Prop) B (f : B -> A) l :
  filterP d (map f l) = map f (filterP (f ↓₁ d) l).
Proof.
  induction l; ins; desf; ins; f_equal; ins.
Qed.

Lemma filterP_set_equiv A (f f' : A -> Prop) (EQ: f ≡₁ f') (l : list A) :
  filterP f l = filterP f' l.
Proof.
  induction l; ins; desf; f_equal; firstorder.
Qed.

Lemma filterP_ext A (f f' : A -> Prop) l
      (EQ: forall x (IN: In x l), f x <-> f' x) :
  filterP f l = filterP f' l.
Proof.
  induction l; ins.
  specialize_full IHl; ins; eauto.
  specialize_full EQ; eauto.
  rewrite IHl; desf; tauto.
Qed.

Lemma Permutation_filterP A (l l' : list A) (P: Permutation l l') f :
  Permutation (filterP f l) (filterP f l').
Proof.
  induction P; ins; desf; vauto.
Qed.

Lemma Permutation_filterP2 A f f' (EQ: f ≡₁ f') l l' (P: Permutation (A:=A) l l') :
  Permutation (filterP f l) (filterP f' l').
Proof.
  replace (filterP f' l') with (filterP f l');
    auto using Permutation_filterP, filterP_set_equiv.
Qed.

Lemma Permutation_filterP_split A f (l : list A) :
  Permutation l (filterP f l ++ filterP (fun x => ~ f x) l).
Proof.
  induction l; ins; desf; simpls;
    eauto using perm_skip, Permutation_cons_app.
Qed.

Instance filterP_Proper A : Proper (_ ==> _ ==> _) _ := Permutation_filterP2 (A:=A).


Lemma filterP_eq_nil A f (l: list A):
  filterP f l = nil <-> forall x (IN: In x l) (COND: f x), False.
Proof.
  split; ins.
  * enough (In x nil) by done.
    rewrite <- H; apply in_filterP_iff; eauto.
  * induction l; ins; desf; eauto; exfalso; eauto.
Qed.

Lemma filterP_eq_cons A f (l l': list A) x:
  filterP f l = x :: l' ->
  f x /\
  exists p p',
    l = p ++ x :: p' /\
    (forall x (IN: In x p) (COND: f x), False) /\
    l' = filterP f p'.
Proof.
  induction l; ins; desf.
    by splits; ins; eexists nil; eexists; splits; ins; desf; eauto.
  eapply IHl in H; desc; splits; ins; desf.
  eexists (_ :: _); eexists; splits; ins; desf; eauto.
Qed.

Lemma filterP_eq_app A f (l l' l'': list A) :
  filterP f l = l' ++ l'' ->
  exists p p',
    l = p ++ p' /\
    l' = filterP f p /\
    l'' = filterP f p'.
Proof.
  revert l'; induction l; ins; desf.
  { destruct l'; ins; desf; exists nil, nil; ins. }
  destruct l'; ins; desf.
    eexists nil, (_ :: _); splits; ins; desf.
  all: apply IHl in H; desf; eexists (_ :: _), _; splits; ins; desf.
Qed.

Lemma filterP_eq_middle A f (l l' l'': list A) x :
  filterP f l = l' ++ x :: l'' ->
  f x /\
  exists p p',
    l = p ++ x :: p' /\
    l' = filterP f p /\
    l'' = filterP f p'.
Proof.
  ins; apply filterP_eq_app in H; desf.
  apply eq_sym, filterP_eq_cons in H1; desf.
  split; ins.
  eexists (_ ++ _), _; rewrite appA, filterP_app; splits; ins.
  apply filterP_eq_nil in H2; rewrite H2.
  apply app_nil_end.
Qed.

Lemma length_filterP A f (l : list A) :
  length (filterP f l) <= length l.
Proof.
  induction l; ins; desf; ins; lia.
Qed.

(** List flattening *)
(******************************************************************************)

Fixpoint flatten A (l: list (list A)) :=
  match l with
    | nil => nil
    | x :: l' => x ++ flatten l'
  end.

Lemma in_flatten_iff A (x: A) ll :
  In x (flatten ll) <-> exists l, In l ll /\ In x l.
Proof.
  induction ll; ins.
    by split; ins; desf.
  rewrite in_app_iff, IHll; clear; split; ins; desf; eauto.
Qed.

Lemma flatten_app A (l l' : list (list A)) :
  flatten (l ++ l') = flatten l ++ flatten l'.
Proof.
  by induction l; ins; desf; ins; rewrite appA, IHl.
Qed.

Lemma length_flatten A (l : list (list A)) :
  length (flatten l) = list_sum (map (length (A:=A)) l).
Proof.
  induction l; ins; desf; rewrite length_app; lia.
Qed.

(** List reverse *)
(******************************************************************************)

Lemma in_rev_iff A x (l : list A) :
  In x (rev l) <-> In x l.
Proof.
  symmetry; apply in_rev.
Qed.

Lemma rev_cons A (a : A) (l: list A) : rev (a :: l) = rev l ++ a :: nil.
Proof.
  done.
Qed.

Lemma rev_app A (l1 l2 : list A) :
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  apply rev_app_distr.
Qed.

Lemma rev_snoc A (a : A) (l: list A) : rev (l ++ a :: nil) = a :: rev l.
Proof.
  apply rev_app.
Qed.

Lemma rev_rev A (l : list A) : rev (rev l) = l.
Proof.
  induction l; ins; rewrite rev_app, IHl; ins.
Qed.

Lemma rev_filter A f (l : list A) :
  rev (filter f l) = filter f (rev l).
Proof.
  induction l; ins; desf; ins; rewrite filter_app, IHl; ins; desf; ins.
  auto using app_nil_end.
Qed.

Lemma rev_filterP A f (l : list A) :
  rev (filterP f l) = filterP f (rev l).
Proof.
  induction l; ins; desf; ins; rewrite filterP_app, IHl; ins; desf; ins.
  auto using app_nil_end.
Qed.

Lemma rev_map A B (f : A -> B) (l : list A) :
  rev (map f l) = map f (rev l).
Proof.
  induction l; ins; rewrite map_app, IHl; ins.
Qed.

Lemma rev_eq A (l l' : list A) : rev l = rev l' <-> l = l'.
Proof.
  split; ins; desf.
  apply (f_equal (@rev A)) in H; rewrite !rev_rev in H; ins.
Qed.

Lemma rev_eq_nil A (l : list A) : rev l = nil <-> l = nil.
Proof.
  by rewrite <- rev_eq, rev_rev.
Qed.

Lemma rev_eq_cons A (a : A) (l l' : list A) :
  rev l = a :: l' <-> l = rev l' ++ a :: nil.
Proof.
  by rewrite <- rev_eq, rev_rev.
Qed.

Lemma rev_eq_app A (l l1 l2 : list A) :
  rev l = l1 ++ l2 <-> l = rev l2 ++ rev l1.
Proof.
  by rewrite <- rev_eq, rev_rev, rev_app.
Qed.

Lemma rev_eq_snoc A (a : A) (l l' : list A) :
  rev l = l' ++ a :: nil <-> l = a :: rev l'.
Proof.
  apply rev_eq_app.
Qed.

(** List disjointness *)
(******************************************************************************)

Definition disjoint A (l1 l2 : list A) :=
  forall a (IN1: In a l1) (IN2: In a l2), False.

Lemma disjoint_nil_l A (l : list A) : disjoint nil l.
Proof. done. Qed.

Lemma disjoint_nil_r A (l : list A) : disjoint l nil.
Proof. done. Qed.

Lemma disjoint_one_l A (a : A) (l : list A) : disjoint (a :: nil) l <-> ~ In a l.
Proof. unfold disjoint; intuition; ins; desf; eauto. Qed.

Lemma disjoint_one_r A (a : A) (l : list A) : disjoint l (a :: nil) <-> ~ In a l.
Proof. unfold disjoint; intuition; ins; desf; eauto. Qed.


Lemma disjoint_rev_l A (l1 l2 : list A) :
  disjoint (rev l1) l2 <-> disjoint l1 l2.
Proof.
  unfold disjoint; intuition; eapply H; eauto; try rewrite <- in_rev in *; eauto.
Qed.

Lemma disjoint_rev_r A (l1 l2 : list A) :
  disjoint l1 (rev l2) <-> disjoint l1 l2.
Proof.
  unfold disjoint; intuition; eapply H; eauto; try rewrite <- in_rev in *; eauto.
Qed.


(** Remove duplicate list elements (classical) *)
(******************************************************************************)

Fixpoint undup A (l: list A) :=
  match l with nil => nil
    | x :: l =>
      ifP (In x l) then undup l else x :: undup l
  end.

(** Lemmas about [NoDup] and [undup] *)
(******************************************************************************)

Lemma nodup_one A (x: A) : NoDup (x :: nil).
Proof. vauto. Qed.

Global Hint Resolve NoDup_nil nodup_one : core hahn.

Lemma nodup_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup (map f l).
Proof.
  induction 1; ins; vauto.
  constructor; eauto.
  intro; rewrite in_map_iff in *; desf.
  edestruct H1; try eapply H2; eauto.
  intro; desf.
Qed.

Lemma nodup_cons A (x: A) l:
  NoDup (x :: l) <-> ~ In x l /\ NoDup l.
Proof. split; inversion 1; vauto. Qed.

Lemma nodup_app:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof.
  induction l1; ins.
    by split; ins; desf; vauto.
  rewrite !nodup_cons, IHl1, in_app_iff; unfold disjoint.
  ins; intuition (subst; eauto).
Qed.

Lemma nodup_append_commut A (a b : list A) :
  NoDup (a ++ b) -> NoDup (b ++ a).
Proof.
  ins; rewrite nodup_app in *; unfold disjoint in *.
  desf; splits; ins; eauto.
Qed.

Lemma nodup_append A (l1 l2: list A) :
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_right A (l1 l2: list A) :
  NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_left A (l1 l2: list A) :
  NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_rev A (l : list A) : NoDup (rev l) <-> NoDup l.
Proof.
  induction l; ins.
  rewrite nodup_app, !nodup_cons, IHl, disjoint_rev_l, disjoint_one_r; intuition.
Qed.

Lemma nodup_filter A (l: list A) (ND: NoDup l) f : NoDup (filter f l).
Proof.
  induction l; ins; inv ND; desf; eauto using NoDup.
  econstructor; eauto; rewrite in_filter_iff; tauto.
Qed.

Lemma nodup_filterP A (l: list A) (ND: NoDup l) f : NoDup (filterP f l).
Proof.
  induction l; ins; inv ND; desf; eauto using NoDup.
  econstructor; eauto; rewrite in_filterP_iff; tauto.
Qed.

Global Hint Resolve nodup_filter nodup_filterP : core hahn.

Lemma Permutation_nodup A ( l l' : list A) :
  Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; eauto; rewrite !nodup_cons in *; ins; desf; intuition.
  eby symmetry in H; eapply H0; eapply Permutation_in.
Qed.

Lemma nodup_eq_one A (x : A) l :
   NoDup l -> In x l -> (forall y (IN: In y l), y = x) -> l = x :: nil.
Proof.
  destruct l; ins; f_equal; eauto.
  inv H; desf; clear H H5; induction l; ins; desf; case H4; eauto using eq_sym.
  rewrite IHl in H0; ins; desf; eauto.
Qed.

Lemma nodup_consD A (x : A) l : NoDup (x :: l) -> NoDup l.
Proof. inversion 1; desf. Qed.

Lemma nodup_mapD A B (f : A-> B) l : NoDup (map f l) -> NoDup l.
Proof.
  induction l; ins; rewrite !nodup_cons, in_map_iff in *; desf; eauto 8.
Qed.

Lemma In_NoDup_Permutation A (a : A) l (IN: In a l) (ND : NoDup l) :
  exists l', Permutation l (a :: l') /\ ~ In a l'.
Proof.
  induction l; ins; desf; inv ND; eauto.
  destruct IHl as (l' & ? & ?); eauto.
  destruct (classic (a0 = a)); desf.
  eexists (a0 :: l'); split; try red; ins; desf.
  eapply Permutation_trans, perm_swap; eauto.
Qed.

Lemma in_undup_iff A (x : A) (l : list A) : In x (undup l) <-> In x l.
Proof. induction l; split; ins; desf; ins; desf; eauto. Qed.

Lemma nodup_undup A (l : list A) : NoDup (undup l).
Proof. induction l; ins; desf; constructor; rewrite ?in_undup_iff in *; eauto. Qed.

Global Hint Resolve nodup_undup : core hahn.

Lemma undup_nodup A (l : list A) : NoDup l -> undup l = l.
Proof. induction 1; ins; desf; congruence. Qed.

Lemma undup_nonnil A (l : list A) : l <> nil -> undup l <> nil.
Proof.
  induction l; ins; desf.
  by eapply in_undup_iff in i; intro X; rewrite X in *.
Qed.

Lemma undup_filter A f (l : list A) : undup (filter f l) = filter f (undup l).
Proof.
  induction l; ins; desf; ins; desf;
    rewrite in_filter_iff in *; clarify_not; desf; congruence.
Qed.

Lemma undup_filterP A f (l : list A) : undup (filterP f l) = filterP f (undup l).
Proof.
  induction l; ins; desf; ins; desf;
    rewrite in_filterP_iff in *; clarify_not; desf; congruence.
Qed.

Lemma Permutation_undup A (l l' : list A) :
  Permutation l l' -> Permutation (undup l) (undup l').
Proof.
  ins; eapply NoDup_Permutation; ins; rewrite !in_undup_iff.
  split; eauto using Permutation_in, Permutation_sym.
Qed.

Lemma in_split_perm A (x : A) l (IN: In x l) :
  exists l', Permutation l (x :: l').
Proof.
  induction l; ins; intuition; desf; eauto.
  exists (a :: l'); rewrite H0; vauto.
Qed.

Lemma NoDup_eq_simpl A l1 (a : A) l1' l2 l2'
      (ND : NoDup (l1 ++ a :: l1'))
      (L : l1 ++ a :: l1' = l2 ++ a :: l2') :
      l1 = l2 /\ l1' = l2'.
Proof.
  revert l2 L; induction l1; ins; destruct l2; ins; desf.
    by exfalso; inv ND; eauto using in_or_app, in_eq, in_cons.
    by exfalso; inv ND; eauto using in_or_app, in_eq, in_cons.
  inv ND; eapply IHl1 in H0; desf.
Qed.

Lemma set_finiteE A (s : A -> Prop) :
  set_finite s <-> exists findom, NoDup findom /\ s ≡₁ (fun x => In x findom).
Proof.
  repeat autounfold with unfolderDb; intuition; desf; eauto.
  exists (undup (filterP s findom)); splits; ins.
  all: rewrite in_undup_iff, in_filterP_iff in *; desf; eauto.
Qed.

(** Lemmas about list concatenation *)
(******************************************************************************)

Lemma in_concat_iff A (a: A) ll :
  In a (concat ll) <-> exists l, In a l /\ In l ll.
Proof.
  induction ll; ins; [by split; ins; desf|].
  rewrite in_app_iff, IHll; split; ins; desf; eauto.
Qed.

Lemma in_concat A (a: A) l ll :
  In a l ->
  In l ll ->
  In a (concat ll).
Proof.
  rewrite in_concat_iff; eauto.
Qed.

Add Parametric Morphism X : (@concat X) with
  signature (@Permutation (list X)) ==> (@Permutation X)
      as concat_more.
Proof.
  induction 1; rewrite ?concat_cons,  ?app_assoc;
  eauto using Permutation, Permutation_app, Permutation_app_comm.
Qed.

Lemma NoDup_concat_simpl A (a : A) l1 l2 ll
      (ND: NoDup (concat ll))
      (K: In l1 ll) (K' : In a l1)
      (L: In l2 ll) (L' : In a l2) :
      l1 = l2.
Proof.
  apply in_split_perm in K; desc; rewrite K, concat_cons, nodup_app in *; ins; desf.
  edestruct ND1; eauto using in_concat.
Qed.

Lemma NoDup_concatD A (l: list A) ll :
  NoDup (concat ll) -> In l ll -> NoDup l.
Proof.
  ins; apply in_split_perm in H0; desf.
  rewrite H0, concat_cons, nodup_app in H; desf.
Qed.

Lemma in_concat_fst A a (l : list A) B (l' : list B) ll :
   In (l, l') ll ->
   In a l ->
   In a (concat (map fst ll)).
Proof.
  ins; rewrite <- flat_map_concat_map, in_flat_map; eauto.
Qed.

Lemma in_concat_snd A (l : list A) B a (l' : list B) ll :
   In (l, l') ll ->
   In a l' ->
   In a (concat (map snd ll)).
Proof.
  ins; rewrite <- flat_map_concat_map, in_flat_map; eauto.
Qed.

(** [map_filter] *)
(******************************************************************************)

Section map_filter.

  Variables A B : Type.
  Variable f : A -> option B.

  Fixpoint map_filter l :=
    match l with
      | nil => nil
      | x :: l => match f x with
                    | None => map_filter l
                    | Some b => b :: map_filter l
                  end
    end.

  Lemma in_map_filter x l :
    In x (map_filter l) <-> exists a, f a = Some x /\ In a l.
  Proof using.
    induction l; ins; desf; ins; try (rewrite IHn; clear IHn);
    intuition; desf; eauto.
  Qed.

  Lemma map_filter_app (l l' : list A) :
    map_filter (l ++ l') = map_filter l ++ map_filter l'.
  Proof using.
    induction l; ins; desf; ins; congruence.
  Qed.

  Lemma nodup_map_filter l :
    NoDup l ->
    (forall x y z, In x l -> In y l -> f x = Some z -> f y = Some z -> x = y) ->
    NoDup (map_filter l).
  Proof using.
    induction l; ins; desf; rewrite ?nodup_cons, ?in_map_filter in *;
      desf; splits; eauto.
    by intro; desf; eauto; rewrite (H0 a a0 b) in H; eauto.
  Qed.

End map_filter.

(** Lemmas about Forall *)
(******************************************************************************)

Lemma Forall_cons A (P : A -> Prop) a l :
  Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  split; intro H; desf; vauto; inversion H; desf.
Qed.

Lemma Forall_app A (P : A -> Prop) l1 l2 :
  Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; ins; [by intuition; vauto|].
  by rewrite !Forall_cons, IHl1, and_assoc.
Qed.

Lemma Forall_filter A (P: A -> Prop) f l :
  Forall P l -> Forall P (filter f l).
Proof.
  rewrite !Forall_forall; ins.
  rewrite in_filter_iff in H0; desf; eauto.
Qed.

Lemma Forall_filterP A (P: A -> Prop) f l :
  Forall P l -> Forall P (filterP f l).
Proof.
  rewrite !Forall_forall; ins.
  rewrite in_filterP_iff in H0; desf; eauto.
Qed.

Lemma Forall_in A (P : A -> Prop) l x :
  Forall P l -> In x l -> P x.
Proof.
  ins; eapply Forall_forall; eauto.
Qed.

Lemma Forall_app_cons A (P : A -> Prop) l e l' :
  Forall P (l ++ e :: l') -> Forall P (l ++ l').
Proof.
  rewrite !Forall_app, Forall_cons; ins; desf.
Qed.

Definition ForallE := Forall_forall.

(** [dprod] *)
(******************************************************************************)

Fixpoint dprod A B al (f : A -> list B) :=
  match al with
    | nil => nil
    | a :: al => map (fun b => (a, b)) (f a) ++ dprod al f
  end.

Lemma in_dprod_iff A B x al (f : A -> list B) :
  In x (dprod al f) <-> In (fst x) al /\ In (snd x) (f (fst x)).
Proof.
  induction al; ins; rewrite ?in_app_iff, ?in_map_iff, ?IHal; try clear IHal;
  split; ins; desf; ins; eauto; destruct x; ins; eauto.
Qed.


(** [seq] *)
(******************************************************************************)

Lemma seq0 a : seq a 0 = nil.
Proof. ins. Qed.

Lemma seqS_hd a n : seq a (S n) = a :: seq (S a) n.
Proof. ins. Qed.

Lemma seqS a n : seq a (S n) = seq a n ++ (a + n) :: nil.
Proof.
  revert a; induction n; ins.
    f_equal; lia.
  rewrite IHn; do 3 f_equal; lia.
Qed.

Lemma in_seq_iff a n l : In a (seq n l) <-> n <= a < n + l.
Proof.
  revert n; induction l; ins; rewrite ?IHl; lia.
Qed.

Lemma in_seq0_iff x a : In x (seq 0 a) <-> x < a.
Proof.
  rewrite in_seq_iff; lia.
Qed.

Lemma nodup_seq n l : NoDup (seq n l).
Proof.
  revert n; induction l; ins; constructor; ins; eauto.
  rewrite in_seq_iff; lia.
Qed.

Lemma seq_split :
  forall x a y,
    x <= y ->
    seq a y = seq a x ++ seq (x + a) (y - x).
Proof.
  induction x; ins; rewrite ?Nat.sub_0_r; ins.
  destruct y; ins; try lia.
  f_equal; rewrite IHx; repeat (f_equal; try lia).
Qed.

Lemma seq_split_gen :
  forall l n a,
  n <= a < n + l ->
  seq n l = seq n (a - n) ++ a :: seq (S a) (l + n - a - 1).
Proof.
  induction l; ins; desf; ins; try lia.
    repeat f_equal; lia.
  destruct (eqP n (S n0)); subst.
    replace (n0 - n0) with 0 by lia; ins; repeat f_equal; lia.
  rewrite IHl with (a := S n0); try lia.
  desf; ins; try replace (n0 - n2) with (S (n0 - S n2)) by lia;
  ins; repeat (f_equal; try lia).
Qed.

Lemma seq_split_perm :
  forall l a,
  a < l ->
  exists l', Permutation (seq 0 l) (a :: l') /\ ~ In a l'.
Proof.
  ins; eapply In_NoDup_Permutation;
    eauto using nodup_seq; apply in_seq_iff; lia.
Qed.

Lemma seq_split0 :
  forall l a,
  a < l ->
  seq 0 l = seq 0 a ++ a :: seq (S a) (l - a - 1).
Proof.
  ins; rewrite seq_split_gen with (a := a); repeat f_equal; lia.
Qed.

Lemma seq_add len1 len2 start :
  seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
Proof.
  rewrite seq_split with (x := len1); try lia.
  f_equal; f_equal; lia.
Qed.

Lemma seq_eq_nil start len :
  seq start len = nil <-> len = 0.
Proof.
  destruct len; ins.
Qed.

Lemma seq_eq_cons start len x l :
  seq start len = x :: l
  <-> match len with
        0 => False
      | S len' => start = x /\ seq (S x) len' = l
      end.
Proof.
  desf; split; ins; desf.
Qed.

Lemma seq_eq_app start len l l' :
  seq start len = l ++ l'
  <-> length l <= len /\
      seq start (length l) = l /\
      seq (start + length l) (len - length l) = l'.
Proof.
  revert start len; induction l; ins.
    repeat split; ins; desf; f_equal; lia.
    destruct len; ins.
      split; ins; desf; lia.
    specialize (IHl (S start) len); intuition; desf; intuition; auto using f_equal.
    rewrite Nat.add_succ_comm in *; ins.
    rewrite Nat.add_succ_comm in *; auto using f_equal, le_S_n.
Qed.

Lemma map_nth_seq A (f : nat -> A) a d l
  (EQ: forall i (LTi : i < length l), f (a + i) = nth i l d) :
  map f (seq a (length l)) = l.
Proof.
  revert a EQ; induction l; ins; f_equal.
    rewrite <- (EQ 0); try rewrite Nat.add_0_r; ins; lia.
  eapply IHl; ins; rewrite <- Nat.add_succ_r.
  eapply (EQ (S i)); lia.
Qed.

Lemma map_seq_shift A (f g : nat -> A) a b n
  (EQ: forall i (LTi : i < n), f (a + i) = g (b + i)) :
  map f (seq a n) = map g (seq b n).
Proof.
  induction n; try done.
  rewrite !seqS, !map_app; ins; f_equal.
  apply IHn; ins; apply EQ; lia.
  f_equal; apply EQ; ins.
Qed.

Global Opaque seq.

Lemma filterP_map_seq_eq A (f : A -> Prop) fl a n m
      (Fn : forall i, f (fl i) -> i < a + n)
      (Fm : forall i, f (fl i) -> i < a + m) :
  filterP f (map fl (seq a n)) = filterP f (map fl (seq a m)).
Proof.
  destruct (lt_eq_lt_dec n m) as [[LT|]|LT]; desf.
  { rewrite seq_split with (x := n) (y := m); try lia.
    rewrite map_app, filterP_app.
    symmetry; rewrite app_eq_prefix, filterP_eq_nil; ins.
    rewrite in_map_iff in *; desf.
    rewrite in_seq_iff in *.
    apply Fn in COND; lia.
  }
  { rewrite seq_split with (x := m) (y := n); try lia.
    rewrite map_app, filterP_app.
    rewrite app_eq_prefix, filterP_eq_nil; ins.
    rewrite in_map_iff in *; desf.
    rewrite in_seq_iff in *.
    apply Fm in COND; lia.
  }
Qed.

Lemma nth_filterP A (f : A -> Prop) (l : list A) i d
      (LT : i < length (filterP f l)) :
  exists n, n < length l
            /\ nth i (filterP f l) d = nth n l d
            /\ i = length (filterP f (map (fun i => nth i l d)
                                          (List.seq 0 n))).
Proof.
  revert i LT; induction l using rev_induction; ins; desf; ins; try lia.
  rewrite filterP_app, length_app in *.
  destruct (lt_dec i (length (filterP f l))).
  { specialize_full IHl; eauto; desf.
    exists n; rewrite !app_nth1; splits; ins; try lia.
    do 2 f_equal; apply map_ext_in; ins; rewrite in_seq0_iff in *;
      rewrite app_nth1; ins; lia.
  }
  ins; desf; ins; try lia.
  assert (i = length (filterP f l)) by lia; desf.
  exists (length l); splits; try lia.
  rewrite !app_nth2, !Nat.sub_diag; ins; try lia.
  do 2 f_equal.
  symmetry; eapply map_nth_seq with (d := d); ins.
  apply app_nth1; ins.
Qed.


Lemma nth_filterP' A (f : A -> Prop) (l : list A) n d
      (LT : n < length l) (F: f (nth n l d)):
  nth (length (filterP f (map (fun i => nth i l d)
                              (List.seq 0 n))))
      (filterP f l) d = nth n l d.
Proof.
  revert n F LT; induction l using rev_induction; ins; desf; ins; try lia.
  rewrite filterP_app, length_app in *.
  destruct (lt_dec n (length l)).
  { rewrite !app_nth1 in *; ins.
    specialize_full IHl; eauto; desf.
    rewrite <- IHl.
    do 3 f_equal; apply map_ext_in; ins; rewrite in_seq0_iff in *;
      rewrite app_nth1; ins; lia.
    erewrite <- map_nth_seq
      with (a := 0) (l := l)
           (f := fun i => nth i (l ++ a :: nil) d) at 1; auto using app_nth1.
    rewrite (seq_split0 l0), map_app, filterP_app, length_app; ins; desf; ins;
      try lia.
  }
  ins; desf; ins.
  all: assert (n = length l) by lia; desf.
  all: rewrite app_nth2, Nat.sub_diag in F; ins; desf; try lia.
  rewrite map_nth_seq with (d := d).
    rewrite !app_nth2, ?Nat.sub_diag; ins.
  ins; rewrite app_nth1; ins.
Qed.


(** [mk_list] *)
(******************************************************************************)

Fixpoint mk_list n A (f: nat -> A) :=
  match n with
      0 => nil
    | S n => mk_list n f ++ f n :: nil
  end.

Lemma mk_listE n A (f: nat -> A) :
  mk_list n f = map f (seq 0 n).
Proof.
  induction n; ins; rewrite IHn.
  rewrite seq_split with (x:=n) (y:=S n); try lia.
  by rewrite map_app, plus_0_r, <- minus_Sn_m, minus_diag.
Qed.

Lemma in_mk_list_iff A (x: A) n f :
  In x (mk_list n f) <-> exists m, m < n /\ x = f m.
Proof.
  induction n; ins; try (rewrite in_app_iff, IHn; clear IHn); desc;
    split; ins; desf; try lia; try (by repeat eexists; lia).
  destruct (eqP m n); desf; eauto.
  left; repeat eexists; ins; lia.
Qed.

Lemma mk_list_length A n (f : nat -> A) :
  length (mk_list n f) = n.
Proof.
  induction n; ins; rewrite app_length; ins; lia.
Qed.

Lemma mk_list_nth A i n f (d : A) :
  nth i (mk_list n f) d = if le_lt_dec n i then d else f i.
Proof.
  induction n; ins; desf; rewrite app_nth; desf;
  rewrite mk_list_length in *; desf; try lia.
    apply nth_overflow; ins; lia.
  by assert (i = n) by lia; desf; rewrite minus_diag.
Qed.

Definition length_mk_list := mk_list_length.
Definition nth_mk_list := mk_list_nth.

Hint Rewrite length_mk_list : calc_length.


(** [max_of_list] *)
(******************************************************************************)

Fixpoint max_of_list l :=
  match l with
      nil => 0
    | n :: l => max n (max_of_list l)
  end.

Lemma max_of_list_app l l' :
  max_of_list (l ++ l') = max (max_of_list l) (max_of_list l').
Proof.
  by induction l; ins; rewrite IHl, Max.max_assoc.
Qed.

(** Miscellaneous *)
(******************************************************************************)

Lemma perm_from_subset :
  forall A (l : list A) l',
    NoDup l' ->
    (forall x, In x l' -> In x l) ->
    exists l'', Permutation l (l' ++ l'').
Proof.
  induction l; ins; vauto.
    by destruct l'; ins; vauto; exfalso; eauto.
  destruct (classic (In a l')).

    eapply In_split in H1; desf; rewrite ?nodup_app, ?nodup_cons in *; desf.
    destruct (IHl (l1 ++ l2)); ins.
      by rewrite ?nodup_app, ?nodup_cons in *; desf; repeat split; ins; red;
         eauto using in_cons.
      by specialize (H0 x); rewrite in_app_iff in *; ins; desf;
         destruct (classic (a = x)); subst; try tauto; exfalso; eauto using in_eq.
    eexists; rewrite app_ass in *; ins.
    by eapply Permutation_trans, Permutation_middle; eauto.

  destruct (IHl l'); eauto; ins.
    by destruct (H0 x); auto; ins; subst.
  by eexists (a :: _); eapply Permutation_trans, Permutation_middle; eauto.
Qed.


Lemma list_prod_app A (l l' : list A) B (m : list B) :
  list_prod (l ++ l') m = list_prod l m ++ list_prod l' m.
Proof.
  by induction l; ins; rewrite IHl, app_assoc.
Qed.

Lemma list_prod_nil_r A (l : list A) B :
  list_prod l (@nil B) = nil.
Proof.
  induction l; ins.
Qed.

Lemma list_prod_cons_r A (l : list A) B a (m : list B) :
  Permutation (list_prod l (a :: m)) (map (fun x => (x,a)) l ++ list_prod l m).
Proof.
  induction l; ins.
  eapply Permutation_cons; ins.
  eapply Permutation_trans; [by apply Permutation_app; eauto|].
  rewrite !app_assoc; eauto using Permutation_app, Permutation_app_comm.
Qed.

Lemma list_prod_app_r A (l : list A) B (m m' : list B) :
  Permutation (list_prod l (m ++ m')) (list_prod l m ++ list_prod l m').
Proof.
  induction m; ins; ins.
    by rewrite list_prod_nil_r.
  rewrite list_prod_cons_r.
  eapply Permutation_trans; [by eapply Permutation_app, IHm|].
  rewrite app_assoc; apply Permutation_app; ins.
  symmetry; apply list_prod_cons_r.
Qed.

Lemma Permutation_listprod_r A (l : list A) B (m m' : list B) :
  Permutation m m' ->
  Permutation (list_prod l m) (list_prod l m').
Proof.
  ins; revert l; induction H; ins; eauto using Permutation.
    by rewrite ?list_prod_cons_r; eauto using Permutation_app.
  rewrite list_prod_cons_r.
  eapply Permutation_trans; [by apply Permutation_app, list_prod_cons_r|].
  symmetry.
  rewrite list_prod_cons_r.
  eapply Permutation_trans; [by apply Permutation_app, list_prod_cons_r|].
  rewrite !app_assoc; eauto using Permutation_app, Permutation_app_comm.
Qed.

Ltac in_simp :=
  try match goal with |- ~ _ => intro end;
  repeat first [
    rewrite in_rev_iff in * |
    rewrite in_undup_iff in * |
    rewrite in_flatten_iff in *; desc; clarify |
    rewrite in_map_iff in *; desc; clarify |
    rewrite in_seq0_iff in *; desc; clarify |
    rewrite in_mk_list_iff in *; desc; clarify |
    rewrite in_seq_iff in *; desc; clarify |
    rewrite in_filter_iff in *; desc; clarify |
    rewrite in_filterP_iff in *; desc; clarify ].

Ltac in_des :=
  try match goal with |- ~ _ => intro end;
  repeat first [
    rewrite in_rev_iff in * |
    rewrite in_undup_iff in * |
    rewrite in_flatten_iff in *; desc; clarify |
    rewrite in_map_iff in *; desc; clarify |
    rewrite in_seq0_iff in *; desc; clarify |
    rewrite in_mk_list_iff in *; desc; clarify |
    rewrite in_seq_iff in *; desc; clarify |
    rewrite in_filter_iff in *; desc; clarify |
    rewrite in_filterP_iff in *; desc; clarify |
    rewrite in_app_iff in *; des].
