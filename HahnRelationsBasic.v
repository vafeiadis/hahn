Require Import HahnBase HahnList.
Require Export Relations.

Set Implicit Arguments.

(******************************************************************************)
(** * Relational operators *)
(******************************************************************************)

Arguments clos_trans [A] R x y.
Arguments clos_refl_trans [A] R x y.
Arguments union [A] R1 R2 x y.
Arguments reflexive [A] R.
Arguments symmetric [A] R.
Arguments transitive [A] R.
Arguments antisymmetric [A] R.
Arguments inclusion {A} R1 R2.
Arguments same_relation {A} R1 R2.
Arguments transp [A] R x y.

Section RelDefs.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variables r r' : relation A.

  Definition singl_rel a b : relation A := fun x y => x = a /\ y = b.

  Definition inter_rel : relation A := fun x y => r x y /\ r' x y.

  Definition minus_rel : relation A := fun x y => r x y /\ ~ r' x y.

  Definition eq_rel : relation A := fun x y => f x = f y.

  Definition eqv_rel : relation A := fun x y => x = y /\ cond x.

  Definition eqv_dom_rel dom : relation A :=
    fun x y => x = y /\ In x dom.

  Definition restr_rel : relation A :=
    fun x y => r x y /\ cond x /\ cond y.

  Definition restr_eq_rel : relation A :=
    fun x y => r x y /\ f x = f y.

  Definition seq : relation A :=
    fun x y => exists z, r x z /\ r' z y.

  Definition map_rel (r'' : relation B) : relation A := fun x y => r'' (f x) (f y).

  Definition clos_refl : relation A := fun x y => x = y \/ r x y.

  Definition clos_sym : relation A := fun x y => r x y \/ r y x.

  Definition clos_refl_sym : relation A := fun x y => x = y \/ r x y \/ r y x.

  Definition dom_rel := fun x => exists y, r x y.
  Definition codom_rel := fun y => exists x, r x y.

  Definition collect_rel : relation B := fun x y =>
    exists x' y', r x' y' /\ f x' = x /\ f y' = y.

  Definition immediate : relation A := fun a b =>
    r a b /\ (forall c (R1: r a c) (R2: r c b), False).

  Definition irreflexive := forall x, r x x -> False.

  Definition is_total :=
    forall a (IWa: cond a)
           b (IWb: cond b) (NEQ: a <> b),
      r a b \/ r b a.

  Definition restr_subset :=
    forall a (IWa: cond a)
           b (IWb: cond b) (REL: r a b),
      r' a b.

  Definition upward_closed (P: A -> Prop) :=
    forall x y (REL: r x y) (POST: P y), P x.

  Definition functional := forall x y z, r x y -> r x z -> y=z.

  Definition strict_partial_order := irreflexive /\ transitive r.

  Definition strict_total_order := strict_partial_order /\ is_total.
End RelDefs.

Fixpoint pow_rel A (r: relation A) n :=
  match n with
  | 0 => eqv_rel (fun _ => True)
  | S n => seq (pow_rel r n) r
  end.

Definition bunion A B (P : A -> Prop) (r: A -> relation B) x y :=
  exists a, P a /\ r a x y.

Definition acyclic A (r: relation A) := irreflexive (clos_trans r).

Definition cross_rel A (r r' : A -> Prop) := (fun a b => r a /\ r' b).

Global Hint Unfold reflexive symmetric transitive inclusion same_relation : unfolderDb.
Global Hint Unfold union transp singl_rel inter_rel minus_rel bunion : unfolderDb.
Global Hint Unfold eq_rel eqv_rel eqv_dom_rel restr_rel restr_eq_rel seq map_rel : unfolderDb.
Global Hint Unfold clos_refl clos_sym clos_refl_sym dom_rel codom_rel cross_rel collect_rel : unfolderDb.
Global Hint Unfold immediate irreflexive acyclic is_total functional : unfolderDb.
Global Hint Unfold antisymmetric strict_partial_order strict_total_order : unfolderDb.

(** We introduce the following notation. *)

Notation "P ∩ Q" := (inter_rel P Q) (at level 40, left associativity).
Notation "P ∪ Q" := (union P Q) (at level 50, left associativity).
Notation "P \ Q" := (minus_rel P Q) (at level 46).
Notation "P ⨾ Q" := (seq P Q) (at level 44, right associativity).
Notation "⦗ a ⦘" := (eqv_rel a) (format "⦗ a ⦘").
Notation "∅₂" := (fun _ _ => False).
Notation "P × Q" := (cross_rel P Q) (at level 29, left associativity).

Notation "f ↑ P" := (collect_rel f P) (at level 30).
Notation "f ↓ Q" := (map_rel f Q) (at level 30).

Notation "a ⁻¹" := (transp a) (at level 1, format "a ⁻¹").

Notation "a ^?" := (clos_refl a) (at level 1, format "a ^?").
Notation "a ⁺" := (clos_trans a) (at level 1, format "a ⁺").
Notation "a ＊" := (clos_refl_trans a) (at level 1, format "a ＊").
Notation "a ^⋈" := (clos_sym a) (at level 1, format "a ^⋈").
Notation "a ^⋈?" := (clos_refl_sym a) (at level 1, format "a ^⋈?").

Notation "a ^^ n" := (pow_rel a n) (at level 1).

Notation "a ⊆ b" := (inclusion a b)  (at level 60).
Notation "a ≡ b" := (same_relation a b)  (at level 60).

Notation "⋃ x ∈ s , a" := (bunion s (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  ∈  s ,  '/ ' a ']'").
Notation "'⋃' x , a" := (bunion (fun _ => True) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x ,  '/ ' a ']'").
Notation "'⋃' x < n , a" := (bunion (fun t => t < n) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  <  n ,  '/ ' a ']'").
Notation "'⋃' x <= n , a" := (bunion (fun t => t <= n) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  <=  n ,  '/ ' a ']'").
Notation "'⋃' x > n , a" := (bunion (fun t => n < t) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  >  n ,  '/ ' a ']'").
Notation "'⋃' x >= n , a" := (bunion (fun t => n <= t) (fun x => a))
  (at level 200, x ident, right associativity,
   format "'[' ⋃ '/ ' x  >=  n ,  '/ ' a ']'").

(** Here are some alternative non-unicode notations *)

Notation "P +++ Q" := (union P Q) (at level 50, left associativity, only parsing).
Notation "P ;; Q" := (seq P Q) (at level 44, right associativity, only parsing).
Notation "<| a |>" := (eqv_rel a) (only parsing).
Notation "a ^+" := (clos_trans a) (at level 1, only parsing).
Notation "a ^*" := (clos_refl_trans a) (at level 1, only parsing).
Notation "a ^{-1}" := (transp a) (at level 1, only parsing).
Notation "a <<= b" := (inclusion a b)  (at level 60, only parsing).
Notation "a <--> b" := (same_relation a b)  (at level 60, only parsing).

(******************************************************************************)
(** ** Very basic properties *)
(******************************************************************************)

Lemma r_refl A (r: relation A) x : r^? x x.
Proof. vauto. Qed.

Lemma r_step A (r: relation A) x y : r x y -> r^? x y.
Proof. vauto. Qed.

Global Hint Immediate r_refl r_step : core hahn.

Section BasicProperties.

Variables A B : Type.
Variable dom : A -> Prop.
Variable f: A -> B.
Variables r r' r'' : relation A.

Lemma immediateE : immediate r ≡ r \ (r ⨾ r).
Proof.
  unfold immediate, seq, minus_rel.
  repeat split; try red; ins; desf; eauto.
Qed.

Lemma clos_trans_mon a b :
  r⁺ a b ->
  (forall a b, r a b -> r' a b) ->
  r'⁺ a b.
Proof.
  induction 1; ins; eauto using clos_trans.
Qed.

Lemma clos_refl_trans_mon a b :
  r＊ a b ->
  (forall a b, r a b -> r' a b) ->
  r'＊ a b.
Proof.
  induction 1; ins; eauto using clos_refl_trans.
Qed.

Lemma clos_refl_transE a b :  r＊ a b <-> a = b \/ r⁺ a b.
Proof.
  split; ins; desf; vauto; induction H; desf; vauto.
Qed.

Lemma clos_trans_in_rt a b : r⁺ a b -> r＊ a b.
Proof.
  induction 1; vauto.
Qed.

Lemma rt_t_trans a b c : r＊ a b -> r⁺ b c -> r⁺ a c.
Proof.
  ins; induction H; eauto using clos_trans.
Qed.

Lemma t_rt_trans a b c : r⁺ a b -> r＊ b c -> r⁺ a c.
Proof.
  ins; induction H0; eauto using clos_trans.
Qed.

Lemma t_step_rt x y : r⁺ x y <-> (exists z, r x z /\ r＊ z y).
Proof.
  split; ins; desf.
    by apply clos_trans_tn1 in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma t_rt_step x y : r⁺ x y <-> (exists z, r＊ x z /\ r z y).
Proof.
  split; ins; desf.
    by apply clos_trans_t1n in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma clos_trans_of_transitiveD (T: transitive r) x y :
  r⁺ x y -> r x y.
Proof.
  induction 1; eauto.
Qed.

Lemma clos_trans_of_transitive (T: transitive r) x y :
  r⁺ x y <-> r x y.
Proof.
  by split; ins; eauto using t_step; eapply clos_trans_of_transitiveD.
Qed.

Lemma clos_refl_trans_of_transitive (T: transitive r) x y :
  r＊ x y <-> r^? x y.
Proof.
  by ins; rewrite clos_refl_transE, clos_trans_of_transitive; ins.
Qed.

Lemma clos_trans_eq :
  forall B (f : A -> B)
    (H: forall a b (SB: r a b), f a = f b) a b
    (C: r⁺ a b),
  f a = f b.
Proof.
  ins; induction C; eauto; congruence.
Qed.

Lemma trans_irr_acyclic :
  irreflexive r -> transitive r -> acyclic r.
Proof.
  eby repeat red; ins; eapply H, clos_trans_of_transitiveD.
Qed.

Lemma is_total_restr :
  is_total dom r ->
  is_total dom (restr_rel dom r).
Proof.
  red; ins; eapply H in NEQ; eauto; desf; vauto.
Qed.

Lemma clos_trans_restrD x y :
  clos_trans (restr_rel dom r) x y -> dom x /\ dom y.
Proof.
  unfold restr_rel; induction 1; ins; desf.
Qed.

Lemma clos_trans_restr_eqD x y :
  clos_trans (restr_eq_rel f r) x y -> f x = f y.
Proof.
  unfold restr_eq_rel; induction 1; ins; desf; congruence.
Qed.

Lemma acyclic_antisymmetric :
  acyclic r -> antisymmetric r.
Proof.
  clear; autounfold with unfolderDb; intuition.
  exfalso; eauto using clos_trans.
Qed.

Lemma trans_irr_antisymmetric :
  irreflexive r -> transitive r -> antisymmetric r.
Proof.
  auto using acyclic_antisymmetric, trans_irr_acyclic.
Qed.

Lemma strict_partial_order_antisymmetric :
  strict_partial_order r -> antisymmetric r.
Proof.
  unfold strict_partial_order; ins; desc.
  auto using trans_irr_antisymmetric.
Qed.

Lemma irreflexive_inclusion:
  r ⊆ r' ->
  irreflexive r' ->
  irreflexive r.
Proof.
  unfold irreflexive, inclusion; eauto.
Qed.

Lemma irreflexive_union :
  irreflexive (r ∪ r') <-> irreflexive r /\ irreflexive r'.
Proof.
  unfold irreflexive, union; repeat split;
  try red; ins; desf; eauto.
Qed.

Lemma irreflexive_bunion (s : B -> Prop) (rr : B -> relation A) :
  irreflexive (bunion s rr) <-> forall x, s x -> irreflexive (rr x).
Proof.
  unfold irreflexive, bunion; repeat split;
  try red; ins; desf; eauto.
Qed.

Lemma irreflexive_seqC :
  irreflexive (r ⨾ r') <-> irreflexive (r' ⨾ r).
Proof.
  unfold irreflexive, seq; repeat split;
  try red; ins; desf; eauto.
Qed.

Lemma irreflexive_restr :
  irreflexive r -> irreflexive (restr_rel dom r).
Proof.
  unfold irreflexive, restr_rel; ins; desf; eauto.
Qed.

Lemma inclusion_acyclic :
  r ⊆ r' ->
  acyclic r' ->
  acyclic r.
Proof.
  repeat red; ins; eapply H0, clos_trans_mon; eauto.
Qed.

Lemma transitive_cr : transitive r -> transitive r^?.
Proof.
  unfold clos_refl; red; ins; desf; eauto.
Qed.

Lemma transitive_restr : transitive r -> transitive (restr_rel dom r).
Proof.
  unfold restr_rel; red; ins; desf; eauto.
Qed.

Lemma transitive_ct : transitive r⁺.
Proof. vauto. Qed.

Lemma transitive_rt : transitive r＊.
Proof. vauto. Qed.

Lemma reflexive_rt : reflexive r＊.
Proof. vauto. Qed.

Lemma reflexive_cr : reflexive r^?.
Proof. vauto. Qed.

Lemma reflexive_seq : reflexive r -> reflexive r' -> reflexive (r ⨾ r').
Proof. vauto. Qed.

Lemma reflexive_union_l : reflexive r -> reflexive (r ∪ r').
Proof. vauto. Qed.

Lemma reflexive_union_r : reflexive r' -> reflexive (r ∪ r').
Proof. vauto. Qed.

Lemma reflexive_inter : reflexive r -> reflexive r' -> reflexive (r ∩ r').
Proof. vauto. Qed.

Lemma restr_eq_trans :
  transitive r -> transitive (restr_eq_rel f r).
Proof.
  unfold transitive, restr_eq_rel; ins; desf; split; eauto; congruence.
Qed.

Lemma irreflexive_restr_eq :
  irreflexive (restr_eq_rel f r) <-> irreflexive r.
Proof.
  unfold irreflexive, restr_eq_rel; split; ins; desf; eauto.
Qed.

Lemma upward_closed_seq P :
  upward_closed r P ->
  upward_closed r' P ->
  upward_closed (r ⨾ r') P.
Proof.
  unfold seq; red; ins; desf; eauto.
Qed.

Lemma upward_closed_ct P :
  upward_closed r P -> upward_closed r⁺ P.
Proof.
  induction 2; eauto.
Qed.

Lemma upward_closed_rt P :
  upward_closed r P -> upward_closed r＊ P.
Proof.
  induction 2; eauto.
Qed.

(** Lemmas about inclusion *)
(******************************************************************************)

Lemma eq_in_l : r ≡ r' -> r ⊆ r'.
Proof. by destruct 1. Qed.

Lemma eq_in_r : r ≡ r' -> r' ⊆ r.
Proof. by destruct 1. Qed.

Lemma inclusion_refl : reflexive (@inclusion A).
Proof. repeat red; ins. Qed.

Lemma inclusion_trans : transitive (@inclusion A).
Proof. repeat red; eauto. Qed.

Lemma inclusion_refl2 : r ⊆ r.
Proof. done. Qed.

Lemma same_relation_refl2 : r ≡ r.
Proof. split; ins. Qed.

Lemma inclusion_inter_l1 : r ∩ r' ⊆ r.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_l2 : r ∩ r' ⊆ r'.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_l1_search : r ⊆ r'' -> r ∩ r' ⊆ r''.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_l2_search : r' ⊆ r'' -> r ∩ r' ⊆ r''.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_r : r ⊆ r' -> r ⊆ r'' -> r ⊆ r' ∩ r''.
Proof. clear; firstorder. Qed.

Lemma inclusion_inter_mon s s' : r ⊆ r' -> s ⊆ s' -> r ∩ s ⊆ r' ∩ s'.
Proof. clear; firstorder. Qed.

Lemma inclusion_union_r1 : r ⊆ r ∪ r'.
Proof. vauto. Qed.

Lemma inclusion_union_r2 : r' ⊆ r ∪ r'.
Proof. vauto. Qed.

Lemma inclusion_union_l : r ⊆ r'' -> r' ⊆ r'' -> r ∪ r' ⊆ r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_r1_search : r ⊆ r' -> r ⊆ r' ∪ r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_r2_search : r ⊆ r'' -> r ⊆ r' ∪ r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_r :
  r ⊆ r' \/ r ⊆ r'' -> r ⊆ r' ∪ r''.
Proof.
  unfold union; red; intros; desf; auto.
Qed.

Lemma inclusion_union_mon s s' :
  r ⊆ r' -> s ⊆ s' -> r ∪ s ⊆ r' ∪ s'.
Proof.
  unfold inclusion, union; ins; desf; eauto.
Qed.

Lemma inclusion_bunion_l (P : B -> Prop) (rr : B -> relation A) :
  (forall x, P x -> rr x ⊆ r') -> bunion P rr ⊆ r'.
Proof.
  clear; firstorder.
Qed.

Lemma inclusion_bunion_r (x: B) (P : B -> Prop) (rr : B -> relation A) :
  P x -> r ⊆ rr x -> r ⊆ bunion P rr.
Proof.
  clear; firstorder.
Qed.

Lemma inclusion_seq_mon s s' : r ⊆ r' -> s ⊆ s' -> r ⨾ s ⊆ r' ⨾ s'.
Proof.
  unfold inclusion, seq; ins; desf; eauto.
Qed.

Lemma inclusion_seq_refl :
  r ⊆ r'' -> r' ⊆ r'' -> transitive r'' -> r ⨾ r'^? ⊆ r''.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto.
Qed.

Lemma inclusion_restr : restr_rel dom r ⊆ r.
Proof.
  unfold inclusion, restr_rel; ins; desf.
Qed.

Lemma inclusion_restr_rel_l : r ⊆ r' -> restr_rel dom r ⊆ r'.
Proof.
  unfold inclusion, seq, restr_rel; ins; desf; eauto.
Qed.

Lemma inclusion_restr_eq : restr_eq_rel f r ⊆ r.
Proof.
  unfold restr_eq_rel, inclusion; ins; desf.
Qed.

Lemma inclusion_restr_eq_l : r ⊆ r' -> restr_eq_rel f r ⊆ r'.
Proof.
  unfold inclusion, seq, restr_eq_rel; ins; desf; eauto.
Qed.

Lemma inclusion_minus_rel : r \ r' ⊆ r.
Proof.
  unfold minus_rel, inclusion; ins; desf; auto.
Qed.

Lemma inclusion_minus_mon s s' : r ⊆ r' -> s' ⊆ s -> r \ s ⊆ r' \ s'.
Proof.
  unfold minus_rel, inclusion, not; ins; desf; eauto.
Qed.

Lemma inclusion_minus_l s : r \ r' ⊆ s <-> r ⊆ r' ∪ s.
Proof.
  unfold minus_rel, union, inclusion; split; ins; desf.
    2: by eapply H in H0; desf; eauto.
  by destruct (classic (r' x y)); eauto.
Qed.

Lemma inclusion_union_minus : r ⊆ (r \ r') ∪ r'.
Proof.
  by unfold minus_rel, union, inclusion; clear; intros; tauto.
Qed.

Lemma inclusion_eqv_rel_true : ⦗dom⦘  ⊆ ⦗fun _ => True⦘.
Proof.
  unfold eqv_rel, inclusion; ins; desf; auto.
Qed.

(** Inclusions involving reflexive closure. *)

Lemma inclusion_id_cr : ⦗fun _ => True⦘ ⊆ r^?.
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_eqv_cr : ⦗dom⦘ ⊆ r^?.
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_step_cr : r ⊆ r' -> r ⊆ r'^?.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto.
Qed.

Lemma inclusion_r_cr : r ⊆ r' -> r^? ⊆ r'^?.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto.
Qed.

Lemma inclusion_cr_ind :
  reflexive r' -> r ⊆ r' -> r^? ⊆ r'.
Proof.
  unfold clos_refl; ins; red; ins; desf; eauto.
Qed.

(** Inclusions involving transitive closure. *)

Lemma inclusion_step_t : r ⊆ r' -> r ⊆ r'⁺.
Proof.
  unfold seq; red; ins; desf; eauto using t_step.
Qed.

Lemma inclusion_t_rt : r⁺ ⊆  r＊.
Proof.
  by red; ins; apply clos_trans_in_rt.
Qed.

Lemma inclusion_t_t : r ⊆ r' -> r⁺ ⊆ r'⁺.
Proof.
  by red; ins; eapply clos_trans_mon.
Qed.

Lemma inclusion_t_t2 : r ⊆ r'⁺ -> r⁺ ⊆ r'⁺.
Proof.
  induction 2; eauto using clos_trans.
Qed.

Lemma inclusion_t_ind : r ⊆ r' -> transitive r' -> r⁺ ⊆ r'.
Proof. unfold seq; induction 3; eauto. Qed.

Lemma inclusion_t_ind_left : r ⊆ r' -> r⨾ r' ⊆ r' -> r⁺ ⊆ r'.
Proof.
  unfold seq, inclusion; ins.
  apply clos_trans_t1n in H1; induction H1; eauto.
Qed.

Lemma inclusion_t_ind_right : r ⊆ r' -> r'⨾ r ⊆ r' -> r⁺ ⊆ r'.
Proof.
  unfold seq, inclusion; ins.
  apply clos_trans_tn1 in H1; induction H1; eauto.
Qed.

(** Inclusions involving reflexive-transitive closure. *)

Lemma inclusion_id_rt : ⦗fun _ => True⦘ ⊆ r'＊.
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_eqv_rt : ⦗dom⦘ ⊆ r'＊.
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_step_rt : r ⊆ r' -> r ⊆ r'＊.
Proof.
  unfold seq; red; ins; desf; eauto using rt_step.
Qed.

Lemma inclusion_r_rt : r ⊆ r' -> r^? ⊆ r'＊.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto using rt_step, rt_refl.
Qed.

Lemma inclusion_rt_rt : r ⊆ r' -> r＊ ⊆ r'＊.
Proof.
  red; ins; eapply clos_refl_trans_mon; eauto.
Qed.

Lemma inclusion_rt_rt2 : r ⊆ r'＊ -> r＊ ⊆ r'＊.
Proof.
  induction 2; eauto using clos_refl_trans.
Qed.

Lemma inclusion_rt_ind :
  reflexive r' -> r ⊆ r' -> transitive r' -> r＊ ⊆ r'.
Proof. unfold seq, eqv_rel; induction 4; eauto. Qed.

Lemma inclusion_rt_ind_left :
  reflexive r' -> r⨾ r' ⊆ r' -> r＊ ⊆ r'.
Proof.
  unfold seq, eqv_rel, inclusion; ins.
  apply clos_rt_rt1n in H1; induction H1; eauto.
Qed.

Lemma inclusion_rt_ind_right :
  reflexive r' -> r'⨾ r ⊆ r' -> r＊ ⊆ r'.
Proof.
  unfold seq, eqv_rel, inclusion; ins.
  apply clos_rt_rtn1 in H1; induction H1; eauto.
Qed.

Lemma inclusion_seq_trans t :
  transitive t -> r ⊆ t -> r' ⊆ t -> r⨾ r' ⊆ t.
Proof.
  unfold seq; red; ins; desf; eauto.
Qed.

Lemma inclusion_seq_rt :
  r ⊆ r''＊ -> r' ⊆ r''＊ -> r⨾ r' ⊆ r''＊.
Proof.
  apply inclusion_seq_trans; vauto.
Qed.

Lemma inclusion_seq_l :
  r ⊆ r' -> reflexive r'' -> r ⊆ r' ⨾ r''.
Proof.
  unfold seq, eqv_rel, inclusion; ins; eauto 8.
Qed.

Lemma inclusion_seq_r :
  reflexive r' -> r ⊆ r'' -> r ⊆ r' ⨾ r''.
Proof.
  unfold seq, eqv_rel, inclusion; ins; eauto 8.
Qed.

(** Lemmas about functional relations *)
(******************************************************************************)

Lemma functional_alt :
  functional r <-> r⁻¹ ⨾ r ⊆ ⦗fun _ => True⦘.
Proof.
  unfold functional, seq, transp, eqv_rel, inclusion.
  split; ins; desf; [|apply H]; eauto.
Qed.

Lemma functional_eqv_rel : functional ⦗dom⦘.
Proof.
  unfold functional, eqv_rel; ins; desf.
Qed.

Lemma functional_seq  :
  functional r -> functional r' -> functional (r ⨾ r').
Proof.
  unfold functional, seq; ins; desf.
  assert (z0 = z1); subst; eauto.
Qed.

Lemma functional_union  :
  functional r -> functional r' ->
  (forall x, dom_rel r x -> dom_rel r' x -> False) ->
  functional (r ∪ r').
Proof.
  unfold functional, union, dom_rel; ins; desf; eauto;
    try solve [exfalso; eauto].
Qed.

Lemma functional_inter_l : functional r -> functional (r ∩ r').
Proof. clear; firstorder. Qed.

Lemma functional_inter_r : functional r' -> functional (r ∩ r').
Proof. clear; firstorder. Qed.

Lemma functional_minus : functional r -> functional (r \ r').
Proof. clear; firstorder. Qed.

Lemma functional_restr : functional r -> functional (restr_rel dom r).
Proof. clear; firstorder. Qed.

Lemma functionalE : functional r -> exists f, forall x y, r x y <-> f x = Some y.
Proof.
  clear; unfold functional; ins.
  forward apply unique_choice
    with (R := fun x y => y = None /\ ~ (exists m, r x m) \/
                          exists m, y = Some m /\ r x m) as X; ins; desf.
    by tertium_non_datur (exists m, r x m); desc; [exists (Some m)| exists None];
       split; ins; desf; try f_equal; eauto; try solve [exfalso; eauto].
  exists f; ins; specialize (X x); split; ins; desf; try solve [exfalso; eauto].
  rewrite X; f_equal; eauto.
Qed.

End BasicProperties.

(** Declare several of the above lemmas as hints for [(e)auto]. *)

Global Hint Resolve same_relation_refl2 : core hahn.

Global Hint Resolve
     reflexive_seq reflexive_rt reflexive_cr
     reflexive_union_l reflexive_union_r reflexive_inter
     transitive_rt transitive_ct
  : hahn.

Global Hint Resolve
     inclusion_refl2 same_relation_refl2
     inclusion_inter_l1_search inclusion_inter_l2_search inclusion_inter_r
     inclusion_union_r1 inclusion_union_r2
     inclusion_union_r1_search inclusion_union_r2_search inclusion_union_l
     inclusion_seq_mon inclusion_minus_mon
     inclusion_restr_eq_l inclusion_restr_rel_l
  : hahn.

Global Hint Resolve trans_irr_antisymmetric strict_partial_order_antisymmetric : hahn.

Global Hint Resolve
     inclusion_step_t inclusion_t_t inclusion_t_ind inclusion_rt_rt
     inclusion_r_rt inclusion_step_rt inclusion_step_cr inclusion_r_cr : hahn.

Global Hint Immediate inclusion_acyclic : hahn.

Global Hint Immediate inclusion_t_rt : hahn.
Global Hint Immediate inclusion_eqv_rt inclusion_eqv_cr : hahn.

Lemma clos_trans_of_clos_trans A (r : relation A) x y :
  r⁺⁺ x y <-> r⁺ x y.
Proof.
  apply clos_trans_of_transitive; vauto.
Qed.

Lemma clos_trans_of_clos_trans1 A (r r' : relation A) x y :
  (fun a b => r⁺ a b \/ r' a b)⁺ x y <->
  (fun a b => r a b \/ r' a b)⁺ x y.
Proof.
  split; induction 1; desf;
  eauto using clos_trans, clos_trans_mon.
Qed.
