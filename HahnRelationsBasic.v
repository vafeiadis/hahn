(******************************************************************************)
(** * Basic properties of relations *)
(******************************************************************************)

Require Import HahnBase HahnList.
Require Export Relations.

Set Implicit Arguments.

(* Database of lemmas *)
Create HintDb rel discriminated. 


(** Definitions of relations *)
(******************************************************************************)

(* Make arguments implicit *)
Arguments clos_trans [A] R x y.
Arguments clos_refl_trans [A] R x y.
Arguments union [A] R1 R2 x y.
Arguments reflexive [A] R.
Arguments symmetric [A] R.
Arguments transitive [A] R.
Arguments inclusion {A} R1 R2.
Arguments same_relation {A} R1 R2.
Arguments transp [A] R x y.

Section RelDefs.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variables rel rel' : relation A.
  Variables a b : A.

  Definition immediate :=
    rel a b /\ (forall c (R1: rel a c) (R2: rel c b), False).

  Definition irreflexive := forall x, rel x x -> False.

  Definition is_total X (cond: X -> Prop) (rel: relation X) :=
    forall a (IWa: cond a)
           b (IWb: cond b) (NEQ: a <> b),
      rel a b \/ rel b a.

  Definition restr_subset :=
    forall a (IWa: cond a)
           b (IWb: cond b) (REL: rel a b),
      rel' a b.

  Definition upward_closed (P: A -> Prop) :=
    forall x y (REL: rel x y) (POST: P y), P x.

  Definition singl_rel : relation A := fun x y => x = a /\ y = b.

  Definition inter_rel : relation A := fun x y => rel x y /\ rel' x y.

  Definition minus_rel : relation A := fun x y => rel x y /\ ~ rel' x y.

  Definition eq_rel : relation A := fun x y => f x = f y.

  Definition eqv_rel : relation A := fun x y => x = y /\ cond x.

  Definition eqv_dom_rel dom : relation A := 
    fun x y => x = y /\ In x dom.

  Definition restr_rel : relation A := 
    fun x y => rel x y /\ cond x /\ cond y.

  Definition restr_eq_rel : relation A :=
    fun x y => rel x y /\ f x = f y.

  Definition seq : relation A :=
  fun x y => exists z, rel x z /\ rel' z y.

  Definition clos_refl : relation A := fun x y => x = y \/ rel x y.

  Definition dom_rel := fun x => exists y, rel x y.
  Definition codom_rel := fun y => exists x, rel x y.

  Definition restr_dom := fun x y => rel x y /\ cond y.
  Definition restr_codom := fun x y => rel x y /\ cond y.

End RelDefs.

Definition acyclic A (rel: relation A) := irreflexive (clos_trans rel).

Notation "P ∪ Q" := (union P Q) (at level 50, left associativity).
Notation "P ;; Q" := (seq P Q) (at level 45, right associativity).
Notation "<| a |>" := (eqv_rel a).
(* Notation "[ a ]" := (eqv_rel a). *)
Notation "a ^? " := (clos_refl a) (at level 1).
Notation "a ^+ " := (clos_trans a) (at level 1).
Notation "a ^* " := (clos_refl_trans a) (at level 1).

Notation "a ⊆ b" := (inclusion a b)  (at level 60).
Notation "a ≡ b" := (same_relation a b)  (at level 60).

(* Alternative non-unicode notations *)

Notation "P +++ Q" := (union P Q) (at level 50, left associativity, only parsing).
Notation "a <<= b" := (inclusion a b)  (at level 60, only parsing).
Notation "a <--> b" := (same_relation a b)  (at level 60, only parsing).


(** Very basic properties of relations *)
(******************************************************************************)

Lemma r_refl A (R: relation A) x : clos_refl R x x.
Proof. vauto. Qed.

Lemma r_step A (R: relation A) x y : R x y -> clos_refl R x y.
Proof. vauto. Qed.

Hint Immediate r_refl r_step.

Section BasicProperties.

Variables A B : Type.
Variable dom : A -> Prop.
Variable f: A -> B.
Variables r r' r'' : relation A.

Lemma clos_trans_mon a b :
  clos_trans r a b ->
  (forall a b, r a b -> r' a b) ->
  clos_trans r' a b.
Proof.
  induction 1; ins; eauto using clos_trans.
Qed.

Lemma clos_refl_trans_mon a b :
  clos_refl_trans r a b ->
  (forall a b, r a b -> r' a b) ->
  clos_refl_trans r' a b.
Proof.
  induction 1; ins; eauto using clos_refl_trans.
Qed.

Lemma clos_refl_transE a b :
  clos_refl_trans r a b <-> a = b \/ clos_trans r a b.
Proof.
  split; ins; desf; vauto; induction H; desf; vauto. 
Qed.

Lemma clos_trans_in_rt a b :
  clos_trans r a b -> clos_refl_trans r a b.
Proof.
  induction 1; vauto. 
Qed.

Lemma rt_t_trans a b c :
  clos_refl_trans r a b -> clos_trans r b c -> clos_trans r a c.
Proof.
  ins; induction H; eauto using clos_trans. 
Qed.

Lemma t_rt_trans a b c :
  clos_trans r a b -> clos_refl_trans r b c -> clos_trans r a c.
Proof.
  ins; induction H0; eauto using clos_trans. 
Qed.

Lemma t_step_rt x y : 
  clos_trans r x y <-> exists z, r x z /\ clos_refl_trans r z y.
Proof.
  split; ins; desf.
    by apply clos_trans_tn1 in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma t_rt_step x y : 
  clos_trans r x y <-> exists z, clos_refl_trans r x z /\ r z y.
Proof.
  split; ins; desf.
    by apply clos_trans_t1n in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma clos_trans_of_transitiveD (T: transitive r) x y : 
  clos_trans r x y -> r x y.
Proof.
  induction 1; eauto.
Qed.

Lemma clos_trans_of_transitive (T: transitive r) x y :
  clos_trans r x y <-> r x y.
Proof.
  by split; ins; eauto using t_step; eapply clos_trans_of_transitiveD.
Qed.

Lemma clos_refl_trans_of_transitive (T: transitive r) x y :
  clos_refl_trans r x y <-> clos_refl r x y.
Proof.
  by ins; rewrite clos_refl_transE, clos_trans_of_transitive; ins. 
Qed.

Lemma clos_trans_eq :
  forall B (f : A -> B) 
    (H: forall a b (SB: r a b), f a = f b) a b
    (C: clos_trans r a b),
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

Lemma irreflexive_seqC :
  irreflexive (r ;; r') <-> irreflexive (r' ;; r).
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

Lemma transitive_cr : transitive r -> transitive (clos_refl r).
Proof.
  unfold clos_refl; red; ins; desf; eauto.
Qed.

Lemma transitive_restr : transitive r -> transitive (restr_rel dom r).
Proof.
  unfold restr_rel; red; ins; desf; eauto.
Qed.

Lemma transitive_ct : transitive (clos_trans r).
Proof. vauto. Qed.

Lemma transitive_rt : transitive (clos_refl_trans r).
Proof. vauto. Qed.

Lemma reflexive_rt : reflexive (clos_refl_trans r).
Proof. vauto. Qed.

Lemma reflexive_cr : reflexive (clos_refl r).
Proof. vauto. Qed.

Lemma reflexive_seq : reflexive r -> reflexive r' -> reflexive (r ;; r').
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
  upward_closed (r ;; r') P.
Proof.
  unfold seq; red; ins; desf; eauto.
Qed.

Lemma upward_closed_ct P :
  upward_closed r P -> upward_closed (clos_trans r) P.
Proof.
  induction 2; eauto.
Qed.

Lemma upward_closed_rt P :
  upward_closed r P -> upward_closed (clos_refl_trans r) P.
Proof.
  induction 2; eauto.
Qed.

(** Lemmas about inclusion *)
(******************************************************************************)

Lemma inclusion_refl : reflexive (@inclusion A).
Proof. repeat red; ins. Qed.

Lemma inclusion_trans : transitive (@inclusion A).
Proof. repeat red; eauto. Qed.

Lemma inclusion_refl2 : r ⊆ r.
Proof. done. Qed.

Lemma same_relation_refl2 : r ≡ r.
Proof. split; ins. Qed.

Lemma inclusion_union_r1 : r ⊆ r ∪ r'.
Proof. vauto. Qed.

Lemma inclusion_union_r2 : r' ⊆ r ∪ r'.
Proof. vauto. Qed.

Lemma inclusion_union_l :
  r ⊆ r'' -> r' ⊆ r'' -> r ∪ r' ⊆ r''.
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

Lemma inclusion_seq_mon s s' : r ⊆ r' -> s ⊆ s' -> r ;; s ⊆ r' ;; s'.
Proof.
  unfold inclusion, seq; ins; desf; eauto.
Qed.

Lemma inclusion_seq_refl :
  r ⊆ r'' -> r' ⊆ r'' -> transitive r'' -> r ;; clos_refl r' ⊆ r''.
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

Lemma inclusion_minus_rel : minus_rel r r' ⊆ r.
Proof. 
  unfold minus_rel, inclusion; ins; desf; auto.
Qed.

Lemma inclusion_eqv_rel_true : <| dom |>  ⊆ <| fun _ => True |>.
Proof. 
  unfold eqv_rel, inclusion; ins; desf; auto.
Qed.

(** Inclusions involving reflexive closure. *)

Lemma inclusion_id_cr : <| fun _ => True |> ⊆ clos_refl r'.
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_eqv_cr : <| dom |> ⊆ clos_refl r'.
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_step_cr : r ⊆ r' -> r ⊆ clos_refl r'.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto.
Qed.

Lemma inclusion_r_cr : r ⊆ r' -> clos_refl r ⊆ clos_refl r'.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto.
Qed.

Lemma inclusion_cr_ind :
  reflexive r' -> r ⊆ r' -> clos_refl r ⊆ r'.
Proof. 
  unfold clos_refl; ins; red; ins; desf; eauto.
Qed.

(** Inclusions involving transitive closure. *)

Lemma inclusion_step_t : r ⊆ r' -> r ⊆ clos_trans r'.
Proof.
  unfold seq; red; ins; desf; eauto using t_step.
Qed.

Lemma inclusion_t_rt : clos_trans r ⊆  clos_refl_trans r.
Proof.
  by red; ins; apply clos_trans_in_rt.
Qed.

Lemma inclusion_t_t : r ⊆ r' -> clos_trans r ⊆ clos_trans r'.
Proof.
  by red; ins; eapply clos_trans_mon. 
Qed.

Lemma inclusion_t_t2 : r ⊆ clos_trans r' -> clos_trans r ⊆ clos_trans r'.
Proof.
  induction 2; eauto using clos_trans.
Qed.

Lemma inclusion_t_ind : r ⊆ r' -> transitive r' -> clos_trans r ⊆ r'.
Proof. unfold seq; induction 3; eauto. Qed.

Lemma inclusion_t_ind_left : r ⊆ r' -> r;; r' ⊆ r' -> clos_trans r ⊆ r'.
Proof. 
  unfold seq, inclusion; ins.
  apply clos_trans_t1n in H1; induction H1; eauto.
Qed.

Lemma inclusion_t_ind_right : r ⊆ r' -> r';; r ⊆ r' -> clos_trans r ⊆ r'.
Proof. 
  unfold seq, inclusion; ins.
  apply clos_trans_tn1 in H1; induction H1; eauto.
Qed.

(** Inclusions involving reflexive-transitive closure. *)

Lemma inclusion_id_rt : <| fun _ => True |> ⊆ clos_refl_trans r'.
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_eqv_rt : <| dom |> ⊆ clos_refl_trans r'.
Proof.
  by unfold eqv_rel, inclusion; ins; desf; vauto.
Qed.

Lemma inclusion_step_rt : r ⊆ r' -> r ⊆ clos_refl_trans r'.
Proof.
  unfold seq; red; ins; desf; eauto using rt_step.
Qed.

Lemma inclusion_r_rt : r ⊆ r' -> clos_refl r ⊆ clos_refl_trans r'.
Proof.
  unfold seq, clos_refl; red; ins; desf; eauto using rt_step, rt_refl.
Qed.

Lemma inclusion_rt_rt : r ⊆ r' -> clos_refl_trans r ⊆ clos_refl_trans r'.
Proof.
  red; ins; eapply clos_refl_trans_mon; eauto. 
Qed.

Lemma inclusion_rt_rt2 : r ⊆ clos_refl_trans r' -> clos_refl_trans r ⊆ clos_refl_trans r'.
Proof.
  induction 2; eauto using clos_refl_trans.
Qed.

Lemma inclusion_rt_ind :
  reflexive r' -> r ⊆ r' -> transitive r' -> clos_refl_trans r ⊆ r'.
Proof. unfold seq, eqv_rel; induction 4; eauto. Qed.

Lemma inclusion_rt_ind_left :
  reflexive r' -> r;; r' ⊆ r' -> clos_refl_trans r ⊆ r'.
Proof. 
  unfold seq, eqv_rel, inclusion; ins.
  apply clos_rt_rt1n in H1; induction H1; eauto.
Qed.

Lemma inclusion_rt_ind_right :
  reflexive r' -> r';; r ⊆ r' -> clos_refl_trans r ⊆ r'.
Proof. 
  unfold seq, eqv_rel, inclusion; ins.
  apply clos_rt_rtn1 in H1; induction H1; eauto.
Qed.

Lemma inclusion_seq_trans t : 
  transitive t -> r ⊆ t -> r' ⊆ t -> r;; r' ⊆ t.
Proof.
  unfold seq; red; ins; desf; eauto.
Qed.

Lemma inclusion_seq_rt : 
  r ⊆ clos_refl_trans r'' -> r' ⊆ clos_refl_trans r'' -> 
  r;; r' ⊆ clos_refl_trans r''.
Proof.
  apply inclusion_seq_trans; vauto. 
Qed.

Lemma inclusion_seq_l :
  r ⊆ r' -> reflexive r'' -> r ⊆ r' ;; r''.
Proof. 
  unfold seq, eqv_rel, inclusion; ins; eauto 8. 
Qed.

Lemma inclusion_seq_r :
  reflexive r' -> r ⊆ r'' -> r ⊆ r' ;; r''.
Proof. 
  unfold seq, eqv_rel, inclusion; ins; eauto 8. 
Qed.

End BasicProperties.


Hint Resolve same_relation_refl2.

Hint Resolve 
     reflexive_seq reflexive_rt reflexive_cr 
     transitive_rt transitive_ct 
  : rel.

Hint Resolve
     inclusion_refl2 same_relation_refl2
     inclusion_union_r1 inclusion_union_r2 
     inclusion_union_l inclusion_union_r
     inclusion_seq_mon 
     inclusion_restr_eq_l inclusion_restr_rel_l 
  : rel.

Hint Resolve 
     inclusion_step_t inclusion_t_t inclusion_t_ind inclusion_rt_rt 
     inclusion_r_rt inclusion_step_rt inclusion_step_cr inclusion_r_cr : rel.

Hint Immediate inclusion_acyclic : rel.

Hint Immediate inclusion_t_rt : rel.
Hint Immediate inclusion_eqv_rt inclusion_eqv_cr : rel.

Lemma clos_trans_of_clos_trans A (r : relation A) x y :
  clos_trans (clos_trans r) x y <-> clos_trans r x y.
Proof.
  apply clos_trans_of_transitive; vauto.
Qed.


Lemma clos_trans_of_clos_trans1 A (r r' : relation A) x y :
  clos_trans (fun a b => clos_trans r a b \/ r' a b) x y <->
  clos_trans (fun a b => r a b \/ r' a b) x y.
Proof.
  split; induction 1; desf; 
  eauto using clos_trans, clos_trans_mon.
Qed.


