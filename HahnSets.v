(******************************************************************************)
(** * Operations on sets (unary relations) *)
(******************************************************************************)

Require Import HahnBase.
Require Import Classical Relations.

Set Implicit Arguments.

(** Definitions of set operations *)
(******************************************************************************)

Section SetDefs.

  Variable A : Type.
  Implicit Type s : A -> Prop.

  Definition set_empty       := fun x : A => False.
  Definition set_full        := fun x : A => True.
  Definition set_compl s     := fun x => ~ (s x).
  Definition set_union s s'  := fun x => s x \/ s' x.
  Definition set_inter s s'  := fun x => s x /\ s' x.
  Definition set_minus s s'  := fun x => s x /\ ~ (s' x).
  Definition set_subset s s' := forall x, s x -> s' x.
  Definition set_equiv s s'  := forall x, s x <-> s' x.

End SetDefs.

Arguments set_empty {A}.
Arguments set_full {A}.
Arguments set_subset {A}.
Arguments set_equiv {A}.

Notation "P ∪₁ Q" := (set_union P Q) (at level 50, left associativity).
Notation "P ∩₁ Q" := (set_inter P Q) (at level 40, left associativity).
Notation "P \₁ Q" := (set_minus P Q) (at level 46).
Notation "∅₁"     := (@set_empty _).
Notation "a ⊆₁ b" := (set_subset a b) (at level 60).
Notation "a ≡₁ b" := (set_equiv a b)  (at level 60).

Section SetProperties.
  Local Ltac u :=
    unfold set_union, set_inter, set_minus, set_compl,
           set_equiv, set_subset, set_empty, set_full,
           reflexive, transitive in *;
    ins; try solve [tauto | firstorder].

  Variable A : Type.
  Implicit Type s : A -> Prop.

  (** Properties of set complement. *)

  Lemma set_compl_empty : set_compl ∅₁ ≡₁ @set_full A.
  Proof. u. Qed.

  Lemma set_compl_full : set_compl (@set_full A) ≡₁ ∅₁.
  Proof. u. Qed.

  Lemma set_compl_compl s : set_compl (set_compl s) ≡₁ s.
  Proof. u. Qed.

  Lemma set_compl_union s s' :
    set_compl (s ∪₁ s') ≡₁ set_compl s ∩₁ set_compl s'.
  Proof. u. Qed.

  Lemma set_compl_inter s s' :
    set_compl (s ∩₁ s') ≡₁ set_compl s ∪₁ set_compl s'.
  Proof. u. Qed.

  Lemma set_compl_minus s s' :
    set_compl (s \₁ s') ≡₁ s' ∪₁ set_compl s.
  Proof. u. Qed.

  (** Properties of set union. *)

  Lemma set_unionA s s' s'' : (s ∪₁ s') ∪₁ s'' ≡₁ s ∪₁ (s' ∪₁ s'').
  Proof. u. Qed.

  Lemma set_unionC s s' : s ∪₁ s' ≡₁ s' ∪₁ s.
  Proof. u. Qed.

  Lemma set_unionK s : s ∪₁ s ≡₁ s.
  Proof. u. Qed.

  Lemma set_union_empty_l s : ∅₁ ∪₁ s ≡₁ s.
  Proof. u. Qed.

  Lemma set_union_empty_r s : s ∪₁ ∅₁ ≡₁ s.
  Proof. u. Qed.

  Lemma set_union_full_l s : set_full ∪₁ s ≡₁ set_full.
  Proof. u. Qed.

  Lemma set_union_full_r s : s ∪₁ set_full ≡₁ set_full.
  Proof. u. Qed.

  Lemma set_union_inter_l s s' s'' : (s ∩₁ s') ∪₁ s'' ≡₁ (s ∪₁ s'') ∩₁ (s' ∪₁ s'').
  Proof. u. Qed.

  Lemma set_union_inter_r s s' s'' : s ∪₁ (s' ∩₁ s'') ≡₁ (s ∪₁ s') ∩₁ (s ∪₁ s'').
  Proof. u. Qed.

  (** Properties of set intersection. *)

  Lemma set_interA s s' s'' : (s ∩₁ s') ∩₁ s'' ≡₁ s ∩₁ (s' ∩₁ s'').
  Proof. u. Qed.

  Lemma set_interC s s' : s ∩₁ s' ≡₁ s' ∩₁ s.
  Proof. u. Qed.

  Lemma set_interK s : s ∩₁ s ≡₁ s.
  Proof. u. Qed.

  Lemma set_inter_empty_l s : ∅₁ ∩₁ s ≡₁ ∅₁.
  Proof. u. Qed.

  Lemma set_inter_empty_r s : s ∩₁ ∅₁ ≡₁ ∅₁.
  Proof. u. Qed.

  Lemma set_inter_full_l s : set_full ∩₁ s ≡₁ s.
  Proof. u. Qed.

  Lemma set_inter_full_r s : s ∩₁ set_full ≡₁ s.
  Proof. u. Qed.

  Lemma set_inter_union_l s s' s'' : (s ∪₁ s') ∩₁ s'' ≡₁ (s ∩₁ s'') ∪₁ (s' ∩₁ s'').
  Proof. u. Qed.

  Lemma set_inter_union_r s s' s'' : s ∩₁ (s' ∪₁ s'') ≡₁ (s ∩₁ s') ∪₁ (s ∩₁ s'').
  Proof. u. Qed.

  Lemma set_inter_minus_l s s' s'' : (s \₁ s') ∩₁ s'' ≡₁ (s ∩₁ s'') \₁ s'.
  Proof. u. Qed.

  Lemma set_inter_minus_r s s' s'' : s ∩₁ (s' \₁ s'') ≡₁ (s ∩₁ s') \₁ s''.
  Proof. u. Qed.

  (** Properties of set minus. *)

  Lemma set_minusE s s' : s \₁ s' ≡₁ s ∩₁ set_compl s'.
  Proof. u. Qed.

  Lemma set_minusK s : s \₁ s ≡₁ ∅₁.
  Proof. u. Qed.

  Lemma set_minus_inter_l s s' s'' :
    (s ∩₁ s') \₁ s'' ≡₁ (s \₁ s'') ∩₁ (s' \₁ s'').
  Proof. u. Qed.

  Lemma set_minus_inter_r s s' s'' :
    s \₁ (s' ∩₁ s'') ≡₁ (s \₁ s') ∪₁ (s \₁ s'').
  Proof. u. Qed.

  Lemma set_minus_union_l s s' s'' :
    (s ∪₁ s') \₁ s'' ≡₁ (s \₁ s'') ∪₁ (s' \₁ s'').
  Proof. u. Qed.

  Lemma set_minus_union_r s s' s'' :
    s \₁ (s' ∪₁ s'') ≡₁ (s \₁ s') ∩₁ (s \₁ s'').
  Proof. u. Qed.

  Lemma set_minus_minus_l s s' s'' :
    s \₁ s' \₁ s'' ≡₁ s \₁ (s' ∪₁ s'').
  Proof. u. Qed.

  Lemma set_minus_minus_r s s' s'' :
    s \₁ (s' \₁ s'') ≡₁ (s \₁ s') ∪₁ (s ∩₁ s'').
  Proof. u. Qed.

  (** Properties of set inclusion. *)

  Lemma set_subsetE s s' : s ⊆₁ s' <-> s \₁ s' ≡₁ ∅₁.
  Proof. u; intuition; apply NNPP; firstorder. Qed.

  Lemma set_subset_refl : reflexive _ (@set_subset A).
  Proof. u. Qed.

  Lemma set_subset_trans : transitive _ (@set_subset A).
  Proof. u. Qed.

  Lemma set_subset_empty_l s : ∅₁ ⊆₁ s.
  Proof. u. Qed.

  Lemma set_subset_empty_r s : s ⊆₁ ∅₁ <-> s ≡₁ ∅₁.
  Proof. u. Qed.

  Lemma set_subset_full_l s : set_full ⊆₁ s <-> s ≡₁ set_full.
  Proof. u. Qed.

  Lemma set_subset_full_r s : s ⊆₁ set_full.
  Proof. u. Qed.

  Lemma set_subset_union_l s s' s'' : s ∪₁ s' ⊆₁ s'' <-> s ⊆₁ s'' /\ s' ⊆₁ s''.
  Proof. u. Qed.

  Lemma set_subset_inter_r s s' s'' : s ⊆₁ s' ∩₁ s'' <-> s ⊆₁ s' /\ s ⊆₁ s''.
  Proof. u. Qed.

  Lemma set_subset_compl s s' (S1: s' ⊆₁ s) : set_compl s ⊆₁ set_compl s'.
  Proof. u. Qed.

  Lemma set_subset_inter s s' (S1: s ⊆₁ s') t t' (S2: t ⊆₁ t') : s ∩₁ t ⊆₁ s' ∩₁ t'.
  Proof. u. Qed.

  Lemma set_subset_union s s' (S1: s ⊆₁ s') t t' (S2: t ⊆₁ t') : s ∪₁ t ⊆₁ s' ∪₁ t'.
  Proof. u. Qed.

  Lemma set_subset_minus s s' (S1: s ⊆₁ s') t t' (S2: t' ⊆₁ t) : s \₁ t ⊆₁ s' \₁ t'.
  Proof. u. Qed.

  (** Properties of set equivalence. *)

  Lemma set_equivE s s' : s ≡₁ s' <-> s ⊆₁ s' /\ s' ⊆₁ s.
  Proof. u; firstorder. Qed.

  Lemma set_equiv_refl : reflexive _ (@set_equiv A).
  Proof. u. Qed.

  Lemma set_equiv_symm : symmetric _ (@set_equiv A).
  Proof. u. Qed.

  Lemma set_equiv_trans : transitive _ (@set_equiv A).
  Proof. u. Qed.

  Lemma set_equiv_compl s s' (S1: s ≡₁ s') : set_compl s ≡₁ set_compl s'.
  Proof. u. Qed.

  Lemma set_equiv_inter s s' (S1: s ≡₁ s') t t' (S2: t ≡₁ t') : s ∩₁ t ≡₁ s' ∩₁ t'.
  Proof. u. Qed.

  Lemma set_equiv_union s s' (S1: s ≡₁ s') t t' (S2: t ≡₁ t') : s ∪₁ t ≡₁ s' ∪₁ t'.
  Proof. u. Qed.

  Lemma set_equiv_minus s s' (S1: s ≡₁ s') t t' (S2: t ≡₁ t') : s \₁ t ≡₁ s' \₁ t'.
  Proof. u. Qed.

  Lemma set_equiv_subset s s' (S1: s ≡₁ s') t t' (S2: t ≡₁ t') : s ⊆₁ t <-> s' ⊆₁ t'.
  Proof. u. Qed.

  (** Absorption properties. *)

  Lemma set_union_absorb_l s s' (SUB: s ⊆₁ s') : s ∪₁ s' ≡₁ s'.
  Proof. u; firstorder. Qed.

  Lemma set_union_absorb_r s s' (SUB: s ⊆₁ s') : s' ∪₁ s ≡₁ s'.
  Proof. u; firstorder. Qed.

  Lemma set_inter_absorb_l s s' (SUB: s ⊆₁ s') : s' ∩₁ s ≡₁ s.
  Proof. u; firstorder. Qed.

  Lemma set_inter_absorb_r s s' (SUB: s ⊆₁ s') : s ∩₁ s' ≡₁ s.
  Proof. u; firstorder. Qed.

  Lemma set_minus_absorb_l s s' (SUB: s ⊆₁ s') : s \₁ s' ≡₁ ∅₁.
  Proof. u; firstorder. Qed.

End SetProperties.

(** Add rewriting support. *)

Require Import Setoid Morphisms.

Add Parametric Relation A : (A -> Prop) (set_subset (A:=A))
  reflexivity proved by (set_subset_refl (A:=A))
  transitivity proved by (set_subset_trans (A:=A))
  as set_subset_rel.

Add Parametric Relation A : (A -> Prop) (set_equiv (A:=A))
  reflexivity proved by (set_equiv_refl (A:=A))
  symmetry proved by (set_equiv_symm (A:=A))
  transitivity proved by (set_equiv_trans (A:=A))
  as set_equiv_rel.

Instance set_compl_Proper A : Proper (_ --> _) _ := set_subset_compl (A:=A).
Instance set_union_Proper A : Proper (_ ==> _ ==> _) _ := set_subset_union (A:=A).
Instance set_inter_Proper A : Proper (_ ==> _ ==> _) _ := set_subset_inter (A:=A).
Instance set_minus_Proper A : Proper (_ ++> _ --> _) _ := set_subset_minus (A:=A).

Instance set_compl_Propere A : Proper (_ ==> _) _ := set_equiv_compl (A:=A).
Instance set_union_Propere A : Proper (_ ==> _ ==> _) _ := set_equiv_union (A:=A).
Instance set_inter_Propere A : Proper (_ ==> _ ==> _) _ := set_equiv_inter (A:=A).
Instance set_minus_Propere A : Proper (_ ==> _ ==> _) _ := set_equiv_minus (A:=A).
Instance set_subset_Proper A : Proper (_ ==> _ ==> _) _ := set_equiv_subset (A:=A).

Hint Unfold  set_empty set_full set_compl set_union set_inter set_minus set_subset set_equiv : unfolderDb.
