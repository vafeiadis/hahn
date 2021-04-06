(******************************************************************************)
(** Lifting of relations to partial equivalence classes                       *)
(******************************************************************************)

Require Import HahnBase HahnSets HahnRelationsBasic.
Require Import Setoid HahnEquational.

Set Implicit Arguments.

Definition rel_classes T (eqv : relation T) (X : T -> Prop) :=
  exists x, X ≡₁ eqv x.

Definition rel_lift T (eqv r : relation T) (X Y : T -> Prop) :=
  exists x y, r x y /\ X ≡₁ eqv x /\ Y ≡₁ eqv y.

Definition rel_delift T (eqv : relation T) (r : relation (T -> Prop)) x y :=
  r (eqv x) (eqv y) /\ eqv x x /\ eqv y y.

Global Hint Unfold rel_classes rel_lift rel_delift : unfolderDb.

Add Parametric Morphism A : (@rel_lift A) with signature
  same_relation ==> same_relation ==> same_relation as rel_lift_more.
Proof.
  autounfold with unfolderDb in *; splits; ins; desf;
    do 2 eexists; splits; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@rel_lift A) with signature
  eq ==> inclusion ==> inclusion as rel_lift_mori.
Proof.
  autounfold with unfolderDb in *; splits; ins; desf;
    do 2 eexists; splits; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@rel_delift A) with signature
  eq ==> same_relation ==> same_relation as rel_delift_more.
Proof.
  autounfold with unfolderDb in *; splits; ins; desf; eauto 10.
Qed.

Add Parametric Morphism A : (@rel_delift A) with signature
  eq ==> inclusion ==> inclusion as rel_delift_mori.
Proof.
  autounfold with unfolderDb in *; ins; desf; eauto 10.
Qed.

Section lift_lemmas.

Variable T : Type.
Variables eqv r : relation T.
Hypothesis REFL: forall x y, r x y \/ r y x -> eqv x x.
Hypothesis SYM: symmetric eqv.
Hypothesis TRAN: transitive eqv.

Local Ltac u :=
  autounfold with unfolderDb in *; desc.

Lemma eq_class_expand x y z (D: r x z \/ r z x \/ r y z \/ r z y) :
  eqv x ≡₁ eqv y <-> eqv x y.
Proof using REFL SYM TRAN.
  u; intuition; eauto.
Qed.  

Lemma step_lift x y :
  r x y -> (rel_lift eqv r) (eqv x) (eqv y).
Proof using.
  u; eauto 10.
Qed.

Lemma step_lift_iff x y :
  (rel_lift eqv r) (eqv x) (eqv y) <-> (eqv ⨾ r ⨾ eqv) x y.
Proof using REFL SYM TRAN.
  u; split; induction 1; desf; eauto.
  { repeat eexists; try apply H; splits; eauto. }
  all: do 2 eexists; splits; try edone; ins; desf; eauto.
Qed.

Lemma ct_lift :
  (rel_lift eqv r)⁺ ≡ rel_lift eqv (r ⨾ eqv)⁺.
Proof using REFL SYM TRAN.
  split; red; ins.
  { u; induction H; desf; eauto.
    { do 2 eexists; splits; eauto 6 using t_step. }
    exists x1, y0; splits; try eapply t_trans with x0; eauto.
    apply ct_end in IHclos_trans1; u.
    apply ct_end; u; do 2 (eexists; split; eauto).
  }
  red in H; desf; generalize dependent x; generalize dependent y.
  apply clos_trans_t1n in H.
  induction H; ins; desf; red in H; desc.
    apply t_step; u; do 2 eexists; splits; eauto.
  eapply t_trans; eauto.
  eapply t_step; u; do 2 eexists; splits; eauto.
Qed.

Lemma acyclic_lift :
  acyclic (rel_lift eqv r) <-> acyclic (r ⨾ eqv).
Proof using REFL SYM TRAN.
  unfold acyclic; rewrite ct_lift.
  unfold rel_lift, irreflexive; split; ins; desc; eauto 6.
  apply (H x0), ct_end; apply ct_end in H0; u; eauto 10.
Qed.

Lemma delift_restr_classes rel :
  rel_delift eqv (restr_rel (rel_classes eqv) rel) ≡ rel_delift eqv rel.
Proof using.
  u; intuition; desf; splits; ins; eauto. 
Qed.

Lemma delift_lift rel :
  rel_delift eqv (rel_lift eqv rel) ≡ eqv ⨾ rel ⨾ eqv.
Proof using SYM TRAN.
  u; splits; ins; desf; splits; ins; desf; eauto 8.
  do 2 eexists; splits; eauto.
Qed.

Lemma delift_ct_lift :
  rel_delift eqv (rel_lift eqv r)⁺ ≡ eqv ⨾ (r ⨾ eqv)⁺.
Proof using REFL SYM TRAN.
  rewrite ct_lift, delift_lift, ct_end, !seqA.
  do 3 (apply seq_more; ins).
  u; split; ins; desf; eauto. 
Qed.

End lift_lemmas.
