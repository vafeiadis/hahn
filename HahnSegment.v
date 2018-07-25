(******************************************************************************)
(** * Lemmas about segments of finitely-supported total orders *)
(******************************************************************************)

Require Import HahnBase HahnSets HahnList HahnRelationsBasic HahnWf HahnMinElt.
Require Import HahnEquational HahnSorted.

Set Implicit Arguments.

Lemma fsupp_immediate_pred A (R: relation A)
    (FS: fsupp R) (IRR: irreflexive R) (TRANS: transitive R)
    x (NMIN: ~ min_elt R x):
  exists x', immediate R x' x.
Proof.
  clarify_not.
  apply fsupp_imm_t, ct_end in NMIN; eauto. 
  destruct NMIN; desf; eauto.
Qed.

Section Segments.

Variable A : Type.
Variable cond : A -> Prop.
Variable r : relation A.
Variable STO : strict_total_order cond r.
Variable FSUPP: fsupp r.

(** Every finitely-supported total order has a starting segment *)

Lemma starting_segment_exists x (Cx: cond x):
  exists l, << SORTED: StronglySorted r l >> /\ 
            << INIT: forall x', cond x' /\ r^* x' x <->  In x' l >>.
Proof.
  destruct STO as [[IRR T] TOT]. 
  assert (WF: well_founded (restr_rel cond r)).
    by eauto using wf_restr, fsupp_well_founded.
  apply fsupp_restr with (cond:=cond) in FSUPP.
  induction x using (well_founded_induction WF).
  destruct (classic (min_elt (restr_rel cond r) x)).
  * exists (x :: nil); repeat split; ins; desf; vauto.
    rewrite clos_refl_transE in H2; desf; eauto.
    apply clos_trans_of_transitiveD in H2; eauto; firstorder.
  * forward eapply fsupp_immediate_pred as [y [M N]]; 
      eauto using fsupp_restr, irreflexive_restr, transitive_restr.
    specialize_full H; eauto; red in M; desf.
    exists (l ++ x :: nil); splits; ins.
      rewrite StronglySorted_app_iff, StronglySorted_cons_iff; splits; ins; desf; vauto.
      apply INIT in IN1; desf.
      apply ct_of_trans, ct_end; vauto. 
    rewrite in_app_iff, <- INIT; ins.
    intuition; desf; eauto using clos_refl_trans.
    tertium_non_datur (y = x') as [|NEQ]; desf; eauto using clos_refl_trans.
    apply TOT in NEQ; desf; eauto using clos_refl_trans.
    apply rt_of_trans in H2; ins; red in H2; desf; eauto.
    destruct (N x'); vauto. 
Qed.

Lemma starting_segment_exists_unique x (Cx: cond x):
  exists! l, << SORTED: StronglySorted r l >> /\ 
             << INIT: forall x', cond x' /\ r^* x' x <->  In x' l >>.
Proof.
  assert (X:=starting_segment_exists Cx); desc.
  destruct STO.
  exists l; split; ins; desc.
  eapply StronglySorted_eq; eauto.
  by ins; rewrite <- INIT, INIT0.
Qed.

Definition starting_segment x Cx := 
   proj1_sig (constructive_definite_description _ 
                (@starting_segment_exists_unique x Cx)).

Lemma starting_segment_property x (Cx: cond x) : 
  << SORTED: StronglySorted r (starting_segment Cx) >> /\ 
  << INIT: forall x', cond x' /\ r^* x' x <->  In x' (starting_segment Cx) >>.
Proof.
  unfold starting_segment; match goal with [ |- context[proj1_sig ?t] ] => destruct t end; 
    eauto.
Qed.

Lemma in_starting_segment_iff x (Cx: cond x) z :
  In z (starting_segment Cx) <-> cond z /\ r＊ z x.
Proof.
  symmetry; apply starting_segment_property.
Qed.

Lemma starting_segment_contains_endpoint x (Cx: cond x) :
  In x (starting_segment Cx).
Proof.
  apply in_starting_segment_iff; vauto.
Qed.

Lemma start_of_starting_endpoint x (Cx: cond x) :
  exists l, starting_segment Cx = l ++ x :: nil.
Proof.
  assert (X:=starting_segment_contains_endpoint Cx).
  apply in_split in X; desf.
  enough (l2 = nil) by (desf; eauto). 
  assert (Y:=starting_segment_property Cx); desf.
  rewrite X in *; clear X.
  apply StronglySorted_app_iff, proj2, proj1 in SORTED.
  apply StronglySorted_cons_iff, proj2 in SORTED.
  destruct l2; ins.
  rewrite Forall_cons in *.
  assert (r^* a x) by (apply INIT; eauto with hahn).
  destruct STO as [[IRR T] TOT]. 
  exfalso; eapply IRR, ct_of_trans, t_rt_step; desf; vauto.
Qed.  

Lemma NoDup_starting_segment x (Cx: cond x) :
  NoDup (starting_segment Cx).
Proof.
  destruct STO as [[IRR T] TOT]. 
  eapply NoDup_StronglySorted; eauto. 
  apply starting_segment_property.
Qed.

Lemma not_in_starting_segment x (Cx: cond x) y (Cy: cond y):
  ~ In y (starting_segment Cx) -> r x y.
Proof.
  ins; apply NNPP; intro.
  destruct H; apply starting_segment_property.
  split; ins.
  destruct STO as [[IRR T] TOT]. 
  specialize (TOT _ Cx _ Cy).
  apply imply_to_or in TOT; desf; clarify_not; vauto.
Qed.



(* NB: Cy is not necessary, but it is easier to use the lemma with it. *)
Lemma start_of_starting_segment x (Cx : cond x) y (Cy : cond y) l l':
   starting_segment Cx = l ++ y :: l'
   -> starting_segment Cy = l ++ y :: nil.
Proof.
  assert (T := STO); do 2 (red in T; desc).
  ins; eapply StronglySorted_eq; vauto.
  * by apply starting_segment_property.
  * eapply StronglySorted_app_l.
    rewrite <- app_assoc; ins.
    rewrite <- H.
    by apply starting_segment_property.
  * split; ins.
    + apply starting_segment_property in H0; desc.
      specialize (starting_segment_property Cx); ins; desf; rewrite H in *.
      forward apply (proj1 (INIT x0)) as X.
      { split; ins.
        eapply rt_trans; eauto.
        eapply starting_segment_property. 
        rewrite H; eauto with hahn. }
      rewrite in_app_iff in X; ins; desf; eauto with hahn.
      exfalso.
      apply StronglySorted_app_r, StronglySorted_inv in SORTED; desf.
      rewrite Forall_forall in SORTED0.
      apply SORTED0 in X.
      rewrite clos_refl_transE in H1; desf. 
        eby eapply T.
      apply (ct_of_trans T1) in H1.
      eby eapply T, T1.
    + apply starting_segment_property.
      specialize (starting_segment_property Cx); ins; desf; rewrite H in *.
      forward apply (proj2 (INIT x0)) as X.
        by rewrite in_app_iff in H0; ins; desf; eauto with hahn.
      split; desf.
      clear - H0 SORTED.
      rewrite in_app_iff in *; ins; desf; vauto.
      apply StronglySorted_app_iff in SORTED; desf.
      apply rt_step; eauto with hahn.
Qed.

Definition segment x (Cx : cond x) y (Cy : cond y) :=
  filterP (fun e => ~ In e (starting_segment Cx)) (starting_segment Cy).

Lemma segment_property x (Cx: cond x) y (Cy: cond y):
  ⟪SORTED: StronglySorted r (segment Cx Cy)⟫ /\
  ⟪SEGMENT: forall z, cond z /\ r x z /\ r＊ z y <-> In z (segment Cx Cy)⟫.
Proof.
  ins; splits.
    by apply StronglySorted_filterP, starting_segment_property.
  split; ins; desf.
  * apply in_filterP_iff; split.
      by apply starting_segment_property.
    intro N; apply starting_segment_property in N; desf.
    destruct STO as [[IRR T] TOT]. 
    apply clos_refl_transE in N0; desf; eauto. 
    apply clos_trans_of_transitiveD in N0; eauto.
  * unfold segment in H; apply in_filterP_iff in H; desf.
    apply starting_segment_property in H; desf; splits; try done.
    eby eapply not_in_starting_segment.
Qed.

Lemma in_segment_iff x (Cx: cond x) y (Cy: cond y) z :
  In z (segment Cx Cy) <-> cond z /\ r x z /\ r^* z y.
Proof.
  symmetry; apply segment_property.
Qed.

Lemma starting_segment_decomp x (Cx: cond x) y (Cy: cond y) (Rxy: r^* x y):
  starting_segment Cy = starting_segment Cx ++ segment Cx Cy.
Proof.
  destruct STO as [[IRR T] TOT]. 
  eapply StronglySorted_eq; eauto.
  * by red; eauto.
  * by apply starting_segment_property.
  * apply StronglySorted_app; ins.
      by apply starting_segment_property.
      by apply segment_property.
    apply starting_segment_property in IN1; apply segment_property in IN2; desf.
    rewrite clos_refl_transE in *; desf; eauto.
    all: repeat match goal with H : _⁺ _ _ |- _ => apply (ct_of_trans T) in H end; eauto.
  * ins; rewrite in_app_iff, !in_starting_segment_iff, in_segment_iff.
    intuition; eauto using clos_refl_trans.
    tertium_non_datur (x0 = x) as [->|NEQ]; eauto using clos_refl_trans.
    eapply TOT in NEQ; desf; eauto using clos_refl_trans.
Qed.

End Segments.