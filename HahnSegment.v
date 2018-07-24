(******************************************************************************)
(** * Lemmas about starting segments of finitely-supported total orders *)
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

(** Every finitely-supported total order has a starting segment *)

Lemma starting_segment_exists A cond (r: relation A) 
    (STO: strict_total_order cond r) (FSUPP: fsupp r) x (Cx: cond x):
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

Lemma starting_segment_exists_unique A cond (r: relation A) 
    (STO: strict_total_order cond r) (FSUPP: fsupp r) x (Cx: cond x):
  exists! l, << SORTED: StronglySorted r l >> /\ 
             << INIT: forall x', cond x' /\ r^* x' x <->  In x' l >>.
Proof.
  assert (X:=starting_segment_exists STO FSUPP x Cx); desc.
  destruct STO.
  exists l; split; ins; desc.
  eapply StronglySorted_eq; eauto.
  by ins; rewrite <- INIT, INIT0.
Qed.

Definition starting_segment A cond R STO FSUPP x Cx := 
   proj1_sig (constructive_definite_description _ 
                (@starting_segment_exists_unique A cond R STO FSUPP x Cx)).
   
Lemma starting_segment_property A cond R STO FSUPP x Cx:
  << SORTED: StronglySorted R  (@starting_segment A cond R STO FSUPP x Cx) >> /\ 
  << INIT: forall x', cond x' /\ R^* x' x <->  In x' (@starting_segment A cond R STO FSUPP x Cx) >>.
Proof.
  unfold starting_segment; match goal with [ |- context[proj1_sig ?t] ] => destruct t end; 
    eauto.
Qed.

Lemma starting_segment_contains_endpoint A cond R STO FSUPP x Cx:
  In x (@starting_segment A cond R STO FSUPP x Cx).
Proof.
  apply starting_segment_property; vauto.
Qed.

Lemma start_of_starting_endpoint A cond R STO FSUPP x Cx:
  exists l, @starting_segment A cond R STO FSUPP x Cx = l ++ x :: nil.
Proof.
  assert (X:=starting_segment_contains_endpoint STO FSUPP x Cx).
  apply in_split in X; desf.
  enough (l2 = nil) by (desf; eauto). 
  assert (Y:=starting_segment_property STO FSUPP x Cx); desf.
  rewrite X in *; clear X.
  apply StronglySorted_app_iff, proj2, proj1 in SORTED.
  apply StronglySorted_cons_iff, proj2 in SORTED.
  destruct l2; ins.
  rewrite Forall_cons in *.
  assert (R^* a x) by (apply INIT; eauto with hahn).
  do 2 (red in STO; desc). 
  exfalso; eapply STO, ct_of_trans, ct_end; vauto.
Qed.  

Lemma NoDup_starting_segment A cond R STO FSUPP x Cx:
  NoDup (@starting_segment A cond R STO FSUPP x Cx).
Proof.
  do 2 (red in STO; desc).
  eapply NoDup_StronglySorted; eauto. 
  apply starting_segment_property.
Qed.

Lemma not_in_starting_segment A (cond: A -> Prop) R STO FSUPP x Cx y (Cy: cond y):
  ~ In y (@starting_segment A cond R STO FSUPP x Cx) -> R x y.
Proof.
  ins; apply NNPP; intro.
  destruct H; apply starting_segment_property.
  split; ins.
  red in STO; desf.
  specialize (STO0 _ Cx _ Cy).
  apply imply_to_or in STO0; desf; vauto.
  apply NNPP in STO0; desf; vauto.
Qed.


(* NB: Cy is not necessary, but it is easier to use the lemma with it. *)
Lemma start_of_starting_segment A cond R STO FSUPP x Cx y Cy l l':
   @starting_segment A cond R STO FSUPP x Cx = l ++ y :: l'
   -> @starting_segment A cond R STO FSUPP y Cy = l ++ y :: nil.
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
      specialize (starting_segment_property STO FSUPP x Cx); ins; desf; rewrite H in *.
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
      specialize (starting_segment_property STO FSUPP x Cx); ins; desf; rewrite H in *.
      forward apply (proj2 (INIT x0)) as X.
        by rewrite in_app_iff in H0; ins; desf; eauto with hahn.
      split; desf.
      clear - H0 SORTED.
      rewrite in_app_iff in *; ins; desf; vauto.
      apply StronglySorted_app_iff in SORTED; desf.
      apply rt_step; eauto with hahn.
Qed.

