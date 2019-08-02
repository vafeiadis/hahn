(******************************************************************************)
(** * Decomposing paths and cycles *)
(******************************************************************************)

Require Import Omega.
Require Import HahnBase HahnList HahnRelationsBasic.
Require Import HahnEquational HahnMaxElt HahnRewrite.
Require Import HahnDom HahnMinPath HahnPath.

Set Implicit Arguments.

Lemma acyclic_restr A d (r: relation A) : acyclic r -> acyclic (restr_rel d r).
Proof.
  eauto using acyclic_mon with hahn.
Qed.

Lemma acyclic_seqC A (r r' : relation A) : acyclic (r ⨾ r') <-> acyclic (r' ⨾ r).
Proof.
  unfold acyclic; rewrite clos_trans_rotl.
  unfold irreflexive, seq; ins; desf; intuition; desf; [|eapply H];
    rewrite t_rt_step in *; desf; eauto 10.
Qed.

Lemma acyc_simple_helper A (r1 r2: relation A): 
  acyclic (r1 ∪ r2) -> acyclic (r1⨾ r2).
Proof.
  ins.
  arewrite (r1 ⊆ r1 ∪ r2).
  arewrite (r2 ⊆ r1 ∪ r2) at 2.
  rewrite (ct_step (r1 ∪ r2)).
  rewrite inclusion_t_rt at 1.
  relsf.
  red; rels.
Qed.

Definition acyclic_rotl := acyclic_seqC.

Lemma acyclic_via_expand_minus :
  forall X (r : relation X)
    (IRR1: irreflexive r)
    (IRR2: irreflexive ((r ⨾ r \ r) ⨾ r＊)),
    acyclic r.
Proof.
  unfold acyclic; ins; rewrite ct_begin.
  by rewrite seq_rt_absorb_l, irreflexive_union.
Qed.

Lemma acyclic_seq_via_expand_minus :
  forall X (r r' : relation X)
    (IRR1: irreflexive (r ⨾ r'))
    (IRR2: irreflexive ((r ⨾ r' ⨾ r \ r) ⨾ r' ⨾ (r ⨾ r')＊)),
    acyclic (r ⨾ r').
Proof.
  unfold acyclic; ins; rewrite ct_end, <- seqA.
  rewrite seq_rt_absorb_r, !seqA; relsf.
  rewrite irreflexive_union; split; ins.
  by rewrite seqA, irreflexive_seqC, seqA.
Qed.

Lemma acyclic_union A (r r': relation A) (R: acyclic r) (FF: acyclic (r' ⨾ r＊)):
  acyclic (r ∪ r').
Proof.
  unfold acyclic; ins; rewrite path_union.
  apply irreflexive_union; split; auto.
  rewrite irreflexive_seqC. 
  rewrite ct_begin, !seqA; relsf.
  rewrite <- seqA; rewrite <- ct_begin.
    by rewrite acyclic_seqC in FF.
Qed.

Lemma acyclic_union1 A (r r': relation A) (R: acyclic r) 
      (R': acyclic r')
      (FF: acyclic (r⁺ ⨾ r'⁺)):
  acyclic (r ∪ r').
Proof.
  unfold acyclic; ins; rewrite path_union.
  apply irreflexive_union; split; auto.
  rewrite irreflexive_seqC.
  rewrite ct_begin, !seqA; relsf.
  rewrite <- seqA, <- ct_begin.
  rewrite rtE; relsf.
  rewrite path_union.
  apply irreflexive_union; split; auto.
  rewrite irreflexive_seqC. 
  rewrite ct_begin, !seqA; relsf.
  rewrite <- !seqA, <- ct_begin.
  apply acyclic_rotl.
  rewrite <- seqA, <- ct_begin.
    by apply acyclic_rotl.
Qed.

(******************************************************************************)
(** Extension of a relation with a singleton *)
(******************************************************************************)

Lemma cycle_decomp_u1 A (r : relation A) a b c :
  (r ∪ singl_rel a b)⁺ c c -> r⁺ c c \/ r＊ b a.
Proof.
  ins; apply ct_union_singl in H; unfolder in H. 
  desf; eauto using clos_refl_trans.
Qed.

Lemma acyclic_union_singl A (r : relation A) a b :
  acyclic (r ∪ singl_rel a b) <-> acyclic r /\ ~ r＊ b a.
Proof.
  unfold acyclic; rewrite ct_union_singl, irreflexive_union.
  rewrite irreflexive_seqC, seqA; rels; intuition;
    unfolder in *; ins; desf; eauto.
Qed.

Lemma acyclic_union_singl_max A (r : relation A) a b (MAX: max_elt r b) :
  acyclic (r ∪ singl_rel a b) <-> acyclic r /\ a <> b.
Proof.
  rewrite acyclic_union_singl; intuition; desf; eauto using rt_refl.
  apply rt_begin in H; unfolder in H; desf; eauto.
Qed.

(******************************************************************************)
(** Union with a total relation *)
(******************************************************************************)

Section AcyclicUnionTotal.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma acyclic_decomp_u_total r dom r' (T: is_total dom r') (DB: domb r' dom) :
      acyclic (r ∪ r') <-> acyclic r /\ irreflexive (r＊ ⨾ r'⁺).
  Proof.
    split; intuition.
      by eapply inclusion_acyclic; try eassumption; eauto with hahn.
      eapply irreflexive_inclusion; try eassumption.
      by rewrite <- rt_ct with (r := r ∪ r'); eauto with hahn.
    unfold acyclic; rewrite path_decomp_u_total; eauto.
    eapply irreflexive_union; splits; ins; rewrite irreflexive_seqC, seqA in *; rels.
  Qed.

  Lemma acyclic_union_total_r r dom r' (T: is_total dom r') (DB: domb r' dom) :
      acyclic (r ∪ r') <-> acyclic r /\ acyclic r' /\ irreflexive (r⁺ ⨾ r'⁺).
  Proof.
    rewrite acyclic_decomp_u_total; eauto; rewrite rtE; relsf;
      rewrite irreflexive_union; tauto.
  Qed.

  Lemma acyclic_union_total_l r dom r' (T: is_total dom r) (DB: domb r dom) :
      acyclic (r ∪ r') <-> acyclic r /\ acyclic r' /\ irreflexive (r⁺ ⨾ r'⁺).
  Proof.
    rewrite unionC, irreflexive_seqC, acyclic_union_total_r; eauto; tauto.
  Qed.

  Lemma acyclic_utd :
    forall r (ACYC: acyclic r)
           r' (T: transitive r') (IRR: irreflexive r') dom
           (F: is_total dom r') (DB: domb r' dom)
           (I': irreflexive (r' ⨾ r⁺)),
    acyclic (r ∪ r').
  Proof.
    ins; eapply acyclic_union_total_r; splits; eauto using trans_irr_acyclic. 
    rewrite irreflexive_seqC; relsf.
  Qed.

End AcyclicUnionTotal.

(******************************************************************************)
(** Union of relations where one has a certain domain/codomain. *)
(******************************************************************************)

Section PathDom.

  Variable X : Type.
  Implicit Type r : relation X.

  Lemma acyclic_du r r' adom bdom (A: doma r adom) (B: domb r bdom) :
    acyclic r' ->
    acyclic (r ∪ ⦗bdom⦘ ⨾ r'⁺ ⨾ ⦗adom⦘) ->
    acyclic (r ∪ r').
  Proof.
    unfold acyclic; ins.
    rewrite path_ur2; eauto.
    rewrite (unionC r), path_ur, <- (unionC r); eauto.
    rewrite seq_union_r, !irreflexive_union; repeat split; ins.
    eapply irreflexive_inclusion, H.
    rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r, ct_of_ct, cr_of_ct, rt_ct;
      auto with hahn.
    rewrite irreflexive_seqC, seqA, inclusion_ct_seq_eqv_l, !seqA.
    seq_rewrite seq_eqvK; do 2 rewrite ct_of_ct at 1.
    rewrite !crE, !seq_union_l, !seq_id_l, !seq_union_r, !seq_id_r.
    rewrite !irreflexive_union; repeat split; ins.

    rewrite ct_end, seqA, !seq_union_l, !seqA.
    rewrite <- rt_ct in H0; eapply irreflexive_inclusion, H0.
    eapply inclusion_seq_mon, inclusion_union_l; ins.
      assert (EQ: r ≡ r ⨾ eqv_rel bdom).
        by split; rewrite seq_eqv_r; red; ins; desf; eauto.
      by rewrite EQ at 1; rewrite seqA;
         eauto using inclusion_step2_ct with hahn.
    rewrite (inclusion_seq_eqv_l (dom:=adom)).
    by sin_rewrite ct_ct; eauto with hahn.

    rewrite ct_begin, irreflexive_seqC, <- !seqA, !seq_union_r, !seqA.
    rewrite <- ct_rt in H0; eapply irreflexive_inclusion, H0.
    apply inclusion_seq_mon; ins.
    apply inclusion_union_l; ins.
      assert (EQ: r ≡ eqv_rel adom ⨾ r).
        by split; rewrite seq_eqv_l; red; ins; desf; eauto.
      by rewrite EQ at 1; rewrite <- !seqA;
         eauto using inclusion_step2_ct with hahn.
    rewrite <- inclusion_union_r2.
    apply inclusion_step_t, inclusion_seq_mon; ins.
    by rewrite inclusion_seq_eqv_l; sin_rewrite ct_ct.

    rewrite seqA; sin_rewrite ct_ct.
    eapply irreflexive_inclusion, H0; eauto using inclusion_t_r_t with hahn.
  Qed.

  Lemma acyclic_ud r r' adom bdom (A: doma r' adom) (B: domb r' bdom) :
    acyclic r ->
    acyclic (⦗bdom⦘ ⨾ r⁺ ⨾ ⦗adom⦘∪ r') ->
    acyclic (r ∪ r').
  Proof.
    ins; rewrite unionC in *; eauto using acyclic_du.
  Qed.

End PathDom.


(******************************************************************************)
(** Union with a transitive relation *)
(******************************************************************************)

Section PathUnionTransitive.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma acyclic_ut r r' (T: transitive r') :
    acyclic (r ∪ r') <->
    acyclic r /\ irreflexive r' /\ acyclic (r' ⨾ r⁺).
  Proof.
    unfold acyclic; ins; rewrite path_ut2; ins.
    rewrite irreflexive_union, irreflexive_seqC, !seqA, rt_rt, (rtE r); relsf.
    rewrite irreflexive_union, <- ct_end, irreflexive_seqC, rtE; relsf.
    rewrite irreflexive_union; intuition.
    rewrite ct_begin, seqA; sin_rewrite (rewrite_trans T).
    by rewrite <- seqA, <- ct_begin.
  Qed.

  Lemma acyclic_utt r r' (T: transitive r) (T': transitive r') :
    acyclic (r ∪ r') <->
    irreflexive r /\ irreflexive r' /\ acyclic (r ⨾ r').
  Proof.
    ins; rewrite acyclic_ut, ct_of_trans, acyclic_rotl; ins.
    by unfold acyclic; rewrite ct_of_trans.
  Qed.

End PathUnionTransitive.

(******************************************************************************)
(** Absorption *)
(******************************************************************************)

Lemma acyclic_absorb A (r r': relation A) (F: r' ⨾ r ⊆ r \/ r' ⨾ r ⊆ r') :
  acyclic (r ∪ r') <-> acyclic r /\ acyclic r'.
Proof.
  intuition; eauto 2 using acyclic_mon with hahn. 
  all: unfold acyclic; ins; rewrite path_absorb; eauto.
  all: rewrite !irreflexive_union; splits; ins.
  all: apply irreflexive_seqC.
  * eapply irreflexive_inclusion, H1. 
    eapply ct_ind_right with (P:= fun x => x ;; _); ins; eauto with hahn.
    all: rewrite ct_begin at 1; rewrite ?seqA;
         sin_rewrite H; rewrite <- ct_begin; relsf.
  * eapply irreflexive_inclusion, H2.
    eapply ct_ind_left with (P:= fun x => _ ;; x); ins; eauto with hahn.
    all: rewrite ct_end at 1; rewrite ?seqA; 
         sin_rewrite H; seq_rewrite <- ct_end; relsf.
Qed.

(******************************************************************************)
(** Paths with disconnected relations *)
(******************************************************************************)

Lemma acyclic_disj A (r : relation A) (D: r ⨾ r ≡ ∅₂) : acyclic r.
Proof.
  by apply irreflexive_disj, ct_ct_disj.
Qed.

Lemma acyclic_unc X (r r' : relation X)
      (A : r ⨾ r ≡ ∅₂)
      (B : r' ⨾ r' ≡ ∅₂) :
  acyclic (r ∪ r') <-> acyclic (r ⨾ r').
Proof.
  unfold acyclic.
  rewrite pathp_unc, !irreflexive_union; ins.
  rewrite (irreflexive_seqC r), (irreflexive_seqC r').
  rewrite seq_rtE_l, seqA, A, !seq_false_r, union_false_r.
  rewrite seq_rtE_l, seqA, B, !seq_false_r, union_false_r.
  rewrite (acyclic_rotl r' r); intuition.
  by red; ins; eapply A; vauto.
  by red; ins; eapply B; vauto.
Qed.

(** Paths with specific attributes *)
(******************************************************************************)

Lemma acyclic_specific_absorb A (r r' : relation A) :
  r ⨾ r' ⊆ r ⨾ r ->
  r' ⨾ r' ⊆ r' ⨾ r ->
  acyclic r ->
  irreflexive r' ->
  acyclic (r ∪ r').
Proof.
  ins. red.
  rewrite path_specific_absorb; try done.
  apply irreflexive_union; split; try done.
  rewrite irreflexive_seqC.
  rewrite rtE; relsf.
  apply irreflexive_union; split; try done.
  by rewrite ct_end, seqA, H, <- seqA, <- ct_end, ct_unit.
Qed.

Lemma acyclic_seq_union_incompat A (r r' r'' : relation A) 
      (DISJ: r' ⨾ r'' ⊆ ∅₂) (DISJ': r'' ⨾ r' ⊆ ∅₂)
      (ACYC: acyclic (r ⨾ r'＊)) (ACYC': acyclic (r''⁺ ⨾ (r ⨾ r'＊)⁺)) :
  acyclic (r ⨾ (r' ∪ r'')＊).
Proof.
  ins; desf.
  arewrite ((r' ∪ r'')＊ <<= r'＊ ∪ r''⁺). 
    apply inclusion_rt_ind_left; ins; vauto.
    relsf; unionL; rels.
      by rewrite rt_begin at 1; relsf; sin_rewrite DISJ'; relsf.
      by rewrite ct_begin at 1; relsf; sin_rewrite DISJ; relsf.
    by arewrite (r'' <<= r''^*) at 1; relsf. 
  relsf.
  red; rewrite <- ct_of_union_ct_r.
  apply acyclic_ut; splits; ins.
  apply acyclic_seqC. 
  arewrite (r <<= (r ⨾ r'＊)⁺) by (unfolder; eauto using rt_refl, t_step). 
  arewrite (r <<= (r ⨾ r'＊)⁺) at 1 by (unfolder; eauto using rt_refl, t_step). 
  apply acyclic_seqC.
  rewrite ct_begin with (r := _ ;; r''^+); rewrite !seqA. 
  sin_rewrite ct_ct; rewrite <- seqA, <- ct_begin; red; rels.
  by apply acyclic_seqC.
Qed.



(** Preferential union *)
(******************************************************************************)

Definition pref_union X (r r' : relation X) x y :=
  r x y \/ r' x y /\ ~ r y x.

Lemma acyclic_pref_union :
  forall X (r r' : relation X) (dom : X -> Prop)
         (IRR: irreflexive r)
         (T: transitive r)
         (TOT: is_total dom r)
         (DL: forall x y (R: r' x y), dom x /\ ~ dom y),
    acyclic (pref_union r r').
Proof.
  ins; unfold pref_union.
  assert (EQ: restr_rel (fun x => ~ dom x)
                    (fun x y => r x y \/ r' x y /\ ~ r y x)
          ≡ restr_rel (fun x => ~ dom x) r).
    unfold restr_rel; split; red; ins; desf; eauto.
    by specialize_full DL; eauto; ins; desf.

  apply min_cycle with (dom := dom) (r' := r);
    repeat split; repeat red; ins; desf; eauto using t_step;
    try hahn_rewrite EQ in H;
    try hahn_rewrite EQ in S';
    repeat match goal with
          | H : clos_trans _ _ _ |- _ =>
            rewrite (clos_trans_of_transitive (transitive_restr T)) in H
          | H : clos_refl_trans _ _ _ |- _ =>
            rewrite (clos_refl_trans_of_transitive (transitive_restr T)) in H
          | H : r' _ _ |- _ => apply DL in H; desf
        end;
    unfold restr_rel, clos_refl, seq in *; desf; eauto.
Qed.

Lemma in_pref_union :
  forall X (r r' : relation X) (dom : X -> Prop)
         (IRR: irreflexive r)
         (T: transitive r)
         (TOT: is_total dom r)
         (DL: forall x y (R: r' x y), dom x /\ ~ dom y) x y
         (R: clos_trans (pref_union r r') x y)
         (D: dom y),
    r x y.
Proof.
  unfold pref_union; ins; apply clos_trans_t1n in R; induction R; desf; eauto.
    by eapply DL in H; desf.
  apply clos_t1n_trans in R.
  assert (K:=DL _ _ H); desc.
  destruct (classic (x = z)) as [|N]; [|apply TOT in N]; desf; ins.
    by exfalso; eauto.
  exfalso; eapply acyclic_pref_union with (r:=r), t_trans, t_trans; vauto.
Qed.
