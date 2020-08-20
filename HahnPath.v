(******************************************************************************)
(** * Decomposing paths and cycles *)
(******************************************************************************)

Require Import Omega.
Require Import HahnBase HahnList HahnRelationsBasic.
Require Import HahnEquational HahnMaxElt HahnRewrite.
Require Import HahnDom HahnMinPath.

Set Implicit Arguments.

Lemma wf_finite : 
  forall A (r: relation A) (ACYC: acyclic r) l (DOMA : doma r (fun x => List.In x l)),
    well_founded r.
Proof.
  unfold acyclic; ins.
  rewrite ct_step; red; ins; apply ct_doma in DOMA; revert DOMA. 
  generalize (transitive_ct (r:=r)) as T; revert ACYC.
  generalize r⁺; clear r; intro r.
  remember (length l) as n.
  revert r l Heqn.
  induction n.
   by destruct l; ins; econs; ins; exfalso; eauto.
  econs; intros b Rba.
  assert (IN:=DOMA _ _ Rba); apply in_split in IN; desf.
  rewrite app_length in *; ins.
  forward apply (IHn (restr_rel (fun x => x <> b) r) (l1 ++ l2)); 
    eauto using irreflexive_restr, transitive_restr.
  by rewrite app_length in *; ins; omega.
  by unfold restr_rel; red; ins; desf; eapply DOMA in REL; rewrite <- Permutation_middle in *; ins; desf; eauto.

  clear - Rba ACYC T; unfold restr_rel.
  econs; ins.
  destruct H; specialize (H y); specialize_full H; splits; try intro; desf; eauto.
  clear Rba.
  by induction H; econs; ins; eapply H1; splits; try intro; desf; eauto.
Qed.

(******************************************************************************)

Lemma rt_unionE A (r r' : relation A) : (r ∪ r')＊ ≡ r'＊ ⨾ (r ⨾ r'＊)＊.
Proof.
  split; eauto 8 using inclusion_seq_rt, inclusion_rt_rt2 with hahn.
  apply inclusion_rt_ind_left; relsf; unionL; rels. 
  rewrite <- seqA; rels; rewrite rtE at 2; relsf. 
Qed.

Lemma ct_unionE A (r r' : relation A) : (r ∪ r')⁺ ≡ r'⁺ ∪ r'＊ ⨾ (r ⨾ r'＊)⁺.
Proof.
  rewrite ct_begin, rt_unionE; relsf; rewrite <- seqA; rels.
  split; unionL; eauto using inclusion_seq_r, inclusion_seq_l with hahn.
    by rewrite rtE; relsf; unionL; eauto with hahn.
  by rewrite rtE at 1; relsf; unionL; eauto with hahn.
Qed.


(******************************************************************************)
(** Extension of a relation with a singleton *)
(******************************************************************************)

Lemma ct_union_singl A (r : relation A) a b :
  (r ∪ singl_rel a b)⁺ ≡ r⁺ ∪ r＊ ⨾ singl_rel a b ⨾ r＊.
Proof.
  split.
  { unfold inclusion, union, singl_rel, seq.
    induction 1; desf; eauto 9 using clos_trans, clos_refl_trans, clos_trans_in_rt.
  }
  eapply inclusion_union_l; eauto with hahn.
  rewrite <- rt_ct, ct_begin; eauto with hahn.
Qed.

Lemma rt_union_singl A (r : relation A) a b :
  (r ∪ singl_rel a b)＊ ≡ r＊ ∪ r＊ ⨾ singl_rel a b ⨾ r＊.
Proof.
  by rewrite rtE, rtE at 1; rewrite ct_union_singl, !unionA.
Qed.

Lemma ct_union_singl_max A (r : relation A) a b (MAX: max_elt r b) :
  (r ∪ singl_rel a b)⁺ ≡ r⁺ ∪ r＊ ⨾ singl_rel a b.
Proof.
  rewrite ct_union_singl, seq_singl_max_rt; ins.
Qed.

Lemma rt_union_singl_max A (r : relation A) a b (MAX: max_elt r b) :
  (r ∪ singl_rel a b)＊ ≡ r＊ ⨾ (singl_rel a b) ^?.
Proof.
  rewrite rt_union_singl, crE, seq_singl_max_rt; relsf.
Qed.

(******************************************************************************)
(** Union with a total relation *)
(******************************************************************************)

Section PathUnionTotal.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma path_decomp_u_total r dom r' (T: is_total dom r') (DB: domb r' dom)
      (IRR: irreflexive (r＊ ⨾ r'⁺)) :
    (r ∪ r')⁺ ≡ r⁺ ∪ r＊ ⨾ r'⁺ ⨾ r＊.
  Proof.
    split; ins.
    { intros ? ? C; unfold seq, union in *.
      induction C; desf; eauto 8 using rt_refl, clos_trans;
        eauto 8 using clos_trans_in_rt, rt_trans.

      destruct (classic (z1 = z3)) as [|NEQ]; desf;
        eauto 6 using t_trans, rt_trans.
      eapply T in NEQ; desf.
      by exfalso; eauto 10 using clos_trans, rt_trans.
      by eauto 8 using clos_trans, rt_trans.
      by eapply t_rt_step in IHC0; desf; eauto.
      by eapply t_rt_step in IHC4; desf; eauto.
    }
    eapply inclusion_union_l; eauto with hahn.
    rewrite <- rt_ct with (r := r ∪ r'),
            <- ct_rt with (r := r ∪ r'); eauto 8 with hahn.
  Qed.

End PathUnionTotal.


(******************************************************************************)
(** Path absorption properties *)
(******************************************************************************)

Section PathAbsorb.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma path_absorb1 r r' (F: r' ⨾ r ⊆ r') :
    (r ∪ r')⁺ ≡ r⁺ ∪ r'⁺ ∪ r⁺ ⨾ r'⁺.
  Proof.
    split; cycle 1.
      repeat apply inclusion_union_l; eauto with hahn.
      by repeat apply inclusion_seq_trans; eauto with hahn; vauto.
    apply inclusion_t_ind_right; relsf;
      repeat apply inclusion_union_l;
      eauto 10 using inclusion_t_r_t with hahn;
    try solve [rewrite (ct_end r'), !seqA, F, <- ct_end; eauto 10 with hahn].
    rewrite (ct_end r') at 3; rewrite seqA; eauto 10 with hahn.
  Qed.

  Lemma path_absorb2 r r' (F: r' ⨾ r ⊆ r) :
    (r ∪ r')⁺ ≡ r⁺ ∪ r'⁺ ∪ r⁺ ⨾ r'⁺.
  Proof.
    split; cycle 1.
      repeat apply inclusion_union_l; eauto with hahn.
      by repeat apply inclusion_seq_trans; eauto with hahn; vauto.
    apply inclusion_t_ind_left; relsf;
      repeat apply inclusion_union_l;
      eauto 10 using inclusion_r_t_t with hahn;
    try solve [rewrite (ct_begin r), <- !seqA, F, <- ct_begin; eauto 10 with hahn].
    rewrite (ct_begin r) at 3; rewrite seqA; eauto 10 with hahn.
  Qed.

  Lemma path_absorb r r' (F: r' ⨾ r ⊆ r \/ r' ⨾ r ⊆ r') :
    (r ∪ r')⁺ ≡ r⁺ ∪ r'⁺ ∪ r⁺ ⨾ r'⁺.
  Proof.
    ins; desf; eauto using path_absorb1, path_absorb2.
  Qed.

  Lemma path_absorb_lt r r' (F: r' ⨾ r ⊆ r \/ r' ⨾ r ⊆ r') (T: transitive r) :
    (r ∪ r')⁺ ≡ r'⁺ ∪ r ⨾ r'＊.
  Proof.
    ins; rewrite path_absorb, rtE; relsf; hahn_rel.
  Qed.

  Lemma path_absorb_rt r r' (F: r'⨾ r ⊆ r \/ r'⨾ r ⊆ r') (T: transitive r') :
    (r ∪ r')⁺ ≡ r⁺ ∪ r＊ ⨾ r'.
  Proof.
    ins; rewrite path_absorb, rtE; relsf; hahn_rel.
  Qed.

  Lemma minus_seq_l r r' (T: transitive r) :
    (r ⨾ r') \ r ⊆ r ⨾ (r' \ r).
  Proof.
    unfold minus_rel, seq; red; ins; desf; repeat eexists; eauto.
  Qed.

  Lemma minus_seq_r r r' (T: transitive r') :
    (r ⨾ r') \ r' ⊆ (r \ r') ⨾ r'.
  Proof.
    unfold minus_rel, seq; red; ins; desf; repeat eexists; eauto.
  Qed.

  Lemma seq_rt_absorb_l r r' : r ⨾ r'＊ ⊆ r ∪ ((r ⨾ r') \ r) ⨾ r'＊.
  Proof.
    unfold seq, union, inclusion, minus_rel; ins; desf.
    induction H0 using clos_refl_trans_ind_left; desf; eauto.
    destruct (classic (r x z0)); eauto 8 using clos_refl_trans.
    right; repeat eexists; eauto using clos_refl_trans.
  Qed.

  Lemma seq_ct_absorb_l r r' : r ⨾ r'⁺ ⊆ r ∪ ((r ⨾ r') \ r) ⨾ r'＊.
  Proof.
    rewrite <- seq_rt_absorb_l; eauto with hahn.
  Qed.

  Lemma seq_rt_absorb_r r r' : r＊ ⨾ r' ⊆ r' ∪ r＊ ⨾ ((r ⨾ r') \ r').
  Proof.
    apply inclusion_transpE.
    rewrite !transp_union, !transp_seq, !transp_minus, !transp_rt, !transp_seq;
    auto using seq_rt_absorb_l, transitive_transp.
  Qed.

  Lemma seq_ct_absorb_r r r' : r⁺ ⨾ r' ⊆ r' ∪ r＊ ⨾ ((r ⨾ r') \ r').
  Proof.
    rewrite <- seq_rt_absorb_r; eauto with hahn.
  Qed.

  Lemma seq_rt_absorb_lt r r' (T: transitive r) :
    r ⨾ r'＊ ⊆ r ∪ r ⨾ (r' \ r) ⨾ r'＊.
  Proof.
    by rewrite seq_rt_absorb_l, minus_seq_l, seqA.
  Qed.

  Lemma seq_ct_absorb_lt r r' (T: transitive r) :
    r ⨾ r'⁺ ⊆ r ∪ r ⨾ (r' \ r) ⨾ r'＊.
  Proof.
    by rewrite seq_ct_absorb_l, minus_seq_l, seqA.
  Qed.

  Lemma seq_rt_absorb_rt r r' (T: transitive r') :
    r＊ ⨾ r' ⊆ r' ∪ r＊ ⨾ (r \ r') ⨾ r'.
  Proof.
    by rewrite seq_rt_absorb_r, minus_seq_r.
  Qed.

  Lemma seq_ct_absorb_rt r r' (T: transitive r') :
    r⁺ ⨾ r' ⊆ r' ∪ r＊ ⨾ (r \ r') ⨾ r'.
  Proof.
    by rewrite seq_ct_absorb_r, minus_seq_r.
  Qed.
End PathAbsorb.

(******************************************************************************)

Lemma clos_trans_restr_trans_mid :
  forall X (r r' : relation X) f x y
    (A : (restr_rel f (r ∪ r'))⁺ x y)
    z (B : r y z) w
    (C : (restr_rel f (r ∪ r'))⁺ z w),
    (restr_rel f (r ∪ r'))⁺ x w.
Proof.
  ins; eapply t_trans, t_trans; vauto.
  eapply t_step; repeat split; vauto.
    by apply clos_trans_restrD in A; desc.
  by apply clos_trans_restrD in C; desc.
Qed.

Lemma clos_trans_restr_trans_cycle :
  forall X (r r' : relation X) f x y
    (A : clos_trans (restr_rel f (r ∪ r')) x y)
    (B : r y x),
    clos_trans (restr_rel f (r ∪ r')) x x.
Proof.
  ins; eapply t_trans, t_step; unfold union; eauto.
  red; apply clos_trans_restrD in A; desf; auto.
Qed.

(******************************************************************************)
(** Union of relations where one has a certain domain/codomain. *)
(******************************************************************************)

Section PathDom.

  Variable X : Type.
  Implicit Type r : relation X.

  Lemma path_tur r r' adom bdom
        (T: transitive r) (DA: doma r' adom) (DB: domb r' bdom) :
    (r ∪ r')⁺ ≡ r ∪ (r ⨾ ⦗adom⦘ ∪ r')⁺ ⨾ (⦗bdom⦘ ⨾ r)^?.
  Proof.
    split.
      rewrite seq_eqv_r, seq_eqv_l.
      unfold seq, union, clos_refl; intros ? ? P.
      apply clos_trans_tn1 in P; induction P; desf; eauto 14 using clos_trans; clear P.
      apply clos_trans_t1n in IHP; induction IHP;
      intuition; desf; eauto 14 using clos_trans.
    rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l.
    eauto using inclusion_t_r_t with hahn.
  Qed.

  Lemma path_ur r r' adom bdom (DA: doma r' adom) (DB: domb r' bdom) :
    (r ∪ r')⁺ ≡ r⁺ ∪ (r⁺ ⨾ ⦗adom⦘ ∪ r')⁺ ⨾ (⦗bdom⦘ ⨾ r⁺)^?.
  Proof.
    by ins; rewrite <- path_tur, ct_of_union_ct_l; eauto; vauto.
  Qed.

  Lemma path_tur2 r r' adom bdom
        (T: transitive r')
        (DA: doma r adom) (DB: domb r bdom) :
    (r ∪ r')⁺ ≡ r' ∪ (r' ⨾ ⦗adom⦘)^? ⨾ (r ∪ ⦗bdom⦘ ⨾ r')⁺.
  Proof.
    split.
      rewrite seq_eqv_r, seq_eqv_l.
      unfold seq, union, clos_refl; intros ? ? P.
      apply clos_trans_t1n in P; induction P; desf; eauto 14 using clos_trans; clear P.
      apply clos_trans_tn1 in IHP0; induction IHP0;
      intuition; desf; eauto 14 using clos_trans.
    rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l.
    eauto using inclusion_r_t_t with hahn.
  Qed.

  Lemma path_ur2 r r' adom bdom (A: doma r adom) (B: domb r bdom) :
    (r ∪ r')⁺ ≡ r'⁺ ∪ (r'⁺ ⨾ ⦗adom⦘)^? ⨾ (r ∪ ⦗bdom⦘ ⨾ r'⁺)⁺.
  Proof.
    ins; rewrite <- path_tur2, ct_of_union_ct_r; eauto; vauto.
  Qed.

End PathDom.

(** Misc properties *)
(******************************************************************************)

Lemma clos_trans_imm :
  forall X (r : relation X) (I: irreflexive r)
         (T: transitive r) L (ND: NoDup L) a b
         (D: forall c, r a c -> r c b -> In c L)
         (REL: r a b),
    (immediate r)⁺ a b.
Proof.
  intros until 3; induction ND; ins; vauto.
  destruct (classic (r a x /\ r x b)) as [|N]; desf;
    [apply t_trans with x|]; eapply IHND; ins;
    forward eapply (D c); eauto; intro; desf; exfalso; eauto.
Qed.

Lemma clos_trans_rotl A (r r' : relation A) :
  (r ⨾ r')⁺ ≡ r ⨾ (r' ⨾ r)＊ ⨾ r'.
Proof.
  split; red; ins; unfold seq in *; desf.
    by induction H; desf; eauto 10 using clos_refl_trans.
  cut (exists m, clos_refl_trans (r ⨾ r') x m /\ r m z0); unfold seq in *.
    by ins; desf; eapply t_rt_step; eauto.
  clear H1; induction H0 using clos_refl_trans_ind_left; desf;
  eauto 8 using clos_refl_trans.
Qed.

Lemma immediate_clos_trans_elim A (r : relation A) a b :
  immediate r⁺ a b ->
  r a b /\ (forall c, r⁺ a c -> r⁺ c b -> False).
Proof.
  unfold immediate; ins; desf; split; ins.
  apply t_step_rt in H; desf.
  apply clos_refl_transE in H1; desf; exfalso; eauto using t_step.
Qed.

Lemma clos_trans_immediate1 A (r : relation A) (T: transitive r) a b :
  (immediate r)⁺ a b -> r a b.
Proof.
  unfold immediate; induction 1; desf; eauto.
Qed.

Lemma clos_trans_immediate2 A (r : relation A)
      (T: transitive r) (IRR: irreflexive r) dom
      (D: domb r (fun x => In x dom)) a b :
  r a b ->
  (immediate r)⁺ a b.
Proof.
  assert (D': forall c, r a c -> r c b -> In c dom).
    by ins; apply D in H; desf.
  clear D; revert a b D'.
  remember (length dom) as n; revert dom Heqn; induction n.
    by destruct dom; ins; vauto.
  ins; destruct (classic (exists c, r a c /\ r c b)); desf.
  2: by eapply t_step; split; ins; eauto.
  forward eapply D' as X; eauto; apply in_split in X; desf.
  rewrite app_length in *; ins; rewrite <- plus_n_Sm, <- app_length in *; desf.
  apply t_trans with c; eapply IHn with (dom := l1 ++ l2); ins;
  forward eapply (D' c0); eauto;
  rewrite !in_app_iff; ins; desf; eauto; exfalso; eauto.
Qed.


(** Union with a transitive relation *)
(******************************************************************************)

Section PathUnionTransitive.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma inclusion_seq_l r r1 r2 : r ⊆ r1 -> reflexive r2 -> r ⊆ r1 ⨾ r2.
  Proof. firstorder. Qed.

  Lemma inclusion_seq_r r r1 r2 : r ⊆ r2 -> reflexive r1 -> r ⊆ r1 ⨾ r2.
  Proof. firstorder. Qed.

  Hint Resolve inclusion_seq_l inclusion_seq_r : hahn_full.

  Lemma path_ut r r' (T: transitive r') :
    (r ∪ r')＊ ≡ r＊ ⨾ (r' ⨾ r⁺)＊ ⨾ r'^?.
  Proof.
    split.
    - apply inclusion_rt_ind; hahn_rel; eauto 4 with hahn hahn_full.
      apply transitiveI.
      rewrite crE at 1; relsf; unionL.
        hahn_frame_r; rewrite rtE with (r:=r' ⨾ r⁺) at 1; relsf; hahn_rel.
        hahn_frame_l; rewrite ct_end, !seqA; rels.
        by apply inclusion_seq_rt; ins; rewrite <- seqA, <- ct_begin; eauto with hahn.
      hahn_frame_l; rewrite rtE with (r:=r) at 1; relsf; hahn_rel; [|hahn_frame_r].
        rewrite rtE with (r:=r' ⨾ r⁺) at 2; relsf; hahn_rel.
        hahn_frame_r; rewrite ct_begin with (r:=r' ⨾ r⁺); rewrite !seqA; relsf. 
        by apply inclusion_seq_rt; ins; rewrite <- seqA, <- ct_begin; eauto with hahn.
      by apply inclusion_seq_rt; ins; rewrite <- seqA, <- ct_begin; eauto with hahn.
    - rewrite inclusion_t_rt.
      eauto 10 using inclusion_seq_trans, inclusion_rt_rt2 with hahn.
  Qed.

  Lemma path_ut2 r r' (T: transitive r') :
    (r ∪ r')⁺ ≡ r⁺ ∪ r＊⨾ (r'⨾ r⁺)＊ ⨾ r'⨾ r＊.
  Proof.
    split.
      rewrite ct_end, path_ut; ins; relsf.
      rewrite !seqA, (rewrite_trans_seq_cr_l T), crE; relsf; hahn_rel.
      2: by rewrite (rtE r) at 3; relsf.
      rewrite (rt_end (r' ⨾ r⁺)) at 1; relsf.
      rewrite <- ct_end, !seqA; hahn_rel.
      rewrite inclusion_t_rt with (r:=r) at 2; rewrite <- ct_end.
      rewrite inclusion_t_rt with (r:=r) at 2; hahn_rel.
    hahn_rel.
    rewrite inclusion_t_rt, <- (rt_ct (r ∪ r')); seq_rewrite <- ct_end.
    apply inclusion_seq_mon; eauto with hahn.
    apply inclusion_t_t2; rewrite ct_begin; eauto with hahn.
  Qed.

End PathUnionTransitive.

(** More path union properties *)
(******************************************************************************)

Section PathUnion.
  Variable A : Type.
  Implicit Type r : relation A.

  Lemma path_ut_first r r' :
    (r ∪ r')⁺ ≡ r⁺ ∪ r＊ ⨾ r' ⨾ (r ∪ r')＊.
  Proof.
    split.
    - apply inclusion_t_ind_right.
      + apply inclusion_union_l.
        * apply inclusion_union_r; left; eauto with hahn.
        * apply inclusion_union_r; right; basic_solver 10.
      + relsf; repeat apply inclusion_union_l.
        * apply inclusion_union_r; left.
          unfold inclusion, seq; ins; desf; vauto.
        * apply inclusion_union_r; right.
          rewrite !seqA.
          arewrite (r ⊆ (r ∪ r')＊) at 3.
          rewrite rt_rt.
          done.
        * basic_solver 10.
        * apply inclusion_union_r; right.
          rewrite !seqA.
          arewrite (r' ⊆ (r ∪ r')＊) at 3.
          rewrite rt_rt.
          done.
    - arewrite (r ⊆ (r ∪ r')⁺) at 1.
      arewrite (r＊ ⊆ (r ∪ r')＊) at 1.
      arewrite (r' ⊆ (r ∪ r')⁺) at 3.
      rels.
  Qed.

  Lemma path_ut_last r r' :
    (r ∪ r')⁺ ≡ r⁺ ∪ (r ∪ r')＊ ⨾ r' ⨾ r＊.
  Proof.
    split.
    - apply inclusion_t_ind_right.
      + rewrite (ct_step r) at 1. basic_solver 10.
      + relsf; unionL.
        * rewrite ct_end at 2; basic_solver 10.
        * rewrite !seqA; rewrite <- ct_end; basic_solver 10.
        * arewrite (r ⊆ (r ∪ r')); basic_solver 10.
        * arewrite (r ⊆ (r ∪ r')) at 2.
          arewrite (r' ⊆ (r ∪ r')＊) at 2.
          rels; basic_solver 10.
    - arewrite (r ⊆ (r ∪ r')⁺) at 1.
      arewrite (r ⊆ (r ∪ r')＊) at 3. arewrite (r' ⊆ (r ∪ r')⁺) at 3.
      rels.
  Qed.

  Lemma path_union (r r': relation A) : (r ∪ r')⁺ ⊆ r⁺ ∪ (r＊ ⨾ r')⁺ ⨾ r＊.
  Proof.
    apply inclusion_t_ind_right.
    unionL; [vauto|].
      by rewrite rtE; rewrite <- !ct_step; basic_solver 12.
      relsf; unionL.
    - by unionR left; rewrite ct_unit.
    - by rewrite !seqA; rewrite <- ct_end; basic_solver 12.
    - rewrite (ct_step (r⁺ ⨾ r')).
      rewrite <- inclusion_t_rt at 1; basic_solver 22.
    - rewrite !seqA, inclusion_t_rt at 1.
      rewrite <- (ct_end (r＊ ⨾ r')); basic_solver 12.
  Qed.

  Lemma path_union1 (r r': relation A) : (r ∪ r')⁺ ⊆ r'⁺ ∪ r'＊ ⨾ (r ∪ r ⨾ r'⁺)⁺.
  Proof.
    apply inclusion_t_ind_right.
    unionL; [|vauto].
      by rewrite rtE; rewrite <- !ct_step; basic_solver 12.
      relsf; unionL; rewrite ?seqA.
    - unionR right.
      arewrite (r'⁺ ⊆ r'＊); hahn_frame.
      rewrite <- !ct_step; basic_solver 12.
    - by arewrite (r ⊆ (r ∪ r ⨾ r'⁺)＊) at 3; relsf.
    - arewrite (r'⁺ ⊆ r'＊) at 1.
      rewrite <- ct_end; basic_solver.
    - unionR right.
      rewrite ct_end, !seqA.
      arewrite ((r ∪ r ⨾ r'⁺) ⨾ r' ⊆ (r ∪ r ⨾ r'⁺)).
      relsf; unionL.
      * rewrite <- !ct_step; basic_solver 12.
      * rewrite !seqA.
        arewrite (r'⁺ ⊆ r'＊) at 1.
        rewrite <- ct_end; basic_solver.
      * relsf.
  Qed.

  Lemma path_union2 (r r': relation A) : 
    (r ∪ r')⁺ ⊆ r⁺ ∪ r'⁺ ⨾ r＊ ∪ r'＊ ⨾ (r⁺ ⨾ r'⁺)⁺ ⨾ r＊.
  Proof.
    rewrite path_union1; unionL.
    basic_solver 12.
    rewrite path_union.
    relsf.
    unionL.
    basic_solver 12.
    arewrite (r＊ ⨾ r ⊆ r⁺).
    basic_solver 12.
  Qed.
End PathUnion.

Lemma ct_minus_transitive {A} (r r': relation A) (TR : transitive r) :
  r'⁺ \ r ⊆ (r' ∩ r)＊ ⨾  (r' \ r) ⨾  r'＊.
Proof.
  ins.
  arewrite (r' ⊆ (r' ∩ r) ∪ (r' \ r)) at 1.
  { by unfolder; ins; desf; tauto. }
  rewrite path_ut_first, minus_union_l.
  unionL.
  {  by arewrite (r' ∩ r ⊆ r); relsf. }
  arewrite ((r' ∩ r) ∪ (r' \ r) ⊆ r') at 1.
  basic_solver 12.
Qed.

(** Union with a total relation *)
(******************************************************************************)

Lemma path_utd_helper :
  forall X (r r' : relation X) (T: transitive r') dom
         (F: is_total dom r') (DA: doma r' dom) (DB: domb r' dom) x y
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    r⁺ x y \/
    (exists z w, r＊ x z /\ r' z w /\ r＊ w y) \/
    (exists z w, r' z w /\ r＊ w z).
Proof.
  ins; induction P; desf; eauto 9 using clos_trans, clos_refl_trans, clos_trans_in_rt.
  right; destruct (classic (z1 = w)) as [|NEQ]; desf; eauto 8 using clos_refl_trans.
  eapply F in NEQ; desf; eauto 8 using clos_refl_trans.
Qed.

Lemma path_utd :
  forall X (r r' : relation X) (T: transitive r') dom
         (F: is_total dom r') (DA: doma r' dom) (DB: domb r' dom)
         (I': irreflexive (r' ⨾ r＊)),
    (r ∪ r')⁺ ≡ r⁺ ∪ r＊ ⨾ r' ⨾ r＊.
Proof.
  split.
    unfold inclusion, seq, union in *; ins; desf.
    eapply path_utd_helper with (2:=F) in H; desf; eauto 8; exfalso; eauto 8.
  apply inclusion_union_l; eauto with hahn.
  rewrite <- rt_ct, ct_begin; eauto with hahn.
Qed.


(** Paths with disconnected relations *)
(******************************************************************************)

Lemma ct_no_step A (r : relation A) (D: r ⨾ r ≡ ∅₂) : r⁺ ≡ r.
Proof.
  by apply ct_of_trans, transitiveI; rewrite D.
Qed.

Lemma ct_ct_disj A (r : relation A) (D: r ⨾ r ≡ ∅₂) : r⁺ ⨾ r⁺ ≡ ∅₂.
Proof.
  rewrite ct_no_step; ins.
Qed.

Lemma irreflexive_disj A (r : relation A) (D: r ⨾ r ≡ ∅₂) : irreflexive r.
Proof.
  red; ins; eapply D; vauto.
Qed.

Lemma path_unc X (r r' : relation X)
      (A : r ⨾ r ≡ ∅₂)
      (B : r' ⨾ r' ≡ ∅₂) :
  (r ∪ r')＊ ≡
  (r ⨾ r')＊ ∪ (r' ⨾ r)＊ ∪ r ⨾ (r' ⨾ r)＊ ∪ r' ⨾ (r ⨾ r')＊.
Proof.
  split.
    eapply inclusion_rt_ind_left; eauto with hahn.
    rewrite seq_union_l, !seq_union_r, <- !seqA, <- !ct_begin.
    rewrite (seq_rtE_r r (r ⨾ r')), (seq_rtE_r r' (r' ⨾ r)), <- !seqA.
    rewrite A, B, ?seq_false_l, ?union_false_l, ?union_false_r.
    by unfold union, seq; red; ins; desf;
       eauto 6 using clos_trans_in_rt, rt_refl.
  hahn_rel;
  repeat first [apply inclusion_union_l|apply inclusion_seq_rt|
                eapply inclusion_rt_rt2]; vauto.
Qed.

Lemma pathp_unc X (r r' : relation X)
      (A : r ⨾ r ≡ ∅₂)
      (B : r' ⨾ r' ≡ ∅₂) :
  (r ∪ r')⁺ ≡ (r ⨾ r')⁺ ∪ (r' ⨾ r)⁺ ∪ r ⨾ (r' ⨾ r)＊ ∪ r' ⨾ (r ⨾ r')＊.
Proof.
  rewrite ct_begin, path_unc; ins.
  rewrite seq_union_l, !seq_union_r, <- !seqA, <- !ct_begin.
  rewrite (seq_rtE_r r (seq r r')), (seq_rtE_r r' (seq r' r)), <- !seqA.
  rewrite A, B, ?seq_false_l, ?union_false_l, ?union_false_r.
  by unfold union, seq; split; red; ins; desf; eauto 8 using rt_refl.
Qed.

(** Paths with specific attributes *)
(******************************************************************************)

Lemma path_specific_absorb A (r r' : relation A) : 
  r ⨾ r' ⊆ r ⨾ r ->
  r' ⨾ r' ⊆ r' ⨾ r ->
  (r ∪ r')⁺ ⊆ r⁺ ∪ r' ⨾ r＊.
Proof.
  ins.
  assert (r⁺ ⨾ r' ⊆ r⁺) by
    (by rewrite ct_end, !seqA, H, <- seqA; rewrite rt_unit at 1).
  apply inclusion_t_ind_right.
  - (* base *)
    unionL.
    + unionR left. apply ct_step.
    + unionR right; basic_solver 25.
  - (* step *)
    relsf; unionL.
    + (* r⁺ ; r *) by unionR left; rewrite ct_unit.
    + (* (r' ; r＊) ; r *) by unionR right; rewrite !seqA, rt_unit.
    + (* r⁺ ; r' *) by unionR left; rewrite H1.
    + (* (r' ; r＊) ; r' *)
      rewrite rtE at 1; relsf; unionL; unionR right.
      * by rewrite H0; arewrite (r ⊆ r＊) at 1.
      * by rewrite !seqA, H1, inclusion_t_rt.
Qed.

(** Paths involving [bunion] *)
(******************************************************************************)

Lemma pow_union_decomposition (n : nat) A (r r': relation A) :
  (r ∪ r')^^n ⊆ r'^^n ∪ (⋃k < n, r'^^k ⨾ r ⨾ (r ∪ r')^^(n - k - 1)).
Proof.
  induction n using (well_founded_ind Wf_nat.lt_wf).
  destruct n as [| n']; [by firstorder|].
  simpl (_ ^^ (S n')).
  rewrite !seq_pow_l, H; clear H; try done. 
  autorewrite with hahn; autorewrite with hahn hahn_full.
  unionL; eauto with hahn.
  - unionR right; eapply inclusion_bunion_r with 0; ins; try omega; rels.
    replace (n' - 0) with n' by omega; eauto with hahn. 
  - unionR right; eapply inclusion_bunion_r with 0; ins; try omega; rels.
    hahn_frame_l.
    arewrite (r ⊆ (r ∪ r') ^^ 1) at 1 by simpl; rels.
    arewrite (r' ⊆ r ∪ r') at 1; rewrite !pow_nm.
    replace (x + (1 + (n' - x - 1))) with (n' - 0) by omega; rels.
  - unionR right; eapply inclusion_bunion_r with (S x); ins; try omega; rels.
    by rewrite seq_pow_l, !seqA.
Qed.

Lemma ct_inclusion_from_rt_inclusion1 A (r r': relation A)
      (d d' : A -> Prop) (ACYC : acyclic r) :
  r＊ ⨾ ⦗d⦘ ⊆ ⦗d'⦘ ⨾ r'＊ -> r⁺ ⨾ ⦗d⦘ ⊆ ⦗d'⦘ ⨾ r'⁺.
Proof.
  rewrite !rtE; autounfold with unfolderDb; ins; desf.
  specialize (H x y); desf.
  assert (d' x /\ (x = y /\ True \/ r'⁺ x y)).
  { edestruct H; eauto. desf; eauto. }
  desf; eauto.
  exfalso; eapply ACYC; edone.
Qed.

Lemma ct_inclusion_from_rt_inclusion2 A (r r': relation A)
      (d d' : A -> Prop) (ACYC : acyclic r) :
  ⦗d⦘ ⨾ r＊ ⊆ r'＊ ⨾ ⦗d'⦘ -> ⦗d⦘ ⨾ r⁺ ⊆ r'⁺ ⨾ ⦗d'⦘.
Proof.
  rewrite !rtE; autounfold with unfolderDb; ins; desf.
  specialize (H z y); desf.
  assert (d' y /\ (z = y /\ True \/ r'⁺ z y)).
  { edestruct H; eauto. desf; eauto. }
  desf; eauto.
  exfalso; eapply ACYC; edone.
Qed.
