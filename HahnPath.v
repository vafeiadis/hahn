(******************************************************************************)
(** * Lemmas about paths and cycles *)
(******************************************************************************)

Require Import Classical.
Require Import HahnBase HahnList HahnRelationsBasic.
Require Import HahnEquational HahnMaxElt HahnRewrite.
Require Import HahnDom HahnMinPath.

Set Implicit Arguments.

(******************************************************************************)

Lemma path_decomp_u1 X (r : relation X) a b :
  (r ∪ singl_rel a b)⁺ ≡ r⁺ ∪ r^* ⨾ singl_rel a b ⨾ r^*.
Proof.
  split.
  { unfold inclusion, union, singl_rel, seq.
    induction 1; desf; eauto 9 using clos_trans, clos_refl_trans, clos_trans_in_rt.
  }
  eapply inclusion_union_l; eauto with rel.
  rewrite <- rt_ct, ct_begin; eauto with rel.
Qed.

Lemma cycle_decomp_u1 X (r : relation X) a b c :
  (r ∪ singl_rel a b)⁺ c c ->
  r⁺ c c \/ r^* b a.
Proof.
  ins; apply path_decomp_u1 in H.
  unfold seq, union, singl_rel in *; desf; eauto using clos_refl_trans.
Qed.

Lemma acyclic_decomp_u1 X (r : relation X) a b :
  acyclic r ->
  ~ r^* b a ->
  acyclic (r ∪ singl_rel a b).
Proof.
  unfold acyclic, irreflexive; ins.
  forward eapply cycle_decomp_u1; ins; desf; eauto.
Qed.

Lemma path_decomp_u1_max X (r : relation X) a b (MAX: max_elt r b) :
  (r ∪ singl_rel a b)⁺ ≡ r⁺ ∪ r^* ⨾ singl_rel a b.
Proof.
  rewrite path_decomp_u1, seq_singl_max_rt; vauto.
Qed.

Lemma acyclic_u1_max X (r : relation X) a b (MAX: max_elt r b) :
  acyclic (r ∪ singl_rel a b) <->
  acyclic r /\ a <> b.
Proof.
  unfold acyclic;
  rewrite path_decomp_u1_max, irreflexive_union, irreflexive_seqC, seq_singl_max_rt;
  intuition; unfold irreflexive, singl_rel in *; ins; desf; eauto.
Qed.

(******************************************************************************)

Lemma path_decomp_u_total :
  forall X (r : relation X) dom r' (T: is_total dom r') (DB: domb r' dom)
    (IRR: irreflexive (r^* ⨾ r'⁺)),
  (r ∪ r')⁺ ≡ r⁺ ∪ r^* ⨾ r'⁺ ⨾ r^*.
Proof.
  unfold doma, domb; split; ins.
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
  eapply inclusion_union_l; eauto with rel.
  rewrite <- rt_ct with (r := r ∪ r'),
          <- ct_rt with (r := r ∪ r'); eauto 8 with rel.
Qed.

Lemma acyclic_decomp_u_total :
  forall X (r : relation X) dom r' (T: is_total dom r') (DB: domb r' dom)
    (A: acyclic r)
    (IRR: irreflexive (r^* ⨾ r'⁺)),
    acyclic (r ∪ r').
Proof.
  red; ins.
  rewrite path_decomp_u_total; eauto.
  eapply irreflexive_union; split; ins.
  by rewrite irreflexive_seqC, seqA, rt_rt, irreflexive_seqC.
Qed.

Lemma clos_trans_disj_rel :
  forall X (r r' : relation X)
    (DISJ: forall x y (R: r x y) z (R': r' y z), False) x y
    (R: r⁺ x y) z
    (R': r'⁺ y z),
    False.
Proof.
  ins; induction R; eauto; induction R'; eauto.
Qed.

Lemma path_absorb1 X (r r' : relation X) (F: r' ⨾ r ⊆ r') :
  (r ∪ r')⁺ ≡ r⁺ ∪ r'⁺ ∪ r⁺ ⨾ r'⁺.
Proof.
  split; cycle 1.
    repeat apply inclusion_union_l; eauto with rel.
    by repeat apply inclusion_seq_trans; eauto with rel; vauto.
  apply inclusion_t_ind_right; relsf;
    repeat apply inclusion_union_l;
    eauto 10 using inclusion_t_r_t with rel;
  try solve [rewrite (ct_end r'), !seqA, F, <- ct_end; eauto 10 with rel].
  rewrite (ct_end r') at 3; rewrite seqA; eauto 10 with rel.
Qed.

Lemma path_absorb2 X (r r' : relation X) (F: r' ⨾ r ⊆ r) :
  (r ∪ r')⁺ ≡ r⁺ ∪ r'⁺ ∪ r⁺ ⨾ r'⁺.
Proof.
  split; cycle 1.
    repeat apply inclusion_union_l; eauto with rel.
    by repeat apply inclusion_seq_trans; eauto with rel; vauto.
  apply inclusion_t_ind_left; relsf;
    repeat apply inclusion_union_l;
    eauto 10 using inclusion_r_t_t with rel;
  try solve [rewrite (ct_begin r), <- !seqA, F, <- ct_begin; eauto 10 with rel].
  rewrite (ct_begin r) at 3; rewrite seqA; eauto 10 with rel.
Qed.

Lemma path_absorb X (r r' : relation X) (F: r' ⨾ r ⊆ r \/ r' ⨾ r ⊆ r') :
  (r ∪ r')⁺ ≡ r⁺ ∪ r'⁺ ∪ r⁺ ⨾ r'⁺.
Proof.
  ins; desf; eauto using path_absorb1, path_absorb2.
Qed.

Lemma acyclic_absorb :
  forall X (r r' : relation X)
         (F: r' ⨾ r ⊆ r \/ r' ⨾ r ⊆ r')
    (A1: acyclic r)
    (A2: acyclic r'),
    acyclic (r ∪ r').
Proof.
  unfold acyclic; ins; rewrite path_absorb; eauto.
  unfold union, seq, irreflexive, inclusion in *; ins; desf; eauto.

  apply clos_trans_tn1 in H0; induction H0; apply ct_begin in H; destruct H; desc;
  eauto 8 using t_rt_trans, t_step.

  apply clos_trans_t1n in H; induction H; apply ct_end in H0; destruct H0; desc;
  eauto 8 using rt_t_trans, t_step.
Qed.


Lemma path_absorb_lt :
  forall X (r r' : relation X)
    (F: r' ⨾ r ⊆ r \/ r' ⨾ r ⊆ r')
    (T: transitive r),
    (r ∪ r')⁺ ≡ r'⁺ ∪ r ⨾ r'^*.
Proof.
  ins; rewrite path_absorb, rtE; relsf; hahn_rel.
Qed.

Lemma path_absorb_rt :
  forall X (r r' : relation X)
    (F: r'⨾ r ⊆ r \/ r'⨾ r ⊆ r')
    (T: transitive r'),
    (r ∪ r')⁺ ≡ r⁺ ∪ r^* ⨾ r'.
Proof.
  ins; rewrite path_absorb, rtE; relsf; hahn_rel.
Qed.

Lemma cycle_disj :
  forall X (r : relation X)
    (DISJ: forall x y (R: r x y) z (R': r y z), False) x
    (T: r⁺ x x), False.
Proof.
  ins; inv T; eauto using clos_trans_disj_rel.
Qed.

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


Lemma path_tur :
  forall X (r r' : relation X) (adom bdom : X -> Prop)
         (T: transitive r)
         (A: doma r' adom)
         (B: domb r' bdom),
    (r ∪ r')⁺ ≡ r ∪ (r ⨾ ⦗adom⦘ ∪ r')⁺ ⨾ (⦗bdom⦘ ⨾ r)^?.
Proof.
  split.
    rewrite seq_eqv_r, seq_eqv_l.
    unfold seq, union, clos_refl; intros ? ? P.
    apply clos_trans_tn1 in P; induction P; desf; eauto 14 using clos_trans; clear P.
    apply clos_trans_t1n in IHP; induction IHP;
    intuition; desf; eauto 14 using clos_trans.
  rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l.
  eauto using inclusion_t_r_t with rel.
Qed.

Lemma path_ur :
  forall X (r r' : relation X) (adom bdom : X -> Prop)
         (A: doma r' adom)
         (B: domb r' bdom),
    (r ∪ r')⁺ ≡ r⁺ ∪ (r⁺ ⨾ ⦗adom⦘ ∪ r')⁺ ⨾ (⦗bdom⦘ ⨾ r⁺)^?.
Proof.
  by ins; rewrite <- path_tur, ct_of_union_ct_l; eauto; vauto.
Qed.

Lemma path_tur2 :
  forall X (r r' : relation X) (adom bdom : X -> Prop)
         (T: transitive r')
         (A: doma r adom)
         (B: domb r bdom),
    (r ∪ r')⁺ ≡ r' ∪ (r' ⨾ ⦗adom⦘)^? ⨾ (r ∪ ⦗bdom⦘ ⨾ r')⁺.
Proof.
  split.
    rewrite seq_eqv_r, seq_eqv_l.
    unfold seq, union, clos_refl; intros ? ? P.
    apply clos_trans_t1n in P; induction P; desf; eauto 14 using clos_trans; clear P.
    apply clos_trans_tn1 in IHP0; induction IHP0;
    intuition; desf; eauto 14 using clos_trans.
  rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l.
  eauto using inclusion_r_t_t with rel.
Qed.

Lemma path_ur2 :
  forall X (r r' : relation X) (adom bdom : X -> Prop)
         (A: doma r adom)
         (B: domb r bdom),
    (r ∪ r')⁺ ≡ r'⁺ ∪ (r'⁺ ⨾ ⦗adom⦘)^? ⨾ (r ∪ ⦗bdom⦘ ⨾ r'⁺)⁺.
Proof.
  ins; rewrite <- path_tur2, ct_of_union_ct_r; eauto; vauto.
Qed.


Lemma acyclic_ur :
  forall X (r r' : relation X) (adom bdom : X -> Prop)
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y),
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
    auto with rel.
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
       eauto using inclusion_step2_ct with rel.
  rewrite (inclusion_seq_eqv_l (dom:=adom)).
  by sin_rewrite ct_ct; eauto with rel.

  rewrite ct_begin, irreflexive_seqC, <- !seqA, !seq_union_r, !seqA.
  rewrite <- ct_rt in H0; eapply irreflexive_inclusion, H0.
  apply inclusion_seq_mon; ins.
  apply inclusion_union_l; ins.
    assert (EQ: r ≡ eqv_rel adom ⨾ r).
      by split; rewrite seq_eqv_l; red; ins; desf; eauto.
    by rewrite EQ at 1; rewrite <- !seqA;
       eauto using inclusion_step2_ct with rel.
  rewrite <- inclusion_union_r2.
  apply inclusion_step_t, inclusion_seq_mon; ins.
  by rewrite inclusion_seq_eqv_l; sin_rewrite ct_ct.

  rewrite seqA; sin_rewrite ct_ct.
  eapply irreflexive_inclusion, H0; eauto using inclusion_t_r_t with rel.
Qed.

(*
Lemma cycle_ur :
  forall X (r r' : relation X) (adom bdom : X -> Prop)
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y) x
    (P: clos_trans (fun x y => r x y \/ r' x y) x x),
    r'⁺ x x \/
    exists x,
      clos_trans (fun x y => r x y \/ r'⁺ x y /\ bdom x /\ adom y) x x.
Proof.
  ins; eapply path_ur2 with (adom:=adom) (bdom:=bdom) in P; desf; eauto.
  eapply clos_trans_mon,
    path_tur with (adom:=adom) (bdom:=bdom) (r':=r)
                  (r:=fun a b => r'⁺ a b /\ bdom a)  in P0;
  desf; try split; ins; desc; vauto; try tauto.
  right; exists z; eapply clos_trans_mon; eauto; instantiate; ins; tauto.

  eapply t_step_rt in P0; desf.
    rewrite clos_refl_transE in *; desf; eauto using clos_trans.
    right; exists z1; eapply t_trans with z0; eauto 7 using clos_trans.
    eapply clos_trans_mon; eauto; instantiate; ins; tauto.
  right; exists z0; eapply t_trans, t_step_rt; eauto 8 using t_step.
  eexists; split; eauto; eapply clos_refl_trans_mon; eauto; instantiate; ins; tauto.

  eapply clos_trans_mon with
    (r' := fun x y => r'⁺ x y /\ bdom x \/ r x y) in P0; try tauto.
  eapply path_tur with (adom:=adom) (bdom:=bdom) in P0; desf; eauto using clos_trans.

  eapply t_rt_step in P0; desf.
    rewrite clos_refl_transE in *; desf; eauto using clos_trans.
    right; exists z; eapply t_trans with z0; eauto 7 using clos_trans.
    eapply clos_trans_mon; eauto; instantiate; ins; tauto.
  right; exists z0; eapply t_trans, t_step_rt; eauto 8 using t_step.
  eexists; split; eauto; eapply clos_refl_trans_mon; eauto; instantiate; ins; tauto.

  right; exists z; eapply t_trans with z0; eauto 8 using clos_trans.
  eapply clos_trans_mon; eauto; instantiate; ins; tauto.

  by red; ins; desf; vauto.
Qed.
*)


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
  (r ⨾ r')⁺ ≡ r ⨾ (r' ⨾ r)^* ⨾ r'.
Proof.
  split; red; ins; unfold seq in *; desf.
    by induction H; desf; eauto 10 using clos_refl_trans.
  cut (exists m, clos_refl_trans (r ⨾ r') x m /\ r m z0); unfold seq in *.
    by ins; desf; eapply t_rt_step; eauto.
  clear H1; induction H0 using clos_refl_trans_ind_left; desf;
  eauto 8 using clos_refl_trans.
Qed.

Lemma acyclic_rotl A (r r' : relation A) :
  acyclic (r ⨾ r') <-> acyclic (r' ⨾ r).
Proof.
  unfold acyclic; rewrite clos_trans_rotl.
  unfold irreflexive, seq; ins; desf; intuition; desf; [|eapply H];
    rewrite t_rt_step in *; desf; eauto 10.
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



Lemma path_ut_helper :
  forall X (r r' : relation X) (T: transitive r') x y
    (P: clos_refl_trans (fun x y => r x y \/ r' x y) x y),
    exists z w,
      r^* x z /\
      clos_refl_trans (fun x y => exists z, r' x z /\ r⁺ z y) z w /\
      (w = y \/ r' w y).
Proof.
  ins; induction P; eauto 8 using rt_refl.
    by desf; eauto 8 using rt_refl, rt_step.
  clear P1 P2; desf.

  rewrite clos_refl_transE in IHP2; desf;
  [rewrite clos_refl_transE, t_step_rt in IHP0; desf; eauto 8|
   rewrite clos_refl_transE, t_rt_step in IHP4; desf;
   eauto 8 using rt_trans, clos_trans_in_rt];
  (repeat eexists; [eauto|eapply rt_trans, rt_trans|vauto]); eauto;
  apply rt_step; eauto using t_trans.

  rewrite clos_refl_transE in IHP2; desf;
  [rewrite clos_refl_transE, t_step_rt in IHP0; desf; eauto 8|];
  (repeat eexists; [eauto|eapply rt_trans, rt_trans|vauto]); eauto;
  apply rt_step; eauto.

  rewrite clos_refl_transE in IHP2; desf; eauto 8 using rt_trans;
  rewrite clos_refl_transE, t_rt_step in IHP4; desf;
  eauto 8 using rt_trans, clos_trans_in_rt;
  (repeat eexists; [eauto|eapply rt_trans,rt_trans|right; eauto]); eauto;
  apply rt_step; eauto using t_trans.

  rewrite clos_refl_transE in IHP2; desf; eauto 8 using rt_trans;
  [rewrite clos_refl_transE, t_step_rt in IHP0; desf; eauto 8|];
  (repeat eexists; [eauto|eapply rt_trans,rt_trans|right; eauto]); eauto;
  apply rt_step; eauto using t_trans.
Qed.

Lemma path_ut :
  forall X (r r' : relation X) (T: transitive r'),
    (r ∪ r') ^* ≡ r ^*⨾ (r'⨾ r ^+) ^*⨾ r' ^?.
Proof.
  split.
  - unfold seq, union, clos_refl; red; ins; eapply path_ut_helper in H;
    desf; eauto 10.
  - rewrite inclusion_t_rt.
    eauto 10 using inclusion_seq_trans, inclusion_rt_rt2 with rel.
Qed.

Lemma path_ut2 :
  forall X (r r' : relation X) (T: transitive r'),
    (r ∪ r') ^+ ≡ r ^+ ∪ r ^*⨾ (r'⨾ r ^+) ^*⨾ r'⨾ r ^*.
Proof.
  split.
    rewrite ct_end, path_ut; ins; relsf.
    rewrite !seqA, (rewrite_trans_seq_cr_l T), crE; relsf; hahn_rel.
    2: by rewrite (rtE r) at 3; relsf.
    rewrite (rt_end (r' ⨾ r^+)) at 1; relsf.
    rewrite <- ct_end, !seqA; hahn_rel.
    rewrite inclusion_t_rt with (r:=r) at 2; rewrite <- ct_end.
    rewrite inclusion_t_rt with (r:=r) at 2; hahn_rel.
  hahn_rel.
  rewrite inclusion_t_rt, <- (rt_ct (r ∪ r')); seq_rewrite <- ct_end.
  apply inclusion_seq_mon; eauto with rel.
  apply inclusion_t_t2; rewrite ct_begin; eauto with rel.
Qed.


Lemma acyclic_ut :
  forall X (r r' : relation X) (T: transitive r'),
    acyclic (r ∪ r') <->
    acyclic r /\
    irreflexive r' /\
    acyclic (r' ⨾ r⁺).
Proof.
  unfold acyclic; ins; rewrite path_ut2; ins.
  rewrite irreflexive_union, irreflexive_seqC, !seqA, rt_rt, (rtE r); relsf.
  rewrite irreflexive_union, <- ct_end, irreflexive_seqC, rtE; relsf.
  rewrite irreflexive_union; intuition.
  rewrite ct_begin, seqA; sin_rewrite (rewrite_trans T).
  by rewrite <- seqA, <- ct_begin.
Qed.

Lemma acyclic_utt :
  forall X (r r' : relation X) (T: transitive r) (T: transitive r'),
    acyclic (r ∪ r') <->
    irreflexive r /\
    irreflexive r' /\
    acyclic (r ⨾ r').
Proof.
  ins; rewrite acyclic_ut, ct_of_trans, acyclic_rotl; ins.
  by unfold acyclic; rewrite ct_of_trans.
Qed.

Lemma path_utd_helper :
  forall X (r r' : relation X) (T: transitive r') dom
         (F: is_total dom r') (DA: doma r' dom) (DB: domb r' dom) x y
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    r⁺ x y \/
    (exists z w, r^* x z /\ r' z w /\ r^* w y) \/
    (exists z w, r' z w /\ r^* w z).
Proof.
  ins; induction P; desf; eauto 9 using clos_trans, clos_refl_trans, clos_trans_in_rt.
  right; destruct (classic (z1 = w)) as [|NEQ]; desf; eauto 8 using clos_refl_trans.
  eapply F in NEQ; desf; eauto 8 using clos_refl_trans.
Qed.

Lemma path_utd :
  forall X (r r' : relation X) (T: transitive r') dom
         (F: is_total dom r') (DA: doma r' dom) (DB: domb r' dom)
         (I': irreflexive (r' ⨾ r^*)),
    (r ∪ r')⁺ ≡ r⁺ ∪ r^* ⨾ r' ⨾ r^*.
Proof.
  split.
    unfold inclusion, seq, union in *; ins; desf.
    eapply path_utd_helper with (2:=F) in H; desf; eauto 8; exfalso; eauto 8.
  apply inclusion_union_l; eauto with rel.
  rewrite <- rt_ct, ct_begin; eauto with rel.
Qed.

Lemma acyclic_utd :
  forall X (r: relation X) (A: acyclic r)
         r' (T: transitive r') (IRR: irreflexive r') dom
         (F: is_total dom r') (DA: doma r' dom) (DB: domb r' dom)
         (I': irreflexive (r' ⨾ r⁺)),
  acyclic (r ∪ r').
Proof.
  unfold acyclic; ins.
  assert (irreflexive (r'⨾ r^*)).
    by rewrite rtE; relsf; rewrite irreflexive_union.
  unfold acyclic; ins; rewrite path_utd, irreflexive_union; eauto.
  by split; ins; rewrite irreflexive_seqC, seqA, rt_rt.
Qed.

Lemma reflexive_union_l A (r r' : relation A) :
  reflexive r -> reflexive (r ∪ r').
Proof. vauto. Qed.

Lemma reflexive_union_r A (r r' : relation A) :
  reflexive r' -> reflexive (r ∪ r').
Proof. vauto. Qed.
 
Lemma reflexive_seq A (r r' : relation A) :
  reflexive r -> reflexive r' -> reflexive (r ⨾ r').
Proof. vauto. Qed.

Hint Resolve reflexive_union_l reflexive_union_r reflexive_seq : rel.

Lemma path_unc X (r r' : relation X)
      (A : r ⨾ r ≡ ∅₂)
      (B : r' ⨾ r' ≡ ∅₂) :
  (r ∪ r')^* ≡ 
  (r ⨾ r')^* ∪ (r' ⨾ r)^* ∪ r ⨾ (r' ⨾ r)^* ∪ r' ⨾ (r ⨾ r')^*.
Proof.
  split.
    eapply inclusion_rt_ind_left; eauto with rel.
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
  (r ∪ r')⁺ ≡ (r ⨾ r')⁺ ∪ (r' ⨾ r)⁺ ∪ r ⨾ (r' ⨾ r)^* ∪ r' ⨾ (r ⨾ r')^*.
Proof.
  rewrite ct_begin, path_unc; ins.
  rewrite seq_union_l, !seq_union_r, <- !seqA, <- !ct_begin.
  rewrite (seq_rtE_r r (seq r r')), (seq_rtE_r r' (seq r' r)), <- !seqA.
  rewrite A, B, ?seq_false_l, ?union_false_l, ?union_false_r.
  by unfold union, seq; split; red; ins; desf; eauto 8 using rt_refl.
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


Lemma minus_seq_l A (r r': relation A) (T: transitive r) :
  r ⨾ r' \ r ⊆ r ⨾ (r' \ r).
Proof.
  unfold minus_rel, seq; red; ins; desf; repeat eexists; eauto.
Qed.

Lemma minus_seq_r A (r r': relation A) (T: transitive r') :
  r ⨾ r' \ r' ⊆ (r \ r') ⨾ r'.
Proof.
  unfold minus_rel, seq; red; ins; desf; repeat eexists; eauto.
Qed.

Lemma seq_rt_absorb_l A (r r': relation A) :
  r ⨾ r'^* ⊆ r ∪ (r ⨾ r' \ r) ⨾ r'^*.
Proof.
  unfold seq, union, inclusion, minus_rel; ins; desf.
  induction H0 using clos_refl_trans_ind_left; desf; eauto.
  destruct (classic (r x z0)); eauto 8 using clos_refl_trans.
  right; repeat eexists; eauto using clos_refl_trans.
Qed.

Lemma seq_ct_absorb_l A (r r': relation A) :
  r ⨾ r'⁺ ⊆ r ∪ (r ⨾ r' \ r) ⨾ r'^*.
Proof.
  rewrite <- seq_rt_absorb_l; eauto with rel.
Qed.

Lemma seq_rt_absorb_r A (r r': relation A) :
  r^* ⨾ r' ⊆ r' ∪ r^* ⨾ (r ⨾ r' \ r').
Proof.
  apply inclusion_transpE.
  rewrite !transp_union, !transp_seq, !transp_minus, !transp_rt, !transp_seq;
  auto using seq_rt_absorb_l, transitive_transp.
Qed.

Lemma seq_ct_absorb_r A (r r': relation A) :
  r⁺ ⨾ r' ⊆ r' ∪ r^* ⨾ (r ⨾ r' \ r').
Proof.
  rewrite <- seq_rt_absorb_r; eauto with rel.
Qed.

Lemma seq_rt_absorb_lt A (r r': relation A) (T: transitive r) :
  r ⨾ r'^* ⊆ r ∪ r ⨾ (r' \ r) ⨾ r'^*.
Proof.
  by rewrite seq_rt_absorb_l, minus_seq_l, seqA.
Qed.

Lemma seq_ct_absorb_lt A (r r': relation A) (T: transitive r) :
  r ⨾ r'⁺ ⊆ r ∪ r ⨾ (r' \ r) ⨾ r'^*.
Proof.
  by rewrite seq_ct_absorb_l, minus_seq_l, seqA.
Qed.

Lemma seq_rt_absorb_rt A (r r': relation A) (T: transitive r') :
  r^* ⨾ r' ⊆ r' ∪ r^* ⨾ (r \ r') ⨾ r'.
Proof.
  by rewrite seq_rt_absorb_r, minus_seq_r.
Qed.

Lemma seq_ct_absorb_rt A (r r': relation A) (T: transitive r') :
  r⁺ ⨾ r' ⊆ r' ∪ r^* ⨾ (r \ r') ⨾ r'.
Proof.
  by rewrite seq_ct_absorb_r, minus_seq_r.
Qed.

Lemma acyclic_via_expand_minus :
  forall X (r r' : relation X)
    (IRR1: irreflexive r)
    (IRR2: irreflexive ((r ⨾ r \ r) ⨾ r^*)),
    acyclic r.
Proof.
  unfold acyclic; ins; rewrite ct_begin.
  by rewrite seq_rt_absorb_l, irreflexive_union.
Qed.

Lemma acyclic_seq_via_expand_minus :
  forall X (r r' : relation X)
    (IRR1: irreflexive (r ⨾ r'))
    (IRR2: irreflexive ((r ⨾ r' ⨾ r \ r) ⨾ r' ⨾ (r ⨾ r')^*)),
    acyclic (r ⨾ r').
Proof.
  unfold acyclic; ins; rewrite ct_end, <- seqA.
  rewrite seq_rt_absorb_r, !seqA; relsf.
  rewrite irreflexive_union; split; ins.
  by rewrite seqA, irreflexive_seqC, seqA.
Qed.


