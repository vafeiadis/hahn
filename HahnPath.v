(******************************************************************************)
(** * Lemmas about paths and cycles *)
(******************************************************************************)

Require Import Classical.
Require Import HahnBase HahnList HahnRelationsBasic.
Require Import HahnEquational HahnMaxElt HahnRewrite.

Set Implicit Arguments.

(** Minimum cycle lemma *)

Lemma min_cycle X (rel rel' : relation X) (dom : X -> Prop)
    (TOT: is_total dom rel') 
    (T : transitive rel')
    (INCL: inclusion rel' (clos_trans rel))
    (INV: forall a b (R: rel a b) (R': rel' b a), False) :
    acyclic rel <->
    acyclic (restr_rel (fun x => ~ dom x) rel) /\
    (forall x (CYC: rel x x) (D: dom x), False) /\
    (forall c1 b1 (R: rel c1 b1) b2 
       (S : clos_refl rel' b1 b2) c2 
       (R': rel b2 c2) (S': clos_refl_trans (restr_rel (fun x => ~ dom x) rel) c2 c1)
       (D1 : dom b1) (D2: dom b2) (ND1: ~ dom c1) (ND2: ~ dom c2), False).
Proof.
  split; intros A; repeat split; ins; desc; eauto.
    by intros x P; eapply A, clos_trans_mon; eauto; unfold restr_rel; ins; desf.
    by eauto using t_step.
    eapply (A c1), t_trans, rt_t_trans, t_rt_trans; eauto using t_step;
      try (by eapply clos_refl_trans_mon; eauto; unfold restr_rel; ins; desf).
    by red in S; desf; eauto using clos_refl_trans, clos_trans_in_rt.
  assert (INCL': forall a b (R: rel a b) (D: dom a) (D': dom b), rel' a b).
    by ins; destruct (classic (a = b)) as [|N]; 
       [|eapply TOT in N]; desf; exfalso; eauto.
  intros x P.

  assert (J: clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) x x \/
             rel' x x /\ dom x /\ dom x \/
          dom x /\ (exists m n k, clos_refl rel' x m /\ rel m n /\
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) n k 
            /\ clos_refl rel k x 
            /\ dom m /\ ~ dom n /\ ~ dom k) \/
          (exists k m,
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) x k /\
            rel k m /\ clos_refl rel' m x /\
            ~ dom k /\ dom m /\ dom x) \/
          (exists k m m' n,
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) x k /\
            rel k m /\ clos_refl rel' m m' /\ rel m' n /\
            clos_refl_trans (restr_rel (fun x : X => ~ dom x) rel) n x /\
            ~ dom k /\ dom m /\ dom m' /\ ~ dom n)).
    by vauto.
  revert P J; generalize x at 1 4 6 8 11 13 14 16.
  unfold restr_rel in *; ins; apply clos_trans_tn1 in P; induction P; eauto.
  { rename x0 into x; desf; eauto.
    destruct (classic (dom x)); rewrite clos_refl_transE in *; desf; eauto using clos_trans. 
      by destruct (clos_trans_restrD J); desf. 
    by destruct (clos_trans_restrD J); eapply A, t_trans, t_step; vauto. 

    unfold clos_refl in J3; desf.
      by eapply A1 with (c1 := x) (b2 := m); eauto using rt_trans, rt_step.
    destruct (classic (dom x)).
      by eapply A1 with (c1 := k) (b2 := m); eauto; 
         unfold clos_refl in *; desf; eauto.
    by eapply A1 with (c1 := x) (b2 := m); eauto using rt_trans, rt_step.

    destruct (classic (dom y)).
      by rewrite clos_refl_transE in J; desf; 
         destruct (clos_trans_restrD J); desf.
    by eapply A1 with (c1 := k) (b2 := x); eauto 8 using rt_trans, rt_step.

    destruct (classic (dom x)).
      by rewrite clos_refl_transE in J3; desf; destruct (clos_trans_restrD J3); desf. 
    destruct (classic (dom y)).
      by rewrite clos_refl_transE in J; desf; destruct (clos_trans_restrD J); desf. 
    by eapply A1 with (c1 := k) (b2 := m'); eauto 8 using rt_trans, rt_step.
  }
  eapply clos_tn1_trans in P; desf.
  {
    destruct (classic (dom y)).
      rewrite clos_refl_transE in J; desf.
        destruct (classic (dom x0)).
          by eapply IHP; right; left; eauto using t_step.
        eapply IHP; do 2 right; left; split; ins.
        by eexists y,x0,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
      destruct (clos_trans_restrD J).
      apply IHP; right; right; left; split; ins.
      by eexists y,z,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
    rewrite clos_refl_transE in J; desf.
      destruct (classic (dom x0)).
        eapply IHP; do 3 right; left.
        by eexists y,x0; repeat eexists; vauto; eauto using clos_trans_in_rt.
      by eapply IHP; left; vauto.
    by destruct (clos_trans_restrD J); eapply IHP; left; 
       eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
  }
  {
    destruct (classic (dom y)).
      by apply IHP; eauto 8 using clos_trans.
    apply IHP; do 3 right; left; eexists y, z; 
    repeat eexists; vauto; eauto using clos_trans_in_rt. 
  }
  { destruct (classic (dom y)).
      by eapply IHP; do 2 right; left; split; ins; eexists m; repeat eexists; 
         eauto; red in J0; red; desf; eauto. 
    destruct (classic (dom x0)).
    
    destruct (classic (m = x0)) as [|NEQ]; subst.
      by eapply IHP; do 3 right; left; eexists y,z; repeat eexists; vauto. 
    eapply TOT in NEQ; desf.
      by eapply IHP; do 3 right; left; eexists y,z; repeat eexists; vauto;
         eauto; red; red in J0; desf; eauto. 
    by red in J3; desf; eapply A1 with (c1 := k) (b2 := m); 
       eauto 8 using rt_trans, rt_step, clos_trans_in_rt.

    by eapply IHP; do 4 right; eexists y,z; repeat eexists; vauto; 
       unfold clos_refl in *; desf; vauto.
  }

  { destruct (classic (dom z)).
      by rewrite clos_refl_transE in J; desf; 
         destruct (clos_trans_restrD J); desf.
    destruct (classic (y = m)) as [|NEQ]; desf.
      by unfold clos_refl in *; desf; eauto.
    destruct (classic (dom y)).
      eapply TOT in NEQ; desf.
        by unfold clos_refl in *; desf; 
           apply IHP; right; left; eauto using t_rt_trans, t_step.
      by eapply A1 with (c1 := k) (b2 := y); 
         eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
    by eapply IHP; do 3 right; left; eexists k, m; repeat eexists; vauto.
  }

    destruct (classic (dom x0)).
      by rewrite clos_refl_transE in J3; desf; destruct (clos_trans_restrD J3); desf. 
    destruct (classic (dom z)).
      by rewrite clos_refl_transE in J; desf; destruct (clos_trans_restrD J); desf. 
    destruct (classic (y = m)) as [|NEQ]; desf.
      by eapply IHP; do 2 right; left; split; ins; eexists m', n; repeat eexists; vauto.
    destruct (classic (dom y)).
      eapply TOT in NEQ; desf.
        by unfold clos_refl in *; desf; eapply IHP; do 2 right; left; split; ins; 
           eexists m', n; repeat eexists; vauto;
           eauto using rt_trans, clos_trans_in_rt.
      by eapply A1 with (c1 := k) (b2 := y); 
         eauto 8 using rt_trans, rt_step, clos_trans_in_rt.
    by eapply IHP; do 4 right; eexists k,m,m'; repeat eexists; vauto.
Qed.

Lemma min_cycle1 X (r r' : relation X) (d : X -> Prop)
    nd (ND: nd = fun x => ~ d x) 
    (TOT: is_total d r') 
    (T : transitive r')
    (INCL: r' ⊆ r^+)
    (INV: irreflexive (r ⨾ r')) :
    acyclic r <->
    acyclic (<| nd |> ⨾ r ⨾ <| nd |>) /\
    irreflexive (<| d |> ⨾ r ⨾ <| d |>) /\
    irreflexive (<| nd |> ⨾ r ⨾ <| d |> ⨾ r'^? ⨾ <| d |> ⨾ 
                 r ⨾ <| nd |> ⨾ (<| nd |> ⨾ r ⨾ <| nd |>)^*).
Proof.
generalize (@min_cycle X r r' d TOT T INCL); ins.
assert (XX: forall a b : X, r a b -> r' b a -> False).
  by unfold irreflexive, seq in *; eauto.
rewrite ND.
specialize (H XX); clear TOT T INCL INV XX ND nd.
assert (AA: restr_rel (fun x : X => ~ d x) r <--> <| fun x : X => ~ d x |>⨾ r⨾ <| fun x : X => ~ d x |>).
  by red; unfold  seq, eqv_rel, restr_rel, inclusion in *; split; ins; desf; eauto 10.
split.
- intro H1; apply H in H1; clear H.
  desc; split.
  by rewrite <- AA.
  split.
  by unfold irreflexive, seq, eqv_rel; ins; desc; subst; eauto.
  by rewrite <- AA; unfold eqv_rel, seq; red; ins; desc; subst; eauto.
- ins; desc; apply H; split.
  by rewrite AA.
  split.
  by unfold irreflexive, seq, eqv_rel in *; eauto 10.
  rewrite <- AA in *; ins; apply (H2 c1).
  by unfold irreflexive, seq, eqv_rel in *; repeat eexists; eauto.
Qed.


(******************************************************************************)

Lemma path_decomp_u1 X (rel : relation X) a b : 
  clos_trans (rel ∪ singl_rel a b) ≡
  clos_trans rel ∪ clos_refl_trans rel ⨾ singl_rel a b ⨾ clos_refl_trans rel.
Proof.
  split. 
  { unfold inclusion, union, singl_rel, seq. 
    induction 1; desf; eauto 9 using clos_trans, clos_refl_trans, clos_trans_in_rt.
  }
  eapply inclusion_union_l; eauto with rel.
  rewrite <- rt_ct, ct_begin; eauto with rel.
Qed.

Lemma cycle_decomp_u1 X (rel : relation X) a b c : 
  clos_trans (rel ∪ singl_rel a b) c c ->
  clos_trans rel c c \/ clos_refl_trans rel b a.
Proof.
  ins; apply path_decomp_u1 in H.
  unfold seq, union, singl_rel in *; desf; eauto using clos_refl_trans.
Qed.

Lemma acyclic_decomp_u1 X (rel : relation X) a b : 
  acyclic rel ->
  ~ clos_refl_trans rel b a ->
  acyclic (rel ∪ singl_rel a b).
Proof.
  unfold acyclic, irreflexive; ins. 
  forward eapply cycle_decomp_u1; ins; desf; eauto.
Qed.

Lemma path_decomp_u1_max X (rel : relation X) a b (MAX: max_elt rel b) :
  clos_trans (rel ∪ singl_rel a b) ≡
  clos_trans rel ∪ clos_refl_trans rel ⨾ singl_rel a b.
Proof.
  rewrite path_decomp_u1, seq_singl_max_rt; vauto.
Qed.

Lemma acyclic_u1_max X (rel : relation X) a b (MAX: max_elt rel b) :
  acyclic (rel ∪ singl_rel a b) <->
  acyclic rel /\ a <> b.
Proof.
  unfold acyclic; 
  rewrite path_decomp_u1_max, irreflexive_union, irreflexive_seqC, seq_singl_max_rt;
  intuition; unfold irreflexive, singl_rel in *; ins; desf; eauto.
Qed.

(******************************************************************************)

Lemma path_decomp_u_total :
  forall X (rel1 : relation X) dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b)
    (IRR: irreflexive (clos_refl_trans rel1 ⨾ clos_trans rel2)),
  clos_trans (rel1 ∪ rel2) ≡
  clos_trans rel1 ∪
  clos_refl_trans rel1 ⨾ clos_trans rel2 ⨾ clos_refl_trans rel1. 
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
    by eapply t_rt_step in IHC0; desf; specialize_full D; eauto; tauto.
    by eapply t_rt_step in IHC4; desf; specialize_full D; eauto; tauto.
  }
  eapply inclusion_union_l; eauto with rel.
  rewrite <- rt_ct with (rel := rel1 ∪ rel2),
          <- ct_rt with (rel := rel1 ∪ rel2); eauto 8 with rel.
Qed.

Lemma acyclic_decomp_u_total :
  forall X (rel1 : relation X) dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b)
    (A: acyclic rel1)
    (IRR: irreflexive (clos_refl_trans rel1 ⨾ clos_trans rel2)),
    acyclic (rel1 ∪ rel2).
Proof.
  red; ins.
  rewrite path_decomp_u_total; eauto. 
  eapply irreflexive_union; split; ins.
  by rewrite irreflexive_seqC, seqA, rt_rt, irreflexive_seqC.
Qed.

Lemma clos_trans_disj_rel :
  forall X (rel rel' : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False) x y
    (R: clos_trans rel x y) z
    (R': clos_trans rel' y z),
    False.
Proof.
  ins; induction R; eauto; induction R'; eauto.
Qed.

Lemma path_absorb1 :
  forall X (rel rel' : relation X) (F: inclusion (rel' ⨾ rel) rel'),
    clos_trans (rel ∪ rel') ≡
    clos_trans rel ∪ clos_trans rel' ∪ clos_trans rel ⨾ clos_trans rel'.
Proof.
  split; cycle 1.
    repeat apply inclusion_union_l; eauto with rel.
    by repeat apply inclusion_seq_trans; eauto with rel; vauto.
  apply inclusion_t_ind_right; relsf; 
    repeat apply inclusion_union_l; 
    eauto 10 using inclusion_t_r_t with rel;
  try solve [rewrite (ct_end rel'), !seqA, F, <- ct_end; eauto 10 with rel].
  rewrite (ct_end rel') at 3; rewrite seqA; eauto 10 with rel.
Qed.

Lemma path_absorb2 :
  forall X (rel rel' : relation X) (F: inclusion (rel' ⨾ rel) rel),
    clos_trans (rel ∪ rel') ≡
    clos_trans rel ∪ clos_trans rel' ∪ clos_trans rel ⨾ clos_trans rel'.
Proof.
  split; cycle 1.
    repeat apply inclusion_union_l; eauto with rel.
    by repeat apply inclusion_seq_trans; eauto with rel; vauto.
  apply inclusion_t_ind_left; relsf; 
    repeat apply inclusion_union_l; 
    eauto 10 using inclusion_r_t_t with rel;
  try solve [rewrite (ct_begin rel), <- !seqA, F, <- ct_begin; eauto 10 with rel].
  rewrite (ct_begin rel) at 3; rewrite seqA; eauto 10 with rel.
Qed.

Lemma path_absorb :
  forall X (rel rel' : relation X) 
         (F: rel'⨾ rel ⊆ rel \/ rel'⨾ rel ⊆ rel'),
    clos_trans (rel ∪ rel') ≡
    clos_trans rel ∪ clos_trans rel' ∪ clos_trans rel ⨾ clos_trans rel'.
Proof.
  ins; desf; eauto using path_absorb1, path_absorb2.
Qed.

Lemma acyclic_absorb :
  forall X (rel rel' : relation X)
         (F: rel'⨾ rel ⊆ rel \/ rel'⨾ rel ⊆ rel')
    (A1: acyclic rel)
    (A2: acyclic rel'),
    acyclic (rel ∪ rel').
Proof.
  unfold acyclic; ins; rewrite path_absorb; eauto.
  unfold union, seq, irreflexive, inclusion in *; ins; desf; eauto.

  apply clos_trans_tn1 in H0; induction H0; apply ct_begin in H; destruct H; desc; 
  eauto 8 using t_rt_trans, t_step.
  
  apply clos_trans_t1n in H; induction H; apply ct_end in H0; destruct H0; desc; 
  eauto 8 using rt_t_trans, t_step.
Qed.


Lemma path_absorb_lt :
  forall X (rel rel' : relation X) 
    (F: rel'⨾ rel ⊆ rel \/ rel'⨾ rel ⊆ rel')
    (T: transitive rel),
    clos_trans (rel ∪ rel') ≡
    clos_trans rel' ∪ rel ⨾ clos_refl_trans rel'.
Proof.
  ins; rewrite path_absorb, rtE; relsf; hahn_rel.
Qed.

Lemma path_absorb_rt :
  forall X (rel rel' : relation X) 
    (F: rel'⨾ rel ⊆ rel \/ rel'⨾ rel ⊆ rel')
    (T: transitive rel'),
    clos_trans (rel ∪ rel') ≡
    clos_trans rel ∪ clos_refl_trans rel ⨾ rel'.
Proof.
  ins; rewrite path_absorb, rtE; relsf; hahn_rel.
Qed.

Lemma cycle_disj :
  forall X (rel : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel y z), False) x
    (T: clos_trans rel x x), False.
Proof.
  ins; inv T; eauto using clos_trans_disj_rel.
Qed.

Lemma clos_trans_restr_trans_mid : 
  forall X (rel rel' : relation X) f x y
    (A : clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) x y)
    z (B : rel y z) w
    (C : clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) z w),
    clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) x w.
Proof.
  ins; eapply t_trans, t_trans; vauto.
  eapply t_step; repeat split; eauto.
    by apply clos_trans_restrD in A; desc.
  by apply clos_trans_restrD in C; desc.
Qed.

Lemma clos_trans_restr_trans_cycle : 
  forall X (rel rel' : relation X) f x y
    (A : clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) x y)
    (B : rel y x),
    clos_trans (restr_rel f (fun x y => rel x y \/ rel' x y)) x x.
Proof.
  ins; eapply t_trans, t_step; eauto. 
  by red; apply clos_trans_restrD in A; desf; auto.
Qed.


Lemma path_tur :
  forall X (r r' : relation X) (adom bdom : X -> Prop)
         (T: transitive r)
         (A: forall x y (R: r' x y), adom x)
         (B: forall x y (R: r' x y), bdom y),
    clos_trans (r ∪ r') ≡
    r ∪
      clos_trans (r ⨾ eqv_rel adom ∪ r') ⨾
      clos_refl (eqv_rel bdom ⨾ r).
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
         (A: forall x y (R: r' x y), adom x)
         (B: forall x y (R: r' x y), bdom y),
    clos_trans (r ∪ r') ≡
    clos_trans r ∪
      clos_trans (clos_trans r ⨾ <| adom |> ∪ r') ⨾
      clos_refl (<| bdom |> ⨾ clos_trans r).
Proof.
  by ins; rewrite <- path_tur, clos_trans_union_ct; eauto; vauto. 
Qed. 

Lemma path_tur2 :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (T: transitive r')  
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y),
    clos_trans (r ∪ r') ≡
    r' ∪ clos_refl (r' ⨾ <| adom |>) ⨾ clos_trans (r ∪ <| bdom |> ⨾ r').
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
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y),
    clos_trans (r ∪ r') ≡
    clos_trans r' ∪
      clos_refl (clos_trans r' ⨾ eqv_rel adom) ⨾
      clos_trans (r ∪ eqv_rel bdom ⨾ clos_trans r').
Proof.
  ins; rewrite <- path_tur2; eauto; vauto. 
  rewrite unionC, <- clos_trans_union_ct, unionC; eauto; vauto. 
Qed. 


(*
Lemma seq_cr_cr A (rel rel' : relation A) :
  clos_refl rel ⨾ clos_refl rel' ≡
  clos_refl (rel ⨾ rel').
Proof.
  rewrite !crE, seq_union_l, seq_id_l, seq_union_r, seq_id_r.
*)

Lemma acyclic_ur :
  forall X (r r' : relation X) (adom bdom : X -> Prop) 
         (A: forall x y (R: r x y), adom x)
         (B: forall x y (R: r x y), bdom y),
    acyclic r' ->
    acyclic (r ∪ eqv_rel bdom ⨾ clos_trans r' ⨾ eqv_rel adom) ->
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
    clos_trans r' x x \/
    exists x, 
      clos_trans (fun x y => r x y \/ clos_trans r' x y /\ bdom x /\ adom y) x x.
Proof.
  ins; eapply path_ur2 with (adom:=adom) (bdom:=bdom) in P; desf; eauto. 
  eapply clos_trans_mon, 
    path_tur with (adom:=adom) (bdom:=bdom) (r':=r)
                  (r:=fun a b => clos_trans r' a b /\ bdom a)  in P0;
  desf; try split; ins; desc; vauto; try tauto.
  right; exists z; eapply clos_trans_mon; eauto; instantiate; ins; tauto.

  eapply t_step_rt in P0; desf. 
    rewrite clos_refl_transE in *; desf; eauto using clos_trans.
    right; exists z1; eapply t_trans with z0; eauto 7 using clos_trans. 
    eapply clos_trans_mon; eauto; instantiate; ins; tauto.
  right; exists z0; eapply t_trans, t_step_rt; eauto 8 using t_step.
  eexists; split; eauto; eapply clos_refl_trans_mon; eauto; instantiate; ins; tauto.

  eapply clos_trans_mon with 
    (r' := fun x y => clos_trans r' x y /\ bdom x \/ r x y) in P0; try tauto.
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
  forall X (R : relation X) (I: irreflexive R) 
         (T: transitive R) L (ND: NoDup L) a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    clos_trans (immediate R) a b.
Proof.
  intros until 3; induction ND; ins; vauto.
  destruct (classic (R a x /\ R x b)) as [|N]; desf;
    [apply t_trans with x|]; eapply IHND; ins;
    forward eapply (D c); eauto; intro; desf; exfalso; eauto.
Qed.



Lemma clos_trans_rotl A (r r' : relation A) :
  clos_trans (r ⨾ r') ≡ r ⨾ clos_refl_trans (r' ⨾ r) ⨾ r'.
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
  immediate (clos_trans r) a b ->
  r a b /\ (forall c, clos_trans r a c -> clos_trans r c b -> False).
Proof.
  unfold immediate; ins; desf; split; ins.
  apply t_step_rt in H; desf.
  apply clos_refl_transE in H1; desf; exfalso; eauto using t_step.
Qed.

Lemma clos_trans_immediate1 A (r : relation A) (T: transitive r) a b :
  clos_trans (immediate r) a b -> r a b.
Proof.
  unfold immediate; induction 1; desf; eauto.
Qed.

Lemma clos_trans_immediate2 A (r : relation A)
      (T: transitive r) (IRR: irreflexive r) dom
      (D: forall a b (R: r a b), In b dom) a b :
  r a b ->
  clos_trans (immediate r) a b.
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

  apply min_cycle with (dom := dom) (rel' := r); 
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
    unfold restr_rel, clos_refl in *; desf; eauto.
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
      clos_refl_trans r x z /\
      clos_refl_trans (fun x y => exists z, r' x z /\ clos_trans r z y) z w /\
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
    acyclic (r' ⨾ clos_trans r).
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
         (F: is_total dom r')
         (R: forall a b, r' a b -> dom a /\ dom b) x y
    (P: clos_trans (fun x y => r x y \/ r' x y) x y),
    clos_trans r x y \/
    (exists z w, clos_refl_trans r x z /\ r' z w /\ clos_refl_trans r w y) \/
    (exists z w, r' z w /\ clos_refl_trans r w z).
Proof.
  ins; induction P; desf; eauto 9 using clos_trans, clos_refl_trans, clos_trans_in_rt.
  right; destruct (classic (z1 = w)) as [|NEQ]; desf; eauto 8 using clos_refl_trans.
  eapply F in NEQ; desf; eauto 8 using clos_refl_trans.
  eapply R in IHP4; desf.
  eapply R in IHP0; desf.
Qed.

Lemma path_utd :
  forall X (r r' : relation X) (T: transitive r') dom
         (F: is_total dom r')
         (R: forall a b, r' a b -> dom a /\ dom b)
         (I': irreflexive (r' ⨾ clos_refl_trans r)),
    clos_trans (r ∪ r') ≡
    clos_trans r ∪
    (clos_refl_trans r ⨾ r' ⨾ clos_refl_trans r).
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
         (F: is_total dom r')
         (R: forall a b, r' a b -> dom a /\ dom b)
         (I': irreflexive (r' ⨾ clos_trans r)),
  acyclic (r ∪ r').
Proof.
  unfold acyclic; ins.
  assert (irreflexive (r'⨾ clos_refl_trans r)).
    by rewrite rtE; relsf; rewrite irreflexive_union.
  unfold acyclic; ins; rewrite path_utd, irreflexive_union; eauto.
  by split; ins; rewrite irreflexive_seqC, seqA, rt_rt.
Qed.



Lemma acyclic_case_split A (R : relation A) f :
  acyclic R <->
  acyclic (restr_rel f R) /\ (forall x (NEG: ~ f x) (CYC: clos_trans R x x), False).
Proof.
  unfold restr_rel; repeat split; repeat red; ins; desc; eauto.
    by eapply H, clos_trans_mon; eauto; instantiate; ins; desf. 
  destruct (classic (f x)) as [X|X]; eauto.
  assert (M: clos_refl_trans (fun a b => R a b /\ f a /\ f b) x x) by vauto.
  generalize X; revert H0 M X; generalize x at 2 3 5; ins.
  apply clos_trans_tn1 in H0; induction H0; eauto 6 using rt_t_trans, t_step.
  destruct (classic (f y)); eauto 6 using clos_refl_trans.
  eapply H1; eauto.
  eapply t_rt_trans, rt_trans; eauto using t_step, clos_trans_in_rt, clos_tn1_trans. 
  by eapply clos_refl_trans_mon; eauto; instantiate; ins; desf. 
Qed.

Lemma path_unc X (r r' : relation X)
  (A: r ⨾ r ≡ (fun x y => False))
  (B: r' ⨾ r' ≡ (fun x y => False)) :
  clos_refl_trans (r ∪ r') ≡
  clos_refl_trans (r ⨾ r') ∪
  (clos_refl_trans (r' ⨾ r) ∪
   (r ⨾ clos_refl_trans (r' ⨾ r) ∪
    r' ⨾ clos_refl_trans (r ⨾ r'))).
Proof.
  split.
    eapply inclusion_rt_ind_left; [by vauto|].
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
  (A: r ⨾ r ≡ (fun x y => False))
  (B: r' ⨾ r' ≡ (fun x y => False)) :
  clos_trans (r ∪ r') ≡
  clos_trans (r ⨾ r') ∪
  (clos_trans (r' ⨾ r) ∪
   (r ⨾ clos_refl_trans (r' ⨾ r) ∪
    r' ⨾ clos_refl_trans (r ⨾ r'))).
Proof.
  rewrite ct_begin, path_unc; ins.
  rewrite seq_union_l, !seq_union_r, <- !seqA, <- !ct_begin.
  rewrite (seq_rtE_r r (seq r r')), (seq_rtE_r r' (seq r' r)), <- !seqA.
  rewrite A, B, ?seq_false_l, ?union_false_l, ?union_false_r.
  by unfold union, seq; split; red; ins; desf; eauto 8 using rt_refl.   
Qed.

Lemma acyclic_unc X (r r' : relation X)
  (A: r ⨾ r ≡ (fun x y => False))
  (B: r' ⨾ r' ≡ (fun x y => False)) :
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
  minus_rel (r ⨾ r') r ⊆ r ⨾ minus_rel r' r.
Proof.
  unfold minus_rel, seq; red; ins; desf; repeat eexists; eauto.
Qed.

Lemma minus_seq_r A (r r': relation A) (T: transitive r') :
  minus_rel (r ⨾ r') r' ⊆ minus_rel r r' ⨾ r'.
Proof.
  unfold minus_rel, seq; red; ins; desf; repeat eexists; eauto.
Qed.

Lemma seq_rt_absorb_l A (r r': relation A) :
  r ⨾ clos_refl_trans r' ⊆ r ∪ minus_rel (r ⨾ r') r ⨾ clos_refl_trans r'.
Proof.
  unfold seq, union, inclusion, minus_rel; ins; desf.
  induction H0 using clos_refl_trans_ind_left; desf; eauto.
  destruct (classic (r x z0)); eauto 8 using clos_refl_trans.
  right; repeat eexists; eauto using clos_refl_trans. 
Qed.

Lemma seq_ct_absorb_l A (r r': relation A) :
  r ⨾ clos_trans r' ⊆ r ∪ minus_rel (r ⨾ r') r ⨾ clos_refl_trans r'.
Proof.
  rewrite <- seq_rt_absorb_l; eauto with rel. 
Qed.

Lemma seq_rt_absorb_r A (r r': relation A) :
  clos_refl_trans r ⨾ r' ⊆ r' ∪ clos_refl_trans r ⨾ minus_rel (r ⨾ r') r'. 
Proof.
  apply inclusion_transpE.
  rewrite !transp_union, !transp_seq, !transp_minus, !transp_rt, !transp_seq;
  auto using seq_rt_absorb_l, transitive_transp. 
Qed.

Lemma seq_ct_absorb_r A (r r': relation A) : 
  clos_trans r ⨾ r' ⊆ r' ∪ clos_refl_trans r ⨾ minus_rel (r ⨾ r') r'. 
Proof.
  rewrite <- seq_rt_absorb_r; eauto with rel. 
Qed.

Lemma seq_rt_absorb_lt A (r r': relation A) (T: transitive r) :
  r ⨾ clos_refl_trans r' ⊆ r ∪ r ⨾ minus_rel r' r ⨾ clos_refl_trans r'.
Proof.
  by rewrite seq_rt_absorb_l, minus_seq_l, seqA.
Qed.

Lemma seq_ct_absorb_lt A (r r': relation A) (T: transitive r) :
  r ⨾ clos_trans r' ⊆ r ∪ r ⨾ minus_rel r' r ⨾ clos_refl_trans r'.
Proof.
  by rewrite seq_ct_absorb_l, minus_seq_l, seqA.
Qed.

Lemma seq_rt_absorb_rt A (r r': relation A) (T: transitive r') :
  clos_refl_trans r ⨾ r' ⊆ r' ∪ clos_refl_trans r ⨾ minus_rel r r' ⨾ r'.
Proof.
  by rewrite seq_rt_absorb_r, minus_seq_r. 
Qed.

Lemma seq_ct_absorb_rt A (r r': relation A) (T: transitive r') :
  clos_trans r ⨾ r' ⊆ r' ∪ clos_refl_trans r ⨾ minus_rel r r' ⨾ r'.
Proof.
  by rewrite seq_ct_absorb_r, minus_seq_r. 
Qed.



Lemma acyclic_via_expand_minus :
  forall X (r r' : relation X)
    (IRR1: irreflexive r)
    (IRR2: irreflexive (minus_rel (r ⨾ r) r ⨾ clos_refl_trans r)),
    acyclic r.
Proof.
  unfold acyclic; ins; rewrite ct_begin. 
  by rewrite seq_rt_absorb_l, irreflexive_union.
Qed.

Lemma acyclic_seq_via_expand_minus :
  forall X (r r' : relation X)
    (IRR1: irreflexive (r ⨾ r'))
    (IRR2: irreflexive (minus_rel (r ⨾ r' ⨾ r) r ⨾ r' ⨾ clos_refl_trans (r ⨾ r'))),
    acyclic (r ⨾ r').
Proof.
  unfold acyclic; ins; rewrite ct_end, <- seqA. 
  rewrite seq_rt_absorb_r, !seqA; relsf. 
  rewrite irreflexive_union; split; ins.
  by rewrite seqA, irreflexive_seqC, seqA. 
Qed.



Require Import Omega. 

Lemma get_first_nat (P : nat -> Prop) :
  (exists m, P m /\ forall k, P k -> m <= k) \/ forall k, ~ P k.
Proof.
  apply NNPP; intro X; apply not_or_and in X; desf.
  apply not_all_not_ex in X0; desf; destruct X. 
  revert P X0; induction n; ins.
    by exists 0; split; ins; desf; auto with arith. 
  destruct (classic (P 0)).
    by exists 0; split; ins; desf; auto with arith. 
  specialize (IHn (fun n => P (S n)) X0); desf.
  eexists (S m); split; ins; eauto.
  destruct k; try done; eauto using le_n_S.
Qed.

Lemma get_max_bounded_nat (P : nat -> Prop) x n (LE: x <= n) (SAT: P x) :
  exists m, m <= n /\ P m /\ forall k, k <= n -> P k -> k <= m.
Proof.
  destruct get_first_nat with (P := fun x => P (n - x)); desf.
  exists (n - m); repeat split; ins; eauto; try omega. 
  replace k with (n - (n - k)) in H2; [apply H0 in H2|]; omega.
  destruct (H (n - x)).
  replace (n - (n - x)) with x; eauto; omega.
Qed.

Lemma path_minimize :
  forall X (r : relation X) a b
    (PATH: clos_trans r a b),
    exists f n, 
      << START: f 0 = a >> /\ 
      << END: f (S n) = b >> /\
      << STEP: forall i (LT: i <= n), r (f i) (f (S i)) >> /\
      << MIN: forall i (LTi: i <= n) j (LTj: i < j <= S n), 
                r (f i) (f j) -> j = S i >> .
Proof.
  ins; apply clos_trans_tn1 in PATH; induction PATH; desf; unnw.
    exists (fun x => match x with 0 => a | S _ => y end), 0; intuition; try omega. 
      by apply NPeano.Nat.le_0_r in LT; desf.

  destruct (get_first_nat (fun x => x <= n /\ r (f x) z)) as [(m & M)|M]; desc.
  { exists (fun x => if Compare_dec.le_dec x m then f x else z), m;
    repeat split; ins; desf; try omega.
      by eapply STEP; omega.
    by assert (i = m) by omega; desf. 
    by eapply MIN; eauto; omega.
    assert (j = S m) by omega; desf.
    specialize (M0 i); specialize_full M0; try split; ins; omega. }
  { exists (fun x => if Compare_dec.le_dec x (S n) then f x else z), (S n);
    repeat split; ins; desf; try omega.
      by eapply STEP; omega.
    assert (i = S n) by omega; desf. 
    eapply MIN; eauto; try omega.
    destruct (eqP i (S n)); desf; try omega.
    destruct (M i); split; ins; omega. }
Qed.


Lemma acyclic_minimize1 X (r : relation X) :
  acyclic r <->
  ~ exists f n, 
      << ENDS: f 0 = f (S n) >> /\ 
      << STEP: forall i (LT: i <= n), r (f i) (f (S i)) >> /\
      << MIN: forall i (LTi: i <= n) j (LTj: j <= S n), 
                r (f i) (f j) -> j = S i \/ i = n /\ j = 0 >>.
Proof.
  split; repeat red; ins; desf.
  { destruct (H (f 0)).
    rewrite ENDS at 2; clear - STEP.
    induction n; vauto.
      by apply t_step, STEP.
    by eapply t_trans, t_step; eauto. }
  apply path_minimize in H0; desf.
  destruct H; unnw.
  destruct (get_first_nat (fun x => x <= n /\ exists mm, mm <= x /\ 
                                                         r (f x) (f mm))) 
    as [(m & M & M'')|M]; desc.
  assert (M' : forall k k', k' <= k -> k <= n -> r (f k) (f k') -> m <= k).
    by ins; apply M''; eauto.
  clear M''.
  { 
    forward eapply get_max_bounded_nat 
    with (P := fun x => r (f m) (f x)) (x := mm) (n := m) as [kk K]; ins; desc.
    clear mm M0 M1; rename kk into mm.
    exists (fun x => if x == (S (m - mm)) then (f mm) else (f (x + mm))), (m - mm); 
      repeat split; ins; desf; desf; try omega.
    by rewrite NPeano.Nat.sub_add.
    eapply STEP; omega.
    left; apply M' in H; omega.  
    destruct (eqP j 0); desf; ins.
      right; apply M' in H; omega.
    left; apply MIN in H; try split; try omega. 
    apply NNPP; intro K'.
    assert (Z:=H); apply M' in Z; try omega.
    assert (i = m - mm) by omega; subst.
    rewrite Nat.sub_add in *; ins; apply K1 in H; omega.
  }
  { exists f, n;
    repeat split; ins; desf; try omega. 
    destruct (le_lt_dec j i); [edestruct M|]; eauto.
 }
Qed.

Lemma acyclic_minimize X (r : relation X) :
  acyclic r <->
  ~ exists f n, 
      << ENDS: f 0 = f (S n) >> /\ 
      << STEP: forall i (LT: i <= n), r (f i) (f (S i)) >> /\
      << MIN: forall i (LTi: i <= n) j (LTj: j <= S n), 
                r (f i) (f j) -> j = S i \/ i = n /\ j = 0 >> /\
      << NODUP: forall i (LTi: i <= S n) j (LTj: j <= S n), 
                  f i = f j -> 
                  i = j \/ i = 0 /\ j = S n \/ 
                           i = S n /\ j = 0 >>.
Proof.
  rewrite acyclic_minimize1. 
  split; intros A B; destruct A; desc; unnw; eauto. 
  exists f, n; repeat split; ins; eauto.
  destruct (lt_dec i j).
    destruct j; [exfalso; omega|]; ins; auto. 
    specialize (STEP j); specialize_full STEP; try omega.
    rewrite <- H in STEP; eapply MIN in STEP; try omega.
  destruct (lt_dec j i); try omega.
  destruct i; [exfalso; omega|]; ins; auto. 
  specialize (STEP i); specialize_full STEP; try omega.
  rewrite H in STEP; eapply MIN in STEP; try omega.
Qed.



