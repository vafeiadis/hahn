(******************************************************************************)
(** * Extension of a partial order to a total order *)
(******************************************************************************)

Require Import NPeano Omega Setoid Classical.
Require Import HahnBase HahnList HahnRelationsBasic HahnEquational HahnRewrite.
Require Import HahnMaxElt.

Set Implicit Arguments.

(******************************************************************************)
(** Extend an order to make it total on one element. *)

Section one_extension.

  Variable X : Type.
  Variable elem : X.
  Variable rel : relation X.

  Definition one_ext : relation X := 
    fun x y =>
      clos_trans rel x y 
      \/ clos_refl_trans rel x elem /\ ~ clos_refl_trans rel y elem.

  Lemma one_ext_extends x y : rel x y -> one_ext x y. 
  Proof. vauto. Qed.

  Lemma one_ext_trans : transitive one_ext.
  Proof. 
    red; ins; unfold one_ext in *; desf; desf; 
      intuition eauto using clos_trans_in_rt, t_trans, rt_trans.
  Qed.
 
  Lemma one_ext_irr : acyclic rel -> irreflexive one_ext.
  Proof.
    red; ins; unfold one_ext in *; desf; eauto using clos_trans_in_rt.
  Qed.

  Lemma one_ext_total_elem : 
    forall x, x <> elem -> one_ext elem x \/ one_ext x elem.
  Proof.
    unfold one_ext; ins; rewrite !clos_refl_transE; tauto.
  Qed.

End one_extension.

(******************************************************************************)
(** Extend an order to make it total on a list of elements. *)

Fixpoint tot_ext X (dom : list X) (rel : relation X) : relation X :=
  match dom with 
    | nil => clos_trans rel
    | x::l => one_ext x (tot_ext l rel) 
  end.

Lemma tot_ext_extends : 
  forall X dom (rel : relation X) x y, rel x y -> tot_ext dom rel x y. 
Proof. 
  induction dom; ins; eauto using t_step, one_ext_extends.
Qed.

Lemma tot_ext_trans X dom (rel : relation X) :  transitive (tot_ext dom rel).
Proof. 
  induction dom; ins; vauto; apply one_ext_trans. 
Qed.

Lemma tot_ext_irr : 
  forall X (dom : list X) rel, acyclic rel -> irreflexive (tot_ext dom rel).
Proof.
  induction dom; ins.
  apply one_ext_irr, trans_irr_acyclic; eauto using tot_ext_trans.
Qed.

Lemma tot_ext_total : 
  forall X (dom : list X) rel, is_total (fun x => In x dom) (tot_ext dom rel).
Proof.
  induction dom; red; ins; desf.
  eapply one_ext_total_elem in NEQ; desf; eauto.
  eapply not_eq_sym, one_ext_total_elem in NEQ; desf; eauto.
  eapply IHdom in NEQ; desf; eauto using one_ext_extends.
Qed.

Lemma tot_ext_inv :
  forall X dom rel (x y : X),
    acyclic rel -> tot_ext dom rel x y -> ~ rel y x.
Proof.
  red; ins; eapply tot_ext_irr, tot_ext_trans, tot_ext_extends; eauto.
Qed.

Lemma tot_ext_extends_dom 
  X dom dom' (rel : relation X) x y :  
    tot_ext dom rel x y ->
    tot_ext (dom' ++ dom) rel x y.
Proof.
  induction dom'; ins; eauto using one_ext_extends.
Qed.

(******************************************************************************)
(** Extend an order on [nat] to make it total. *)

Definition tot_ext_nat rel (x y: nat) := 
  exists k, tot_ext (rev (List.seq 0 k)) rel x y.

Lemma tot_ext_nat_extends (rel : relation nat) x y : 
  rel x y -> tot_ext_nat rel x y. 
Proof.
  exists 0; eauto using tot_ext_extends.
Qed.

Lemma tot_ext_nat_trans rel :  transitive (tot_ext_nat rel).
Proof. 
  unfold tot_ext_nat; red; ins; desf.
  destruct (le_lt_dec k k0) as [LE|LE]; [|apply Nat.lt_le_incl in LE];
    [exists k0|exists k]; eapply tot_ext_trans; eauto;
    rewrite (list_seq_split _ LE), rev_app_distr; eauto using tot_ext_extends_dom.
Qed.

Lemma tot_ext_nat_irr : 
  forall rel, acyclic rel -> irreflexive (tot_ext_nat rel).
Proof.
  red; unfold tot_ext_nat; ins; desf; eapply tot_ext_irr; eauto.
Qed.

Lemma tot_ext_nat_total : 
  forall rel, is_total (fun _ => true) (tot_ext_nat rel).
Proof.
  unfold tot_ext_nat; red; ins.
  eapply tot_ext_total with (rel:=rel) (dom := rev (List.seq 0 (S (a + b)))) in NEQ;
    desf; eauto; rewrite <- in_rev, in_seq; omega.
Qed.

Lemma tot_ext_nat_inv :
  forall rel x y,
    acyclic rel -> tot_ext_nat rel x y -> ~ rel y x.
Proof.
  red; ins; eapply tot_ext_nat_irr, tot_ext_nat_trans, tot_ext_nat_extends; eauto.
Qed.

(******************************************************************************)
(** Successor-preserving linear extension *)

Definition Successor A (R S: relation A) :=
  << FUN: functional S >> /\
  << INJ: functional S^{-1} >> /\
  << SUC: S^{-1} ;; R ⊆ R^? >> /\
  << INC: S ⊆ R >>.

Lemma succ_helper X (R S: relation X) (SUC: S^{-1} ;; R ⊆ R^?):
  S^{-1}^* ;; (R \ S^+) ⊆ (R \ S^+).
Proof.
eapply rt_ind_left with (P:= fun __ => __ ;; (R \ S^+)); relsf.
intros k IH.
rewrite !seqA, IH; relsf.
unfold seq, transp, minus_rel, clos_refl, inclusion in *.
ins; desf; splits.
assert (x = y \/ R x y).
  by eauto.
desf.
by exfalso; apply H1; econs.
by intro; apply H1; eapply t_trans; try edone; econs.
Qed.

Definition tot_ext_suc X (dom : list X) (R S : relation X) : relation X := 
  S^+ ∪ S^* ;; <| max_elt S |> ;; tot_ext dom R ;; <| max_elt S |> ;; S^{-1}^*.

Lemma functional_path A (S: relation A) (FUN: functional S):
  S^{-1}^*;; S^* ⊆ S^* ∪ S^{-1}^*.
Proof.
(*   pattern_lhs (S^{-1}). *)
  eapply rt_ind_left with (P:= fun __ => __ ;; S^*); relsf.
  intros k IH.
  rewrite !seqA, IH; relsf.
  apply inclusion_union_l.
  rewrite rt_begin at 1; relsf.
  apply inclusion_union_l; vauto.
  by rewrite functional_alt in FUN; sin_rewrite FUN; relsf.
  rewrite rt_begin at 2; relsf.
Qed.

Lemma functional_path_transp A (S: relation A) (FUN: functional S^{-1}):
  S^*;; S^{-1}^* ⊆ S^* ∪ (S^{-1})^*.
Proof.
rewrite functional_path with (S:=S^{-1}); [rels|done].
Qed.

Lemma last_exists A dom (S: relation A) (ACYC: acyclic S)
  a (DOM: forall c, S^* a c -> In c dom):
  exists b, S^* a b /\ max_elt S b.
Proof.
revert a DOM.
induction dom using (well_founded_ind (well_founded_ltof _ (@length _))).
ins; destruct (classic (exists a1, S a a1)); cycle 1.
  by exists a; eexists; splits; [vauto| red; eauto].
assert (INa: In a dom).
  by apply DOM; vauto.
desc; apply in_split in INa; desf.
assert(exists b, S ^* a1 b /\ max_elt S b).
  { eapply (H (l1 ++ l2)).
    * unfold ltof; rewrite !app_length; simpl; omega.
    * ins.
      assert(INc: In c (l1 ++ a :: l2)).
        by eapply DOM; eapply rt_trans; vauto.
      rewrite in_app_iff in *; simpls; desf; eauto.
      exfalso; eapply ACYC; eapply t_step_rt; eauto.
  }
unfold seq in *; desc; exists b; splits; try done.
apply rt_begin; right; eexists; eauto.
Qed.

Lemma last_functional A (S: relation A) (FUN: functional S): 
  functional (S^* ;; <| max_elt S |>).
Proof.
  apply functional_alt.
  rewrite transp_seq; relsf.
  rewrite !seqA, transp_rt. 
  sin_rewrite functional_path; [relsf | done].
  seq_rewrite seq_eqv_max_rt; rels.
  seq_rewrite transp_seq_eqv_max_rt; rels.
  basic_solver.
Qed.

Lemma dom_helper X dom (S: relation X)
  (IN: S ⊆ <| fun x => In x dom |> ;; S ;; <| fun x => In x dom |>)
  a (INa: In a dom): forall b, S ^* a b -> In b dom.
Proof.
  ins; apply clos_refl_transE in H; desf.
  apply t_rt_step in H; desc.
  apply IN in H0; revert H0; basic_solver.
Qed.

Lemma last_exists_rewrite X dom (S: relation X) 
(ACYC: acyclic S)
(IN: S ⊆ <| fun x => In x dom |> ;; S ;; <| fun x => In x dom |>):
<| fun _ => True |> ⊆ S^* ;; <| max_elt S |> ;; S^{-1}^*.
Proof.
unfold inclusion, eqv_rel, seq; ins; desf.
destruct (classic (In y dom)) as [INy|NINy]; cycle 1.
- exists y; splits; vauto.
  exists y; splits; vauto.
  red; ins; apply IN in REL; revert REL; basic_solver.
- generalize (last_exists dom ACYC (dom_helper dom IN INy)); ins; desc.
  exists b; splits; eauto.
  exists b; splits; eauto.
  apply transp_rt with (r:=S); vauto.
Qed.

Lemma tot_ext_suc_trans X dom (R S: relation X) (SUC: Successor R S) :  
  transitive (tot_ext_suc dom R S).
Proof.
unfold tot_ext_suc.
apply transitiveI; relsf.
repeat apply inclusion_union_l.
- by rewrite ct_ct; rels.
- rewrite inclusion_t_rt at 1.
  rewrite !seqA, functional_path; [relsf | apply SUC].
  rewrite seq_eqv_max_rt.
  basic_solver 16.
- basic_solver 16.
- rewrite !seqA.
  sin_rewrite functional_path; [relsf | apply SUC].
  seq_rewrite seq_eqv_max_rt; relsf.
  seq_rewrite transp_seq_eqv_max_rt; relsf.
  arewrite_id (<| max_elt S |>) at 2; relsf.
  sin_rewrite rewrite_trans; [rels| apply tot_ext_trans].
Qed.


Lemma tot_ext_suc_irr X dom (R S: relation X) (SUC: Successor R S) 
  (ACYC: acyclic R): irreflexive (tot_ext_suc dom R S).
Proof.
red in SUC; desc.
unfold tot_ext_suc; ins.
rewrite irreflexive_union; splits.
by rewrite INC.
rewrite irreflexive_seqC, !seqA, functional_path; [relsf | done].
rewrite irreflexive_union; splits.
- rewrite seq_eqv_max_rt.
  generalize (tot_ext_irr dom ACYC); basic_solver.
- rewrite irreflexive_seqC, !seqA.
  rewrite transp_seq_eqv_max_rt.
  generalize (tot_ext_irr dom ACYC); basic_solver.
Qed.

Lemma tot_ext_suc_total X dom (R S: relation X) 
  (ACYC: acyclic R) (SUC: Successor R S)
  (IN: S ⊆ <| fun x => In x dom |> ;; S ;; <| fun x => In x dom |>):
 is_total (fun x => In x dom) (tot_ext_suc dom R S).
Proof.
ins; red; ins.
assert (ACYC': acyclic S).
  by cdes SUC; rewrite INC; done.
generalize (last_exists dom ACYC' (dom_helper dom IN IWa)); ins; desc.
generalize (last_exists dom ACYC' (dom_helper dom IN IWb)); ins; desc.
destruct (classic (b0=b1)) as [EQ1|NEQ1]; subst.
- assert (XX: (S^* ∪ S^{-1}^*) a b).
    apply functional_path_transp; [apply SUC |].
    exists b1; splits.
    by generalize H; basic_solver.
    by apply transp_rt with (r:=S); generalize H0; basic_solver.
  unfold union in XX; desf; apply clos_refl_transE in XX; desf.
  by left; unfold tot_ext_suc; basic_solver 2.
  by right; unfold tot_ext_suc; apply transp_ct in XX; basic_solver 2.
- assert (tot_ext dom R b0 b1 \/ tot_ext dom R b1 b0); desf.
  * generalize (tot_ext_total dom R); intro TOT; eapply TOT; try done.
    + eby eapply dom_helper with (a:=a).
    + eby eapply dom_helper with (a:=b).
  * left; red; right.
    unfold seq in H, H0; desc.
    do 4 (eexists; splits; eauto).
    by apply transp_eqv_rel; eauto.
    by apply transp_rt with (r:=S); generalize H0; basic_solver 2.
  * right; red; right.
    unfold seq in H, H0; desc.
    do 4 (eexists; splits; eauto).
    by apply transp_eqv_rel; eauto.
    by apply transp_rt with (r:=S); generalize H0; basic_solver 2.
Qed.

Lemma tot_ext_suc_extends X dom (R S: relation X) 
  (ACYC: acyclic R) (SUC: Successor R S) 
  (IN: S ⊆ <| fun x => In x dom |> ;; S ;; <| fun x => In x dom |>) :
  R ⊆ tot_ext_suc dom R S.
Proof.
arewrite (R ⊆ (R \ S^+) ∪ S^+).
  by apply inclusion_union_minus.
arewrite (R \ S ^+ ⊆ <| fun _ => True |> ;; (R \ S ^+) ;; <| fun _ => True |>).
  basic_solver.
rewrite !last_exists_rewrite with (S:=S); [|cdes SUC; rewrite INC; done| edone].
rewrite !seqA.
sin_rewrite succ_helper; [|by apply SUC].
rewrite inclusion_minus_rel.
cdes SUC; rewrite INC at 3; rels.
unfold tot_ext_suc.
rewrite inclusion_t_ind with (r' := tot_ext dom R); 
  [auto with rel | red; eapply tot_ext_extends | apply tot_ext_trans].
Qed.

Lemma tot_ext_suc_suc X dom (R S: relation X) (SUC: Successor R S) : 
  Successor (tot_ext_suc dom R S) S.
Proof.
  unfold Successor, tot_ext_suc in *; ins; desf; splits; auto with rel.
  relsf.
  apply inclusion_union_l; ins.
  - rewrite ct_begin at 1.
    rewrite functional_alt in FUN; sin_rewrite FUN; basic_solver.
  - rewrite rt_begin at 1; relsf.
    apply inclusion_union_l; ins.
    * arewrite (S^{-1} ⊆ (S^{-1})^*) at 1.
      seq_rewrite transp_seq_eqv_max_rt; rels; basic_solver 20.
    * rewrite !seqA.
      rewrite functional_alt in FUN; sin_rewrite FUN; rels.
Qed.

(******************************************************************************)
(** Add support for rewriting *)

Add Parametric Morphism X : (@one_ext X) with signature 
  eq ==> same_relation ==> same_relation as one_ext_more.
Proof.
  unfold one_ext, same_relation, inclusion; intuition; 
  eauto 8 using clos_trans_mon, clos_refl_trans_mon. 
Qed.

Add Parametric Morphism X : (@tot_ext X) with signature 
  eq ==> same_relation ==> same_relation as tot_ext_more.
Proof.
  induction y; ins; eauto using clos_trans_more, one_ext_more. 
Qed.

Add Parametric Morphism : tot_ext_nat with signature 
  same_relation ==> same_relation as tot_ext_nat_more.
Proof.
  unfold tot_ext_nat; split; red; ins; desf; exists k;
  eapply tot_ext_more; try eassumption; symmetry; eauto.
Qed.

