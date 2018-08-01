(******************************************************************************)
(** * Extension of a partial order to a total order *)
(******************************************************************************)

Require Import NPeano Omega Setoid.
Require Import HahnBase HahnList HahnRelationsBasic HahnEquational HahnRewrite.
Require Import HahnSets HahnMaxElt.

Set Implicit Arguments.

(******************************************************************************)
(** Extend an order to make it total on one element. *)

Section one_extension.

  Variable A : Type.
  Variable elem : A.
  Variable r : relation A.

  Definition one_ext : relation A :=
    fun x y =>
      r⁺ x y
      \/ r＊ x elem /\ ~ r＊ y elem.

  Lemma one_ext_extends : r ⊆ one_ext.
  Proof. vauto. Qed.

  Lemma one_ext_trans : transitive one_ext.
  Proof.
    red; ins; unfold one_ext in *; desf; desf;
      intuition eauto using clos_trans_in_rt, t_trans, rt_trans.
  Qed.

  Lemma one_ext_irr : acyclic r -> irreflexive one_ext.
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

Fixpoint tot_ext A (dom : list A) (r : relation A) : relation A :=
  match dom with
    | nil => r⁺
    | x::l => one_ext x (tot_ext l r)
  end.

Lemma tot_ext_extends A dom (r : relation A) : r ⊆ tot_ext dom r.
Proof.
  induction dom; ins; eauto using one_ext_extends with hahn.
Qed.

Lemma tot_ext_trans A dom (r : relation A) :  transitive (tot_ext dom r).
Proof.
  induction dom; ins; vauto; apply one_ext_trans.
Qed.

Lemma tot_ext_extends2 A dom (r : relation A) : r⁺ ⊆ tot_ext dom r.
Proof.
  eauto using tot_ext_extends, tot_ext_trans with hahn.
Qed.

Lemma tot_ext_irr A (dom : list A) r :
  acyclic r -> irreflexive (tot_ext dom r).
Proof.
  induction dom; ins.
  apply one_ext_irr, trans_irr_acyclic; eauto using tot_ext_trans.
Qed.

Lemma tot_ext_total A (dom : list A) r :
  is_total (fun x => In x dom) (tot_ext dom r).
Proof.
  induction dom; red; ins; desf.
  eapply one_ext_total_elem in NEQ; desf; eauto.
  eapply not_eq_sym, one_ext_total_elem in NEQ; desf; eauto.
  eapply IHdom in NEQ; desf; eapply one_ext_extends in NEQ; eauto.
Qed.

Lemma tot_ext_inv A dom r (x y : A) :
    acyclic r -> tot_ext dom r x y -> ~ r y x.
Proof.
  red; ins; eapply tot_ext_irr, tot_ext_trans, tot_ext_extends; eauto.
Qed.

Lemma tot_ext_extends_dom A dom dom' (r : relation A) : 
  tot_ext dom r ⊆ tot_ext (dom' ++ dom) r.
Proof.
  induction dom'; ins; eauto using one_ext_extends with hahn.
Qed.

(******************************************************************************)
(** Extend an order on [nat] to make it total. *)

Definition tot_ext_nat r x y := exists k, tot_ext (rev (List.seq 0 k)) r x y.

Lemma tot_ext_nat_extends r : r ⊆ tot_ext_nat r.
Proof.
  exists 0; vauto. 
Qed.

Lemma tot_ext_nat_trans r : transitive (tot_ext_nat r).
Proof.
  unfold tot_ext_nat; red; ins; desf;
  destruct (le_lt_dec k k0) as [LE|LE]; [|apply Nat.lt_le_incl in LE];
    [exists k0|exists k]; eapply tot_ext_trans; eauto;
    rewrite (seq_split _ LE), rev_app_distr; apply tot_ext_extends_dom; eauto.
Qed.

Lemma tot_ext_nat_extends2 r : r⁺ ⊆ tot_ext_nat r.
Proof.
  eauto using tot_ext_nat_extends, tot_ext_nat_trans with hahn.
Qed.

Lemma tot_ext_nat_irr r : acyclic r -> irreflexive (tot_ext_nat r).
Proof.
  red; unfold tot_ext_nat; ins; desf; eapply tot_ext_irr; eauto.
Qed.

Lemma tot_ext_nat_total r : is_total (fun _ => True) (tot_ext_nat r).
Proof.
  unfold tot_ext_nat; red; ins.
  eapply tot_ext_total with (r:=r) (dom := rev (List.seq 0 (S (a + b)))) in NEQ;
    desf; eauto; rewrite <- in_rev, in_seq; omega.
Qed.

Lemma tot_ext_nat_inv r x y :
    acyclic r -> tot_ext_nat r x y -> ~ r y x.
Proof.
  red; ins; eapply tot_ext_nat_irr, tot_ext_nat_trans, tot_ext_nat_extends; eauto.
Qed.

(******************************************************************************)
(** Successor-preserving linear extension *)

Definition Successor A (r s: relation A) :=
  << FUN: functional s >> /\
  << INJ: functional s⁻¹ >> /\
  << SUC: s⁻¹ ⨾ r ⊆ r^? >> /\
  << INC: s ⊆ r >>.

Lemma succ_helper A (r s: relation A) (SUC: s⁻¹ ⨾ r ⊆ r^?):
  s⁻¹＊ ⨾ (r \ s⁺) ⊆ r \ s⁺.
Proof.
  eapply rt_ind_left with (P:= fun __ => __ ⨾ (r \ s⁺)); relsf.
  intros k IH.
  rewrite !seqA, IH; relsf.
  unfold seq, transp, minus_rel, clos_refl, inclusion in *.
  ins; desf; splits.
    assert (x = y \/ r x y) by eauto. 
    by desf; destruct H1; vauto. 
  by intro; apply H1; vauto. 
Qed.

Definition tot_ext_suc A (dom : list A) (r s : relation A) : relation A := 
  s⁺ ∪ s＊ ⨾ ⦗max_elt s⦘ ⨾ tot_ext dom r ⨾ ⦗max_elt s⦘ ⨾ s⁻¹＊.

Lemma functional_path A (s: relation A) (FUN: functional s):
  (s⁻¹)＊ ⨾ s＊ ⊆ s＊ ∪ (s⁻¹)＊.
Proof.
  eapply rt_ind_left with (P:= fun __ => __ ⨾ s＊); relsf.
  intros k IH.
  rewrite !seqA, IH; relsf.
  apply inclusion_union_l.
  rewrite rt_begin at 1; relsf.
  apply inclusion_union_l; vauto.
  by rewrite functional_alt in FUN; sin_rewrite FUN; relsf.
  rewrite rt_begin at 2; relsf.
Qed.

Lemma functional_path_transp A (s: relation A) (FUN: functional s⁻¹):
  s＊⨾ s⁻¹＊ ⊆ s＊ ∪ (s⁻¹)＊.
Proof.
  rewrite functional_path with (s:=s⁻¹); [rels|done].
Qed.

Lemma last_exists A dom (s: relation A) (ACYC: acyclic s)
  a (DOM: forall c, s＊ a c -> In c dom):
  exists b, s＊ a b /\ max_elt s b.
Proof.
  revert a DOM.
  induction dom using (well_founded_ind (well_founded_ltof _ (@length _))).
  ins; destruct (classic (exists a1, s a a1)); cycle 1.
    by exists a; eexists; splits; [vauto| red; eauto].
  assert (INa: In a dom).
    by apply DOM; vauto.
  desc; apply in_split in INa; desf.
  assert(exists b, s ＊ a1 b /\ max_elt s b).
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

Lemma last_functional A (s: relation A) (FUN: functional s): 
  functional (s＊ ⨾ ⦗max_elt s⦘).
Proof.
  apply functional_alt.
  rewrite transp_seq; relsf.
  rewrite !seqA, transp_rt. 
  sin_rewrite functional_path; [relsf | done].
  seq_rewrite seq_eqv_max_rt; rels.
  seq_rewrite transp_seq_eqv_max_rt; rels.
  basic_solver.
Qed.

Lemma dom_helper A dom (s: relation A)
  (IN: s ⊆ ⦗fun x => In x dom⦘ ⨾ s ⨾ ⦗fun x => In x dom⦘)
  a (INa: In a dom) b (H: s ＊ a b) : In b dom.
Proof.
  ins; apply clos_refl_transE in H; desf.
  apply t_rt_step in H; desc.
  apply IN in H0; revert H0; basic_solver.
Qed.

Lemma last_exists_rewrite A dom (s: relation A) 
      (ACYC: acyclic s)
      (IN: s ⊆ ⦗fun x : A => In x dom⦘ ⨾ s ⨾ ⦗fun x : A => In x dom⦘):
  ⦗fun _ => True⦘ ⊆ s＊ ⨾ ⦗max_elt s⦘ ⨾ s⁻¹＊.
Proof.
unfold inclusion, eqv_rel, seq; ins; desf.
destruct (classic (In y dom)) as [INy|NINy]; cycle 1.
- exists y; splits; vauto.
  exists y; splits; vauto.
  red; ins; apply IN in REL; revert REL; basic_solver.
- generalize (last_exists dom ACYC (dom_helper dom IN INy)); ins; desc.
  exists b; splits; eauto.
  exists b; splits; eauto.
  apply transp_rt with (r:=s); vauto.
Qed.

Lemma tot_ext_suc_trans A dom (r s: relation A) (SUC: Successor r s) :  
  transitive (tot_ext_suc dom r s).
Proof.
unfold tot_ext_suc.
apply transitiveI; relsf.
repeat apply inclusion_union_l; eauto with hahn.
- by rewrite ct_ct; rels.
- rewrite inclusion_t_rt at 1.
  rewrite !seqA, functional_path; [relsf | apply SUC].
  rewrite seq_eqv_max_rt.
  basic_solver 16.
- rewrite !seqA.
  sin_rewrite functional_path; [relsf | apply SUC].
  seq_rewrite seq_eqv_max_rt; relsf.
  seq_rewrite transp_seq_eqv_max_rt; relsf.
  arewrite_id (⦗max_elt s⦘) at 2; relsf.
  sin_rewrite rewrite_trans; [rels| apply tot_ext_trans].
Qed.


Lemma tot_ext_suc_irr A dom (r s: relation A) (SUC: Successor r s) 
  (ACYC: acyclic r): irreflexive (tot_ext_suc dom r s).
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

Lemma tot_ext_suc_total A dom (r s: relation A) 
  (ACYC: acyclic r) (SUC: Successor r s)
  (IN: s ⊆ ⦗fun x => In x dom⦘ ⨾ s ⨾ ⦗fun x => In x dom⦘):
 is_total (fun x => In x dom) (tot_ext_suc dom r s).
Proof.
ins; red; ins.
assert (ACYC': acyclic s).
  by cdes SUC; rewrite INC; done.
generalize (last_exists dom ACYC' (dom_helper dom IN IWa)); ins; desc.
generalize (last_exists dom ACYC' (dom_helper dom IN IWb)); ins; desc.
destruct (classic (b0=b1)) as [EQ1|NEQ1]; subst.
- assert (XX: (s＊ ∪ s⁻¹＊) a b).
    apply functional_path_transp; [apply SUC |].
    exists b1; splits.
    by generalize H; basic_solver.
    by apply transp_rt with (r:=s); generalize H0; basic_solver.
  unfold union in XX; desf; apply clos_refl_transE in XX; desf.
  by left; unfold tot_ext_suc; basic_solver 2.
  by right; unfold tot_ext_suc; apply transp_ct in XX; basic_solver 2.
- assert (tot_ext dom r b0 b1 \/ tot_ext dom r b1 b0); desf.
  * generalize (tot_ext_total dom r); intro TOT; eapply TOT; try done.
    + eby eapply dom_helper with (a:=a).
    + eby eapply dom_helper with (a:=b).
  * left; red; right.
    unfold seq in H, H0; desc.
    do 4 (eexists; splits; eauto).
    by apply transp_eqv_rel; eauto.
    by apply transp_rt with (r:=s); generalize H0; basic_solver 2.
  * right; red; right.
    unfold seq in H, H0; desc.
    do 4 (eexists; splits; eauto).
    by apply transp_eqv_rel; eauto.
    by apply transp_rt with (r:=s); generalize H0; basic_solver 2.
Qed.

Lemma tot_ext_suc_extends A dom (r s: relation A) 
  (ACYC: acyclic r) (SUC: Successor r s) 
  (IN: s ⊆ ⦗fun x => In x dom⦘ ⨾ s ⨾ ⦗fun x => In x dom⦘) :
  r ⊆ tot_ext_suc dom r s.
Proof.
arewrite (r ⊆ (r \ s⁺) ∪ s⁺).
  by apply inclusion_union_minus.
arewrite (r \ s ⁺ ⊆ ⦗fun _ => True⦘ ⨾ (r \ s ⁺) ⨾ ⦗fun _ => True⦘).
  basic_solver.
rewrite !last_exists_rewrite with (s:=s); [|cdes SUC; rewrite INC; done| edone].
rewrite !seqA.
sin_rewrite succ_helper; [|by apply SUC].
rewrite inclusion_minus_rel.
cdes SUC; rewrite INC at 3; rels.
unfold tot_ext_suc.
rewrite inclusion_t_ind with (r' := tot_ext dom r); 
  [auto with hahn | red; eapply tot_ext_extends | apply tot_ext_trans].
Qed.

Lemma tot_ext_suc_suc A dom (r s: relation A) (SUC: Successor r s) : 
  Successor (tot_ext_suc dom r s) s.
Proof.
  unfold Successor, tot_ext_suc in *; ins; desf; splits; auto with hahn.
  relsf.
  apply inclusion_union_l; ins.
  - rewrite ct_begin at 1.
    rewrite functional_alt in FUN; sin_rewrite FUN; basic_solver.
  - rewrite rt_begin at 1; relsf.
    apply inclusion_union_l; ins.
    * arewrite (s⁻¹ ⊆ (s⁻¹)＊) at 1.
      seq_rewrite transp_seq_eqv_max_rt; rels; basic_solver 20.
    * rewrite !seqA.
      rewrite functional_alt in FUN; sin_rewrite FUN; rels.
Qed.

(******************************************************************************)
(** Add support for rewriting *)

Add Parametric Morphism A : (@one_ext A) with signature
  eq ==> same_relation ==> same_relation as one_ext_more.
Proof.
  unfold one_ext, same_relation, inclusion; intuition;
  eauto 8 using clos_trans_mon, clos_refl_trans_mon.
Qed.

Add Parametric Morphism A : (@tot_ext A) with signature
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

Add Parametric Morphism A : (@tot_ext_suc A) with signature
  eq ==> same_relation ==> same_relation ==> same_relation as tot_ext_suc_more.
Proof.
  by unfold tot_ext_suc; ins; rewrite H, H0. 
Qed.



