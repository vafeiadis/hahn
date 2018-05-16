(******************************************************************************)
(** * Well-founded and finitely supported relations *)
(******************************************************************************)

Require Import HahnBase HahnList HahnSets HahnRelationsBasic HahnEquational HahnRewrite.
Require Import Wf_nat Omega.

Set Implicit Arguments.

Ltac clarify_not :=
  repeat (match goal with 
  | H : ~ False |- _ => clear H
  | H : ~ _ |- _ => apply imply_to_and in H; desc
  | H : ~ _ |- _ => apply not_and_or in H; des
  | H : ~ _ |- _ => apply not_all_ex_not in H; desc
  end; clarify).

Tactic Notation "tertium_non_datur" constr(P) "as" simple_intropattern(pattern) :=
  destruct (classic P) as pattern; clarify_not.

Section well_founded. 

  Variable A : Type.
  Implicit Types r : relation A. 

  Lemma wf_impl_no_inf_seq r (WF: well_founded r) x :
    ~ exists a, a 0 = x /\ forall n, r (a (S n)) (a n).
  Proof.
    specialize (WF x); induction WF.
    intro CONTRA; desf.
    specialize (CONTRA0 0)  as C.
    apply H0 in C; destruct C.
    exists (fun n => a (S n)); ins.
  Qed.

  Lemma wf_impl_min_elt r (WF: well_founded r) B (NONEMPTY: ~ B ≡₁ ∅₁) :
    exists b, B b /\ forall b', B b' -> ~ r b' b.
  Proof.
    apply set_nonemptyE in NONEMPTY; desc.
    apply NNPP; intro C.
    induction x using (well_founded_ind WF).
    destruct C; eexists; split; try edone; red; ins; eauto.
  Qed.

  Lemma wf_mon r1 r2 (INCL: r1 ⊆ r2) (WF: well_founded r2) : well_founded r1.
  Proof.
    unfold well_founded in *; ins;
    induction (WF a); econstructor; eauto.
  Qed.

  Lemma wf_imm_succ r (WF: well_founded r) a b (REL: r a b) :
    exists c, immediate r a c.
  Proof.
    revert a REL; induction b using (well_founded_ind WF); ins.
    tertium_non_datur (immediate r a b) as [?|NIM]; eauto.
  Qed.

End well_founded.

Section finite_support. 

  Variable A : Type.
  Implicit Types r : relation A. 

  (** A relation is finitely supported iff every element has a finite number of 
      predecessors. *)
  Definition fsupp r :=
    forall y, exists findom, forall x (REL: r x y), In x findom.
    
  Theorem fsupp_well_founded r (FS: fsupp r) 
          (IRR: irreflexive r) (TRANS: transitive r) : 
    well_founded r.
  Proof.
    intros a; specialize (FS a); desf; revert a FS.
    induction findom 
      using (well_founded_induction (well_founded_ltof _ (@length _))).
    unfold ltof in *.
    constructor; intros y Rya.
    assert (IN := FS _ Rya).
    apply In_split in IN; desf.
    eapply H with (y0 := l1 ++ l2); ins.
      by rewrite !app_length; simpl; omega.
    assert (Rxa: r x a) by eauto.
    generalize (FS _ Rxa); rewrite !in_app_iff; ins; desf; eauto.
    exfalso; eauto.
  Qed.
   
  Lemma fsupp_imm_t r (FS: fsupp r) 
          (IRR: irreflexive r) (TRANS: transitive r) : 
    r ≡ (immediate r)⁺.
  Proof.
    split; [|by eauto with rel].
    red; ins.
    specialize (FS y); desf.
    assert (M: forall n, r x n -> r n y -> In n findom) by eauto.
    clear FS; revert x y H M.
    induction findom 
      using (well_founded_induction (well_founded_ltof _ (@length _))).
    unfold ltof in *.
    ins.
    tertium_non_datur (immediate r x y) as [|NIMM]; vauto.
    assert (N := M _ NIMM NIMM0); apply In_split in N; desf.
    apply t_trans with (y := n); eapply H with (y := l1 ++ l2); ins.
    1,3: by rewrite !app_length; simpl; omega.
    - apply M in H1; eauto; rewrite !in_app_iff in *; ins; desf; eauto.
      exfalso; eauto.
    - apply M in H2; eauto; rewrite !in_app_iff in *; ins; desf; eauto.
      exfalso; eauto.
  Qed.
   
  Lemma fsupp_mon r r' (SUBS: r ⊆ r') (FS: fsupp r') : fsupp r.
  Proof.
    unfold fsupp in *; ins; specialize (FS y); des; eauto.
  Qed.

  Lemma fsupp_union r1 r2 : fsupp (r1 ∪ r2) <-> fsupp r1 /\ fsupp r2.
  Proof.
    unfold fsupp, union in *; intuition; 
      repeat match goal with [ H : _, y : A |- _ ] => specialize (H y) end; 
      desf; first [exists (findom ++ findom0) | exists findom];
      ins; desf; eauto using in_or_app.
  Qed.

  Lemma fsupp_unionI r1 r2 (FS1: fsupp r1) (FS2: fsupp r2) : fsupp (r1 ∪ r2). 
  Proof.
    by apply fsupp_union.
  Qed.

  Lemma fsupp_list r (FS: fsupp r) l : 
    exists findom, forall x y (REL: r x y) (IN: In y l), In x findom.
  Proof.
    induction l; ins; desf.
      by exists nil; ins.
    specialize (FS a); desf.
    exists (findom ++ findom0); ins; desf; eauto using in_or_app.
  Qed.

  Lemma fsupp_seqI r1 r2 (FS1: fsupp r1) (FS2: fsupp r2) : fsupp (r1 ⨾ r2). 
  Proof.
    unfold fsupp, seq; desf; ins; desf. 
    specialize (FS2 y); desf.
    apply fsupp_list with (l:=findom) in FS1; desf.
    exists findom0; ins; desf; eauto.
  Qed.

  Lemma fsupp_seq_eqv_l r d (FS: fsupp r) : fsupp (⦗d⦘ ⨾ r). 
  Proof.
    unfold fsupp, seq, eqv_rel; desf; ins; desf. 
    specialize (FS y); desf; exists findom; ins; desf; eauto.
  Qed.

  Lemma fsupp_seq_eqv_r r d (FS: fsupp r) : fsupp (r ⨾ ⦗d⦘). 
  Proof.
    unfold fsupp, seq, eqv_rel; desf; ins; desf. 
    specialize (FS y); desf; exists findom; ins; desf; eauto.
  Qed.

End finite_support.

Require Import Setoid Morphisms.

Add Parametric Morphism A : (@fsupp A) with signature
  inclusion --> Coq.Program.Basics.impl as fsupp_mori.
Proof.
  red; ins; eapply fsupp_mon; eauto.
Qed.

Add Parametric Morphism A : (@fsupp A) with signature
  same_relation ==> iff as fsupp_more.
Proof.
  unfold same_relation; split; ins; desf; eauto using fsupp_mon.
Qed.

Hint Resolve fsupp_unionI fsupp_seqI fsupp_seq_eqv_l fsupp_seq_eqv_r : rel. 

