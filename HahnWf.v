(******************************************************************************)
(** * Well-founded and finitely supported relations *)
(******************************************************************************)

Require Import Setoid Morphisms Wf_nat Omega.
Require Import HahnBase HahnList HahnSets HahnRelationsBasic HahnEquational HahnRewrite.

Set Implicit Arguments.

(** A relation is finitely supported iff every element has a finite number of 
    predecessors. *)
Definition fsupp A (r: relation A) :=
  forall y, exists findom, forall x (REL: r x y), In x findom.

Hint Unfold fsupp ltof : unfolderDb.

Add Parametric Morphism A : (@fsupp A) with signature
  inclusion --> Coq.Program.Basics.impl as fsupp_mori.
Proof.
  unfolder; ins; desf; specialize (H0 y0); desf; eauto.
Qed.

Add Parametric Morphism A : (@fsupp A) with signature
  same_relation ==> iff as fsupp_more.
Proof.
  unfold same_relation; split; ins; desf; eapply fsupp_mori; eauto.
Qed.


(** Properties of well-founded relations. *)

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

  Lemma wf_impl_min_elt r (WF: well_founded r) B (NONEMPTY: ~ B ≡₁ ∅) :
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

  Lemma wf_restr r (WF: well_founded r) cond : well_founded (restr_rel cond r).
  Proof.
    red; ins; induction a using (well_founded_induction WF).
    constructor; ins; unfolder in H0; desf; eauto.
  Qed.

End well_founded.

Hint Resolve wf_restr : hahn.

(** Properties of finitely supported relations. *)

Section finite_support. 

  Variable A : Type.
  Implicit Types r : relation A. 
    
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
    split; [|by eauto with hahn].
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
    unfolder in *; ins; specialize (FS y); des; eauto.
  Qed.

  Lemma fsupp_empty : fsupp (A:=A) ∅₂.
  Proof.
    exists nil; ins. 
  Qed.

  Lemma fsupp_eqv (d : A -> Prop) : fsupp ⦗d⦘.
  Proof.
    unfolder; ins; exists (y :: nil); ins; desf; eauto. 
  Qed.

  Lemma fsupp_cross (s s': A -> Prop) (F: set_finite s) : fsupp (s × s').
  Proof.
    unfolder in *; ins; desf; eexists; ins; desf; eauto.
  Qed.

  Lemma fsupp_union r1 r2 : fsupp (r1 ∪ r2) <-> fsupp r1 /\ fsupp r2.
  Proof.
    unfolder in *; intuition; 
      repeat match goal with [ H : _, y : A |- _ ] => specialize (H y) end; 
      desf; first [exists (findom ++ findom0) | exists findom];
      ins; desf; eauto using in_or_app.
  Qed.

  Lemma fsupp_unionI r1 r2 (FS1: fsupp r1) (FS2: fsupp r2) : fsupp (r1 ∪ r2). 
  Proof.
    by apply fsupp_union.
  Qed.

  Lemma fsupp_bunion B s (rr : B -> relation A) 
        (FIN: set_finite s) (FS: forall x (IN: s x), fsupp (rr x)) :
    fsupp (bunion s rr).
  Proof.
    unfolder in *; desf; ins.
    revert s FIN FS; induction findom; ins.
      by exists nil; ins; desf; eauto.
    specialize (IHfindom (fun x => s x /\ x <> a)); ins.
    specialize_full IHfindom; ins; desf; eauto.
    by apply FIN in IN; desf; eauto.
    tertium_non_datur (s a) as [X|X]. 
      eapply FS in X; desf.
      exists (findom1 ++ findom0); ins; desf. 
      tertium_non_datur (a = a0); desf; eauto 8 using in_or_app.
    exists findom0; ins; desf; apply IHfindom; eexists; splits; eauto; congruence.
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

  Lemma fsupp_ct_rt r : fsupp r⁺ -> fsupp r＊. 
  Proof.
    rewrite rtE, fsupp_union; eauto using fsupp_eqv.
  Qed.

  Lemma fsupp_restr r (FS: fsupp r) cond : fsupp (restr_rel cond r).
  Proof.
    firstorder.
  Qed.

  Lemma functional_inv_fsupp r (F: functional r⁻¹) : fsupp r.
  Proof.
    unfolder; ins.
    tertium_non_datur (exists x, r x y); ins; desf.
    - exists (x :: nil); ins; eauto.
    - exists nil; ins; eauto. 
  Qed.

End finite_support.

Hint Resolve fsupp_empty fsupp_eqv fsupp_cross : hahn.
Hint Resolve fsupp_unionI fsupp_seqI fsupp_ct_rt fsupp_restr : hahn.
