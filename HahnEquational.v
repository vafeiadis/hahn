(******************************************************************************)
(** * Equational properties of relations *)
(******************************************************************************)

Require Import Classical NPeano Omega Permutation List Setoid.
Require Import HahnBase HahnList HahnRelationsBasic.

Set Implicit Arguments.

(******************************************************************************)
(** Set up setoid rewriting *)
(******************************************************************************)

(** First, for inclusion. *)

Add Parametric Relation (X : Type) : (relation X) (@inclusion X) 
 reflexivity proved by (@inclusion_refl _)
 transitivity proved by (@inclusion_trans _)
 as inclusion_rel.

Add Parametric Morphism X : (@inclusion X) with signature 
  inclusion --> inclusion ++> Basics.impl as inclusion_mori.
Proof.
  unfold inclusion, Basics.impl; ins; eauto. 
Qed.

Add Parametric Morphism X : (@union X) with signature 
  inclusion ==> inclusion ==> inclusion as union_mori.
Proof.
  unfold inclusion, union; intuition; eauto. 
Qed.

Add Parametric Morphism X : (@inter_rel X) with signature 
  inclusion ==> inclusion ==> inclusion as inter_rel_mori.
Proof.
  unfold inclusion, inter_rel; intuition; eauto. 
Qed.

Add Parametric Morphism X : (@minus_rel X) with signature 
  inclusion ++> inclusion --> inclusion as minus_rel_mori.
Proof.
  unfold inclusion, minus_rel; intuition; eauto. 
Qed.

Add Parametric Morphism X : (@seq X) with signature 
  inclusion ==> inclusion ==> inclusion as seq_mori.
Proof.
  unfold inclusion, seq; intuition; desf; eauto. 
Qed.

Add Parametric Morphism X : (@irreflexive X) with signature 
  inclusion --> Basics.impl as irreflexive_mori.
Proof.
  unfold inclusion, irreflexive, Basics.impl; intuition; desf; eauto. 
Qed.

Add Parametric Morphism X : (@clos_trans X) with signature 
  inclusion ==> inclusion as clos_trans_mori.
Proof.
  unfold inclusion; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl_trans X) with signature 
  inclusion ==> inclusion as clos_refl_trans_mori.
Proof.
  unfold inclusion; eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl X) with signature 
  inclusion ==> inclusion as clos_refl_mori.
Proof.
  unfold inclusion, clos_refl; intuition; eauto.
Qed.

Add Parametric Morphism X P : (@restr_rel X P) with signature 
  inclusion ==> inclusion as restr_rel_mori.
Proof.
  unfold inclusion, restr_rel; intuition; eauto. 
Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature 
  eq ==> inclusion ==> inclusion as restr_eq_rel_mori.
Proof.
  unfold inclusion, restr_eq_rel; intuition; eauto. 
Qed.

Add Parametric Morphism X : (@acyclic X) with signature 
  inclusion --> Basics.impl as acyclic_mori.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity. 
Qed.

Add Parametric Morphism X : (@is_total X) with signature 
  eq ==> inclusion ==> Basics.impl as is_total_mori.
Proof.
  unfold inclusion, is_total, Basics.impl; ins; desf. 
  eapply H0 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism X : (@transp X) with signature
  inclusion ==> inclusion as transp_mori.
Proof.
  unfold inclusion, transp; eauto.
Qed.

(** Second, for equivalence. *)

Lemma same_relation_exp A (r r' : relation A) (EQ: r ≡ r') :
  forall x y, r x y <-> r' x y.
Proof. split; apply EQ. Qed.

Lemma same_relation_refl A : reflexive (@same_relation A).
Proof. split; ins. Qed.

Lemma same_relation_sym A : symmetric (@same_relation A).
Proof. unfold same_relation; split; ins; desf. Qed.

Lemma same_relation_trans A : transitive (@same_relation A).
Proof. unfold same_relation; split; ins; desf; red; eauto. Qed.

Add Parametric Relation (X : Type) : (relation X) (@same_relation X) 
 reflexivity proved by (@same_relation_refl X)
 symmetry proved by (@same_relation_sym X)
 transitivity proved by (@same_relation_trans X)
 as same_rel.

Add Parametric Morphism X : (@inclusion X) with signature 
  same_relation ==> same_relation ==> iff as inclusion_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@union X) with signature 
  same_relation ==> same_relation ==> same_relation as union_more.
Proof.
  unfold same_relation, union; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@inter_rel X) with signature 
  same_relation ==> same_relation ==> same_relation as inter_rel_more.
Proof.
  unfold same_relation, inter_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@minus_rel X) with signature 
  same_relation ==> same_relation ==> same_relation as minus_rel_more.
Proof.
  unfold same_relation, minus_rel; ins; desf; split; red; intuition. 
Qed.

Add Parametric Morphism X : (@seq X) with signature 
  same_relation ==> same_relation ==> same_relation as seq_more.
Proof.
  unfold same_relation, seq; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@eqv_dom_rel X) with signature 
  (@Permutation _) ==> same_relation as eqv_dom_rel_more.
Proof.
  by unfold same_relation, eqv_dom_rel; ins; desf; split; red; ins; desf; 
     rewrite H in *. 
Qed.

Add Parametric Morphism X P : (@restr_rel X P) with signature 
  same_relation ==> same_relation as restr_rel_more.
Proof.
  unfold same_relation, restr_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature 
  eq ==> same_relation ==> same_relation as restr_eq_rel_more.
Proof.
  unfold same_relation, restr_eq_rel; intuition; eauto using restr_eq_rel_mori. 
Qed.

Add Parametric Morphism X : (@clos_trans X) with signature 
  same_relation ==> same_relation as clos_trans_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl_trans X) with signature 
  same_relation ==> same_relation as clos_relf_trans_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; 
  eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl X) with signature 
  same_relation ==> same_relation as clos_relf_more.
Proof.
  unfold same_relation, clos_refl; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@irreflexive X) with signature 
  same_relation ==> iff as irreflexive_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@acyclic X) with signature 
  same_relation ==> iff as acyclic_more.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism X : (@transitive X) with signature 
  same_relation ==> iff as transitive_more.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@is_total X) with signature 
  eq ==> same_relation ==> iff as is_total_more.
Proof.
  unfold is_total, same_relation; split; ins; eapply H0 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism X : (@transp X) with signature
  same_relation ==> same_relation as transp_more.
Proof.
  unfold same_relation, transp; ins; desf; eauto; split; red; ins; desf; eauto.
Qed.



(******************************************************************************)
(** Basic properties of sequential composition and relational union *)
(******************************************************************************)

Section PropertiesSeqUnion.

  Variable A : Type.
  Implicit Type r : relation A.

  Lemma seqA r1 r2 r3 : (r1 ;; r2) ;; r3 ≡ r1 ;; (r2 ;; r3).
  Proof.
    unfold seq; split; red; ins; desf; eauto. 
  Qed.

  Lemma seq_false_l r : (fun _ _ => False) ;; r ≡ (fun _ _ => False).
  Proof.
    split; unfold seq, inclusion; ins; desf. 
  Qed.

  Lemma seq_false_r r : r ;; (fun _ _ => False) ≡ (fun _ _ => False).
  Proof.
    split; unfold seq, inclusion; ins; desf. 
  Qed.

  Lemma seq_id_l r :  <| fun _ => True |> ;; r ≡ r.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto.
  Qed.

  Lemma seq_id_r r : r ;; <| fun _ => True |> ≡ r.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto.
  Qed.

  Lemma unionA r1 r2 r3 : (r1 ∪ r2) ∪ r3 ≡ r1 ∪ (r2 ∪ r3).
  Proof.
    unfold seq, union; split; red; ins; desf; eauto. 
  Qed.

  Lemma unionC r1 r2 : r1 ∪ r2 ≡ r2 ∪ r1.
  Proof.
    unfold seq, union; split; red; ins; desf; eauto. 
  Qed.

  Lemma unionAC r r' r'' : r ∪ (r' ∪ r'') ≡ r' ∪ (r ∪ r'').
  Proof.
    rewrite <- !unionA, (unionC r r'); vauto.
  Qed.
  
  Lemma unionK r : r ∪ r ≡ r.
  Proof.
    split; eauto with rel.
  Qed.

  Lemma union_false_r r : r ∪ (fun _ _ => False) ≡ r.
  Proof.
    split; unfold union, inclusion; ins; desf; eauto.
  Qed.

  Lemma union_false_l r : (fun _ _ => False) ∪ r ≡ r.
  Proof.
    by rewrite unionC, union_false_r.
  Qed.

  Lemma seq_union_l r1 r2 r : (r1 ∪ r2) ;; r ≡ (r1 ;; r) ∪ (r2 ;; r).
  Proof.
    unfold seq, union; split; red; ins; desf; eauto. 
  Qed.

  Lemma seq_union_r r r1 r2 : r ;; (r1 ∪ r2) ≡ (r ;; r1) ∪ (r ;; r2). 
  Proof.
    unfold seq, union; split; red; ins; desf; eauto. 
  Qed.

  Lemma minus_union_l r1 r2 r : 
    minus_rel (r1 ∪ r2) r ≡ minus_rel r1 r ∪ minus_rel r2 r.
  Proof.
    unfold minus_rel, union; split; red; ins; desf; eauto. 
  Qed.

  Lemma minusK r : minus_rel r r ≡ (fun _ _ => False).
  Proof.
    unfold minus_rel; split; red; intuition. 
  Qed.

  Lemma seq_eqvK (dom : A -> Prop) : <| dom |>;; <| dom |> ≡ <| dom |>.
  Proof.
    unfold eqv_rel, seq; split; red; ins; desf; eauto.
  Qed.

End PropertiesSeqUnion.

Hint Rewrite seq_false_l seq_false_r union_false_l union_false_r unionK : rel.
Hint Rewrite seq_id_l seq_id_r seq_eqvK : rel.

Ltac rel_simpl :=
  repeat first [rewrite seq_false_l | rewrite seq_false_r | 
                rewrite union_false_l | rewrite union_false_r |
                rewrite seq_id_l | rewrite seq_id_r |
                rewrite minusK | rewrite minus_union_l |
                rewrite seq_union_l | rewrite seq_union_r];
    eauto 8 with rel.

Ltac hahn_rel := 
  rel_simpl; 
  try match goal with |- (_ <--> _) => split end;
  repeat apply inclusion_union_l; eauto 8 with rel.

Ltac hahn_frame_r := 
  rewrite <- ?seqA; apply inclusion_seq_mon; [|reflexivity]; rewrite ?seqA.

Ltac hahn_frame_l := 
  rewrite ?seqA; apply inclusion_seq_mon; [reflexivity|].


Ltac hahn_frame :=
  rewrite <- ?seqA; 
  repeat (
      match goal with 
      | |- inclusion _ (_ ;; clos_refl_trans _) => fail 1
      | |- inclusion _ (_ ;; clos_trans _) => fail 1
      | |- _ => apply inclusion_seq_mon; [|reflexivity] 
      end);
  rewrite ?seqA; 
  repeat (
      match goal with 
      | |- inclusion _ (clos_refl_trans _ ;; _) => fail 1
      | |- inclusion _ (clos_trans _ ;; _) => fail 1
      | |- _ => apply inclusion_seq_mon; [reflexivity|] 
      end);
  try solve [ apply inclusion_seq_l; try done; auto with rel
            | apply inclusion_seq_r; try done; auto with rel].



(******************************************************************************)
(** Basic properties of reflexive and transitive closures *)
(******************************************************************************)

Section PropertiesClos.

  Variable A : Type.
  Implicit Types r rel : relation A.

  Lemma rtE r : r ^* ≡ <| fun _ => True |> ∪ r ^+.
  Proof.
    unfold eqv_rel, union, same_relation, inclusion.
    split; ins; rewrite clos_refl_transE in *; tauto.
  Qed.

  Lemma crE r : r ^? ≡ <| fun _ => True |> ∪ r.
  Proof.
    unfold eqv_rel, union, same_relation, inclusion, clos_refl.
    split; ins; tauto.
  Qed.

  Lemma ct_begin r : r ^+ ≡ r ;; r ^*.
  Proof.
    unfold seq; split; red; ins; desf; rewrite t_step_rt in *; eauto.
  Qed.

  Lemma ct_end r : r ^+ ≡ r ^* ;; r.
  Proof.
    unfold seq; split; red; ins; desf; rewrite t_rt_step in *; eauto.
  Qed.

  Lemma rt_begin rel : 
    rel ^* ≡ <| fun _ => True |> ∪ rel ;; rel ^*.
  Proof.
    rewrite <- ct_begin, <- rtE; vauto. 
  Qed.

  Lemma rt_end rel : 
    rel ^* ≡ <| fun _ => True |> ∪ rel ^* ;; rel.
  Proof.
    rewrite <- ct_end, <- rtE; vauto. 
  Qed.

  Lemma rt_rt rel : rel ^* ;; rel ^* ≡ rel ^*.
  Proof.
    unfold seq; split; red; ins; desf; eauto using rt_trans, rt_refl. 
  Qed.

  Lemma rt_ct rel : rel ^* ;; rel ^+ ≡ rel ^+.
  Proof.
    unfold seq; split; red; ins; desf; eauto using rt_t_trans, rt_refl. 
  Qed.

  Lemma ct_rt rel : rel ^+ ;; rel ^* ≡ rel ^+.
  Proof.
    unfold seq; split; red; ins; desf; eauto using t_rt_trans, rt_refl. 
  Qed.

  Lemma ct_ct rel : rel ^+ ;; rel ^+ ⊆ rel ^+.
  Proof.
    unfold seq; red; ins; desf; eauto using t_trans.
  Qed.

  Lemma ct_of_ct rel: (rel ^+) ^+ ≡ rel ^+. 
  Proof.
    split; eauto with rel.
  Qed.

  Lemma rt_of_ct rel : (rel ^+) ^* ≡ rel ^*. 
  Proof.
    split; eauto using inclusion_rt_rt2 with rel.
  Qed.

  Lemma ct_of_trans r (T: transitive r) : r ^+ ≡ r.
  Proof.
    split; eauto with rel. 
  Qed.

  Lemma rt_of_trans r (T: transitive r) : r ^* ≡ r ^?.
  Proof.
    rewrite rtE, crE, ct_of_trans; vauto.
  Qed.

  Lemma cr_of_ct rel : (rel ^+) ^? ≡ rel ^*. 
  Proof.
    rewrite <- rt_of_trans, rt_of_ct; vauto.
  Qed.

  Lemma cr_union_l r r' : (r ∪ r') ^? ≡ r ^? ∪ r'.
  Proof.
    by rewrite !crE, unionA.
  Qed.

  Lemma cr_union_r r r' : (r ∪ r') ^? ≡ r ∪ r' ^?.
  Proof.
    by rewrite unionC, cr_union_l, unionC.
  Qed.

  Lemma seq_rtE_r r r' : r ;; r' ^* ≡ r ∪ (r ;; r') ;; r' ^*.
  Proof.
    rewrite rt_begin at 1; rel_simpl; rewrite seqA; hahn_rel.
  Qed.

  Lemma seq_rtE_l r r' : r' ^* ;; r ≡ r ∪ (r' ^* ;; r' ;; r).
  Proof.
    rewrite rt_end at 1; rel_simpl; rewrite seqA; hahn_rel.
  Qed.

  Lemma ct_seq_swap r r' :
    (r ;; r') ^+ ;; r ≡ r ;; (r' ;; r) ^+.
  Proof.
    split.
    { rewrite (ct_end (r' ;; r)); hahn_frame.
      apply inclusion_t_ind_left; hahn_frame. 
      rewrite <- seqA, <- ct_begin; hahn_rel. }
    rewrite (ct_begin (r ;; r')); hahn_frame.
    apply inclusion_t_ind_left; hahn_frame. 
    rewrite <- seqA, <- ct_begin; hahn_rel.
  Qed.

  Lemma rt_seq_swap r r' :
    (r ;; r') ^* ;; r ≡ r ;; (r' ;; r) ^*.
  Proof.
    by rewrite !rtE; rel_simpl; rewrite ct_seq_swap. 
  Qed.

  Lemma ct_rotl r r' :
    (r ;; r') ^+ ≡ r ;; (r' ;; r) ^* ;; r'.
  Proof.
    by rewrite rt_seq_swap, ct_begin, seqA.
  Qed.

  Lemma crt_double r : 
    r ^* ≡ r ^? ;; (r ;; r) ^*.
  Proof.
    split; [|by eauto 7 using inclusion_seq_trans, inclusion_rt_rt2 with rel].
    apply inclusion_rt_ind_left; eauto with rel.
    rewrite !crE; hahn_rel.
    rewrite <- seqA, <- ct_begin; hahn_rel.
  Qed.

End PropertiesClos.


(******************************************************************************)
(** Properties of [eqv_rel] *)
(******************************************************************************)

Lemma seq_eqv_r A (rel : relation A) dom : 
  rel ;; eqv_rel dom ≡ (fun x y => rel x y /\ dom y). 
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma seq_eqv_l A (rel : relation A) dom : 
  eqv_rel dom ;; rel ≡ (fun x y => dom x /\ rel x y). 
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_l A (rel : relation A) dom : 
  <| dom |>;; rel ⊆ rel.
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_r A (rel : relation A) dom : 
  rel ;; <| dom |> ⊆ rel.
Proof.
  unfold eqv_rel, seq, same_relation, inclusion; intuition; desf; eauto.
Qed.


(******************************************************************************)
(** Properties of restrictions *)
(******************************************************************************)

Lemma same_relation_restr X (f : X -> Prop) rel rel' :
   (forall x (CONDx: f x) y (CONDy: f y), rel x y <-> rel' x y) ->
   (restr_rel f rel ≡ restr_rel f rel').
Proof.
  unfold restr_rel; split; red; ins; desf; rewrite H in *; eauto.
Qed.

Lemma restr_union X (f : X -> Prop) rel rel' :
  restr_rel f (rel ∪ rel') ≡ restr_rel f rel ∪ restr_rel f rel'.
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
Qed.

Lemma union_restr X (f : X -> Prop) rel rel' :
  restr_rel f rel ∪ restr_rel f rel' ≡ restr_rel f (rel ∪ rel').
Proof.
  symmetry; apply restr_union.
Qed.

Lemma ct_restr X (f : X -> Prop) rel (UC: upward_closed rel f) :
  (restr_rel f rel) ^+ ≡ restr_rel f (rel ^+).
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
    split; [|by apply clos_trans_restrD in H].
    by eapply clos_trans_mon; eauto; unfold restr_rel; ins; desf.
  clear H0; apply clos_trans_tn1 in H.
  induction H; eauto 10 using clos_trans.
Qed.

Lemma restr_eq_union:
  forall (X : Type) (rel rel' : relation X) (B : Type) (f : X -> B),
  restr_eq_rel f (rel ∪ rel') ≡ 
  restr_eq_rel f rel ∪ restr_eq_rel f rel'.
Proof.
  unfold restr_eq_rel, union, same_relation, inclusion; intuition.
Qed.

Lemma restr_eq_elim : 
  forall X (rel : relation X) B (f: X -> B)
         (R: forall x y, rel x y -> f x = f y),
   restr_eq_rel f rel ≡ rel.
Proof.
  unfold restr_eq_rel; split; red; ins; intuition.
Qed.

Lemma restr_eq_seq_eqv_rel X (rel : relation X) (B : Type) (f : X -> B) dom :
  restr_eq_rel f (rel;; <| dom |>) ≡ restr_eq_rel f rel;; <| dom |>.
Proof.
  ins; rewrite !seq_eqv_r; unfold restr_eq_rel.
  split; red; ins; desf.
Qed.


(******************************************************************************)
(** Lemmas about [transp] *)
(******************************************************************************)

Lemma transp_union  X (r1 r2 : relation X) :
  transp (r1 ∪ r2) ≡ transp r1 ∪ transp r2.
Proof. 
  unfold transp, union; split; red; intuition.
Qed.

Lemma transp_seq  X (r1 r2 : relation X) :
  transp (r1 ;; r2) ≡ transp r2 ;; transp r1.
Proof. 
  unfold transp, seq; split; red; ins; desf; eauto. 
Qed.

Lemma transp_inter  X (r1 r2 : relation X) :
  transp (inter_rel r1 r2) ≡ inter_rel (transp r1) (transp r2).
Proof. 
  unfold transp, inter_rel; split; red; intuition.
Qed.

Lemma transp_minus  X (r1 r2 : relation X) :
  transp (minus_rel r1 r2) ≡ minus_rel (transp r1) (transp r2).
Proof. 
  unfold transp, minus_rel; split; red; intuition.
Qed.

Lemma transp_rt  X (r : relation X) :
  transp (r ^*) ≡ (transp r) ^*.
Proof. 
  unfold transp, seq; split; red; ins; induction H; vauto. 
Qed.

Lemma transp_ct  X (r : relation X) :
  transp (r ^+) ≡ (transp r) ^+.
Proof. 
  unfold transp, seq; split; red; ins; induction H; vauto. 
Qed.

Lemma transp_cr  X (r : relation X) :
  transp (clos_refl r) ≡ clos_refl (transp r).
Proof. 
  unfold transp, clos_refl; split; red; intuition. 
Qed.

Lemma transitive_transp X (r : relation X) : 
  transitive r -> transitive (transp r).
Proof.
  unfold transp, transitive; eauto.
Qed.

Lemma inclusion_transpE A (r r': relation A) :
  transp r ⊆ transp r' -> r ⊆ r'.
Proof. 
  by unfold transp, inclusion; intuition.
Qed.


(** Misc properties *)
(******************************************************************************)


Lemma acyclic_mon X (rel rel' : relation X) :
  acyclic rel -> rel' ⊆ rel -> acyclic rel'.
Proof.
  eby repeat red; ins; eapply H, clos_trans_mon.
Qed.

Lemma acyclic_seqC A (r r' : relation A) :
  acyclic (r ;; r') <-> acyclic (r' ;; r).
Proof.
  by unfold acyclic; rewrite ct_rotl, irreflexive_seqC, !seqA, <- ct_end.
Qed.


Lemma clos_trans_imm :
  forall X (R : relation X) (I: irreflexive R) 
         (T: transitive R) L (ND: NoDup L) a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    (immediate R) ^+ a b.
Proof.
  intros until 3; induction ND; ins; vauto.
  destruct (classic (R a x /\ R x b)) as [|N]; desf;
    [apply t_trans with x|]; eapply IHND; ins;
  forward (by eapply (D c); eauto) as K; desf; exfalso; eauto.
Qed.

Lemma immediate_clos_trans_elim A (r : relation A) a b : 
  immediate (r ^+) a b ->
  r a b /\ (forall c, r ^+ a c -> r ^+ c b -> False).
Proof.
  unfold immediate; ins; desf; split; ins.
  apply t_step_rt in H; desf.
  apply clos_refl_transE in H1; desf; exfalso; eauto using t_step.
Qed.

Lemma clos_trans_immediate1 A (r : relation A) (T: transitive r) a b :
  (immediate r) ^+ a b -> r a b.
Proof.
  unfold immediate; induction 1; desf; eauto.
Qed.

Lemma clos_trans_immediate2 A (r : relation A)
      (T: transitive r) (IRR: irreflexive r) dom
      (D: forall a b (R: r a b), In b dom) a b :
  r a b ->
  (immediate r) ^+ a b.
Proof.
  assert (D': forall c, r a c -> r c b -> In c dom).
    by ins; apply D in H; desf.
  clear D; revert a b D'.
  remember (length dom) as n; revert dom Heqn; induction n.
    by destruct dom; ins; vauto.
  ins; destruct (classic (exists c, r a c /\ r c b)); desf.
  2: by eapply t_step; split; ins; eauto.
  forward (by eapply D'; eauto) as X; apply in_split in X; desf.
  rewrite app_length in *; ins; rewrite <- plus_n_Sm, <- app_length in *; desf.
  apply t_trans with c; eapply IHn with (dom := l1 ++ l2); ins;
  forward (by eapply (D' c0); eauto);
  rewrite !in_app_iff; ins; desf; eauto; exfalso; eauto.
Qed.

Lemma clos_trans_imm2 :
  forall X (R : relation X) (I: irreflexive R) 
         (T: transitive R) L a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    (immediate R) ^+ a b.
Proof.
  ins; eapply clos_trans_imm with (L := undup L); ins;
  try rewrite in_undup_iff; eauto using nodup_undup.
Qed.


Lemma total_immediate_unique:
  forall X (rel: X -> X -> Prop) (P: X -> Prop)
         (Tot: is_total P rel)
         a b c (pa: P a) (pb: P b) (pc: P c)
         (iac: immediate rel a c)
         (ibc: immediate rel b c),
    a = b.
Proof.
  ins; destruct (classic (a = b)) as [|N]; eauto.
  exfalso; unfold immediate in *; desf.
  eapply Tot in N; eauto; desf; eauto.
Qed.

Lemma acyclic_case_split A (R : relation A) f :
  acyclic R <->
  acyclic (restr_rel f R) /\ (forall x (NEG: ~ f x) (CYC: R ^+ x x), False).
Proof.
  unfold restr_rel; repeat split; repeat red; ins; desc; eauto.
    by eapply H, clos_trans_mon; eauto; instantiate; ins; desf. 
  destruct (classic (f x)) as [X|X]; eauto.
  assert (M: (fun a b => R a b /\ f a /\ f b) ^* x x) by vauto.
  generalize X; revert H0 M X; generalize x at 2 3 5; ins.
  apply clos_trans_tn1 in H0; induction H0; eauto 6 using rt_t_trans, t_step.
  destruct (classic (f y)); eauto 6 using clos_refl_trans.
  eapply H1; eauto.
  eapply t_rt_trans, rt_trans; eauto using t_step, clos_trans_in_rt, clos_tn1_trans. 
  by eapply clos_refl_trans_mon; eauto; instantiate; ins; desf. 
Qed.

Lemma seqA2 X (r r' r'' : relation X) x y :
  ((r;; r');; r'') x y <-> (r;; r';; r'') x y.
Proof.
  unfold seq; split; ins; desf; eauto 8.
Qed.

Lemma inclusion_t_r_t A (rel rel' rel'': relation A) : 
  rel ⊆ rel'' ->
  rel' ⊆ rel'' ^* ->
  rel ^+ ;; rel' ⊆ rel'' ^+.
Proof.
  by ins; rewrite H, H0, ct_rt.
Qed.

Lemma inclusion_r_t_t A (rel rel' rel'': relation A) : 
  rel ⊆ rel'' ^* ->
  rel' ⊆ rel'' ->
  rel ;; rel' ^+ ⊆ rel'' ^+.
Proof.
  by ins; rewrite H, H0, rt_ct.
Qed.

Lemma inclusion_step2_ct A (rel rel' rel'': relation A) : 
  rel ⊆ rel'' ->
  rel' ⊆ rel'' ->
  rel ;; rel' ⊆ rel'' ^+.
Proof.
  ins; rewrite H, H0, <- ct_ct; eauto with rel.
Qed.

Lemma clos_trans_union_ct A (rel rel' : relation A) : 
  (rel ^+ ∪ rel') ^+ ≡ (rel ∪ rel') ^+.
Proof.  
  split; eauto 8 with rel.
Qed.

Lemma inclusion_ct_seq_eqv_l A dom (rel : relation A) :
  (<| dom |> ;; rel) ^+ ⊆ <| dom |> ;; rel ^+.
Proof.
  by rewrite ct_begin, seqA, inclusion_seq_eqv_l with (rel:=rel), <- ct_begin.
Qed.
