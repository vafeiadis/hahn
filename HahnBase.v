(* ************************************************************************** *)
(** * Basic tactics *)
(* ************************************************************************** *)

(** This file collects a number of basic tactics for better proof automation,
    structuring large proofs, or rewriting.  Many of the definitions have been
    ported from ss-reflect. *)

(** Symbols starting with [hahn__] are internal. *)

Require Import Bool Arith ZArith String.
Require ClassicalFacts.
Require Export ClassicalDescription FunctionalExtensionality.

Open Scope bool_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(** Set up hint databases *)
Create HintDb hahn discriminated.      (* General stuff, used by done *)
Create HintDb hahn_refl discriminated. (* Decidable equalities *)
Create HintDb hahn_full discriminated. (* Expensive lemmas *)

(** Shorthand for applying functional extensionality. *)

Ltac exten := apply functional_extensionality.

(** Notation for classical if-then-else *)

Notation "'ifP' c 'then' u 'else' v" :=
  (if excluded_middle_informative c then u else v)
  (at level 200).


(* ************************************************************************** *)
(** ** Coersion of [bool] into [Prop] *)
(* ************************************************************************** *)

(** Coersion of bools into Prop *)
Coercion is_true (b : bool) : Prop := b = true.

(** Hints for auto *)
Lemma hahn__true_is_true : true.
Proof. reflexivity. Qed.

Lemma hahn__not_false_is_true : ~ false.
Proof. discriminate. Qed.

Global Hint Resolve hahn__true_is_true hahn__not_false_is_true : core.

(* ************************************************************************** *)
(** ** Very basic automation *)
(* ************************************************************************** *)

(** Set up for basic simplification *)


(** Adaptation of the ss-reflect "[done]" tactic. *)

Ltac hahn__basic_done :=
  solve [trivial with hahn | simple apply sym_equal; trivial | discriminate | contradiction].

Ltac done := trivial with hahn; hnf; intros;
  solve [try hahn__basic_done; split;
         try hahn__basic_done; split;
         try hahn__basic_done; split;
         try hahn__basic_done; split;
         try hahn__basic_done; split; hahn__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

(** A variant of the ssr "done" tactic that performs "eassumption". *)

Ltac edone := try eassumption; trivial; hnf; intros;
  solve [try eassumption; try hahn__basic_done; split;
         try eassumption; try hahn__basic_done; split;
         try eassumption; try hahn__basic_done; split;
         try eassumption; try hahn__basic_done; split;
         try eassumption; try hahn__basic_done; split;
         try eassumption; hahn__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Tactic Notation "by"  tactic(tac) := (tac; done).
Tactic Notation "eby" tactic(tac) := (tac; edone).

(* ************************************************************************** *)
(** ** Equality types *)
(* ************************************************************************** *)

Module Equality.

  Definition axiom T (e : T -> T -> bool) :=
    forall x y, reflect (x = y) (e x y).

  Structure mixin_of T := Mixin {op : T -> T -> bool; _ : axiom op}.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.

    Structure type := Pack {sort; _ : class_of sort; _ : Type}.

    Definition class cT' :=
      match cT' return class_of (sort cT') with @Pack _ c _ => c end.

    Definition pack (T: Type) c := @Pack T c T.

  End ClassDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation eqType := type.
    Notation EqMixin := Mixin.
    Notation EqType T m := (@pack T m).
  End Exports.

End Equality.
Export Equality.Exports.

Definition eq_op T := Equality.op (Equality.class T).
Arguments eq_op {T}.

Lemma eqE : forall T x, eq_op x = Equality.op (Equality.class T) x.
Proof. done. Qed.

Lemma eqP : forall T, Equality.axiom (@eq_op T).
Proof. by unfold eq_op; destruct T as [? []]. Qed.
Arguments eqP [T] x y.

(*
Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x != y" := (negb (x == y))
  (at level 70, no associativity) : bool_scope.
Notation "x != y :> T" := (negb (x == y :> T))
  (at level 70, y at next level) : bool_scope.
*)

Lemma hahn__internal_eqP :
  forall (T: eqType) (x y : T), reflect (x = y) (eq_op x y).
Proof. apply eqP. Qed.

Lemma neqP : forall (T: eqType) (x y: T), reflect (x <> y) (negb (eq_op x y)).
Proof. intros; case eqP; constructor; auto. Qed.

Lemma beq_refl : forall (T : eqType) (x : T), eq_op x x.
Proof. by intros; case eqP. Qed.

Lemma beq_sym : forall (T : eqType) (x y : T), (eq_op x y) = (eq_op y x).
Proof. intros; do 2 case eqP; congruence. Qed.

Global Hint Resolve beq_refl : hahn.
Hint Rewrite beq_refl : hahn_trivial.

Notation eqxx := beq_refl.

(** Comparison for [nat] *)

Fixpoint eqn_rec (x y: nat) {struct x} :=
   match x, y with
     | O, O => true
     | S x, S y => eqn_rec x y
     | _, _ => false
   end.

Definition eqn := match tt with tt => eqn_rec end.

Lemma eqnP: forall x y, reflect (x = y) (eqn x y).
Proof.
  induction x; destruct y; try (constructor; done).
  change (eqn (S x) (S y)) with (eqn x y).
  case IHx; constructor; congruence.
Qed.

Canonical Structure nat_eqMixin := EqMixin eqnP.
Canonical Structure nat_eqType := Eval hnf in EqType nat nat_eqMixin.

Lemma eqnE : eqn = (@eq_op _).
Proof. done. Qed.


(* ************************************************************************** *)
(** ** Basic simplification tactics *)
(* ************************************************************************** *)

Lemma hahn__negb_rewrite : forall b, negb b -> b = false.
Proof. by intros []. Qed.

Lemma hahn__andb_split : forall b1 b2, b1 && b2 -> b1 /\ b2.
Proof. by intros [] []. Qed.

Lemma hahn__nandb_split : forall b1 b2, b1 && b2 = false -> b1 = false \/ b2 = false.
Proof. intros [] []; auto. Qed.

Lemma hahn__orb_split : forall b1 b2, b1 || b2 -> b1 \/ b2.
Proof. intros [] []; auto. Qed.

Lemma hahn__norb_split : forall b1 b2, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof. intros [] []; auto. Qed.

Lemma hahn__eqb_split : forall b1 b2 : bool, (b1 -> b2) -> (b2 -> b1) -> b1 = b2.
Proof. intros [] [] H H'; unfold is_true in *; auto using sym_eq. Qed.

Lemma hahn__beq_rewrite (T : eqType) (x1 x2 : T) : eq_op x1 x2 -> x1 = x2.
Proof. by case eqP. Qed.


(** Set up for basic simplification: database of reflection lemmas *)

Global Hint Resolve hahn__internal_eqP neqP eqnP : hahn_refl.
Global Hint Resolve Z.eqb_spec Z.leb_spec0 Z.ltb_spec0 : hahn_refl.
Global Hint Resolve N.eqb_spec N.leb_spec0 N.ltb_spec0 : hahn_refl.
Global Hint Resolve Pos.eqb_spec Pos.leb_spec0 Pos.ltb_spec0 : hahn_refl.
Global Hint Resolve Nat.eqb_spec Nat.leb_spec0 Nat.ltb_spec0 : hahn_refl.
Global Hint Resolve Ascii.eqb_spec String.eqb_spec : hahn_refl.
Global Hint Resolve Bool.eqb_spec : hahn_refl.

Ltac hahn__complaining_inj f H :=
  let X := fresh in
  (match goal with | [|- ?P ] => set (X := P) end);
  injection H; clear H; intros; subst X;
  try subst.

Ltac hahn__clarify1 :=
  try subst;
  repeat match goal with
  | [H: is_true (andb _ _) |- _] =>
      let H' := fresh H in case (hahn__andb_split H); clear H; intros H' H
  | [H: is_true (negb ?x) |- _] => rewrite (hahn__negb_rewrite H) in *
  | [H: is_true ?x        |- _] => rewrite H in *
  | [H: ?x = true         |- _] => rewrite H in *
  | [H: ?x = false        |- _] => rewrite H in *
  | [H: is_true (eq_op _ _)  |- _] => generalize (hahn__beq_rewrite H); clear H; intro H
  | [H: @existT _ _ _ _ = @existT _ _ _ _ |- _] => apply inj_pair2 in H; try subst
  | [H: ?f _             = ?f _             |- _] => hahn__complaining_inj f H
  | [H: ?f _ _           = ?f _ _           |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _         = ?f _ _ _         |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _ _       = ?f _ _ _ _       |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _] => hahn__complaining_inj f H
  | [H: ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _] => hahn__complaining_inj f H
  end; try done.

(** Perform injections & discriminations on all hypotheses *)

Ltac clarify :=
  hahn__clarify1;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; discriminate
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; hahn__clarify1
  end; (* autorewrite with hahn_trivial; *) try done.

(** Kill simple goals that require up to two econstructor calls. *)

Ltac vauto :=
  (clarify; try edone;
   try [> econstructor; (solve [edone | [> econstructor; edone]])]).

Ltac inv x := inversion x; clarify.
Ltac simpls  := simpl in *; try done.
Ltac ins := simpl in *; try done; intros.

Ltac hahn__clarsimp1 :=
  clarify; (autorewrite with hahn_trivial hahn in * );
  (autorewrite with hahn_trivial in * ); try done;
  clarify; auto 1 with hahn.

Ltac clarsimp := intros; simpl in *; hahn__clarsimp1.

Ltac autos   := clarsimp; auto with hahn.

Tactic Notation "econs" := econstructor.
Tactic Notation "econs" int_or_var(x) := econstructor x.

(* ************************************************************************** *)
(** Destruct but give useful names *)
(* ************************************************************************** *)

Definition  NW (P: unit -> Prop) : Prop := P tt.

Notation "⟪ x : t ⟫" := (NW (fun x => t)) (at level 80, x ident, no associativity).
Notation "<< x : t >>" := (NW (fun x => t))
  (at level 80, x ident, no associativity, only parsing).
Notation "⟪ t ⟫" := (NW (fun _ => t)) (at level 79, no associativity, format "⟪ t ⟫").

Ltac unnw := unfold NW in *.
Ltac rednw := red; unnw.

Global Hint Unfold NW : core.

Ltac splits :=
  intros; unfold NW;
  repeat match goal with
  | [ |- _ /\ _ ] => split
  end.

Ltac esplits :=
  intros; unfold NW;
  repeat match goal with
  | [ |- @ex _ _ ] => eexists
  | [ |- _ /\ _ ] => split
  | [ |- @sig _ _ ] => eexists
  | [ |- @sigT _ _ ] => eexists
  | [ |- @prod _  _ ] => split
  end.

(** Destruct, but no case split *)
Ltac desc :=
  repeat match goal with
    | H: is_true (eq_op _ _) |- _ => generalize (hahn__beq_rewrite H); clear H; intro H
    | H : exists x, NW (fun y => _) |- _ =>
      progress first [try (destruct H as [? H] ; fail 1) | (* Check it's not a Section Hypothesis *)
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y']
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : ?p /\ ?q |- _ =>
      progress first [try (destruct H as [H ?] ; fail 1) | (* Check it's not a Section Hypothesis *)
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end]
    | H : is_true (_ && _) |- _ =>
          let H' := fresh H in case (hahn__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
          let H' := fresh H in case (hahn__norb_split H); clear H; intros H H'
    | H : ?x = ?x   |- _ => clear H

(*    | H: is_true ?x |- _ => eapply elimT in H; [|solve [trivial with hahn_refl]]
    | H: ?x = true  |- _ => eapply elimT in H; [|solve [trivial with hahn_refl]]
    | H: ?x = false |- _ => eapply elimFn in H; [|solve [trivial with hahn_refl]]
    | H: ?x = false |- _ => eapply elimF in H; [|solve [trivial with hahn_refl]]  *)
  end.

Ltac des :=
  repeat match goal with
    | H: is_true (eq_op _ _) |- _ => generalize (hahn__beq_rewrite H); clear H; intro H
    | H : exists x, NW (fun y => _) |- _ =>
      progress first [try (destruct H as [? H] ; fail 1) | (* Check it's not a Section Hypothesis *)
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y']
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : ?p /\ ?q |- _ =>
      progress first [try (destruct H as [H ?] ; fail 1) | (* Check it's not a Section Hypothesis *)
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end]
    | H : is_true (_ && _) |- _ =>
        let H' := fresh H in case (hahn__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
        let H' := fresh H in case (hahn__norb_split H); clear H; intros H H'
    | H : ?x = ?x |- _ => clear H
    | H : ?p <-> ?q |- _ =>
      progress first [try (destruct H as [H ?] ; fail 1) | (* Check it's not a Section Hypothesis *)
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => unfold NW at 1 in x'; red in y' | _ => idtac end;
      match q with | NW _ => unfold NW at 1 in y'; red in x' | _ => idtac end]
    | H : ?p \/ ?q |- _ =>
      progress first [try (destruct H as [H|H] ; fail 1) | (* Check it's not a Section Hypothesis *)
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => H end in
      destruct H as [x' | y'];
      [ match p with | NW _ => red in x' | _ => idtac end
      | match q with | NW _ => red in y' | _ => idtac end]]
    | H : is_true (_ || _) |- _ => case (hahn__orb_split H); clear H; intro H
    | H : (_ && _) = false |- _ => case (hahn__nandb_split H); clear H; intro H
  end.

Ltac desc_section :=
  repeat match goal with
    | H : exists x, NW (fun y => _) |- _ =>
      try (destruct H as [? H] ; fail 1); (* Check it is a Section Hypothesis *)
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; clear H; red in y'
    | H : exists x, ?p |- _ =>
      try (destruct H as [? H] ; fail 1); (* Check it is a Section Hypothesis *)
      let x' := fresh x in let y' := fresh H in destruct H as [x' y']; clear H; red in y'
    | H : ?p /\ ?q |- _ =>
      try (destruct H as [H ?] ; fail 1); (* Check it is a Section Hypothesis *)
      let x' := match p with | NW (fun z => _) => fresh z | _ => fresh H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y']; clear H;
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end
    | H : ?x = ?x   |- _ => clear H
  end; desc.


Ltac cdes H :=
  let H' := fresh H in assert (H' := H); try red in H'; desc.

Ltac des_if_asm :=
  clarify;
  repeat
    match goal with
      | H: context[ match ?x with _ => _ end ] |- _ =>
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool =>
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with hahn_refl);
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
        end
    end.

Ltac des_if_goal :=
  clarify;
  repeat
    match goal with
      | |- context[match ?x with _ => _ end] =>
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool =>
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with hahn_refl);
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
        end
    end.

Ltac des_if :=
  clarify;
  repeat
    match goal with
      | |- context[match ?x with _ => _ end] =>
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool =>
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with hahn_refl);
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
        end
      | H: context[ match ?x with _ => _ end ] |- _ =>
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool =>
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with hahn_refl);
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
        end
    end.

Ltac des_eqrefl :=
  match goal with
    | H: context[match ?X with _ => _ end Logic.eq_refl] |- _ =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    revert H;
    generalize (Logic.eq_refl X); generalize X at 1 3;
    intros id' EQ; destruct id'; intros H
    | |- context[match ?X with _ => _ end Logic.eq_refl] =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    generalize (Logic.eq_refl X); generalize X at 1 3;
    intros id' EQ; destruct id'
  end.

Ltac desf_asm := clarify; des; des_if_asm.

Ltac desf := clarify; des; des_if.

Ltac clarassoc := clarsimp; autorewrite with hahn_trivial hahn hahnA in *; try done.

Ltac hahn__hacksimp1 :=
   clarsimp;
   match goal with
     | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                         |rewrite <- H; clear H; clarsimp]
     | _ => solve [f_equal; clarsimp]
   end.

Ltac hacksimp :=
   clarsimp;
   try match goal with
   | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                              |rewrite <- H; clear H; clarsimp]
   | |- context[match ?p with _ => _ end] => solve [destruct p; hahn__hacksimp1]
   | _ => solve [f_equal; clarsimp]
   end.

Ltac clarify_not :=
  repeat (match goal with
  | H : ~ False |- _ => clear H
  | H : ~ ~ _ |- _ => apply NNPP in H
  | H : ~ _ |- _ => apply imply_to_and in H; desc
  | H : ~ _ |- _ => apply not_or_and in H; desc
  | H : ~ _ |- _ => apply not_and_or in H; des
  | H : ~ _ |- _ => apply not_all_ex_not in H; desc
  end; clarify).

Tactic Notation "tertium_non_datur" constr(P) :=
  destruct (classic P); clarify_not.

Tactic Notation "tertium_non_datur" constr(P) "as" simple_intropattern(pattern) :=
  destruct (classic P) as pattern; clarify_not.

(* ************************************************************************** *)
(** ** Unification helpers *)
(* ************************************************************************** *)

Tactic Notation "pattern_lhs" uconstr(term) :=
  match goal with
    |- _ ?lhs _ =>
    let P := fresh in
    pose (P := lhs); pattern term in P; change lhs with P; subst P
  end.

Tactic Notation "pattern_rhs" uconstr(term) :=
  match goal with
    |- _ _ ?rhs =>
    let P := fresh in
    pose (P := rhs); pattern term in P; change rhs with P; subst P
  end.

(* ************************************************************************** *)
(** ** Exploiting a hypothesis *)
(* ************************************************************************** *)

Tactic Notation "forward" tactic1(tac) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [tac|].

Tactic Notation "forward" tactic1(tac) "as" simple_intropattern(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [tac|intros H].

Tactic Notation "specialize_full" ident(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [eapply H|try clear H; intro H].


(** Exploit an assumption (adapted from CompCert). *)

Ltac exploit x :=
    refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _) _)
 || refine ((fun x y => y x) (x _ _) _)
 || refine ((fun x y => y x) (x _) _).
