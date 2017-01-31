(******************************************************************************)
(** * Basic properties of relations *)
(******************************************************************************)

Require Import HahnBase HahnList HahnRelationsBasic.
Require Import Classical NPeano Omega Permutation List Setoid.

Set Implicit Arguments.

Tactic Notation "hahn_rewrite" uconstr(EQ) :=
  match goal with 
    | |- _ _ _ => apply <- same_relation_exp; [|rewrite EQ; reflexivity]
    | |- _ => rewrite EQ
  end.

Tactic Notation "hahn_rewrite" "<-" uconstr(EQ) :=
  match goal with 
    | |- _ _ _ => apply <- same_relation_exp; [|rewrite <- EQ; reflexivity]
    | |- _ => rewrite <- EQ
  end.

Tactic Notation "hahn_rewrite" uconstr(EQ) "in" hyp(H) :=
  match type of H with 
    | _ _ _ => apply <- same_relation_exp in H; [|rewrite EQ; reflexivity]
    | _ => rewrite EQ in H
  end.

Tactic Notation "hahn_rewrite" "<-" uconstr(EQ) "in" hyp(H) :=
  match type of H with 
    | _ _ _ => apply <- same_relation_exp in H; [|rewrite <- EQ; reflexivity]
    | _ => rewrite <- EQ in H
  end.

Lemma seq2 A (r r' r'': relation A) (L : r ;; r' ≡ r'') s :
   r ;; r' ;; s ≡ r'' ;; s.
Proof.
  rewrite <- L, seqA; vauto.
Qed.

Lemma seq3 A (r1 r2 r3 r: relation A) (L : r1 ;; r2 ;; r3 ≡ r) s :
   r1 ;; r2 ;; r3 ;; s ≡ r ;; s.
Proof.
  rewrite <- L, !seqA; vauto.
Qed.

Lemma seq4 A (r1 r2 r3 r4 r: relation A) (L : r1 ;; r2 ;; r3 ;; r4 ≡ r) s :
   r1 ;; r2 ;; r3 ;; r4 ;; s ≡ r ;; s.
Proof.
  rewrite <- L, !seqA; vauto.
Qed.

Tactic Notation "seq_rewrite" uconstr(x) :=
  first [ hahn_rewrite x
        | hahn_rewrite (seq2 x)
        | hahn_rewrite (seq2 (x _))
        | hahn_rewrite (seq2 (x _ _)) 
        | hahn_rewrite (seq2 (x _ _ _))
        | hahn_rewrite (seq2 (x _ _ _ _)) 
        | hahn_rewrite (seq2 (x _ _ _ _ _))
        | hahn_rewrite (seq2 (x _ _ _ _ _ _)) 
        | hahn_rewrite (seq3 x)
        | hahn_rewrite (seq3 (x _))
        | hahn_rewrite (seq3 (x _ _)) 
        | hahn_rewrite (seq3 (x _ _ _))
        | hahn_rewrite (seq3 (x _ _ _ _)) 
        | hahn_rewrite (seq3 (x _ _ _ _ _))
        | hahn_rewrite (seq3 (x _ _ _ _ _ _)) 
        | hahn_rewrite (seq4 x)
        | hahn_rewrite (seq4 (x _))
        | hahn_rewrite (seq4 (x _ _))
        | hahn_rewrite (seq4 (x _ _ _))
        | hahn_rewrite (seq4 (x _ _ _ _)) 
        | hahn_rewrite (seq4 (x _ _ _ _ _))
        | hahn_rewrite (seq4 (x _ _ _ _ _ _)) 
        ].

Tactic Notation "seq_rewrite" "<-" uconstr(x) :=
  first [ hahn_rewrite <- x
        | hahn_rewrite (seq2 (same_relation_sym x)) 
        | hahn_rewrite (seq2 (same_relation_sym (x _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _ _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _ _ _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _ _ _ _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _ _ _ _ _))) 
        | hahn_rewrite (seq3 (same_relation_sym x)) 
        | hahn_rewrite (seq3 (same_relation_sym (x _))) 
        | hahn_rewrite (seq3 (same_relation_sym (x _ _))) 
        | hahn_rewrite (seq3 (same_relation_sym (x _ _ _))) 
        | hahn_rewrite (seq3 (same_relation_sym (x _ _ _ _))) 
        | hahn_rewrite (seq3 (same_relation_sym (x _ _ _ _ _))) 
        | hahn_rewrite (seq3 (same_relation_sym (x _ _ _ _ _ _))) 
        | hahn_rewrite (seq4 (same_relation_sym x)) 
        | hahn_rewrite (seq4 (same_relation_sym (x _))) 
        | hahn_rewrite (seq4 (same_relation_sym (x _ _))) 
        | hahn_rewrite (seq4 (same_relation_sym (x _ _ _))) 
        | hahn_rewrite (seq4 (same_relation_sym (x _ _ _ _))) 
        | hahn_rewrite (seq4 (same_relation_sym (x _ _ _ _ _))) 
        | hahn_rewrite (seq4 (same_relation_sym (x _ _ _ _ _ _))) 
        ].

Tactic Notation "seq_rewrite" "!" uconstr(x) :=
  seq_rewrite x; repeat seq_rewrite x.

Tactic Notation "seq_rewrite" "?" uconstr(x) := 
  repeat seq_rewrite x.

Tactic Notation "seq_rewrite" "<-" "!" uconstr(x) :=
  seq_rewrite <- x; repeat seq_rewrite <- x.

Tactic Notation "seq_rewrite" "<-" "?" uconstr(x) := 
  repeat seq_rewrite <- x.

Lemma sin2 A (r1 r2 r : relation A) (L : r1 ;; r2 ⊆ r) s :
  r1 ;; r2 ;; s ⊆ r ;; s. 
Proof.
  rewrite <- L, seqA; vauto.
Qed.

Lemma sin3 A (r1 r2 r3 r : relation A) (L : r1 ;; r2 ;; r3 ⊆ r) s :
  r1 ;; r2 ;; r3 ;; s ⊆ r ;; s. 
Proof.
  rewrite <- L, !seqA; vauto.
Qed.

Lemma sin4 A (r1 r2 r3 r4 r : relation A) (L : r1 ;; r2 ;; r3 ;; r4 ⊆ r) s :
  r1 ;; r2 ;; r3 ;; r4 ;; s ⊆ r ;; s. 
Proof.
  rewrite <- L, !seqA; vauto.
Qed.

Tactic Notation "sin_rewrite" uconstr(x) :=
  first [ rewrite x at 1
        | rewrite (sin2 x) at 1 
        | rewrite (sin2 (x _)) at 1 
        | rewrite (sin2 (x _ _)) at 1 
        | rewrite (sin2 (x _ _ _))  at 1
        | rewrite (sin2 (x _ _ _ _))  at 1
        | rewrite (sin2 (x _ _ _ _ _)) at 1
        | rewrite (sin2 (x _ _ _ _ _ _)) at 1
        | rewrite (sin3 x) at 1
        | rewrite (sin3 (x _)) at 1
        | rewrite (sin3 (x _ _)) at 1 
        | rewrite (sin3 (x _ _ _)) at 1 
        | rewrite (sin3 (x _ _ _ _)) at 1
        | rewrite (sin3 (x _ _ _ _ _))  at 1
        | rewrite (sin3 (x _ _ _ _ _ _))  at 1
        | rewrite (sin4 x) at 1
        | rewrite (sin4 (x _)) at 1
        | rewrite (sin4 (x _ _)) at 1 
        | rewrite (sin4 (x _ _ _)) at 1 
        | rewrite (sin4 (x _ _ _ _)) at 1
        | rewrite (sin4 (x _ _ _ _ _))  at 1
        | rewrite (sin4 (x _ _ _ _ _ _))  at 1
        ].

Tactic Notation "sin_rewrite" "!" uconstr(x) :=
  sin_rewrite x; repeat sin_rewrite x.

Tactic Notation "sin_rewrite" "?" uconstr(x) := 
  repeat sin_rewrite x.

