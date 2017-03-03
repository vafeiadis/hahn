Require Import HahnBase HahnList HahnRelationsBasic HahnEquational.

Set Implicit Arguments.

(** We add some support for rewriting with [inclusion] and [same_relation]
relations. We start with some basic helper lemmas. *)

Section HelperLemmas.

  Variable A : Type.
  Variables r1 r2 r3 r4 r r' : relation A.

  Lemma hahn_inclusion_exp :
    r ⊆ r' -> forall x y, r x y -> r' x y.
  Proof.
    eauto.
  Qed.

  Lemma seq2 (L : r1 ;; r2 ≡ r) s : 
    r1 ;; r2 ;; s ≡ r ;; s.
  Proof.
    rewrite <- L, seqA; vauto.
  Qed.

  Lemma seq3 (L : r1 ;; r2 ;; r3 ≡ r) s :
     r1 ;; r2 ;; r3 ;; s ≡ r ;; s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma seq4 (L : r1 ;; r2 ;; r3 ;; r4 ≡ r) s :
     r1 ;; r2 ;; r3 ;; r4 ;; s ≡ r ;; s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma sin2 (L : r1 ;; r2 ⊆ r) s :
    r1 ;; r2 ;; s ⊆ r ;; s. 
  Proof.
    rewrite <- L, seqA; vauto.
  Qed.

  Lemma sin3 (L : r1 ;; r2 ;; r3 ⊆ r) s :
    r1 ;; r2 ;; r3 ;; s ⊆ r ;; s. 
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma sin4 (L : r1 ;; r2 ;; r3 ;; r4 ⊆ r) s :
    r1 ;; r2 ;; r3 ;; r4 ;; s ⊆ r ;; s. 
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

End HelperLemmas.

(** We proceed with a set of rewrite tactics *)

Tactic Notation "hahn_rewrite" uconstr(EQ) :=
  match goal with 
    | |- _ _ _ => eapply hahn_inclusion_exp; [rewrite EQ; reflexivity|]
    | |- _ => rewrite EQ
  end.

Tactic Notation "hahn_rewrite" "<-" uconstr(EQ) :=
  match goal with 
    | |- _ _ _ => eapply hahn_inclusion_exp; [rewrite <- EQ; reflexivity|]
    | |- _ => rewrite <- EQ
  end.

Tactic Notation "hahn_rewrite" uconstr(EQ) "in" hyp(H) :=
  match type of H with 
    | _ _ _ => eapply hahn_inclusion_exp in H; [|rewrite EQ; reflexivity]
    | _ => rewrite EQ in H
  end.

Tactic Notation "hahn_rewrite" "<-" uconstr(EQ) "in" hyp(H) :=
  match type of H with 
    | _ _ _ => eapply hahn_inclusion_exp in H; [|rewrite <- EQ; reflexivity]
    | _ => rewrite <- EQ in H
  end.

Tactic Notation "seq_rewrite" uconstr(x) :=
  first [ hahn_rewrite x
        | hahn_rewrite (seq2 x)
        | hahn_rewrite (fun a => seq2 (x a))
        | hahn_rewrite (fun a b => seq2 (x a b)) 
        | hahn_rewrite (fun a b c => seq2 (x a b c))
        | hahn_rewrite (fun a b c d => seq2 (x a b c d)) 
        | hahn_rewrite (fun a b c d e => seq2 (x a b c d e))
        | hahn_rewrite (fun a b c d e f => seq2 (x a b c d e f))
        | hahn_rewrite (seq3 x)
        | hahn_rewrite (fun a => seq3 (x a))
        | hahn_rewrite (fun a b => seq3 (x a b)) 
        | hahn_rewrite (fun a b c => seq3 (x a b c))
        | hahn_rewrite (fun a b c d => seq3 (x a b c d)) 
        | hahn_rewrite (fun a b c d e => seq3 (x a b c d e))
        | hahn_rewrite (fun a b c d e f => seq3 (x a b c d e f))
        | hahn_rewrite (seq4 x)
        | hahn_rewrite (fun a => seq4 (x a))
        | hahn_rewrite (fun a b => seq4 (x a b)) 
        | hahn_rewrite (fun a b c => seq4 (x a b c))
        | hahn_rewrite (fun a b c d => seq4 (x a b c d)) 
        | hahn_rewrite (fun a b c d e => seq4 (x a b c d e))
        | hahn_rewrite (fun a b c d e f => seq4 (x a b c d e f))
        ].

Tactic Notation "seq_rewrite" "<-" uconstr(x) :=
  first [ hahn_rewrite <- x
        | hahn_rewrite (seq2 (same_relation_sym x)) 
        | hahn_rewrite (seq2 (same_relation_sym (x _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _ _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _ _ _))) 
        | hahn_rewrite (seq2 (same_relation_sym (x _ _ _ _ _))) 
        | hahn_rewrite (fun a => seq2 (same_relation_sym (x a)))
        | hahn_rewrite (fun a b => seq2 (same_relation_sym (x a b)))
        | hahn_rewrite (fun a b c => seq2 (same_relation_sym (x a b c)))
        | hahn_rewrite (fun a b c d => seq2 (same_relation_sym (x a b c d)))
        | hahn_rewrite (fun a b c d e => seq2 (same_relation_sym (x a b c d e)))
        | hahn_rewrite (fun a b c d e f => seq2 (same_relation_sym (x a b c d e f)))
        | hahn_rewrite (seq3 (same_relation_sym x)) 
        | hahn_rewrite (fun a => seq3 (same_relation_sym (x a)))
        | hahn_rewrite (fun a b => seq3 (same_relation_sym (x a b)))
        | hahn_rewrite (fun a b c => seq3 (same_relation_sym (x a b c)))
        | hahn_rewrite (fun a b c d => seq3 (same_relation_sym (x a b c d)))
        | hahn_rewrite (fun a b c d e => seq3 (same_relation_sym (x a b c d e)))
        | hahn_rewrite (fun a b c d e f => seq3 (same_relation_sym (x a b c d e f)))
        | hahn_rewrite (seq4 (same_relation_sym x)) 
        | hahn_rewrite (fun a => seq4 (same_relation_sym (x a)))
        | hahn_rewrite (fun a b => seq4 (same_relation_sym (x a b)))
        | hahn_rewrite (fun a b c => seq4 (same_relation_sym (x a b c)))
        | hahn_rewrite (fun a b c d => seq4 (same_relation_sym (x a b c d)))
        | hahn_rewrite (fun a b c d e => seq4 (same_relation_sym (x a b c d e)))
        | hahn_rewrite (fun a b c d e f => seq4 (same_relation_sym (x a b c d e f)))
        ].

Tactic Notation "seq_rewrite" "!" uconstr(x) :=
  seq_rewrite x; repeat seq_rewrite x.

Tactic Notation "seq_rewrite" "?" uconstr(x) := 
  repeat seq_rewrite x.

Tactic Notation "seq_rewrite" "<-" "!" uconstr(x) :=
  seq_rewrite <- x; repeat seq_rewrite <- x.

Tactic Notation "seq_rewrite" "<-" "?" uconstr(x) := 
  repeat seq_rewrite <- x.

Tactic Notation "sin_rewrite" uconstr(x) :=
  first [ rewrite x at 1
        | rewrite (sin2 x) at 1
        | rewrite (fun a => sin2 (x a)) at 1
        | rewrite (fun a b => sin2 (x a b)) at 1
        | rewrite (fun a b c => sin2 (x a b c)) at 1
        | rewrite (fun a b c d => sin2 (x a b c d)) at 1
        | rewrite (fun a b c d e => sin2 (x a b c d e)) at 1
        | rewrite (fun a b c d e f => sin2 (x a b c d e f)) at 1
        | rewrite (sin3 x) at 1
        | rewrite (fun a => sin3 (x a)) at 1
        | rewrite (fun a b => sin3 (x a b)) at 1
        | rewrite (fun a b c => sin3 (x a b c)) at 1
        | rewrite (fun a b c d => sin3 (x a b c d)) at 1
        | rewrite (fun a b c d e => sin3 (x a b c d e)) at 1
        | rewrite (fun a b c d e f => sin3 (x a b c d e f)) at 1
        | rewrite (sin4 x) at 1
        | rewrite (fun a => sin4 (x a)) at 1
        | rewrite (fun a b => sin4 (x a b)) at 1
        | rewrite (fun a b c => sin4 (x a b c)) at 1
        | rewrite (fun a b c d => sin4 (x a b c d)) at 1
        | rewrite (fun a b c d e => sin4 (x a b c d e)) at 1
        | rewrite (fun a b c d e f => sin4 (x a b c d e f)) at 1
        ].

Tactic Notation "sin_rewrite" "!" uconstr(x) :=
  sin_rewrite x; repeat sin_rewrite x.

Tactic Notation "sin_rewrite" "?" uconstr(x) := 
  repeat sin_rewrite x.

