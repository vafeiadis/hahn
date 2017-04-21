Require Import HahnBase HahnList HahnRelationsBasic HahnEquational.

Set Implicit Arguments.

(** We add some support for rewriting with [inclusion] and [same_relation]
relations. We start with some basic helper lemmas. *)

Section HelperLemmas.

  Variable A : Type.
  Variables r1 r2 r3 r4 r5 r6 r r' : relation A.

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

  Lemma seq5 (L : r1 ;; r2 ;; r3 ;; r4 ;; r5 ≡ r) s :
     r1 ;; r2 ;; r3 ;; r4 ;; r5 ;; s ≡ r ;; s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma seq6 (L : r1 ;; r2 ;; r3 ;; r4 ;; r5 ;; r6 ≡ r) s :
     r1 ;; r2 ;; r3 ;; r4 ;; r5 ;; r6 ;; s ≡ r ;; s.
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

  Lemma sin5 (L : r1 ;; r2 ;; r3 ;; r4 ;; r5 ⊆ r) s :
    r1 ;; r2 ;; r3 ;; r4 ;; r5 ;; s ⊆ r ;; s. 
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma sin6 (L : r1 ;; r2 ;; r3 ;; r4 ;; r5 ;; r6 ⊆ r) s :
    r1 ;; r2 ;; r3 ;; r4 ;; r5 ;; r6 ;; s ⊆ r ;; s. 
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
        | hahn_rewrite (seq5 x)
        | hahn_rewrite (fun a => seq5 (x a))
        | hahn_rewrite (fun a b => seq5 (x a b)) 
        | hahn_rewrite (fun a b c => seq5 (x a b c))
        | hahn_rewrite (fun a b c d => seq5 (x a b c d)) 
        | hahn_rewrite (fun a b c d e => seq5 (x a b c d e))
        | hahn_rewrite (fun a b c d e f => seq5 (x a b c d e f))
        | hahn_rewrite (seq6 x)
        | hahn_rewrite (fun a => seq6 (x a))
        | hahn_rewrite (fun a b => seq6 (x a b)) 
        | hahn_rewrite (fun a b c => seq6 (x a b c))
        | hahn_rewrite (fun a b c d => seq6 (x a b c d)) 
        | hahn_rewrite (fun a b c d e => seq6 (x a b c d e))
        | hahn_rewrite (fun a b c d e f => seq6 (x a b c d e f))
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
        | hahn_rewrite (seq5 (same_relation_sym x)) 
        | hahn_rewrite (fun a => seq5 (same_relation_sym (x a)))
        | hahn_rewrite (fun a b => seq5 (same_relation_sym (x a b)))
        | hahn_rewrite (fun a b c => seq5 (same_relation_sym (x a b c)))
        | hahn_rewrite (fun a b c d => seq5 (same_relation_sym (x a b c d)))
        | hahn_rewrite (fun a b c d e => seq5 (same_relation_sym (x a b c d e)))
        | hahn_rewrite (fun a b c d e f => seq5 (same_relation_sym (x a b c d e f)))
        | hahn_rewrite (seq6 (same_relation_sym x)) 
        | hahn_rewrite (fun a => seq6 (same_relation_sym (x a)))
        | hahn_rewrite (fun a b => seq6 (same_relation_sym (x a b)))
        | hahn_rewrite (fun a b c => seq6 (same_relation_sym (x a b c)))
        | hahn_rewrite (fun a b c d => seq6 (same_relation_sym (x a b c d)))
        | hahn_rewrite (fun a b c d e => seq6 (same_relation_sym (x a b c d e)))
        | hahn_rewrite (fun a b c d e f => seq6 (same_relation_sym (x a b c d e f)))
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



Lemma rewrite_trans A (r: relation A) :
  transitive r -> r ;; r ⊆ r.
Proof.
  unfold inclusion, seq; ins; desf; eauto. 
Qed.

Lemma rewrite_trans_seq_cr_l A (r: relation A) :
  transitive r -> r^? ;; r ⊆ r.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto. 
Qed.

Lemma rewrite_trans_seq_cr_r A (r: relation A) :
  transitive r -> r ;; r^? ⊆ r.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto. 
Qed.

Lemma rewrite_trans_seq_cr_cr A (r: relation A) :
  transitive r -> r^? ;; r^? ⊆ r^?.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto. 
Qed.

Lemma transitiveI A (r: relation A) :
  inclusion (r ;; r) r -> transitive r.
Proof.
  unfold transitive, inclusion, seq; ins; desf; eauto. 
Qed.

Ltac rels := 
  repeat first [progress autorewrite with rel |
                seq_rewrite seq_eqvK |
                seq_rewrite ct_cr | seq_rewrite ct_rt |
                seq_rewrite rt_cr | seq_rewrite rt_ct | seq_rewrite rt_rt |
                seq_rewrite cr_ct | seq_rewrite cr_rt |
                seq_rewrite <- ct_end | seq_rewrite <- ct_begin ];
    try done; eauto 3 with rel.

Ltac relsf := 
  repeat first [progress autorewrite with rel |
                seq_rewrite seq_eqvK |
                seq_rewrite ct_cr | seq_rewrite ct_rt |
                seq_rewrite rt_cr | seq_rewrite rt_ct | seq_rewrite rt_rt |
                seq_rewrite cr_ct | seq_rewrite cr_rt |
                match goal with H: transitive _ |- _ =>
                  progress repeat first [rewrite (ct_of_trans H) | 
                                rewrite (rt_of_trans H) |
                                sin_rewrite (rewrite_trans H) |
                                sin_rewrite (rewrite_trans_seq_cr_l H) |
                                sin_rewrite (rewrite_trans_seq_cr_r H) |
                                sin_rewrite (rewrite_trans_seq_cr_cr H) ] end |
                progress autorewrite with rel rel_full ];
    try done; eauto 3 with rel.



Ltac hahn_rel := 
  rels; 
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
