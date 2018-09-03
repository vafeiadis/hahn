(** * Support for rewriting *)

Require Import HahnBase HahnList HahnRelationsBasic HahnEquational HahnFuneq HahnSets.

Set Implicit Arguments.

(** We add some support for rewriting with [inclusion] and [same_relation]
relations. We start with some basic helper lemmas. *)

Section HelperLemmas.

  Variable A : Type.
  Variables r1 r2 r3 r4 r5 r6 r7 r r' : relation A.

  Lemma hahn_subset_exp (s s' : A -> Prop) :
    s ⊆₁ s' -> forall x, s x -> s' x.
  Proof.
    eauto.
  Qed.

  Lemma hahn_inclusion_exp :
    r ⊆ r' -> forall x y, r x y -> r' x y.
  Proof.
    eauto.
  Qed.

  Lemma seq2 (L : r1 ⨾ r2 ≡ r) s :
    r1 ⨾ r2 ⨾ s ≡ r ⨾ s.
  Proof.
    rewrite <- L, seqA; vauto.
  Qed.

  Lemma seq3 (L : r1 ⨾ r2 ⨾ r3 ≡ r) s :
     r1 ⨾ r2 ⨾ r3 ⨾ s ≡ r ⨾ s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma seq4 (L : r1 ⨾ r2 ⨾ r3 ⨾ r4 ≡ r) s :
     r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ s ≡ r ⨾ s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma seq5 (L : r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ≡ r) s :
     r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ⨾ s ≡ r ⨾ s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma seq6 (L : r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ⨾ r6 ≡ r) s :
     r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ⨾ r6 ⨾ s ≡ r ⨾ s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma sin2 (L : r1 ⨾ r2 ⊆ r) s :
    r1 ⨾ r2 ⨾ s ⊆ r ⨾ s.
  Proof.
    rewrite <- L, seqA; vauto.
  Qed.

  Lemma sin3 (L : r1 ⨾ r2 ⨾ r3 ⊆ r) s :
    r1 ⨾ r2 ⨾ r3 ⨾ s ⊆ r ⨾ s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma sin4 (L : r1 ⨾ r2 ⨾ r3 ⨾ r4 ⊆ r) s :
    r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ s ⊆ r ⨾ s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma sin5 (L : r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ⊆ r) s :
    r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ⨾ s ⊆ r ⨾ s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

  Lemma sin6 (L : r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ⨾ r6 ⊆ r) s :
    r1 ⨾ r2 ⨾ r3 ⨾ r4 ⨾ r5 ⨾ r6 ⨾ s ⊆ r ⨾ s.
  Proof.
    rewrite <- L, !seqA; vauto.
  Qed.

End HelperLemmas.

(** We proceed with a set of rewrite tactics *)

Tactic Notation "hahnf_rewrite" uconstr(EQ) :=
  match goal with
    | |- _ _ _ => eapply hahn_inclusion_exp; [solve[rewrite EQ; apply inclusion_refl2]|]
    | |- _ _ => eapply hahn_subset_exp; [solve[rewrite EQ; apply set_subset_refl2]|]
    | |- _ => rewrite EQ
  end.

Tactic Notation "hahnf_rewrite" "<-" uconstr(EQ) :=
  match goal with
    | |- _ _ _ => eapply hahn_inclusion_exp; [solve[rewrite <- EQ; apply inclusion_refl2]|]
    | |- _ _ => eapply hahn_subset_exp; [solve[rewrite <- EQ; apply set_subset_refl2]|]
    | |- _ => rewrite <- EQ
  end.

Tactic Notation "hahnf_rewrite" uconstr(EQ) "in" hyp(H) :=
  match type of H with
    | _ _ _ => eapply hahn_inclusion_exp in H; [|solve[rewrite EQ; apply inclusion_refl2]]
    | _ _ => eapply hahn_subset_exp in H; [|solve[rewrite EQ; apply set_subset_refl2]]
    | _ => rewrite EQ in H
  end.

Tactic Notation "hahnf_rewrite" "<-" uconstr(EQ) "in" hyp(H) :=
  match type of H with
    | _ _ _ => eapply hahn_inclusion_exp in H; [|solve[rewrite <- EQ; apply inclusion_refl2]]
    | _ _ => eapply hahn_subset_exp in H; [|solve[rewrite <- EQ; apply set_subset_refl2]]
    | _ => rewrite <- EQ in H
  end.

Tactic Notation "hahn_rewrite" uconstr(EQ) :=
  match goal with
    | |- _ _ _ => eapply hahn_inclusion_exp; [solve [rewrite EQ; apply inclusion_refl2]|]
    | |- _ => rewrite EQ
  end.

Tactic Notation "hahn_rewrite" "<-" uconstr(EQ) :=
  match goal with
    | |- _ _ _ => eapply hahn_inclusion_exp; [solve [rewrite <- EQ; apply inclusion_refl2]|]
    | |- _ => rewrite <- EQ
  end.

Tactic Notation "hahn_rewrite" uconstr(EQ) "in" hyp(H) :=
  match type of H with
    | _ _ _ => eapply hahn_inclusion_exp in H; [|solve [rewrite EQ; apply inclusion_refl2]]
    | _ => rewrite EQ in H
  end.

Tactic Notation "hahn_rewrite" "<-" uconstr(EQ) "in" hyp(H) :=
  match type of H with
    | _ _ _ => eapply hahn_inclusion_exp in H; [|solve [rewrite <- EQ; apply inclusion_refl2]]
    | _ => rewrite <- EQ in H
  end.

Tactic Notation "hahn_seq_rewrite" uconstr(x) :=
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

Tactic Notation "seq_rewrite" uconstr(x) :=
  first [ rewrite x
        | rewrite (seq2 x)
        | rewrite (fun a => seq2 (x a))
        | rewrite (fun a b => seq2 (x a b))
        | rewrite (fun a b c => seq2 (x a b c))
        | rewrite (fun a b c d => seq2 (x a b c d))
        | rewrite (fun a b c d e => seq2 (x a b c d e))
        | rewrite (fun a b c d e f => seq2 (x a b c d e f))
        | rewrite (seq3 x)
        | rewrite (fun a => seq3 (x a))
        | rewrite (fun a b => seq3 (x a b))
        | rewrite (fun a b c => seq3 (x a b c))
        | rewrite (fun a b c d => seq3 (x a b c d))
        | rewrite (fun a b c d e => seq3 (x a b c d e))
        | rewrite (fun a b c d e f => seq3 (x a b c d e f))
        | rewrite (seq4 x)
        | rewrite (fun a => seq4 (x a))
        | rewrite (fun a b => seq4 (x a b))
        | rewrite (fun a b c => seq4 (x a b c))
        | rewrite (fun a b c d => seq4 (x a b c d))
        | rewrite (fun a b c d e => seq4 (x a b c d e))
        | rewrite (fun a b c d e f => seq4 (x a b c d e f))
        | rewrite (seq5 x)
        | rewrite (fun a => seq5 (x a))
        | rewrite (fun a b => seq5 (x a b))
        | rewrite (fun a b c => seq5 (x a b c))
        | rewrite (fun a b c d => seq5 (x a b c d))
        | rewrite (fun a b c d e => seq5 (x a b c d e))
        | rewrite (fun a b c d e f => seq5 (x a b c d e f))
        | rewrite (seq6 x)
        | rewrite (fun a => seq6 (x a))
        | rewrite (fun a b => seq6 (x a b))
        | rewrite (fun a b c => seq6 (x a b c))
        | rewrite (fun a b c d => seq6 (x a b c d))
        | rewrite (fun a b c d e => seq6 (x a b c d e))
        | rewrite (fun a b c d e f => seq6 (x a b c d e f))
        ].

Tactic Notation "hahn_seq_rewrite" "<-" uconstr(x) :=
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

Tactic Notation "seq_rewrite" "<-" uconstr(x) :=
  first [ rewrite <- x
        | rewrite (seq2 (same_relation_sym x))
        | rewrite (seq2 (same_relation_sym (x _)))
        | rewrite (seq2 (same_relation_sym (x _ _)))
        | rewrite (seq2 (same_relation_sym (x _ _ _)))
        | rewrite (seq2 (same_relation_sym (x _ _ _ _)))
        | rewrite (seq2 (same_relation_sym (x _ _ _ _ _)))
        | rewrite (fun a => seq2 (same_relation_sym (x a)))
        | rewrite (fun a b => seq2 (same_relation_sym (x a b)))
        | rewrite (fun a b c => seq2 (same_relation_sym (x a b c)))
        | rewrite (fun a b c d => seq2 (same_relation_sym (x a b c d)))
        | rewrite (fun a b c d e => seq2 (same_relation_sym (x a b c d e)))
        | rewrite (fun a b c d e f => seq2 (same_relation_sym (x a b c d e f)))
        | rewrite (seq3 (same_relation_sym x))
        | rewrite (fun a => seq3 (same_relation_sym (x a)))
        | rewrite (fun a b => seq3 (same_relation_sym (x a b)))
        | rewrite (fun a b c => seq3 (same_relation_sym (x a b c)))
        | rewrite (fun a b c d => seq3 (same_relation_sym (x a b c d)))
        | rewrite (fun a b c d e => seq3 (same_relation_sym (x a b c d e)))
        | rewrite (fun a b c d e f => seq3 (same_relation_sym (x a b c d e f)))
        | rewrite (seq4 (same_relation_sym x))
        | rewrite (fun a => seq4 (same_relation_sym (x a)))
        | rewrite (fun a b => seq4 (same_relation_sym (x a b)))
        | rewrite (fun a b c => seq4 (same_relation_sym (x a b c)))
        | rewrite (fun a b c d => seq4 (same_relation_sym (x a b c d)))
        | rewrite (fun a b c d e => seq4 (same_relation_sym (x a b c d e)))
        | rewrite (fun a b c d e f => seq4 (same_relation_sym (x a b c d e f)))
        | rewrite (seq5 (same_relation_sym x))
        | rewrite (fun a => seq5 (same_relation_sym (x a)))
        | rewrite (fun a b => seq5 (same_relation_sym (x a b)))
        | rewrite (fun a b c => seq5 (same_relation_sym (x a b c)))
        | rewrite (fun a b c d => seq5 (same_relation_sym (x a b c d)))
        | rewrite (fun a b c d e => seq5 (same_relation_sym (x a b c d e)))
        | rewrite (fun a b c d e f => seq5 (same_relation_sym (x a b c d e f)))
        | rewrite (seq6 (same_relation_sym x))
        | rewrite (fun a => seq6 (same_relation_sym (x a)))
        | rewrite (fun a b => seq6 (same_relation_sym (x a b)))
        | rewrite (fun a b c => seq6 (same_relation_sym (x a b c)))
        | rewrite (fun a b c d => seq6 (same_relation_sym (x a b c d)))
        | rewrite (fun a b c d e => seq6 (same_relation_sym (x a b c d e)))
        | rewrite (fun a b c d e f => seq6 (same_relation_sym (x a b c d e f)))
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
        | rewrite (sin5 x) at 1
        | rewrite (fun a => sin5 (x a)) at 1
        | rewrite (fun a b => sin5 (x a b)) at 1
        | rewrite (fun a b c => sin5 (x a b c)) at 1
        | rewrite (fun a b c d => sin5 (x a b c d)) at 1
        | rewrite (fun a b c d e => sin5 (x a b c d e)) at 1
        | rewrite (fun a b c d e f => sin5 (x a b c d e f)) at 1
        | rewrite (sin6 x) at 1
        | rewrite (fun a => sin6 (x a)) at 1
        | rewrite (fun a b => sin6 (x a b)) at 1
        | rewrite (fun a b c => sin6 (x a b c)) at 1
        | rewrite (fun a b c d => sin6 (x a b c d)) at 1
        | rewrite (fun a b c d e => sin6 (x a b c d e)) at 1
        | rewrite (fun a b c d e f => sin6 (x a b c d e f)) at 1
        ].

Tactic Notation "sin_rewrite" "!" uconstr(x) :=
  sin_rewrite x; repeat sin_rewrite x.

Tactic Notation "sin_rewrite" "?" uconstr(x) :=
  repeat sin_rewrite x.

Lemma rewrite_trans A (r: relation A) :
  transitive r -> r ⨾ r ⊆ r.
Proof.
  unfold inclusion, seq; ins; desf; eauto.
Qed.

Lemma rewrite_trans_seq_cr_l A (r: relation A) :
  transitive r -> r^? ⨾ r ⊆ r.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto.
Qed.

Lemma rewrite_trans_seq_cr_r A (r: relation A) :
  transitive r -> r ⨾ r^? ⊆ r.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto.
Qed.

Lemma rewrite_trans_seq_cr_cr A (r: relation A) :
  transitive r -> r^? ⨾ r^? ⊆ r^?.
Proof.
  unfold inclusion, seq, clos_refl; ins; desf; eauto.
Qed.

Lemma transitiveI A (r: relation A) :
  inclusion (r ⨾ r) r <-> transitive r.
Proof.
  red; splits; unfold transitive, inclusion, seq; ins; desf; eauto.
Qed.

Ltac simpl_rels :=
  rewrite ?eqv_empty, ?seq_false_l, ?seq_false_r, ?seq_id_l, ?seq_id_r, ?seqA; seq_rewrite ? seq_eqvK.

Ltac rels :=
  repeat first [progress autorewrite with hahn |
                seq_rewrite seq_eqvK |
                seq_rewrite ct_cr | seq_rewrite ct_rt |
                seq_rewrite rt_cr | seq_rewrite rt_ct | seq_rewrite rt_rt |
                seq_rewrite cr_ct | seq_rewrite cr_rt |
                seq_rewrite <- ct_end | seq_rewrite <- ct_begin ];
    try done; eauto 3 with hahn.

Ltac relsf :=
  repeat first [progress autorewrite with hahn |
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
                progress autorewrite with hahn hahn_full ];
    try done; eauto 3 with hahn.

Hint Resolve eq_in_l eq_in_r rt_rt ct_rt rt_ct cr_ct ct_cr cr_rt rt_cr ct_begin ct_end : hahn_full.
Hint Resolve inclusion_seq_eqv_r inclusion_seq_eqv_l clos_rt_idempotent inclusion_t_rt : hahn_full.
Hint Resolve inclusion_eqv_rel_true inclusion_minus_rel rewrite_trans : hahn_full.

Hint Resolve pow_rel_mori : hahn.


(** Helpful tactics for inclusions *)

Ltac apply_unionL_once := 
  first [apply irreflexive_union; split |
         apply inclusion_union_l | apply inclusion_bunion_l; intros | 
         apply set_subset_union_l; split | apply set_subset_bunion_l; intros].

Tactic Notation "unionL" := repeat apply_unionL_once. 

Tactic Notation "unionR" tactic(dir) :=  
  first [apply inclusion_union_r | apply set_subset_union_r]; dir.

Tactic Notation "unionR" tactic(dir) "->" tactic(dir') :=  
  unionR dir; unionR dir'.

Tactic Notation "unionR" tactic(dir) "->" tactic(dir') "->" tactic(dir'') := 
  unionR dir; unionR dir'; unionR dir''.

Tactic Notation "unionR" tactic(dir) "->" tactic(dir') "->" tactic(dir'') "->" tactic(dir''') := 
  unionR dir; unionR dir'; unionR dir''; unionR dir'''.

Ltac hahn_rel :=
  rels;
  try match goal with |- (_ ≡ _) => split end;
  unionL; eauto 8 with hahn.

Ltac hahn_frame_r :=
  rewrite <- ?seqA; apply inclusion_seq_mon; [|reflexivity]; rewrite ?seqA.

Ltac hahn_frame_l :=
  rewrite ?seqA; apply inclusion_seq_mon; [reflexivity|].

Ltac hahn_frame :=
  rewrite <- ?seqA;
  repeat (
      match goal with
      | |- inclusion _ (_ ⨾ clos_refl_trans _) => fail 1
      | |- inclusion _ (_ ⨾ clos_trans _) => fail 1
      | |- _ => apply inclusion_seq_mon; [|reflexivity]
      end);
  rewrite ?seqA;
  repeat (
      match goal with
      | |- inclusion _ (clos_refl_trans _ ⨾ _) => fail 1
      | |- inclusion _ (clos_trans _ ⨾ _) => fail 1
      | |- _ => apply inclusion_seq_mon; [reflexivity|]
      end);
  try solve [ apply inclusion_seq_l; try done; auto with hahn
            | apply inclusion_seq_r; try done; auto with hahn].

(** Rewrite with proof search *)

Tactic Notation "arewrite" uconstr(EQ) :=
  let H := fresh in
  first [assert (H: EQ) |
    let typ1 := fresh in let binder1 := fresh in
    evar (typ1 : Type); evar (binder1 : typ1);
    first [assert (H: EQ binder1); subst binder1 typ1 |
      let typ2 := fresh in let binder2 := fresh in
      evar (typ2 : Type); evar (binder2 : typ2);
      assert (H: EQ binder1 binder2); subst binder1 typ1 binder2 typ2]]; cycle 1;
  [ first [seq_rewrite H|sin_rewrite H]; clear H; rewrite ?seqA
  | eauto 4 with hahn hahn_full; try done ]; cycle 1.

Tactic Notation "arewrite" uconstr(EQ) "at" int_or_var(index) :=
  let H := fresh in
  assert (H : EQ); [eauto 4 with hahn hahn_full; try done|
                    rewrite H at index; clear H; rewrite ?seqA].

Tactic Notation "arewrite" uconstr(EQ) "by" tactic(t) :=
  let H := fresh in
    assert (H: EQ) by (by t; eauto with hahn hahn_full);
    first [seq_rewrite H|sin_rewrite H]; clear H; rewrite ?seqA; try done.

Tactic Notation "arewrite" uconstr(EQ) "at" int_or_var(index) "by" tactic(t) :=
  let H := fresh in
    assert (H : EQ) by (by t; eauto with hahn hahn_full);
    rewrite H at index; clear H; rewrite ?seqA; try done.

Tactic Notation "arewrite" "!" uconstr(EQ) :=
  let H := fresh in
  first [assert (H: EQ) |
    let typ1 := fresh in let binder1 := fresh in
    evar (typ1 : Type); evar (binder1 : typ1);
    first [assert (H: EQ binder1); subst binder1 typ1 |
      let typ2 := fresh in let binder2 := fresh in
      evar (typ2 : Type); evar (binder2 : typ2);
      assert (H: EQ binder1 binder2); subst binder1 typ1 binder2 typ2]]; cycle 1;
  [ first [seq_rewrite !H|sin_rewrite !H]; clear H; rewrite ?seqA
  | eauto 4 with hahn hahn_full; try done ]; cycle 1.


Tactic Notation "arewrite_false" constr(exp) :=
  arewrite (exp ≡ fun _ _ => False); [split;[|vauto]|].
Tactic Notation "arewrite_false" "!" constr(exp) :=
  arewrite !(exp ≡ fun _ _ => False); [split;[|vauto]|].
Tactic Notation "arewrite_false" constr(exp) "at" int_or_var(index) :=
  arewrite (exp ≡ fun _ _ => False) at index; [split;[|vauto]|].
Tactic Notation "arewrite_id" constr(exp) :=
  arewrite (exp ⊆ ⦗fun _ => True⦘).
Tactic Notation "arewrite_id" "!" constr(exp) :=
  arewrite !(exp ⊆ ⦗fun _ => True⦘).
Tactic Notation "arewrite_id" constr(exp) "at" int_or_var(index) :=
  arewrite (exp ⊆ ⦗fun _ => True⦘) at index.

(** Unfolding of relational operations **)

Tactic Notation "unfolder_prepare" := 
  rewrite ?seqA;
  repeat hahn_rewrite seq_eqv;
  repeat hahn_seq_rewrite seq_eqv;
  repeat hahn_rewrite seq_eqv_lr;
  repeat hahn_rewrite seq_eqv_r;
  repeat hahn_rewrite seq_eqv_l;
  repeat hahn_rewrite <- id_union.

Tactic Notation "unfolder_prepare"  "in" hyp(H) := 
  rewrite ?seqA in H;
  repeat hahn_rewrite seq_eqv in H;
  repeat hahn_rewrite seq_eqv_lr in H;
  repeat hahn_rewrite seq_eqv_r in H;
  repeat hahn_rewrite seq_eqv_l in H;
  repeat hahn_rewrite <- id_union in H.

Tactic Notation "unfolder" := 
  unfolder_prepare; repeat autounfold with unfolderDb.

Tactic Notation "unfolder" "in" hyp(H) := 
  unfolder_prepare in H; autounfold with unfolderDb in H.

Tactic Notation "unfolder" "in" "*" "|-" :=
  repeat match goal with | [H:_ |- _] => progress unfolder in H
end.

Tactic Notation "unfolder" "in" "*" :=
  unfolder; unfolder in * |-.

(** basic_solver tactic **)
Tactic Notation "basic_solver" int_or_var(index) :=
  by ( rewrite ?rtE; unfolder; splits; ins; desf; eauto index; done).

Tactic Notation "basic_solver" :=
  basic_solver 4.

(** Case analysis *)

Tactic Notation "case_union"  uconstr(x) uconstr(y) :=
  first [rewrite seq_union_l with (r1 := x) (r2 := y)
        |rewrite seq_union_r with (r1 := x) (r2 := y)].
  
Tactic Notation "case_union_2"  uconstr(x) uconstr(y) :=
  simpl_rels;
  (repeat(
    case_union x y +
    case_union x (y ⨾ _) +
    case_union x (_ ⨾ y) +
    case_union x (_ ⨾ y ⨾ _) +
    case_union x (_ ⨾ _ ⨾ y) +
    case_union x (_ ⨾ _ ⨾ y ⨾ _) +
    case_union x (_ ⨾ _ ⨾ _ ⨾ y) +
    case_union x (_ ⨾ _ ⨾ _ ⨾ y ⨾ _) +
    case_union x (_ ⨾ _ ⨾ _ ⨾ _ ⨾ y) +
    case_union x (_ ⨾ _ ⨾ _ ⨾ _ ⨾ y ⨾ _) +
    case_union x (_ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ y) +
    case_union x (_ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ y ⨾ _) +
    case_union x (_ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ y) +
    case_union x (_ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ y ⨾ _) +
    case_union (x ⨾ _) y +
    case_union (_ ⨾ x) y +
    case_union (_ ⨾ x ⨾ _) y +
    case_union (_ ⨾ _ ⨾ x) y +
    case_union (_ ⨾ _ ⨾ x ⨾ _) y +
    case_union (_ ⨾ _ ⨾ _ ⨾ x) y +
    case_union (_ ⨾ _ ⨾ _ ⨾ x ⨾ _) y +
    case_union (_ ⨾ _ ⨾ _ ⨾ _ ⨾ x) y +
    case_union (_ ⨾ _ ⨾ _ ⨾ _ ⨾ x ⨾ _) y +
    case_union (_ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ x) y +
    case_union (_ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ x ⨾ _) y +
    case_union (_ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ x) y +
    case_union (_ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ _ ⨾ x ⨾ _) y
  ); unionL; [simpl_rels|]).

Tactic Notation "case_union_3" uconstr(x) uconstr(y) uconstr(z) :=
  simpl_rels; case_union_2 _ z; [case_union_2 x y|].

Tactic Notation "case_union_4" uconstr(x) uconstr(y) uconstr(z) uconstr(w) :=
  simpl_rels; case_union_2 _ w; [case_union_3 x y z|].

Tactic Notation "case_union_5" uconstr(x) uconstr(y) uconstr(z) uconstr(w) uconstr(t) :=
  simpl_rels; case_union_2 _ t; [case_union_4 x y z w|].

Tactic Notation "case_refl"  uconstr(x) "at" int(index) :=
  simpl_rels; rewrite crE with (r := x) at index; case_union_2 _ x.

Tactic Notation "case_refl"  uconstr(x) := case_refl x at 1.
