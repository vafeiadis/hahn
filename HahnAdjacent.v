Require Import HahnBase HahnRelationsBasic.
Require Import HahnRewrite.
Require Import Setoid.
Set Implicit Arguments.

Section Defs.
  Variable A : Type.

  Definition adjacent A (rel: relation A) a b :=
    ⟪ LA_ac : forall c, rel b c -> rel a c ⟫ /\ 
    ⟪ LA_ca : forall c, rel c b -> rel^? c a ⟫ /\
    ⟪ LA_cb : forall c, rel c a -> rel c b ⟫ /\
    ⟪ LA_bc : forall c, rel a c -> rel^? b c ⟫.

  Definition adjacentW A (rel: relation A) a b :=
    ⟪ LA_ac : forall c, rel b c -> rel a c ⟫ /\ 
    ⟪ LA_cb : forall c, rel c a -> rel c b ⟫.
End Defs.

Lemma adjacent_weaken A (rel: relation A) a b : 
  adjacent rel a b -> adjacentW rel a b.
Proof. unfold adjacent, adjacentW; intuition. Qed.

Lemma immediate_adjacent A (r: relation A) (dom: A -> Prop)
  (STOT1: ⦗dom⦘ ⨾ r ⨾ r^{-1} ⊆ r^? ∪ r^{-1})
  (STOT2: r^{-1} ⨾ ⦗dom⦘ ⨾ r ⊆ r^? ∪ r^{-1})
  (T: transitive r) (IRR: irreflexive r):  
⦗dom⦘ ⨾ immediate r ≡ ⦗dom⦘ ⨾ (adjacent r ∩ r).
Proof.
unfold adjacent; unfolder in *; ins.
split; splits; desf; ins; try done.
1, 3: by eauto with hahn.
assert (AA: dom x /\ (exists z : A, r x z /\ r c z) ) by eauto.
by specialize (STOT1 x c AA) ; desf; [auto|exfalso; eauto |econs].
assert (AA: (exists z : A, r z y /\ dom z /\ r z c) ) by eauto.
by specialize (STOT2 y c AA) ; desf; [auto|econs | exfalso; eauto].
apply LA_bc in R1; apply LA_ca in R2; desf; eapply IRR, T; eauto.
Qed.

Lemma adjacent_unique1 A (r: relation A) (ACYC: acyclic r):
  forall a b c : A,  r a b ->  r a c -> adjacent r a b -> adjacent r a c -> b = c.
Proof.
ins; unfold adjacent in *; desc.
assert (r^? b c) by eauto.
assert (r^? c b) by eauto.
unfolder in *; desf.
by exfalso; eapply ACYC; eapply t_trans; econs; eauto.
Qed.

Lemma adjacent_unique2 A (r: relation A) (ACYC: acyclic r):
  forall a b c : A,  r b a ->  r c a -> adjacent r b a -> adjacent r c a -> b = c.
Proof.
ins; unfold adjacent in *; desc.
assert (r^? b c) by eauto.
assert (r^? c b) by eauto.
unfolder in *; desf.
by exfalso; eapply ACYC; eapply t_trans; econs; eauto.
Qed.
