Require Import NPeano HahnBase HahnList HahnRelationsBasic.

Set Implicit Arguments.
  
Section BEFORE.

  Variable A : Type.
  Implicit Type l : list A.

  Definition list_before (l : list A) (x y : A) : Prop :=
    NoDup l /\ exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3.

  Lemma list_before_nil (x y : A) : ~ list_before nil x y.
  Proof.
    unfold list_before; intro; desf; destruct l1; ins; desf.
  Qed.

  Lemma list_before_singl (a x y : A) : ~ list_before (a :: nil) x y.
  Proof.
    unfold list_before; intro; desf; destruct l1; ins; desf.
    destruct l2; ins; desf.
    destruct l1; ins; desf.
  Qed.

  Lemma list_before_rev l x y : list_before (rev l) x y <-> list_before l y x.
  Proof.
    unfold list_before; rewrite nodup_rev; intuition; desf.
    - apply (f_equal (@rev _)) in H1.
      repeat first [rewrite rev_involutive in * | rewrite rev_app_distr in *; ins ].   
      desf; rewrite <- !app_assoc; ins; eauto.
    - repeat (rewrite rev_app_distr; ins).
      rewrite <- !app_assoc; ins; eauto.
  Qed.
  
  Lemma list_before_app l l' x y :
    list_before (l ++ l') x y <->
    NoDup (l ++ l') /\
    (list_before l x y \/ list_before l' x y
     \/ In x l /\ In y l').
  Proof.
    unfold list_before; intuition; desf.
    all: repeat (rewrite <- app_assoc in *; ins); eauto.
    2: by eexists (_ ++ _), _, _; rewrite app_assoc.
    2: apply in_split in H; desf; apply in_split in H2; desf.
    2: exists l1, (l2 ++ l0), l3; repeat (rewrite <- app_assoc; ins). 
    rewrite nodup_app in *; desf.
    apply list_app_eq_app in H1; desf; eauto 8.
    destruct lr; ins; desf; rewrite ?app_nil_r in *.
    right; left; split; eauto; exists nil; ins; eauto.
    apply list_app_eq_app in H1; desf; eauto 8 with hahn.
    destruct lr0; ins; desf; rewrite ?app_nil_r in *; eauto 8 with hahn.
  Qed.

  Lemma list_before_cons a l x y :
    list_before (a :: l) x y
    <-> a = x /\ ~ In x l /\ In y l /\ NoDup l \/ ~ In a l /\ list_before l x y.
  Proof.
    rewrite list_before_app with (l := a :: nil) (l' := l); ins; rewrite nodup_cons in *.
    split; ins; desf; splits; eauto with hahn;
      try (edestruct list_before_singl; eassumption).
    red in H0; desf.
  Qed.      

  Lemma list_before_hd l x y :
    list_before (x :: l) x y <-> ~ In x l /\ In y l /\ NoDup l.
  Proof.
    rewrite list_before_cons; unfold list_before; intuition; desf; auto with hahn.
  Qed.

  Lemma list_before_cons_other a l x y (NEQ: a <> x) :
    list_before (a :: l) x y <-> list_before l x y /\ ~ In a l.
  Proof.
    rewrite list_before_cons; intuition.
  Qed.

  Lemma list_before_snoc a l x y :
    list_before (l ++ a :: nil) x y
    <-> a = y /\ In x l /\ ~ In y l /\ NoDup l \/ ~ In a l /\ list_before l x y.
  Proof.
    rewrite list_before_app; ins.
    rewrite nodup_app, disjoint_one_r in *.
    split; ins; desf; splits; eauto with hahn;
      try (edestruct list_before_singl; eassumption).
    red in H0; desf.
  Qed.

  Lemma list_before_last l x y :
    list_before (l ++ y :: nil) x y <-> In x l /\ ~ In y l /\ NoDup l.
  Proof.
    rewrite list_before_snoc; unfold list_before; intuition; desf; auto with hahn.
  Qed.

  Lemma list_before_snoc_other a l x y (NEQ: a <> y) :
    list_before (l ++ a :: nil) x y <-> list_before l x y /\ ~ In a l.
  Proof.
    rewrite list_before_snoc; intuition.
  Qed.

  
  Lemma list_before_irr l : irreflexive (list_before l).
  Proof.
    unfold list_before; red; ins; desf.
    rewrite nodup_app, nodup_cons in *; desf; eauto with hahn.
  Qed.

  Lemma list_before_neq l x y : list_before l x y -> x <> y.
  Proof.
    unfold list_before; red; ins; desf.
    rewrite nodup_app, nodup_cons in *; desf; eauto with hahn.
  Qed.

  Lemma list_before_trans l x y z : list_before l x y -> list_before l y z -> list_before l x z.
  Proof.
    unfold list_before; ins; desf; split; ins.
    clear H0; rename H1 into X.
    repeat first [rewrite nodup_app in * | rewrite nodup_cons in *]; desf.
    apply list_app_eq_app in X; desf.
      destruct lr; ins; desf; try solve [exfalso; eauto with hahn].
      by rewrite H7; eexists l0, (lr ++ y :: l2), l3; ins; rewrite <- app_assoc.
    destruct lr; ins; desf; exfalso; eauto with hahn.
  Qed.

  Lemma list_before_antisymm l x y : list_before l x y -> list_before l y x -> False.
  Proof.
    eby ins; eapply list_before_irr, list_before_trans.
  Qed.

  Lemma list_before_nodup l x y : list_before l x y -> NoDup l.
  Proof.
    unfold list_before; tauto.
  Qed.

  Lemma list_before_in l x y : list_before l x y -> In x l /\ In y l.
  Proof.
    unfold list_before; ins; desf; split; auto with hahn.
  Qed.

  Lemma list_before_in1 l x y : list_before l x y -> In x l.
  Proof.
    unfold list_before; ins; desf; auto with hahn.
  Qed.

  Lemma list_before_in2 l x y : list_before l x y -> In y l.
  Proof.
    unfold list_before; ins; desf; auto with hahn.
  Qed.

  Lemma list_before_mid_l l l' x y :
    list_before (l ++ x :: l') x y <-> NoDup (l ++ x :: l') /\ In y l'.
  Proof.
    rewrite list_before_app, list_before_hd; split; ins; desf; splits;
    rewrite nodup_app, nodup_cons in *; desf; eauto;
      try solve [edestruct H2; ins; eauto using list_before_in1].
  Qed.

  Lemma list_before_mid_r l l' x y :
    list_before (l ++ y :: l') x y <-> NoDup (l ++ y :: l') /\ In x l.
  Proof.
    rewrite list_before_app, list_before_cons; split; ins; desf; splits; ins;
      eauto using list_before_in1.
    edestruct H0; ins; eauto using list_before_in2.
  Qed.

  Lemma list_before_filter (f : A -> bool) l x y :
    list_before l x y -> f x -> f y -> list_before (filter f l) x y.
  Proof.
    unfold list_before; ins; desf; splits; eauto with hahn.
    repeat (rewrite filter_app; ins); desf; eauto.
  Qed.

  Lemma list_before_filterP (f : A -> Prop) l x y :
    list_before l x y -> f x -> f y -> list_before (filterP f l) x y.
  Proof.
    unfold list_before; ins; desf; splits; eauto with hahn.
    repeat (rewrite filterP_app; ins); desf; eauto.
  Qed.

  Lemma filter_eq_app (f : A -> bool) l l1 l2 :
    filter f l = l1 ++ l2 ->
    exists l1' l2',
      l = l1' ++ l2' /\ filter f l1' = l1 /\ filter f l2' = l2.
  Proof.
    revert l1 l2; induction l; ins.
    destruct l1, l2; ins; exists nil, nil; ins.
    desf.
      destruct l1; [destruct l2|]; ins; desf.
        by eexists nil, _; splits; try done; ins; desf.
      by apply IHl in H; desf; exists (a0 :: l1'), l2'; ins; desf.
    apply IHl in H; desf; exists (a :: l1'), l2'; ins; desf.
  Qed.

  Lemma filterP_eq_app (f : A -> Prop) l l1 l2 :
    filterP f l = l1 ++ l2 ->
    exists l1' l2',
      l = l1' ++ l2' /\ filterP f l1' = l1 /\ filterP f l2' = l2.
  Proof.
    revert l1 l2; induction l; ins.
    destruct l1, l2; ins; exists nil, nil; ins.
    desf.
      destruct l1; [destruct l2|]; ins; desf.
        by eexists nil, _; splits; try done; ins; desf.
      by apply IHl in H; desf; exists (a0 :: l1'), l2'; ins; desf.
    apply IHl in H; desf; exists (a :: l1'), l2'; ins; desf.
  Qed.

  Lemma filter_eq_app_cons (f : A -> bool) l l1 a l2 :
    filter f l = l1 ++ a :: l2 ->
    exists l1' l2',
      l = l1' ++ a :: l2' /\ filter f l1' = l1 /\ filter f l2' = l2.
  Proof.
    revert l1 l2; induction l; ins.
    destruct l1, l2; ins; exists nil, nil; ins.
    desf.
      destruct l1; ins; desf.
        by eexists nil, l; splits; try done; ins; desf.
      by apply IHl in H; desf; exists (a1 :: l1'), l2'; ins; desf.
    apply IHl in H; desf; exists (a0 :: l1'), l2'; ins; desf.
  Qed.

  Lemma filterP_eq_app_cons (f : A -> Prop) l l1 a l2 :
    filterP f l = l1 ++ a :: l2 ->
    exists l1' l2',
      l = l1' ++ a :: l2' /\ filterP f l1' = l1 /\ filterP f l2' = l2.
  Proof.
    revert l1 l2; induction l; ins.
    destruct l1, l2; ins; exists nil, nil; ins.
    desf.
      destruct l1; ins; desf.
        by eexists nil, l; splits; try done; ins; desf.
      by apply IHl in H; desf; exists (a1 :: l1'), l2'; ins; desf.
    apply IHl in H; desf; exists (a0 :: l1'), l2'; ins; desf.
  Qed.
  
  Lemma list_before_filter_inv (f : A -> bool) l x y :
    list_before (filter f l) x y -> NoDup l -> list_before l x y.
  Proof.
    unfold list_before; ins; desf; splits; ins.
    apply filter_eq_app_cons in H1; desf.
    apply filter_eq_app_cons in H3; desf; eauto.
  Qed.

  Lemma list_before_filterP_inv (f : A -> Prop) l x y :
    list_before (filterP f l) x y -> NoDup l -> list_before l x y.
  Proof.
    unfold list_before; ins; desf; splits; ins.
    apply filterP_eq_app_cons in H1; desf.
    apply filterP_eq_app_cons in H3; desf; eauto.
  Qed.

  Lemma list_before_nth l i j d :
    NoDup l -> i < j < length l -> list_before l (nth i l d) (nth j l d).
  Proof.
    unfold list_before; split; ins; desc.
    eapply nth_split with (d := d) in H1; desf.
    eapply nth_split with (d := d) in H0; desf.
    rewrite H0 in H1 at 1; rewrite <- app_assoc in H1; ins.
    do 3 eexists.
    rewrite H1 at 1; f_equal; f_equal.
    rewrite H1, nth_app, Nat.sub_diag; desf.
    edestruct Nat.lt_irrefl; eauto.
  Qed.
  
End BEFORE.
