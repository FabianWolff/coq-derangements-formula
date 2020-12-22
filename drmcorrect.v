Require Import Lia List FMapWeakList OrderedTypeEx Compare_dec.
Import ListNotations.

Module Import Map := FMapWeakList.Make (Nat_as_OT).

Notation nmap := t.
Notation card := (@cardinal nat).
Notation find := (@find nat).
Notation In := (@In nat).
Notation Empty := (@Empty nat).
Notation eq_dec := (Nat_as_OT.eq_dec).
Notation MapsTo := (@MapsTo nat).

Definition drm_inject_step (m: nmap nat) (last: nat) (k v: nat): nmap nat :=
  (add last v (add k last m)).

Definition drm_inject_fold_step (m: nmap nat) (last: nat) (k v: nat) (a: list (nmap nat)): list (nmap nat) :=
  a ++ [drm_inject_step m last k v].

(* For all keys x in m, if x maps to y, create a new map where x -> last -> y. *)
Definition drm_inject (m: nmap nat) (last: nat): list (nmap nat) :=
  fold (drm_inject_fold_step m last) m [].

Definition drm_add_loop_simple (m: nmap nat) (last1 last2: nat): nmap nat :=
  (add last1 last2 (add last2 last1 m)).

Definition drm_add_loop_step (m: nmap nat) (last1 last2: nat) (k' k v: nat): nmap nat :=
  add k' last1 (add last1 v (add k last2 (add last2 k m))).

Definition drm_add_loop_fold_step (m: nmap nat) (last1 last2: nat) (k' k: nat) (a: list (nmap nat)): list (nmap nat) :=
  a ++ match (find k m) with
       | Some v => [(drm_add_loop_step m last1 last2 k' k v)]
       | None => []
       end.

(* For a derangement of size n, create a derangement of size n+2 where last2 *)
(* is in a direct loop (e.g. exists x, last2 -> x /\ x -> last2).            *)
Definition drm_add_loop (m: nmap nat) (last1 last2: nat): list (nmap nat) :=
  (drm_add_loop_simple m last1 last2)
    :: fold (drm_add_loop_fold_step m last1 last2) m [].

Definition drm (m: nmap nat) (n: nat) :=
  card m = n /\
  (forall k k' v, MapsTo k v m -> MapsTo k' v m -> k = k') /\
  (forall k v, MapsTo k v m -> k <> v /\ k < n /\ v < n) /\
  (forall k, k < n -> (exists v, MapsTo k v m) /\
                      (exists k', MapsTo k' k m)).

Fact card_zero_iff: forall m, cardinal m = 0 <-> Empty m.
Proof.
  destruct m. induction this0.
  - split; intros.
    + unfold Empty. unfold Raw.Empty. intros. intro.
      inversion H0.
    + unfold card. simpl. auto.
  - split; intros.
    + unfold card in H. simpl in H. lia.
    + unfold Empty in H. unfold Raw.Empty in H.
      destruct a as [a1 a2].
      pose proof (H a1 a2). simpl in H0.
      exfalso. apply H0. pose proof add_1.
      unfold Raw.PX.MapsTo. constructor. reflexivity.
Qed.

Fact MapsTo_In: forall m k v, MapsTo k v m -> In k m.
Proof.
  intros. unfold In. unfold Raw.PX.In.
  eexists. apply H.
Qed.

Fact In_MapsTo: forall m k, In k m -> exists v, MapsTo k v m.
Proof.
  intros. unfold In in H. unfold Raw.PX.In in H.
  destruct H. eexists. apply H.
Qed.

Fact Empty_In: forall m, (forall k, ~ In k m) <-> Empty m.
Proof.
  intros. split; intros.
  - unfold Empty. unfold Raw.Empty. intros. intro.
    apply MapsTo_In in H0. apply H in H0. apply H0.
  - intro. unfold Empty in H. unfold Raw.Empty in H.
    apply In_MapsTo in H0. destruct H0.
    pose proof (H k x). apply H1. apply H0.
Qed.

Fact drm_zero_iff: forall m, drm m 0 <-> Empty m.
Proof.
  intros. split; intros.
  - unfold drm in H. destruct H. apply card_zero_iff in H. auto.
  - unfold drm. split; try split.
    + apply card_zero_iff. auto.
    + intros. contradict H. intro. rewrite <- Empty_In in H.
      apply MapsTo_In in H0. pose proof (H k). contradiction.
    + split; intros. contradict H. intro. rewrite <- Empty_In in H.
      apply MapsTo_In in H0. pose proof (H k). auto. lia.
Qed.

Fact drm_In_iff: forall m n, drm m n -> (forall k, k < n <-> In k m).
Proof.
  intros. split; intros.
  - unfold drm in H. destruct H. apply H1 in H0.
    destruct H0 as [[? ?] [? ?]]. eapply MapsTo_In. eauto.
  - unfold drm in H. destruct H as [? [? [? ?]]].
    apply In_MapsTo in H0. destruct H0.
    pose proof (H2 k x H0). destruct H4 as [? [? ?]]. tauto.
Qed.

Corollary drm_not_In: forall m n, drm m n -> ~ In n m.
Proof.
  intros. eapply drm_In_iff in H. intro. apply H in H0. lia.
Qed.

Fact drm_MapsTo: forall m n k v, drm m n -> MapsTo k v m -> (k <> v /\ k < n /\ v < n).
Proof.
  intros. unfold drm in H.
  apply H in H0. lia.
Qed.

Fact drm_lt_MapsTo_1: forall m n k, drm m n -> k < n -> exists v, MapsTo k v m.
Proof.
  intros. unfold drm in H.
  apply H in H0. destruct H0. assumption.
Qed.

Fact drm_lt_MapsTo_2: forall m n v, drm m n -> v < n -> exists k, MapsTo k v m.
Proof.
  intros. unfold drm in H.
  apply H in H0. destruct H0. assumption.
Qed.

Fact SetoidList_NoDupA_cons_rev: forall {X} x xs,
    SetoidList.NoDupA (Raw.PX.eqk (elt:=X)) (x :: xs) ->
    SetoidList.NoDupA (Raw.PX.eqk (elt:=X)) (xs).
Proof.
  intros. inversion H; subst. assumption.
Qed.

Fact SetoidList_NoDupA_cons_rev2: forall x y xs,
    SetoidList.NoDupA (Raw.PX.eqk (elt:=nat)) (x :: y :: xs) ->
    SetoidList.NoDupA (Raw.PX.eqk (elt:=nat)) (x :: xs).
Proof.
  intros. inversion H; subst. inversion H3; subst.
  constructor.
  - contradict H2. constructor 2. assumption.
  - assumption.
Qed.

Fact In_cons_neq_exists: forall k this0 n0 n1 NoDup0,
    k <> n0 ->
    In k {| this := (n0, n1) :: this0; NoDup := NoDup0 |}
    -> exists H, In k {| this := this0; NoDup := H |}.
Proof.
  intros k this0. generalize dependent k. induction this0; intros.
  - unfold In in H0. unfold Raw.PX.In in H0. destruct H0.
    inversion H0; subst.
    + inversion H2. simpl in *. subst. lia.
    + inversion H2.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    exists H1. unfold In in H0. unfold Raw.PX.In in H0.
    destruct H0. simpl in H0. inversion H0; subst.
    + inversion H3. simpl in *. lia.
    + compute. exists x. apply H3.
Qed.

Fact In_add_iff: forall m k k' v, (In k (add k' v m)) <-> (k = k' \/ In k m).
Proof.
  destruct m eqn:Em. induction this0; intros.
  - split; intro.
    + compute in H. destruct H. inversion H; subst.
      * left. destruct H1. auto.
      * inversion H1.
    + destruct H.
      * subst k'. unfold In. unfold Raw.PX.In.
        exists v. apply add_1. auto.
      * inversion H. inversion H0.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    pose proof (IHthis0 H). split; intro.
    + unfold In in H1. unfold Raw.PX.In in H1. destruct H1.
      destruct (Nat_as_OT.eq_dec k k').
      * left. auto.
      * right. assert (k' <> k); try lia.
        eapply add_3 in H2; try apply H1.
        eapply MapsTo_In. apply H2.
    + destruct H1.
      * subst k'. unfold In. unfold Raw.PX.In. eexists.
        apply add_1. auto.
      * { destruct (Nat_as_OT.eq_dec k k').
          - subst k'. unfold In. unfold Raw.PX.In. eexists. apply add_1. auto.
          - destruct a. simpl in H1.
            unfold In. unfold Raw.PX.In.
            destruct (Nat_as_OT.eq_dec k n0).
            + exists n1. simpl.
              destruct (Nat_as_OT.eq_dec k' n0); try lia.
              subst k. constructor. reflexivity.
            + pose proof (In_cons_neq_exists _ _ _ _ _ n2 H1). destruct H2.
              unfold In in H2. unfold Raw.PX.In in H2. destruct H2.
              exists x0. eapply add_2. lia. constructor 2.
              apply H2. }
Qed.

Fact card_drm: forall m n, drm m n -> card m = n.
Proof.
  intros. unfold drm in H. destruct H. assumption.
Qed.

Fact card_add_le: forall m k v, card m <= card (add k v m).
Proof.
  destruct m. induction this0; intros.
  - compute. lia.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    pose proof (IHthis0 H k v). unfold card. destruct a as [k' v'].
    simpl. unfold card in H0. simpl in H0.
    destruct (Nat_as_OT.eq_dec k k'); simpl; lia.
Qed.

Fact card_add_le_S: forall m k v, card (add k v m) <= S (card m).
Proof.
  destruct m. induction this0; intros.
  - compute. lia.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    pose proof (IHthis0 H k v). destruct a as [k' v'].
    unfold card in *. simpl. simpl in H0.
    destruct (eq_dec k k'); simpl; lia.
Qed.

Fact card_add_In: forall m k v, In k m <-> card (add k v m) = card m.
Proof.
  destruct m. induction this0; intros.
  - split; intro.
    + inversion H. inversion H0.
    + inversion H.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    pose proof (IHthis0 H).
    split; intro.
    + destruct a as [a1 a2].
      destruct (Nat_as_OT.eq_dec k a1).
      * unfold card. simpl. destruct (Nat_as_OT.eq_dec k a1); try lia.
        reflexivity.
      * { unfold In in H1. unfold Raw.PX.In in H1. destruct H1.
          inversion H1; subst.
          - inversion H3. simpl in *. lia.
          - assert (MapsTo k x {| this := this0; NoDup := H |}).
            { apply H3. }
            apply MapsTo_In in H2. rewrite -> (H0 k v) in H2.
            unfold card. simpl. destruct (Nat_as_OT.eq_dec k a1); try lia.
            unfold card in H2. simpl in H2. rewrite <- H2. simpl.
            reflexivity. }
    + unfold card in H1. simpl in H1. unfold card in H0. simpl in H0.
      destruct a as [a1 a2].
      destruct (Nat_as_OT.eq_dec k a1).
      * unfold In. unfold Raw.PX.In. exists a2.
        subst k. constructor. reflexivity.
      * simpl in H1. inversion H1. apply H0 in H3.
        unfold In in H3. unfold Raw.PX.In in H3. destruct H3.
        unfold In. unfold Raw.PX.In. exists x.
        constructor 2. apply H2.
Qed.

Corollary card_add_not_In: forall m k v, (~ In k m) <-> card (add k v m) = S (card m).
Proof.
  intros. split; intro.
  - pose proof (card_add_le m k v).
    pose proof (card_add_le_S m k v).
    destruct (Nat_as_OT.eq_dec (card m) (card (add k v m))).
    + symmetry in e. apply card_add_In in e. contradiction.
    + lia.
  - intro. rewrite -> card_add_In in H0. rewrite H in H0. lia.
Qed.

Fact In_add: forall m k k' v', In k m -> In k (add k' v' m).
Proof.
  destruct m. destruct this0; intros.
  - inversion H. inversion H0.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    destruct (eq_dec k k').
    + subst k'. unfold In. unfold Raw.PX.In. exists v'.
      apply add_1. auto.
    + rewrite In_add_iff. right. destruct p as [k'' v''].
      destruct (eq_dec k k'').
      * subst k''. unfold In. unfold Raw.PX.In. exists v''.
        simpl. constructor. reflexivity.
      * eapply In_cons_neq_exists in n0. 2: apply H.
        destruct n0. unfold In. unfold Raw.PX.In.
        unfold In in H1. unfold Raw.PX.In in H1. destruct H1.
        exists x0. constructor 2. apply H1.
Qed.

Fact MapsTo_add_eq: forall m k v, MapsTo k v (add k v m).
Proof.
  intros. destruct m. destruct this0.
  - constructor. reflexivity.
  - apply add_1. reflexivity.
Qed.

Fact SetoidList_NoDupA_InA_cons_rev:
  forall [A : Type] [eqA : A -> A -> Prop] [x : A] [l : list A],
    SetoidList.NoDupA eqA (x :: l) -> ~ SetoidList.InA eqA x l.
Proof.
  intros. intro.
  inversion H. contradiction.
Qed.

Fact SetoidList_InA_eqke_eqk:
  forall l k v v',
    SetoidList.InA (Raw.PX.eqke (elt:=nat)) (k, v) l
    -> SetoidList.InA (Raw.PX.eqk (elt:=nat)) (k, v') l.
Proof.
  induction l; intros.
  - inversion H.
  - destruct a as [a0 a1]. inversion H; subst.
    + inversion H1. simpl in *. subst.
      constructor. reflexivity.
    + constructor 2. eapply IHl. apply H1.
Qed.

Corollary SetoidList_not_InA_eqk_eqke:
  forall l k v v',
    (~ SetoidList.InA (Raw.PX.eqk (elt:=nat)) (k, v) l)
    -> (~ SetoidList.InA (Raw.PX.eqke (elt:=nat)) (k, v') l).
Proof.
  intros. intro. apply SetoidList_InA_eqke_eqk with (v':=v) in H0.
  contradiction.
Qed.

Fact MapsTo_eq_v: forall m k v v', MapsTo k v m -> MapsTo k v' m -> v = v'.
Proof.
  destruct m. induction this0; intros.
  - inversion H.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    pose proof (IHthis0 H1) as IH.
    destruct a as [k'' v''].
    destruct (eq_dec k k'').
    + subst k''.
      pose proof (SetoidList_NoDupA_InA_cons_rev NoDup0).
      unfold MapsTo in *. unfold Raw.PX.MapsTo in *.
      inversion H; subst.
      * inversion H4. simpl in *. subst. clear H4 H3.
        { inversion H0; subst.
          - inversion H4. simpl in *. subst. auto.
          - apply SetoidList_InA_eqke_eqk with (v':=v'') in H4.
            contradiction. }
      * apply SetoidList_InA_eqke_eqk with (v':=v'') in H4.
        contradiction.
    + inversion H; subst.
      * inversion H3. simpl in *. subst. lia.
      * { inversion H0; subst.
          - inversion H4. simpl in *. subst. lia.
          - eapply IH in H3. symmetry. apply H3. apply H4. }
Qed.

Fact MapsTo_add_eq_v: forall m k v v', MapsTo k v (add k v' m) -> v = v'.
Proof.
  destruct m. destruct this0; intros.
  - inversion H; subst.
    + inversion H1. simpl in *. lia.
    + inversion H1.
  - pose proof (MapsTo_add_eq {| this := p :: this0; NoDup := NoDup0 |} k v').
    eapply MapsTo_eq_v in H0. 2: apply H. assumption.
Qed.

Lemma drm_MapsTo_inj: forall k k' v m n,
    drm m n -> MapsTo k v m -> MapsTo k' v m -> k = k'.
Proof.
  intros. unfold drm in *. destruct H as [? [? ?]].
  eapply H2; eauto.
Qed.

Lemma drm_inject_one_drm: forall m last,
    drm m last -> forall k v, MapsTo k v m -> drm (drm_inject_step m last k v) (S last).
Proof.
  unfold drm_inject_step.
  intros. unfold drm. split. 2: split.
  - pose proof (card_drm m last H).
    pose proof (MapsTo_In _ _ _ H0).
    pose proof (drm_not_In _ _ H).
    assert (k < last).
    { eapply drm_In_iff in H. rewrite <- H in H2. auto. }
    assert (~ In last (add k last m)).
    { intro. apply In_add_iff in H5. destruct H5; try lia. auto. }
    rewrite card_add_not_In in H5. rewrite H5. apply eq_S.
    rewrite card_add_In in H2. rewrite H2. lia.
  - intros. destruct (eq_dec k0 k'). auto.
    destruct (eq_dec k0 last).
    + subst k0. apply add_3 in H2; try lia. apply MapsTo_add_eq_v in H1. subst v0.
      destruct (eq_dec k' k). subst k'.
      * apply MapsTo_add_eq_v in H2. eapply drm_MapsTo in H0; eauto. lia.
      * apply add_3 in H2; try lia. contradict n0. eapply drm_MapsTo_inj; eauto.
    + apply add_3 in H1; try lia. destruct (eq_dec k0 k).
      * subst k0. apply MapsTo_add_eq_v in H1. subst v0.
        { destruct (eq_dec k' last).
          - subst k'. apply MapsTo_add_eq_v in H2. subst v.
            eapply drm_MapsTo in H0; eauto. lia.
          - apply add_3 in H2; try lia. apply add_3 in H2; try lia.
            eapply drm_MapsTo in H2; eauto. lia. }
      * apply add_3 in H1; try lia.
        { destruct (eq_dec k' last).
          - subst k'. apply MapsTo_add_eq_v in H2. subst v0.
            contradict n1. eapply drm_MapsTo_inj; eauto.
          - apply add_3 in H2; try lia. destruct (eq_dec k' k).
            + subst k'. apply MapsTo_add_eq_v in H2. subst v0.
              eapply drm_MapsTo in H1; eauto. lia.
            + apply add_3 in H2; try lia. contradict n.
              eapply drm_MapsTo_inj; eauto. }
  - split.
    + intros k' v' ?.
      destruct (eq_dec k' last).
      * subst k'. pose proof (MapsTo_add_eq (add k last m) last v).
        assert (v = v').
        { eapply MapsTo_eq_v; eassumption. }
        subst v'.
        { split.
          - eapply drm_MapsTo in H0. 2: apply H. lia.
          - eapply drm_MapsTo in H0. 2: apply H. lia. }
      * { assert (last <> k'). lia.
          eapply add_3 in H2. 2: apply H1.
          destruct (eq_dec k' k).
          - subst k'. apply MapsTo_add_eq_v in H2. subst v'.
            split. lia. split; try lia. eapply drm_MapsTo in H0.
            2: apply H. lia.
          - eapply add_3 in H2. 2: lia. eapply drm_MapsTo in H2.
            2: apply H. split. lia. split; lia. }
    + intros. split.
      * { destruct (eq_dec k0 last).
          - exists v. subst k0. apply MapsTo_add_eq.
          - assert (k0 < last). lia.
            destruct (eq_dec k0 k).
            + subst k0. exists last. eapply add_2. lia.
              apply MapsTo_add_eq.
            + eapply drm_lt_MapsTo_1 in H2. 2: apply H.
              destruct H2. exists x.
              eapply add_2. lia. eapply add_2. lia.
              assumption. }
      * { destruct (eq_dec k0 last).
          - subst k0. exists k.
            eapply drm_MapsTo in H0. 2: apply H.
            eapply add_2. lia.
            apply MapsTo_add_eq.
          - assert (k0 < last). lia.
            eapply drm_lt_MapsTo_2 in H2. 2: apply H.
            destruct H2. destruct (eq_dec k0 v).
            + subst k0. exists last. apply MapsTo_add_eq.
            + exists x.
              eapply add_2. eapply drm_MapsTo in H2. 2: apply H. lia.
              destruct (eq_dec x k).
              * subst x. eapply MapsTo_eq_v in H2. 2: apply H0. lia.
              * eapply add_2. lia. assumption. }
Qed.

Lemma drm_inject_fold_step_drms: forall m last k v a,
    drm m last -> MapsTo k v m -> (List.Forall (fun x => drm x (S last)) a)
    -> (List.Forall (fun x => drm x (S last)) (drm_inject_fold_step m last k v a)).
Proof.
  intros.
  rewrite Forall_forall in H1. apply Forall_forall. intros m' ?.
  unfold drm_inject_fold_step in H2.
  remember (drm_inject_step m last k v) as next.
  apply in_app_or in H2. destruct H2.
  - apply H1. assumption.
  - inversion H2.
    + assert (drm next (S last)).
      { eapply drm_inject_one_drm in H.
        2: apply H0. rewrite Heqnext. assumption. }
      subst m'. assumption.
    + inversion H3.
Qed.

Lemma fold_list_forall: forall A (P: list A -> Prop) m f init,
    P init -> (forall k v a, MapsTo k v m -> P a -> P (f k v a)) -> P (fold f m init).
Proof.
  intros A P m. destruct m. induction this0; intros.
  - compute. assumption.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    pose proof (IHthis0 H1 f) as IH.
    destruct a as [k' v']. rewrite fold_1.
    replace (elements (elt:=nat) {| this := (k', v') :: this0; NoDup := NoDup0 |})
      with ([(k', v')] ++ (elements (elt:=nat) {| this := this0; NoDup := H1 |})).
    2: reflexivity.
    rewrite fold_left_app. rewrite <- fold_1. simpl.
    assert (P (f k' v' init)).
    { apply H0. 2: apply H. constructor. reflexivity. }
    apply IH. assumption. intros.
    apply H0; auto. unfold MapsTo. unfold Raw.PX.MapsTo.
    simpl. constructor 2. apply H3.
Qed.

Lemma drm_inject_drms: forall m last,
    drm m last -> forall m', List.In m' (drm_inject m last) -> drm m' (S last).
Proof.
  intros m last H. apply Forall_forall. unfold drm_inject.
  apply fold_list_forall.
  - constructor.
  - intros. rewrite Forall_forall in H1.
    apply Forall_forall. intros.
    unfold drm_inject_fold_step in H2.
    apply in_app_or in H2.
    destruct H2; auto. inversion H2.
    + subst x. apply drm_inject_one_drm; assumption.
    + inversion H3.
Qed.

Lemma MapsTo_add_neq_k: forall k k' v v' m,
    v <> v' ->
    MapsTo k v (add k' v' m) ->
    k <> k'.
Proof.
  intros. intro. subst k'. apply MapsTo_add_eq_v in H0. lia.
Qed.

Lemma MapsTo_add_neq: forall k k' v v' m,
    v <> v' ->
    MapsTo k v (add k' v' m) ->
    MapsTo k v m.
Proof.
  intros. eapply add_3. 2: apply H0. assert (k <> k').
  eapply MapsTo_add_neq_k; eauto. lia.
Qed.

Lemma drm_add_loop_simple_drm: forall m n,
    drm m n -> drm (drm_add_loop_simple m n (S n)) (S (S n)).
Proof.
  intros. unfold drm_add_loop_simple. unfold drm. split; intros. 2: split.
  - pose proof (drm_In_iff m n H).
    replace (S (S n)) with (S (card (add (S n) n m))).
    + apply card_add_not_In. intro. apply In_add_iff in H1.
      destruct H1. lia. apply H0 in H1. lia.
    + replace (S (S n)) with (S (S (card m))).
      * apply eq_S. apply card_add_not_In. intro.
        apply H0 in H1. lia.
      * apply eq_S. erewrite card_drm. 2: apply H. reflexivity.
  - intros. destruct (eq_dec k n).
    + subst k. apply MapsTo_add_eq_v in H0. subst v.
      destruct (eq_dec k' n); try lia.
      apply add_3 in H1; try lia.
      apply add_3 in H1. eapply drm_MapsTo in H1; eauto. lia.
      assert (k' <> S n). eapply MapsTo_add_neq_k.
      2: apply H1. lia. lia.
    + apply add_3 in H0; try lia.
      destruct (eq_dec k (S n)).
      * subst k. apply MapsTo_add_eq_v in H0. subst v.
        { destruct (eq_dec k' n).
          - subst k'. apply MapsTo_add_eq_v in H1. lia.
          - apply add_3 in H1; try lia. destruct (eq_dec k' (S n)).
            + subst k'. reflexivity.
            + apply add_3 in H1; try lia. eapply drm_MapsTo in H1; eauto. lia. }
      * apply add_3 in H0; try lia. assert (v < n). eapply drm_MapsTo in H0; eauto. lia.
        apply MapsTo_add_neq in H1; try lia. apply MapsTo_add_neq in H1; try lia.
        eapply drm_MapsTo_inj; eauto.
  - split; intros.
    + destruct (eq_dec k n).
      * subst k. apply MapsTo_add_eq_v in H0.
        repeat (split; lia).
      * { apply add_3 in H0. 2: lia.
          destruct (eq_dec k (S n)).
          - subst k. apply MapsTo_add_eq_v in H0.
            repeat (split; lia).
          - apply add_3 in H0. 2: lia.
            eapply drm_MapsTo in H0. 2: apply H. lia. }
    + split.
      * { destruct (eq_dec k n).
          - subst k. exists (S n). apply MapsTo_add_eq.
          - destruct (eq_dec k (S n)).
            + subst k. exists n. apply add_2. lia.
              apply MapsTo_add_eq.
            + assert (k < n). lia.
              eapply drm_lt_MapsTo_1 in H1. 2: apply H. destruct H1.
              exists x. apply add_2. lia. apply add_2. lia.
              assumption. }
      * { destruct (eq_dec k n).
          - subst k. exists (S n). apply add_2. lia. apply MapsTo_add_eq.
          - destruct (eq_dec k (S n)).
            + subst k. exists n. apply MapsTo_add_eq.
            + assert (k < n). lia.
              eapply drm_lt_MapsTo_2 in H1. 2: apply H. destruct H1.
              exists x. apply add_2. eapply drm_MapsTo in H1. 2: apply H. lia.
              apply add_2. eapply drm_MapsTo in H1. 2: apply H. lia.
              assumption. }
Qed.

Lemma MapsTo_eq_k: forall k v v' m, v = v' -> MapsTo k v (add k v' m).
Proof.
  intros. subst v'. apply MapsTo_add_eq.
Qed.

Lemma drm_add_loop_step_drm: forall m n k' k v,
    drm m n -> MapsTo k' k m -> MapsTo k v m -> drm (drm_add_loop_step m n (S n) k' k v) (S (S n)).
Proof.
  intros. unfold drm. unfold drm_add_loop_step. split; intros. 2: split.
  - eapply drm_MapsTo in H0. 2: apply H.
    eapply drm_MapsTo in H1. 2: apply H.
    assert (In k' (add n v (add k (S n) (add (S n) k m)))).
    { apply In_add. apply In_add. apply In_add. eapply drm_In_iff. apply H. lia. }
    rewrite card_add_In in H2. rewrite H2.
    assert (~ In n (add k (S n) (add (S n) k m))).
    { intro. apply In_add_iff in H3. destruct H3; try lia.
      apply In_add_iff in H3. destruct H3; try lia. eapply drm_not_In; eauto. }
    eapply card_add_not_In in H3. rewrite H3.
    assert (In k (add (S n) k m)).
    { apply In_add. eapply drm_In_iff; eauto. lia. }
    eapply card_add_In in H4. rewrite H4.
    assert (~ In (S n) m).
    { intro. eapply drm_In_iff in H5. 2: apply H. lia. }
    eapply card_add_not_In in H5. rewrite H5. apply card_drm in H. lia.
  - intros. assert (v < n /\ k < n /\ v <> k). eapply drm_MapsTo in H1; eauto. lia.
    destruct (eq_dec k0 k').
    + subst k0. apply MapsTo_add_eq_v in H2. subst v0.
      destruct (eq_dec k'0 k').
      * subst k'0. reflexivity.
      * apply add_3 in H3; try lia.
        repeat (apply MapsTo_add_neq in H3; try lia).
        eapply drm_MapsTo in H3; eauto. lia.
    + apply add_3 in H2; try lia. destruct (eq_dec k0 n).
      * subst k0. apply MapsTo_add_eq_v in H2. subst v0.
        { destruct (eq_dec k'0 k').
          - subst k'0. apply MapsTo_add_eq_v in H3. lia.
          - apply add_3 in H3; try lia. destruct (eq_dec k'0 n).
            + subst k'0. reflexivity.
            + apply add_3 in H3; try lia.
              destruct (eq_dec k'0 k).
              * subst k'0. apply MapsTo_add_eq_v in H3. lia.
              * apply add_3 in H3; try lia.
                apply MapsTo_add_neq in H3; try lia.
                contradict n3. eapply drm_MapsTo_inj; eauto. }
      * { apply add_3 in H2; try lia. destruct (eq_dec k0 k).
          - subst k0. apply MapsTo_add_eq_v in H2. subst v0.
            apply MapsTo_add_neq in H3; try lia.
            apply MapsTo_add_neq in H3; try lia.
            destruct (eq_dec k'0 k); try lia.
            apply add_3 in H3; try lia.
            apply MapsTo_add_neq in H3; try lia.
            eapply drm_MapsTo in H3; eauto. lia.
          - apply add_3 in H2; try lia. destruct (eq_dec k0 (S n)).
            + subst k0. apply MapsTo_add_eq_v in H2. subst v0.
              destruct (eq_dec k'0 k').
              * subst k'0. apply MapsTo_add_eq_v in H3. lia.
              * apply add_3 in H3; try lia.
                { destruct (eq_dec k'0 n).
                  - subst k'0. apply MapsTo_add_eq_v in H3. lia.
                  - apply add_3 in H3; try lia. destruct (eq_dec k'0 k).
                    + subst k'0. apply MapsTo_add_eq_v in H3. lia.
                    + apply add_3 in H3; try lia. destruct (eq_dec k'0 (S n)).
                      * subst k'0. lia.
                      * apply add_3 in H3; try lia. eapply drm_MapsTo_inj in H3.
                        2: apply H. 2: apply H0. lia. }
            + apply add_3 in H2; try lia. destruct (eq_dec k'0 k').
              * subst k'0. apply MapsTo_add_eq_v in H3. subst v0.
                eapply drm_MapsTo in H2; eauto. lia.
              * { apply add_3 in H3; try lia. destruct (eq_dec k'0 n).
                  -  subst k'0. apply MapsTo_add_eq_v in H3. subst v0.
                     contradict n2. eapply drm_MapsTo_inj. apply H.
                     apply H2. apply H1.
                  - apply add_3 in H3; try lia. destruct (eq_dec k'0 k).
                    + subst k'0. apply MapsTo_add_eq_v in H3. subst v0.
                      eapply drm_MapsTo in H2; eauto. lia.
                    + apply add_3 in H3; try lia. destruct (eq_dec k'0 (S n)).
                      * subst k'0. apply MapsTo_add_eq_v in H3. subst v0.
                        contradict n0. eapply drm_MapsTo_inj; eauto.
                      * apply add_3 in H3; try lia. eapply drm_MapsTo_inj; eauto. } }
  - split; intros.
    + destruct (eq_dec k0 k').
      * subst k0. apply MapsTo_add_eq_v in H2. subst v0.
        pose proof H.
        apply drm_not_In in H. eapply drm_MapsTo in H0. 2: apply H2. lia.
      * { apply add_3 in H2. 2: lia.
          destruct (eq_dec k0 n).
          - subst k0. apply MapsTo_add_eq_v in H2. subst v0.
            eapply drm_MapsTo in H1. 2: apply H. lia.
          - apply add_3 in H2. 2: lia. destruct (eq_dec k0 k).
            + subst k0. apply MapsTo_add_eq_v in H2. subst v0.
              eapply drm_MapsTo in H1. 2: apply H. lia.
            + apply add_3 in H2. 2: lia. destruct (eq_dec k0 (S n)).
              * subst k0. apply MapsTo_add_eq_v in H2. subst v0.
                eapply drm_MapsTo in H1. 2: apply H. lia.
              * apply add_3 in H2. 2: lia. eapply drm_MapsTo in H2.
                2: apply H. lia. }
    + split.
      * { destruct (eq_dec k0 k').
          - subst k0. exists n. apply MapsTo_add_eq.
          - destruct (eq_dec k0 n).
            + subst k0. exists v. apply add_2. lia. apply MapsTo_add_eq.
            + destruct (eq_dec k0 k).
              * subst k0. exists (S n). apply add_2. lia. apply add_2. lia.
                apply MapsTo_add_eq.
              * { destruct (eq_dec k0 (S n)).
                  - exists k. apply add_2; auto. apply add_2; auto.
                    apply add_2; auto. subst k0. apply MapsTo_add_eq.
                  - pose proof H. apply drm_lt_MapsTo_1 with (k:=k0) in H3. 2: lia.
                    destruct H3. exists x.
                    repeat (apply add_2; try lia; auto). } }
      * { destruct (eq_dec k0 n).
          - subst k0. exists k'. apply MapsTo_add_eq.
          - destruct (eq_dec k0 v).
            + subst k0. exists n. apply add_2.
              eapply drm_MapsTo in H0; eauto. lia. apply MapsTo_add_eq.
            + destruct (eq_dec k0 (S n)).
              * exists k. apply add_2. eapply drm_MapsTo in H0; eauto. lia.
                apply add_2. eapply drm_MapsTo in H1; eauto. lia. subst k0.
                apply MapsTo_add_eq.
              * { destruct (eq_dec k0 k).
                  - subst k0. exists (S n). eapply drm_MapsTo in H0; eauto.
                    eapply drm_MapsTo in H1; eauto. apply add_2. lia.
                    apply add_2. lia. apply add_2. lia. apply MapsTo_add_eq.
                  - pose proof H. apply drm_lt_MapsTo_2 with (v:=k0) in H3.
                    destruct H3.
                    exists x. 2: lia. pose proof H3.
                    assert (k' <> x).
                    { intro. subst x. eapply MapsTo_eq_v in H0. 2: apply H3. lia. }
                    assert (k <> x).
                    { intro. subst x. eapply MapsTo_eq_v in H3. 2: apply H1. lia. }
                    eapply drm_MapsTo in H4; eauto.
                    repeat (apply add_2; try lia; auto). } }
Qed.

Lemma drm_add_loop_drms: forall m n,
    drm m n -> forall m', List.In m' (drm_add_loop m n (S n)) -> drm m' (S (S n)).
Proof.
  intros m n H. apply Forall_forall. unfold drm_add_loop.
  constructor. apply drm_add_loop_simple_drm. assumption.
  apply fold_list_forall.
  - constructor.
  - intros. rewrite Forall_forall in H1.
    apply Forall_forall. intros. unfold drm_add_loop_fold_step in H2.
    assert (exists v', MapsTo v v' m).
    { eapply drm_MapsTo in H0. 2: apply H.
      assert (v < n). lia. eapply drm_lt_MapsTo_1 in H3.
      2: apply H. destruct H3. exists x0. assumption. }
    destruct H3. apply find_1 in H3. rewrite H3 in H2.
    apply in_app_or in H2. destruct H2.
    + apply H1. assumption.
    + inversion H2; subst; try easy.
      apply drm_add_loop_step_drm; auto.
      apply find_2 in H3. assumption.
Qed.


Definition drm_construct_1 (n: nat) (m: nmap nat): list (nmap nat) :=
  (drm_inject m n).

Definition drm_construct_2 (n: nat) (m: nmap nat): list (nmap nat) :=
  (drm_add_loop m (pred n) n).

Fixpoint drm_construct (n: nat) {struct n}: list (nmap nat) :=
  match n with
  | 0 => [ empty nat ]
  | S 0 => nil
  | S n =>
    (concat (List.map (drm_construct_1 n)
                      (drm_construct n)))
      ++ (concat (List.map (drm_construct_2 n)
                           (drm_construct (pred n))))
  end.

Example length_drm_construct_6: length (drm_construct 6) = 265.
Proof. reflexivity. Qed.


Lemma fold_left_list_forall: forall {A B} (P: list A -> Prop) (l: list B) (f: list A -> B -> list A) init,
    P init -> (forall el a, List.In el l -> P a -> P (f a el)) -> P (fold_left f l init).
Proof.
  intros A B P l. induction l; intros.
  - simpl. assumption.
  - simpl. apply IHl.
    + apply H0. constructor. reflexivity. assumption.
    + intros. apply H0; auto. change (a :: l) with ([a] ++ l).
      apply in_or_app. right. assumption.
Qed.

Theorem drm_construct_correct: forall n,
    Forall (fun m => drm m n) (drm_construct n).
Proof.
  induction n using Wf_nat.lt_wf_ind.
  destruct n.
  - simpl. constructor; auto. unfold drm.
    split. apply card_zero_iff. apply empty_1.
    split; intros; try split; intros.
    + inversion H0.
    + inversion H0.
    + inversion H0.
  - apply Forall_forall. intros m ?. simpl in H0.
    destruct (eq_dec n 0). subst n. inversion H0.
    assert (n > 0). lia.
    assert (exists n', S n' = n). exists (pred n). lia. destruct H2 as [n' ?].
    replace (match n with
             | 0 => []
             | S _ =>
                 concat (List.map (drm_construct_1 n) (drm_construct n)) ++
                 concat (List.map (drm_construct_2 n) (drm_construct (Nat.pred n)))
             end) with
        (concat (List.map (drm_construct_1 n) (drm_construct n)) ++
         concat (List.map (drm_construct_2 n) (drm_construct (Nat.pred n)))) in H0.
    2: (subst n; reflexivity).
    apply in_app_or in H0. destruct H0.
    + apply in_concat in H0. destruct H0 as [ms [? ?]].
      apply in_map_iff in H0. destruct H0 as [m' [? ?]].
      subst ms. assert (n < S n). lia. apply H in H0.
      rewrite Forall_forall in H0. apply H0 in H4.
      eapply drm_inject_drms. apply H4. unfold drm_construct_1 in H3.
      assumption.
    + apply in_concat in H0. destruct H0 as [ms [? ?]].
      apply in_map_iff in H0. destruct H0 as [m' [? ?]].
      subst ms. assert (n < S n). lia. subst n. simpl in H4.
      assert (n' < (S (S n'))). lia. apply H in H2.
      rewrite Forall_forall in H2. apply H2 in H4.
      unfold drm_construct_2 in H3. apply drm_add_loop_drms in H3; auto.
Qed.
