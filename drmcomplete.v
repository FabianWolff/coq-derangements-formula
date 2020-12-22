Require Import Lia List FMapWeakList OrderedTypeEx Compare_dec Permutation
        SetoidList RelationClasses SetoidPermutation Recdef Program.Wf Arith.Wf_nat.
Import ListNotations.

Require Import drmcorrect drmnodup.

Module Import Map := drmcorrect.Map.

Notation nmap := t.
Notation card := (@cardinal nat).
Notation find := (@find nat).
Notation In := (@In nat).
Notation Empty := (@Empty nat).
Notation eq_dec := (Nat_as_OT.eq_dec).
Notation MapsTo := (@MapsTo nat).


Lemma card_remove_In: forall k m,
    In k m -> card (remove k m) = Nat.pred (card m).
Proof.
  intros k m. revert k. destruct m. induction this0; intros; try easy.
  inversion H. inversion H0; subst.
  - destruct a. inversion H2. simpl in *. subst n n0.
    unfold card, remove. simpl. destruct (eq_dec k k); lia.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    assert (In k {| this := this0; NoDup := H1 |}).
    { unfold In. unfold Raw.PX.In. exists x. apply H2. }
    apply (IHthis0 H1 _) in H3.
    simpl in *. unfold card, remove in *. simpl. destruct a as [a0 a1].
    assert (k <> a0).
    { intro. subst a0. inversion NoDup0; subst.
      apply H6. apply Raw.PX.InA_eqke_eqk in H2.
      eapply Raw.PX.InA_eqk. 2: apply H2. reflexivity. }
    destruct (eq_dec k a0); try lia. simpl in *. rewrite H3.
    destruct this0; simpl; easy.
Qed.

Lemma card_add_In: forall k v m,
    In k m -> card (add k v m) = card m.
Proof.
  intros k v m. revert k v. destruct m. induction this0; intros.
  - inversion H. inversion H0.
  - destruct a as [k' v']. inversion H. inversion H0; subst.
    + inversion H2. simpl in *. subst k' v'.
      unfold card, add. simpl. destruct (eq_dec k k); try lia.
      reflexivity.
    + unfold card, add in *. simpl in *. destruct (eq_dec k k'); try easy.
      simpl. pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
      rewrite (IHthis0 H1); eauto. unfold In. unfold Raw.PX.In.
      exists x. apply H2.
Qed.

Lemma MapsTo_remove_false: forall k v m,
    MapsTo k v (remove k m) -> False.
Proof.
  intros.
  assert (~ In k (remove k m)).
  { apply remove_1. reflexivity. }
  apply MapsTo_In in H. contradiction.
Qed.

Lemma MapsTo_remove_neq: forall k k' v m,
    MapsTo k v (remove k' m) -> k <> k'.
Proof.
  intros. destruct (eq_dec k k'); try easy.
  subst k'. exfalso. eapply MapsTo_remove_false. eassumption.
Qed.

Lemma drm_add_loop_simple_complete: forall m n,
    n > 1 ->
    drm m n ->
    (MapsTo (Nat.pred n) (Nat.pred (Nat.pred n)) m /\ MapsTo (Nat.pred (Nat.pred n)) (Nat.pred n) m) ->
    (exists m', drm m' (Nat.pred (Nat.pred n))
                /\ map_equiv m (drm_add_loop_simple m' (Nat.pred (Nat.pred n)) (Nat.pred n))).
Proof.
  intros. destruct H1. exists (remove (Nat.pred (Nat.pred n)) (remove (Nat.pred n) m)).
  assert (drm (remove (elt:=nat) (Nat.pred (Nat.pred n)) (remove (elt:=nat) (Nat.pred n) m)) (Nat.pred (Nat.pred n))).
  { unfold drm. split. 2: split. 3: split.
    - rewrite card_remove_In. rewrite card_remove_In. apply card_drm in H0. lia.
      exists (Nat.pred (Nat.pred n)). assumption.
      exists (Nat.pred n). apply remove_2; try lia. assumption.
    - intros. pose proof (MapsTo_remove_neq _ _ _ _ H3).
      pose proof (MapsTo_remove_neq _ _ _ _ H4).
      apply remove_3 in H3; try lia. apply remove_3 in H4; try lia.
      pose proof (MapsTo_remove_neq _ _ _ _ H3).
      pose proof (MapsTo_remove_neq _ _ _ _ H4).
      apply remove_3 in H3; try lia. apply remove_3 in H4; try lia.
      eapply drm_MapsTo_inj in H4. 3: apply H3. lia. eassumption.
    - intros. pose proof (MapsTo_remove_neq _ _ _ _ H3).
      apply remove_3 in H3; try lia.
      pose proof (MapsTo_remove_neq _ _ _ _ H3). apply remove_3 in H3; try lia.
      pose proof H3.
      eapply drm_MapsTo in H3. 2: apply H0. repeat (split; try lia).
      destruct (eq_dec v (Nat.pred n)).
      + subst v. eapply drm_MapsTo_inj in H6. 2: apply H0. 2: apply H2. lia.
      + destruct (eq_dec v (Nat.pred (Nat.pred n))).
        * subst v. eapply drm_MapsTo_inj in H6. 2: apply H0. 2: apply H1. lia.
        * lia.
    - intros. assert (k < n). lia. pose proof H4.
      eapply drm_lt_MapsTo_1 in H4. 2: apply H0.
      eapply drm_lt_MapsTo_2 in H5. 2: apply H0.
      destruct H4 as [v ?]. destruct H5 as [k' ?]. split.
      + exists v. apply remove_2; try lia. apply remove_2; try lia. assumption.
      + exists k'. destruct (eq_dec k' (Nat.pred (Nat.pred n))).
        * subst k'. eapply MapsTo_eq_v in H5. 2: apply H2. lia.
        * { destruct (eq_dec k' (Nat.pred n)).
            - subst k'. eapply MapsTo_eq_v in H5. 2: apply H1. lia.
            - apply remove_2; try lia. apply remove_2; try lia. assumption. } }
  split; auto.
  unfold drm_add_loop_simple. apply map_equiv_MapsTo. intros.
  destruct (eq_dec k (Nat.pred (Nat.pred n))).
  - subst k. split; intros.
    + eapply MapsTo_eq_v in H4. 2: apply H2. subst v. apply MapsTo_add_eq.
    + apply MapsTo_add_eq_v in H4. subst v. assumption.
  - destruct (eq_dec k (Nat.pred n)).
    + subst k. split; intros.
      * eapply MapsTo_eq_v in H4. 2: apply H1. subst v.
        apply add_2; try lia. apply MapsTo_add_eq.
      * apply add_3 in H4; try lia. apply MapsTo_add_eq_v in H4. subst v. assumption.
    + split; intros.
      * apply add_2; try lia. apply add_2; try lia.
        apply remove_2; try lia. apply remove_2; try lia. assumption.
      * apply add_3 in H4; try lia. apply add_3 in H4; try lia.
        apply remove_3 in H4; try lia. apply remove_3 in H4; try lia. assumption.
Qed.

Lemma drm_add_loop_step_complete: forall m n,
    n > 1 ->
    drm m n ->
    (exists v, MapsTo (Nat.pred n) v m /\ MapsTo v (Nat.pred n) m /\ v <> Nat.pred (Nat.pred n)) ->
    exists m' k' k v, drm m' (Nat.pred (Nat.pred n))
                   /\ MapsTo k' k m' /\ MapsTo k v m'
                   /\ map_equiv m (drm_add_loop_step m' (Nat.pred (Nat.pred n)) (Nat.pred n) k' k v).
Proof.
  intros. destruct H1 as [k [? [? ?]]].
  assert (exists k' v, MapsTo k' (Nat.pred (Nat.pred n)) m /\ MapsTo (Nat.pred (Nat.pred n)) v m).
  { assert ((Nat.pred (Nat.pred n)) < n). lia.
    pose proof H4. eapply drm_lt_MapsTo_1 in H4. 2: apply H0.
    eapply drm_lt_MapsTo_2 in H5. 2: apply H0.
    destruct H4 as [v ?]. destruct H5 as [k' ?]. exists k', v. split; assumption. }
  destruct H4 as [k' [v [? ?]]].
  remember (remove (Nat.pred (Nat.pred n)) (remove (Nat.pred n) (add k' k (add k v m)))) as m'.
  exists m', k', k, v.
  assert (drm m' (Nat.pred (Nat.pred n))).
  { subst m'. unfold drm. split. 2: split. 3: split.
    - rewrite card_remove_In. rewrite card_remove_In. apply card_drm in H0.
      rewrite card_add_In. rewrite card_add_In. lia.
      exists (Nat.pred n). assumption.
      destruct (eq_dec k' k). subst k'. exists v. apply MapsTo_add_eq.
      exists (Nat.pred (Nat.pred n)). apply add_2; try lia. assumption.
      destruct (eq_dec (Nat.pred n) k'). subst k'. exists k. apply MapsTo_add_eq.
      destruct (eq_dec (Nat.pred n) k). subst k. exists v. apply add_2; try lia. apply MapsTo_add_eq.
      exists k. apply add_2; try lia. apply add_2; try lia. assumption.
      pose proof H4. eapply drm_MapsTo in H6. 2: apply H0.
      exists v. apply remove_2; try lia. apply add_2; try lia. apply add_2; try lia. assumption.
    - intros. pose proof (MapsTo_remove_neq _ _ _ _ H6). pose proof (MapsTo_remove_neq _ _ _ _ H7).
      apply remove_3 in H6; try lia. apply remove_3 in H7; try lia.
      pose proof (MapsTo_remove_neq _ _ _ _ H6). pose proof (MapsTo_remove_neq _ _ _ _ H7).
      apply remove_3 in H6; try lia. apply remove_3 in H7; try lia.
      destruct (eq_dec k0 k').
      + subst k0. apply MapsTo_add_eq_v in H6. subst v0.
        destruct (eq_dec k'0 k').
        * subst k'0. reflexivity.
        * { apply add_3 in H7; try lia. destruct (eq_dec k'0 k).
            - subst k'0. apply MapsTo_add_eq_v in H7. subst v.
              eapply drm_MapsTo_inj in H5. 3: apply H1. 2: apply H0. lia.
            - apply add_3 in H7; try lia. eapply drm_MapsTo_inj in H7. 3: apply H1.
              2: apply H0. lia. }
      + apply add_3 in H6; try lia. destruct (eq_dec k0 k).
        * { subst k0. apply MapsTo_add_eq_v in H6. subst v0. destruct (eq_dec k'0 k').
            - subst k'0. apply MapsTo_add_eq_v in H7. subst v.
              eapply drm_MapsTo_inj in H5. 3: apply H1. 2: apply H0. lia.
            - apply add_3 in H7; try lia. destruct (eq_dec k'0 k); try easy.
              apply add_3 in H7; try lia. eapply drm_MapsTo_inj in H7. 3: apply H5.
              2: apply H0. lia. }
        * { apply add_3 in H6; try lia. destruct (eq_dec k'0 k').
            - subst k'0. apply MapsTo_add_eq_v in H7. subst v0.
              eapply drm_MapsTo_inj in H6. 3: apply H1. 2: apply H0. lia.
            - apply add_3 in H7; try lia. destruct (eq_dec k'0 k).
              + subst k'0. apply MapsTo_add_eq_v in H7. subst v0.
                eapply drm_MapsTo_inj in H6. 3: apply H5. 2: apply H0. lia.
              + apply add_3 in H7; try lia. eapply drm_MapsTo_inj in H7. 3: apply H6.
                2: apply H0. lia. }
    - intros. pose proof (MapsTo_remove_neq _ _ _ _ H6).
      apply remove_3 in H6; try lia. pose proof (MapsTo_remove_neq _ _ _ _ H6).
      apply remove_3 in H6; try lia. destruct (eq_dec k0 k').
      + subst k0. apply MapsTo_add_eq_v in H6. subst v0.
        assert (k' <> k).
        { intro. subst k'. eapply MapsTo_eq_v in H4. 2: apply H2. lia. }
        eapply drm_MapsTo in H2. 2: apply H0. eapply drm_MapsTo in H4. 2: apply H0.
        lia.
      + apply add_3 in H6; try lia. destruct (eq_dec k0 k).
        * { subst k0. assert (k <> v).
            { intro. subst v. eapply drm_MapsTo_inj in H5. 3: apply H1. 2: apply H0. lia. }
            eapply MapsTo_add_eq_v in H6. subst v0.
            destruct (eq_dec v (Nat.pred (Nat.pred n))).
            - subst v. eapply drm_MapsTo in H5. 2: apply H0. lia.
            - destruct (eq_dec v (Nat.pred n)).
              + subst v. eapply drm_MapsTo_inj in H5. 3: apply H2. 2: apply H0. lia.
              + eapply drm_MapsTo in H2. 2: apply H0. eapply drm_MapsTo in H5. 2: apply H0. lia. }
        * { apply add_3 in H6; try lia. destruct (eq_dec v0 (Nat.pred (Nat.pred n))).
            - subst v0. eapply drm_MapsTo_inj in H6. 3: apply H4. 2: apply H0. lia.
            - destruct (eq_dec v0 (Nat.pred n)).
              + subst v0. eapply drm_MapsTo_inj in H6. 3: apply H2. 2: apply H0. lia.
              + eapply drm_MapsTo in H6. 2: apply H0. lia. }
    - intros. destruct (eq_dec k0 k').
      + subst k0. split.
        * exists k. apply remove_2; try lia. apply remove_2; try lia. apply MapsTo_add_eq.
        * { assert (k' < n). lia. eapply drm_lt_MapsTo_2 in H7. 2: apply H0. destruct H7 as [k'' ?].
            destruct (eq_dec k'' (Nat.pred n)).
            - subst k''. assert (k' = k). eapply MapsTo_eq_v. apply H7. apply H1.
              subst k'. eapply MapsTo_eq_v in H4. 2: apply H2. lia.
            - destruct (eq_dec k'' (Nat.pred (Nat.pred n))).
              + subst k''. assert (v = k'). eapply MapsTo_eq_v; eauto. subst v.
                exists k. eapply drm_MapsTo in H2. 2: apply H0. apply remove_2; try lia.
                apply remove_2; try lia. apply add_2. 2: apply MapsTo_add_eq.
                intro. subst k'. eapply drm_MapsTo_inj in H7. 3: apply H1. 2: apply H0. lia.
              + exists k''. apply remove_2; try lia. apply remove_2; try lia.
                apply add_2. 2: apply add_2. 3: assumption.
                intro. subst k''. eapply drm_MapsTo in H7. 2: apply H0. lia.
                intro. subst k''. eapply MapsTo_eq_v in H7. 2: apply H2. lia. }
      + destruct (eq_dec k0 k).
        * { subst k0. split.
            - exists v. apply remove_2; try lia. apply remove_2; try lia.
              apply add_2; try lia. apply MapsTo_add_eq.
            - exists k'. pose proof H4. eapply drm_MapsTo in H4. 2: apply H0. apply remove_2; try lia.
              apply remove_2. intro. subst k'. eapply MapsTo_eq_v in H7. 2: apply H1. lia.
              apply MapsTo_add_eq. }
        * { assert (k0 < n). lia. split.
            - eapply drm_lt_MapsTo_1 in H7. 2: apply H0. destruct H7 as [v0 ?]. exists v0.
              apply remove_2; try lia. apply remove_2; try lia. apply add_2; try lia. apply add_2; try lia.
              assumption.
            - eapply drm_lt_MapsTo_2 in H7. 2: apply H0. destruct H7 as [k'0 ?].
              assert (k'0 < n). eapply drm_MapsTo in H7. 2: apply H0. lia.
              assert (k'0 <> (Nat.pred n)). intro. subst k'0. eapply MapsTo_eq_v in H7. 2: apply H1. lia.
              destruct (eq_dec k'0 (Nat.pred (Nat.pred n))).
              + subst k'0. assert (v = k0). eapply MapsTo_eq_v; eauto. subst v.
                exists k. pose proof H2. eapply drm_MapsTo in H2. 2: apply H0.
                apply remove_2; try lia. apply remove_2; try lia. apply add_2.
                intro. subst k'. eapply MapsTo_eq_v in H10. 2: apply H4. lia.
                apply MapsTo_add_eq.
              + exists k'0. apply remove_2; try lia. apply remove_2; try lia.
                apply add_2. intro. subst k'0. eapply MapsTo_eq_v in H7. 2: apply H4. lia.
                apply add_2. intro. subst k'0. eapply MapsTo_eq_v in H7. 2: apply H2. lia.
                assumption. } }
  split; auto.
  assert (k' < n /\ k < n /\ v < n /\ k' <> k /\ k <> v).
  { assert (k' <> k). intro. subst k'. eapply MapsTo_eq_v in H4. 2: apply H2. lia.
    assert (k <> v). intro. subst v. eapply drm_MapsTo_inj in H5. 3: apply H1. lia. apply H0.
    eapply drm_MapsTo in H1; eauto. eapply drm_MapsTo in H4; eauto. eapply drm_MapsTo in H5; eauto. lia. }
  assert (k <> (Nat.pred n)).
  { intro. subst k. eapply drm_MapsTo in H1; eauto. lia. }
  assert (k' <> (Nat.pred n)).
  { intro. subst k'. eapply MapsTo_eq_v in H4. 2: apply H1. lia. }
  assert (k' <> (Nat.pred (Nat.pred n))).
  { intro. subst k'. eapply drm_MapsTo in H4; eauto. lia. }
  subst m'. split. 2: split.
  - apply remove_2; try lia. apply remove_2; try lia. apply MapsTo_add_eq.
  - apply remove_2; try lia. apply remove_2; try lia.
    apply add_2; try lia. apply MapsTo_add_eq.
  - unfold drm_add_loop_step. apply map_equiv_MapsTo. intros.
    destruct (eq_dec k0 (Nat.pred (Nat.pred n))).
    + subst k0. split; intros.
      * apply add_2. intro. subst k'.
        eapply drm_MapsTo in H4. 2: apply H0. lia.
        eapply MapsTo_eq_v in H11. 2: apply H5. subst v0. apply MapsTo_add_eq.
      * apply add_3 in H11; try lia. apply MapsTo_add_eq_v in H11. subst v0. assumption.
    + destruct (eq_dec k0 (Nat.pred n)).
      * { subst k0. split; intros.
          - apply add_2; try lia. apply add_2; try lia. apply add_2; try lia.
            eapply MapsTo_eq_v in H11. 2: apply H1. subst v0. apply MapsTo_add_eq.
          - apply add_3 in H11; try lia. apply add_3 in H11; try lia. apply add_3 in H11; try lia.
            apply MapsTo_add_eq_v in H11. subst v0. assumption. }
      * { destruct (eq_dec k0 k).
          - subst k0. split; intros.
            + apply add_2; try lia. apply add_2; try lia. eapply MapsTo_eq_v in H11. 2: apply H2.
              subst v0. apply MapsTo_add_eq.
            + apply add_3 in H11; try lia. apply add_3 in H11; try lia. apply MapsTo_add_eq_v in H11.
              subst v0. assumption.
          - destruct (eq_dec k0 k').
            + subst k0. split; intros.
              * eapply MapsTo_eq_v in H11. 2: apply H4. subst v0. apply MapsTo_add_eq.
              * apply MapsTo_add_eq_v in H11. subst v0. assumption.
            + split; intros.
              * apply add_2; try lia. apply add_2; try lia. apply add_2; try lia.
                apply add_2; try lia. apply remove_2; try lia. apply remove_2; try lia.
                apply add_2; try lia. apply add_2; try lia. assumption.
              * apply add_3 in H11; try lia. apply add_3 in H11; try lia. apply add_3 in H11; try lia.
                apply add_3 in H11; try lia. apply remove_3 in H11; try lia. apply remove_3 in H11; try lia.
                apply add_3 in H11; try lia. apply add_3 in H11; try lia. assumption. }
Qed.

Lemma drm_add_loop_complete: forall m n,
    n > 1 ->
    drm m n ->
    (exists v, MapsTo (Nat.pred n) v m /\ MapsTo v (Nat.pred n) m) ->
    (exists m', drm m' (Nat.pred (Nat.pred n))
                /\ InA map_equiv m (drm_add_loop m' (Nat.pred (Nat.pred n)) (Nat.pred n))).
Proof.
  intros. destruct H1 as [v [? ?]]. destruct (eq_dec v (Nat.pred (Nat.pred n))).
  - subst v. eapply drm_add_loop_simple_complete in H. 2: apply H0. 2: split; assumption.
    destruct H as [m' [? ?]]. exists m'. split; auto.
    unfold drm_add_loop. constructor. assumption.
  - eapply drm_add_loop_step_complete in H. 2: apply H0. 2: (exists v; easy).
    destruct H as [m' [_k' [_k [_v [? [? [? ?]]]]]]].
    exists m'. split; auto. unfold drm_add_loop. right.
    rewrite drm_add_loop_fold_eq. simpl. apply InA_concat_map.
    exists (_k', _k). simpl. apply find_1 in H4. rewrite H4. split.
    + unfold MapsTo in H3. unfold Raw.PX.MapsTo in H3. apply InA_eqke_In in H3. apply H3.
    + constructor. assumption.
Qed.

Lemma drm_inject_complete: forall m n,
    n > 1 ->
    drm m n ->
    (exists k' v, k' <> v /\ MapsTo k' (Nat.pred n) m /\ MapsTo (Nat.pred n) v m) ->
    (exists m', drm m' (Nat.pred n) /\ InA map_equiv m (drm_inject m' (Nat.pred n))).
Proof.
  intros. destruct H1 as [k' [v [? [? ?]]]].
  remember (remove (Nat.pred n) (add k' v m)) as m'. exists m'.
  assert (drm m' (Nat.pred n)).
  { unfold drm. subst m'. split. 2: split. 3: split.
    - rewrite card_remove_In. apply card_drm in H0.
      rewrite card_add_In. lia.
      unfold In. unfold Raw.PX.In. eexists. apply H2.
      unfold In. unfold Raw.PX.In. destruct (eq_dec (Nat.pred n) k').
      + subst k'. exists v. apply MapsTo_add_eq.
      + exists v. apply add_2; try lia. assumption.
    - intros. destruct (eq_dec k (Nat.pred n)).
      { subst k. apply MapsTo_remove_false in H4. contradiction. }
      destruct (eq_dec k'0 (Nat.pred n)).
      { subst k'0. apply MapsTo_remove_false in H5. contradiction. }
      apply remove_3 in H4; try lia. apply remove_3 in H5; try lia.
      destruct (eq_dec k k').
      { subst k'. apply MapsTo_add_eq_v in H4. subst v0.
        destruct (eq_dec k'0 k); try easy.
        apply add_3 in H5; try lia. eapply drm_MapsTo_inj in H5.
        2: apply H0. 2: apply H3. lia. }
      apply add_3 in H4; try lia.
      destruct (eq_dec k'0 k').
      { subst k'0. apply MapsTo_add_eq_v in H5. subst v0.
        eapply drm_MapsTo_inj in H4. 3: apply H3. 2: apply H0. lia. }
      apply add_3 in H5; try lia. eapply drm_MapsTo_inj in H5; eauto.
    - intros. destruct (eq_dec k (Nat.pred n)).
      { subst k. apply MapsTo_remove_false in H4. contradiction. }
      apply remove_3 in H4; try lia. destruct (eq_dec k k').
      { subst k'. apply MapsTo_add_eq_v in H4. subst v0.
        eapply drm_MapsTo in H2; eauto.
        eapply drm_MapsTo in H3; eauto. lia. }
      apply add_3 in H4; try lia. destruct (eq_dec v0 (Nat.pred n)).
      { subst v0. eapply drm_MapsTo_inj in H4. 3: apply H2. lia. apply H0. }
      eapply drm_MapsTo in H4. 2: apply H0. lia.
    - intros. assert (k < n). lia. pose proof H5.
      eapply drm_lt_MapsTo_1 in H5. 2: apply H0.
      eapply drm_lt_MapsTo_2 in H6. 2: apply H0.
      destruct H5 as [v0 ?].
      destruct H6 as [k'0 ?]. split.
      + destruct (eq_dec k k').
        * subst k'. exists v. apply remove_2; try lia. apply MapsTo_add_eq.
        * exists v0. apply remove_2; try lia. apply add_2; try lia. assumption.
      + destruct (eq_dec k v).
        * subst k. exists k'. eapply drm_MapsTo in H2; eauto. apply remove_2; try lia. apply MapsTo_add_eq.
        * destruct (eq_dec k'0 (Nat.pred n)).
          { subst k'0. eapply MapsTo_eq_v in H6. 2: apply H3. lia. }
          exists k'0. apply remove_2; try lia. destruct (eq_dec k'0 k').
          { subst k'0. eapply MapsTo_eq_v in H6. 2: apply H2. lia. }
          eapply add_2; try lia. assumption. }

  split; auto.
  unfold drm_inject. rewrite drm_inject_fold_step_eq. simpl.
  apply InA_map_iff. exists (k', v). split.
  - assert (k' <> Nat.pred n).
    { eapply drm_MapsTo in H2; eauto. lia. }
    assert (MapsTo k' v m').
    { subst m'. apply remove_2. lia. apply MapsTo_add_eq. }
    unfold MapsTo in H6. unfold Raw.PX.MapsTo in H6.
    apply InA_eqke_In in H6. apply H6.
  - simpl. unfold drm_inject_step. subst m'.
    apply map_equiv_MapsTo. intros.
    destruct (eq_dec k (Nat.pred n)).
    + subst k. split; intros.
      * assert (v = v0). eapply MapsTo_eq_v; eauto.
        subst v0. apply MapsTo_add_eq.
      * assert (v0 = v). eapply MapsTo_add_eq_v; eauto.
        subst v0. assumption.
    + destruct (eq_dec k k').
      * { subst k'. split; intros.
          - assert (Nat.pred n = v0). eapply MapsTo_eq_v; eauto.
            subst v0. apply add_2; try lia. apply MapsTo_add_eq.
          - apply add_3 in H5; try lia.
            assert (v0 = Nat.pred n). eapply MapsTo_add_eq_v; eauto.
            subst v0. assumption. }
      * { split; intros.
          - apply add_2; try lia. apply add_2; try lia.
            apply remove_2; try lia. apply add_2; try lia. assumption.
          - apply add_3 in H5; try lia. apply add_3 in H5; try lia.
            apply remove_3 in H5; try lia. apply add_3 in H5; try lia.
            assumption. }
Qed.

Theorem drm_construct_complete: forall m n,
    drm m n ->
    InA map_equiv m (drm_construct n).
Proof.
  intros m n. revert m. induction n using Wf_nat.lt_wf_ind.
  intros. destruct n.
  - apply drm_zero_iff in H0. simpl. constructor. destruct m.
    unfold empty. unfold Raw.empty. destruct this0.
    unfold map_equiv. simpl. constructor.
    unfold Empty in H0. unfold Raw.Empty in H0. destruct p.
    pose proof (H0 n n0). exfalso. apply H1.
    constructor. reflexivity.
  - destruct n.
    + unfold drm in H0. destruct H0 as [? [? [? ?]]].
      assert (0 < 1). lia. apply H3 in H4.
      destruct H4 as [[v ?] [k' ?]]. apply H2 in H4. lia.
    + assert (exists v, MapsTo (S n) v m).
      { eapply drm_lt_MapsTo_1 in H0. apply H0. lia. }
      destruct H1 as [v ?].
      assert (exists k', MapsTo k' (S n) m).
      { assert (S n < (S (S n))). lia.
        eapply drm_lt_MapsTo_2 in H2. 2: apply H0. apply H2. }
      destruct H2 as [k' ?].
      change (drm_construct (S (S n))) with
            (concat (List.map (drm_construct_1 (S n)) (drm_construct (S n))) ++
                    concat (List.map (drm_construct_2 (S n)) (drm_construct n))).
      apply InA_app_iff. rewrite InA_concat_map. rewrite InA_concat_map.
      destruct (eq_dec k' v).
      * subst k'.
        assert (exists v, MapsTo (Nat.pred (S (S n))) v m /\ MapsTo v (Nat.pred (S (S n))) m).
        { exists v. simpl. split; assumption. }
        apply drm_add_loop_complete in H3. 2: lia. 2: assumption.
        destruct H3 as [m' [? ?]]. simpl in H3. apply H in H3. 2: lia.
        right. apply InA_alt in H3. destruct H3 as [y [? ?]].
        exists y. split; auto. simpl in H4.
        apply drm_construct_2_well_behaved with (n:=(S n)) in H3. 2: lia.
        eapply PermA_InA in H3. 2: apply map_equiv_Equivalence. rewrite <- H3.
        unfold drm_construct_2. simpl. assumption.
      * assert (exists k' v, k' <> v /\ MapsTo k' (Nat.pred (S (S n))) m /\
                             MapsTo (Nat.pred (S (S n))) v m).
        { exists k', v. easy. }
        apply drm_inject_complete in H3. 2: lia. 2: assumption. simpl in H3.
        left. destruct H3 as [m' [? ?]]. apply H in H3. 2: lia.
        apply InA_alt in H3. destruct H3 as [y [? ?]].
        exists y. split; auto. apply drm_construct_1_well_behaved with (n:=(S n)) in H3.
        eapply PermA_InA in H3. 2: apply map_equiv_Equivalence. rewrite <- H3.
        unfold drm_construct_1. assumption.
Qed.
