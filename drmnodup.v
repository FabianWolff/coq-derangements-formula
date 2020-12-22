Require Import Lia List FMapWeakList OrderedTypeEx Compare_dec Permutation
        SetoidList RelationClasses SetoidPermutation Recdef Program.Wf Arith.Wf_nat.
Import ListNotations.

Require Import drmcorrect.

Module Import Map := drmcorrect.Map.

Notation nmap := t.
Notation card := (@cardinal nat).
Notation find := (@find nat).
Notation In := (@In nat).
Notation Empty := (@Empty nat).
Notation eq_dec := (Nat_as_OT.eq_dec).
Notation MapsTo := (@MapsTo nat).

Definition map_equiv (m m': nmap nat) :=
  Permutation (elements m) (elements m').


Lemma nat_pair_dec: forall a b c d: nat, {(a, b) = (c, d)} + {(a, b) <> (c, d)}.
Proof.
  intros.
  destruct (eq_dec a c).
  - subst c. destruct (eq_dec b d).
    + subst d. left. reflexivity.
    + right. intro.
      assert (snd (a, b) = snd (a, d)). rewrite H. reflexivity.
      simpl in H0. lia.
  - right. intro.
    assert (fst (a, b) = fst (c, d)). rewrite H. reflexivity.
    simpl in H0. lia.
Qed.

Lemma PermA_InA: forall {A : Type} (eqA : A -> A -> Prop) (x : A) (l l' : list A),
    Equivalence eqA -> PermutationA eqA l l' -> (InA eqA x l <-> InA eqA x l').
Proof.
  intros A eqA x l l' Heq H. revert x. induction H; intros.
  - split; intros; easy.
  - split; intros.
    + inversion H1; subst.
      * constructor. etransitivity; eauto.
      * constructor 2. apply IHPermutationA. assumption.
    + inversion H1; subst.
      * constructor. etransitivity; eauto. symmetry. auto.
      * constructor 2. apply IHPermutationA. assumption.
  - split; intros.
    + inversion H; subst.
      * constructor 2. constructor 1. assumption.
      * { inversion H1; subst.
          - constructor 1. assumption.
          - constructor 2. constructor 2. assumption. }
    + inversion H; subst.
      * constructor 2. constructor 1. assumption.
      * { inversion H1; subst.
          - constructor 1. assumption.
          - constructor 2. constructor 2. assumption. }
  - etransitivity. apply IHPermutationA1.
    apply IHPermutationA2.
Qed.

Lemma map_equiv_card: forall m m', map_equiv m m' -> card m = card m'.
Proof.
  intros m m' Hm. unfold map_equiv in Hm. unfold card.
  destruct m, m'. simpl in Hm. induction Hm.
  - simpl. reflexivity.
  - simpl in *. apply eq_S. apply IHHm; eapply SetoidList_NoDupA_cons_rev; eassumption.
  - simpl. reflexivity.
  - simpl in *. assert (NoDupA (Raw.PX.eqk (elt:=nat)) l').
    eapply PermutationA_preserves_NoDupA. apply Raw.PX.eqk_equiv.
    apply Permutation_PermutationA. apply Raw.PX.eqk_equiv. apply Hm1. assumption.
    etransitivity. apply IHHm1; auto. apply IHHm2; auto.
Qed.

Lemma list_ind_2_helper: forall [A : Type] (P : list A -> list A -> Prop) n l1 l2,
    length l1 + length l2 <= n ->
    P [] [] ->
    (forall (a : A) (l : list A), P l [] -> P (a :: l) []) ->
    (forall (a : A) (l : list A), P [] l -> P [] (a :: l)) ->
    (forall (a b: A) (l1 l2: list A), P l1 l2 -> P (a :: l1) (b :: l2)) ->
    P l1 l2.
Proof.
  intros A P n.
  induction n using Wf_nat.lt_wf_ind.
  intros. destruct l1, l2; auto.
  - apply H3. apply H with (m:=(length l2)); auto.
  - apply H2. apply H with (m:=(length l1)); simpl in *; auto; lia.
  - apply H4. apply H with (m:=(length l1 + length l2 + 1)); auto; simpl in *; lia.
Qed.

Lemma list_ind_2: forall {A: Type} (P: list A -> list A -> Prop) l1 l2,
    P [] [] ->
    (forall (a : A) (l : list A), P l [] -> P (a :: l) []) ->
    (forall (a : A) (l : list A), P [] l -> P [] (a :: l)) ->
    (forall (a b: A) (l1 l2: list A), P l1 l2 -> P (a :: l1) (b :: l2)) ->
    P l1 l2.
Proof.
  intros. eapply list_ind_2_helper; auto.
Qed.

Lemma list_ind_2_eqlen: forall {A: Type} (P: list A -> list A -> Prop) l1 l2,
    P [] [] ->
    (forall (a b: A) (l1 l2: list A), P l1 l2 -> P (a :: l1) (b :: l2)) ->
    length l1 = length l2 -> P l1 l2.
Proof.
  intros. revert H1.
  apply list_ind_2 with (l3:=l1) (l4:=l2); intros; try easy.
  apply H0. apply H1. simpl in H2. lia.
Qed.

Lemma InA_eqke_In: forall {elt: Type} x l,
    InA (@Raw.PX.eqke elt) x l <-> List.In x l.
Proof.
  intros elt x l. induction l. easy.
  split; intros.
  - destruct x, a. inversion H; subst.
    + inversion H1. simpl in *. subst.
      left. reflexivity.
    + right. apply IHl. assumption.
  - inversion H; subst.
    + constructor. reflexivity.
    + right. apply IHl. assumption.
Qed.

Lemma NoDupA_eqk_eqke: forall {A: Type} l,
    NoDupA (Raw.PX.eqk (elt:=A)) l -> NoDupA (Raw.PX.eqke (elt:=A)) l.
Proof.
  induction l; intros; try easy.
  inversion H; subst. constructor.
  intro. apply Raw.PX.InA_eqke_eqk in H0. contradiction.
  apply IHl. assumption.
Qed.

Lemma NoDupA_eqke_NoDup: forall {A: Type} l,
    NoDupA (Raw.PX.eqke (elt:=A)) l <-> List.NoDup l.
Proof.
  induction l; intros.
  - split; intros. constructor. constructor.
  - split; intros. inversion H; subst.
    constructor. intro. apply InA_eqke_In in H0. contradiction.
    apply IHl. assumption.
    inversion H; subst.
    constructor. intro. apply InA_eqke_In in H0. contradiction.
    apply IHl. assumption.
Qed.

Lemma map_equiv_MapsTo: forall m m', map_equiv m m' <-> (forall k v, MapsTo k v m <-> MapsTo k v m').
Proof.
  intros m m'. split; intros.
  - unfold map_equiv in *. destruct m, m'. simpl in *. induction H.
    + split; intros; easy.
    + destruct x as [k' v']. destruct (nat_pair_dec k v k' v').
      * inversion e. subst. split; intros; constructor; easy.
      * { pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
          pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup1).
          pose proof (IHPermutation H0 H1). unfold MapsTo in *.
          unfold Raw.PX.MapsTo in *. simpl in *.
          split; intros.
          - inversion H3; subst.
            + inversion H5; subst. simpl in *. subst. contradiction.
            + constructor 2. apply H2. assumption.
          - inversion H3; subst.
            + inversion H5; subst. simpl in *. subst. contradiction.
            + constructor 2. apply H2. assumption. }
    + unfold MapsTo. unfold Raw.PX.MapsTo. simpl.
      apply PermA_InA. apply Raw.PX.eqke_equiv. constructor 3.
    + unfold MapsTo in *. unfold Raw.PX.MapsTo in *. simpl in *.
      assert (NoDupA (Raw.PX.eqk (elt:=nat)) l').
      { eapply PermutationA_preserves_NoDupA. apply Raw.PX.eqk_equiv.
        apply Permutation_PermutationA. apply Raw.PX.eqk_equiv.
        apply H. assumption. }
      etransitivity. apply IHPermutation1; auto.
      apply IHPermutation2; auto.
  - destruct m, m'. unfold map_equiv. simpl.
    unfold MapsTo in H. unfold Raw.PX.MapsTo in H. simpl in H.
    apply NoDup_Permutation; try (apply NoDupA_eqke_NoDup; apply NoDupA_eqk_eqke; easy).
    intros. destruct x as [k v]. pose proof (H k v).
    split; intros; apply InA_eqke_In; apply H0; apply InA_eqke_In; assumption.
Qed.

Lemma map_equiv_Equivalence: Equivalence map_equiv.
Proof.
  unfold map_equiv.
  constructor.
  - unfold Reflexive. intros. reflexivity.
  - unfold Symmetric. intros. symmetry. assumption.
  - unfold Transitive. intros. etransitivity; eauto.
Qed.

Instance map_equiv_Equivalence': Equivalence (map_equiv).
Proof. apply map_equiv_Equivalence. Qed.

Lemma InA_eqlist: forall {A} (eqrel: A -> A -> Prop) x l l',
    Equivalence eqrel ->
    eqlistA eqrel l l' -> InA eqrel x l -> InA eqrel x l'.
Proof.
  intros A eqrel x l l' HE Heq. revert x. induction Heq; intros.
  - inversion H.
  - apply InA_cons in H0. destruct H0.
    + apply InA_cons_hd. inversion HE. unfold Transitive in Equivalence_Transitive.
      eapply Equivalence_Transitive; eassumption.
    + apply InA_cons. right. apply IHHeq. assumption.
Qed.

Lemma map_equiv_drm: forall m m' n, drm m n -> map_equiv m m' -> drm m' n.
Proof.
  intros.
  unfold drm in *. destruct H. destruct H1 as [? [? ?]].
  split. apply map_equiv_card in H0. lia.
  split; intros.
  - rewrite map_equiv_MapsTo in H0. apply H0 in H4. apply H0 in H5.
    eapply H1; eauto.
  - split; intros.
    + apply H2. eapply map_equiv_MapsTo; eauto.
    + apply H3 in H4. destruct H4 as [[? ?] [? ?]].
      split. exists x. eapply map_equiv_MapsTo; eauto. symmetry. assumption.
      exists x0. eapply map_equiv_MapsTo; eauto. symmetry. assumption.
Qed.

Lemma InA_concat_map_drm: forall m (f: (nmap nat) -> (list (nmap nat))) (ms: list (nmap nat)) n',
    Forall (fun m' => drm m' n') ms ->
    (forall m m', drm m n' -> drm m' n' -> map_equiv m m' -> PermutationA map_equiv (f m) (f m')) ->
    (InA map_equiv m (concat (List.map f ms)) <->
     exists m', drm m' n' /\ InA map_equiv m' ms /\ InA map_equiv m (f m')).
Proof.
  intros m f ms. revert m f. induction ms; intros.
  - simpl. split; intros.
    + inversion H1.
    + destruct H1 as [? [? [? ?]]]. inversion H2.
  - simpl. split; intros.
    + apply InA_app in H1. destruct H1.
      * exists a. split.
        rewrite Forall_forall in H. apply H. constructor. reflexivity.
        split. left. reflexivity. assumption.
      * rewrite IHms in H1; eauto. 2: eapply Forall_inv_tail; eauto.
        destruct H1 as [m' [? [? ?]]].
        exists m'. split; auto.
    + apply InA_app_iff. destruct H1 as [m' [? [? ?]]].
      inversion H2; subst.
      * left. eapply PermA_InA. apply map_equiv_Equivalence.
        apply H0; eauto. eapply map_equiv_drm; eauto. symmetry.
        assumption. assumption.
      * right. rewrite IHms; eauto. apply Forall_inv_tail in H. apply H.
Qed.

Lemma NoDupA_concat_map_drm: forall f ms n',
    Forall (fun m' => drm m' n') ms ->
    NoDupA map_equiv ms ->
    (forall m, drm m n' -> NoDupA map_equiv (f m)) ->
    (forall m, drm m n' -> Forall (fun m => exists n, drm m n) (f m)) ->
    (forall m m' : nmap nat, drm m n' -> drm m' n' -> map_equiv m m' -> PermutationA map_equiv (f m) (f m')) ->
    (forall x m' m'', drm m' n' -> drm m'' n' -> (InA map_equiv x (f m')) -> (InA map_equiv x (f m'')) -> map_equiv m' m'') ->
    NoDupA map_equiv (concat (List.map f ms)).
Proof.
  pose proof (map_equiv_Equivalence) as HmeE.
  intros f ms. revert f. induction ms; intros.
  - simpl. constructor.
  - simpl. apply NoDupA_app; auto.
    + apply H1. rewrite Forall_forall in H. apply H. constructor. reflexivity.
    + eapply IHms; eauto. apply Forall_inv_tail in H. apply H.
      inversion H0; subst. assumption.
    + intros. inversion H; subst.
      eapply InA_concat_map_drm in H6; eauto.
      destruct H6 as [m' [? [? ?]]].
      inversion H0; subst.
      eapply (H4 x a m') in H8; eauto.
      symmetry in H8.
      eapply InA_eqA in H7; eauto.
Qed.

Lemma NoDupA_concat_map_app_drm: forall (f g: (nmap nat) -> (list (nmap nat))) ms n ms' n',
    Forall (fun m => drm m n) ms ->
    Forall (fun m' => drm m' n') ms' ->
    NoDupA map_equiv ms ->
    NoDupA map_equiv ms' ->
    (forall m, drm m n -> NoDupA map_equiv (f m)) ->
    (forall m, drm m n' -> NoDupA map_equiv (g m)) ->
    (forall m : nmap nat, drm m n -> Forall (fun m0 : nmap nat => exists n0 : nat, drm m0 n0) (f m)) ->
    (forall m : nmap nat, drm m n' -> Forall (fun m0 : nmap nat => exists n0 : nat, drm m0 n0) (g m)) ->
    (forall m m' : nmap nat, drm m n -> drm m' n -> map_equiv m m' -> PermutationA map_equiv (f m) (f m')) ->
    (forall m m' : nmap nat, drm m n' -> drm m' n' -> map_equiv m m' -> PermutationA map_equiv (g m) (g m')) ->
    (forall x m m' : nmap nat, drm m n -> drm m' n -> InA map_equiv x (f m) -> InA map_equiv x (f m') -> map_equiv m m') ->
    (forall x m m' : nmap nat, drm m n' -> drm m' n' -> InA map_equiv x (g m) -> InA map_equiv x (g m') -> map_equiv m m') ->
    (forall x m m', drm m n -> drm m' n' -> InA map_equiv x (f m) -> InA map_equiv x (g m') -> False) ->
    NoDupA map_equiv ((concat (List.map f ms)) ++ (concat (List.map g ms'))).
Proof.
  pose proof map_equiv_Equivalence as HmeE.
  intros f g ms. revert f g. induction ms; intros.
  - simpl. eapply NoDupA_concat_map_drm; eauto.
  - apply NoDupA_app; auto.
    + eapply NoDupA_concat_map_drm; eauto.
    + eapply NoDupA_concat_map_drm; eauto.
    + intros. simpl in *. apply InA_app in H12. destruct H12.
      * eapply InA_concat_map_drm in H13; eauto.
        destruct H13 as [m' [? [? ?]]]. eapply H11; eauto.
        apply Forall_inv in H. apply H.
      * inversion H; subst. eapply InA_concat_map_drm in H12; eauto.
        eapply InA_concat_map_drm in H13; eauto.
        destruct H12 as [? [? [? ?]]].
        destruct H13 as [? [? [? ?]]].
        eapply H11; eauto.
Qed.

Lemma drm_inject_fold_step_eq: forall m m' n (a: list (nmap nat)),
    (fold (drm_inject_fold_step m' n) m a) =
    a ++ (List.map (fun p => drm_inject_step m' n (fst p) (snd p)) (elements m)).
Proof.
  destruct m. induction this0; intros.
  - simpl. unfold fold. simpl. rewrite app_nil_r. reflexivity.
  - unfold fold in *. simpl. destruct a as [k v].
    simpl in IHthis0. rewrite IHthis0.
    + simpl. unfold drm_inject_fold_step.
      change (drm_inject_step m' n k v
                :: List.map (fun p : nat * nat => drm_inject_step m' n (fst p) (snd p)) this0)
        with ([drm_inject_step m' n k v]
                ++ List.map (fun p : nat * nat => drm_inject_step m' n (fst p) (snd p)) this0).
      rewrite app_assoc. reflexivity.
    + eapply SetoidList_NoDupA_cons_rev; eauto.
Qed.


Lemma map_equiv_add: forall k v m m', map_equiv m m' -> map_equiv (add k v m) (add k v m').
Proof.
  intros. unfold map_equiv in *. destruct m, m'. simpl in *.
  induction H.
  - simpl. constructor. constructor.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup1).
    destruct x as [k' v']. apply IHPermutation in H1; auto.
    simpl. destruct (eq_dec k k').
    + constructor. assumption.
    + constructor. assumption.
  - destruct y as [k' v']. destruct x as [k'' v''].
    simpl. destruct (nat_pair_dec k v k' v'), (nat_pair_dec k v k'' v'').
    + inversion e. inversion e0. simpl in *. subst k' k'' v' v''.
      destruct (eq_dec k k); try lia. repeat constructor. reflexivity.
    + inversion e. subst k' v'. destruct (eq_dec k k); try lia.
      destruct (eq_dec k k'').
      * subst k''. inversion NoDup0; subst. contradict H1. constructor.
        constructor.
      * constructor 3.
    + inversion e. subst k'' v''. destruct (eq_dec k k); try lia.
      destruct (eq_dec k k').
      * subst k'. inversion NoDup1; subst. contradict H1. constructor.
        constructor.
      * constructor 3.
    + destruct (eq_dec k k'').
      * { subst k''. destruct (eq_dec k k').
          - subst k'. inversion NoDup0; subst. contradict H1. constructor. constructor.
          - constructor 3. }
      * { destruct (eq_dec k k').
          - constructor 3.
          - constructor 3. }
  - assert (NoDupA (Raw.PX.eqk (elt:=nat)) l').
    { eapply PermutationA_preserves_NoDupA. apply Raw.PX.eqk_equiv.
      apply Permutation_PermutationA. apply Raw.PX.eqk_equiv.
      apply H. assumption. }
    etransitivity. apply IHPermutation1; auto.
    apply IHPermutation2; auto.
Qed.

Lemma PermA_swap_eqA: forall {A: Type} (eqA: A -> A -> Prop) x x' y y' l l',
    Equivalence eqA ->
    PermutationA eqA l l' ->
    eqA x x' ->
    eqA y y' ->
    PermutationA eqA (x :: y :: l) (y' :: x' :: l').
Proof.
  intros A eqA x x' y y' l l' HE H. revert x x' y y'.
  induction H; intros.
  - transitivity ([y; x]). apply permA_swap.
    constructor; auto. constructor; auto. constructor.
  - transitivity (y :: x :: x₁ :: l₁). apply permA_swap.
    repeat (constructor; auto).
  - transitivity (x' :: y' :: x :: y :: l).
    constructor. auto. constructor. auto. apply permA_swap.
    apply permA_swap.
  - transitivity (x' :: y' :: l₃).
    constructor. auto. constructor. auto.
    etransitivity; eauto.
    apply permA_swap.
Qed.

Lemma PermutationA_custom_ind:
  forall {A : Type} [eqA : relation A] [P : list A -> list A -> Prop],
  Equivalence eqA ->
  P [] [] ->
  (forall l, P l l) ->
  (forall (x1 x2 : A) (l1 l2 : list A), eqA x1 x2 -> PermutationA eqA l1 l2 -> P l1 l2 -> P (x1 :: l1) (x2 :: l2)) ->
  (forall (x y : A) (l1 l2 : list A), PermutationA eqA l1 l2 -> P l1 l2 -> P (y :: x :: l1) (x :: y :: l2)) ->
  (forall l1 l2 l3 : list A, PermutationA eqA l1 l2 -> P l1 l2 -> PermutationA eqA l2 l3 -> P l2 l3 -> P l1 l3) ->
  forall l l0 : list A, PermutationA eqA l l0 -> P l l0.
Proof.
  intros. induction H5; subst; auto.
  - apply H3. generalize l. induction l0. constructor. constructor. reflexivity. assumption.
    apply H1.
  - eapply H4; eauto.
Qed.

Lemma drm_construct_1_well_behaved_helper: forall (m m' mx mx' : nmap nat) (n : nat),
    map_equiv m m' ->
    map_equiv mx mx' ->
    PermutationA map_equiv (drmcorrect.Map.fold (drm_inject_fold_step mx n) m [])
                 (drmcorrect.Map.fold (drm_inject_fold_step mx' n) m' []).
Proof.
  assert (Hs: forall (mx mx': nmap nat) (n: nat) l,
             map_equiv mx mx' ->
             eqlistA map_equiv (List.map (fun p : nat * nat => drm_inject_step mx n (fst p) (snd p)) l)
                     (List.map (fun p : nat * nat => drm_inject_step mx' n (fst p) (snd p)) l)).
  { intros mx mx' n l. revert n mx mx'. induction l; intros.
    - reflexivity.
    - simpl. constructor. 2: apply IHl; auto.
      unfold drm_inject_step. apply map_equiv_add.
      apply map_equiv_add. assumption. }
  intros m m' mx mx' n H. unfold map_equiv in *.
  unfold drm_construct_1 in *. unfold drm_inject in *.
  repeat rewrite drm_inject_fold_step_eq in *. repeat rewrite app_nil_l.
  revert n mx mx'.
  destruct m, m'. simpl in *. induction H; intros.
  - simpl. constructor.
  - simpl. destruct x as [k v]. simpl. constructor.
    + unfold drm_inject_step. apply map_equiv_add. apply map_equiv_add. apply H0.
    + apply IHPermutation; try eapply SetoidList_NoDupA_cons_rev; eauto.
  - simpl. apply PermA_swap_eqA. apply map_equiv_Equivalence.
    + generalize l; induction l0; try easy.
      constructor. 2: apply IHl0.
      unfold drm_inject_step. repeat apply map_equiv_add. assumption.
    + unfold drm_inject_step. repeat apply map_equiv_add. assumption.
    + unfold drm_inject_step. repeat apply map_equiv_add. assumption.
  - transitivity (List.map (fun p : nat * nat => drm_inject_step mx n (fst p) (snd p)) l').
    + etransitivity. apply IHPermutation1; auto.
      * eapply PermutationA_preserves_NoDupA; eauto.
        apply Raw.PX.eqk_equiv. apply Permutation_PermutationA.
        apply Raw.PX.eqk_equiv. symmetry. assumption.
      * apply eqlistA_PermutationA. apply Hs. reflexivity.
    + apply IHPermutation2; auto.
      eapply PermutationA_preserves_NoDupA; eauto.
      apply Raw.PX.eqk_equiv. symmetry.
      apply Permutation_PermutationA. apply Raw.PX.eqk_equiv.
      assumption.
Qed.

Corollary drm_construct_1_well_behaved: forall m m' n,
    map_equiv m m' ->
    PermutationA map_equiv (drm_construct_1 n m) (drm_construct_1 n m').
Proof.
  intros. apply drm_construct_1_well_behaved_helper; auto.
Qed.

Lemma InA_map_iff: forall {A B: Type} (eqA: A -> A -> Prop) x f (l: list B),
    (InA eqA x (List.map f l)) <-> (exists el, List.In el l /\ eqA x (f el)).
Proof.
  intros A B eqA x f l. induction l.
  - split; intros.
    + inversion H.
    + destruct H as [? [? ?]]. inversion H.
  - split; intros.
    + inversion H; subst.
      * exists a. split; auto. constructor. reflexivity.
      * apply IHl in H1. destruct H1 as [el [? ?]].
        exists el. split. constructor 2. assumption. assumption.
    + destruct H as [el [? ?]]. simpl. inversion H; subst.
      * constructor. assumption.
      * constructor 2. apply IHl. exists el. split; assumption.
Qed.

Lemma MapsTo_In_elements: forall k v m,
    MapsTo k v m <-> List.In (k, v) (elements (elt:=nat) m).
Proof.
  intros k v m. revert k v. destruct m. induction this0; intros.
  - split; intros; inversion H.
  - destruct a as [k' v']. destruct (nat_pair_dec k v k' v').
    + inversion e. subst. split; intros.
      * simpl. left. reflexivity.
      * unfold MapsTo. constructor. reflexivity.
    + split; intros.
      * { inversion H; subst.
          - inversion H1. simpl in *. subst. contradiction.
          - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
            assert (MapsTo k v {| this := this0; NoDup := H0 |}).
            { apply H1. }
            apply IHthis0 in H2. constructor 2. apply H2. }
      * { inversion H; subst.
          - inversion H0. simpl in *. subst. contradiction.
          - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
            assert (List.In (k, v) (elements (elt:=nat) {| this := this0; NoDup := H1 |})).
            { apply H0. }
            apply IHthis0 in H2. constructor 2. apply H2. }
Qed.

Lemma InA_drm_construct_1: forall x n m,
    ((InA map_equiv x (drm_construct_1 n m)) <->
     exists k v: nat, MapsTo k v m /\ map_equiv x (drm_inject_step m n k v)).
Proof.
  unfold drm_construct_1. unfold drm_inject. intros. split; intros.
  - rewrite drm_inject_fold_step_eq in H. simpl in H.
    apply InA_map_iff in H. destruct H as [[k v] [? ?]].
    exists k, v. simpl in H0. split; auto.
    apply elements_2. apply In_InA; auto.
    apply Raw.PX.eqke_equiv.
  - rewrite drm_inject_fold_step_eq. simpl.
    apply InA_map_iff. destruct H as [k [v [? ?]]].
    exists (k, v). split.
    + apply MapsTo_In_elements. assumption.
    + simpl. assumption.
Qed.

Lemma drm_construct_1_injective: forall m m' n x,
    drm m n ->
    drm m' n ->
    InA map_equiv x (drm_construct_1 n m) ->
    InA map_equiv x (drm_construct_1 n m') ->
    map_equiv m m'.
Proof.
  intros. apply InA_drm_construct_1 in H1.
  apply InA_drm_construct_1 in H2.
  destruct H1 as [k [v [? ?]]]. destruct H2 as [k' [v' [? ?]]].
  unfold drm_inject_step in *.
  apply map_equiv_MapsTo.
  rewrite map_equiv_MapsTo in H3. rewrite map_equiv_MapsTo in H4.
  intros.
  split; intros.
  - pose proof (H3 k0 v0).
    pose proof (H4 k0 v0).
    pose proof H5. eapply drm_MapsTo in H8; eauto.
    pose proof H1 as H8'. eapply drm_MapsTo in H8'; eauto.
    pose proof H2 as H8''. eapply drm_MapsTo in H8''; eauto.
    destruct (eq_dec k0 k).
    + subst k0. assert (v = v0).
      { eapply MapsTo_eq_v; eauto. } subst v0.
      assert (~ MapsTo k v (drmcorrect.Map.add n v (drmcorrect.Map.add k n m))).
      { intro. apply add_3 in H9; try lia. apply MapsTo_add_eq_v in H9. lia. }
      rewrite <- H6 in H9. rewrite H7 in H9.
      assert (~ MapsTo k v (drmcorrect.Map.add k' n m')).
      { intro. apply add_2 with (x:=n) (e':=v') in H10; try lia. contradiction. }
      destruct (eq_dec k k').
      * subst k'. pose proof (H3 n v'). pose proof (H4 n v').
        assert (MapsTo n v' (drmcorrect.Map.add n v' (drmcorrect.Map.add k n m'))).
        { apply MapsTo_add_eq. }
        rewrite <- H12 in H13. rewrite H11 in H13.
        apply MapsTo_add_eq_v in H13. subst v'. assumption.
      * assert (~ MapsTo k v m').
        { intro. apply add_2 with (x:=k') (e':=n) in H11; try lia. contradiction. }
        pose proof (H3 k' n). pose proof (H4 k' n).
        assert (MapsTo k' n (drmcorrect.Map.add n v' (drmcorrect.Map.add k' n m'))).
        { apply add_2; try lia. apply MapsTo_add_eq. }
        rewrite <- H13 in H14. rewrite H12 in H14.
        apply add_3 in H14; try lia. apply add_3 in H14; try lia.
        eapply drm_MapsTo in H14; eauto. lia.
    + assert (v <> v0).
      { intro. subst v0. contradict n0. eapply drm_MapsTo_inj. apply H. apply H5. apply H1. }
      assert (MapsTo k n (add n v (add k n m))).
      { apply add_2; try lia. apply MapsTo_add_eq. }
      rewrite <- H3 in H10. rewrite H4 in H10.
      destruct (eq_dec k k').
      * subst k'. assert (MapsTo n v' (add n v' (add k n m'))).
        { apply MapsTo_add_eq. }
        rewrite <- H4 in H11. rewrite H3 in H11. apply MapsTo_add_eq_v in H11. subst v'.
        assert (MapsTo k0 v0 (add n v (add k n m))).
        { apply add_2; try lia. apply add_2; try lia. assumption. }
        rewrite <- H3 in H11. rewrite H4 in H11.
        apply add_3 in H11; try lia. apply add_3 in H11; try lia. assumption.
      * apply add_3 in H10; try lia. apply add_3 in H10; try lia.
        eapply drm_MapsTo in H10; eauto. lia.
  - pose proof (H3 k0 v0).
    pose proof (H4 k0 v0).
    pose proof H5. eapply drm_MapsTo in H8; eauto.
    pose proof H1 as H8'. eapply drm_MapsTo in H8'; eauto.
    pose proof H2 as H8''. eapply drm_MapsTo in H8''; eauto.
    destruct (eq_dec k0 k').
    + subst k0. assert (v' = v0).
      { eapply MapsTo_eq_v; eauto. } subst v0.
      assert (~ MapsTo k v (drmcorrect.Map.add n v (drmcorrect.Map.add k n m))).
      { intro. apply add_3 in H9; try lia. apply MapsTo_add_eq_v in H9. lia. }
      rewrite <- H3 in H9. rewrite H4 in H9.
      assert (~ MapsTo k v (drmcorrect.Map.add k' n m')).
      { intro. apply add_2 with (x:=n) (e':=v') in H10; try lia. contradiction. }
      destruct (eq_dec k k').
      * subst k'. pose proof (H3 n v'). pose proof (H4 n v').
        assert (MapsTo n v' (drmcorrect.Map.add n v' (drmcorrect.Map.add k n m'))).
        { apply MapsTo_add_eq. }
        rewrite <- H12 in H13. rewrite H11 in H13.
        apply MapsTo_add_eq_v in H13. subst v'. assumption.
      * assert (~ MapsTo k v m').
        { intro. apply add_2 with (x:=k') (e':=n) in H11; try lia. contradiction. }
        pose proof (H3 k' n). pose proof (H4 k' n).
        assert (MapsTo k' n (drmcorrect.Map.add n v' (drmcorrect.Map.add k' n m'))).
        { apply add_2; try lia. apply MapsTo_add_eq. }
        rewrite <- H13 in H14. rewrite H12 in H14.
        apply add_3 in H14; try lia. apply add_3 in H14; try lia.
        eapply drm_MapsTo in H14; eauto. lia.
    + assert (v' <> v0).
      { intro. subst v0. contradict n0. eapply drm_MapsTo_inj. apply H0. apply H5. apply H2. }
      assert (MapsTo k n (add n v (add k n m))).
      { apply add_2; try lia. apply MapsTo_add_eq. }
      rewrite <- H3 in H10. rewrite H4 in H10.
      destruct (eq_dec k k').
      * subst k'. assert (MapsTo n v' (add n v' (add k n m'))).
        { apply MapsTo_add_eq. }
        rewrite <- H4 in H11. rewrite H3 in H11. apply MapsTo_add_eq_v in H11. subst v'.
        assert (MapsTo k0 v0 (add n v (add k n m'))).
        { apply add_2; try lia. apply add_2; try lia. assumption. }
        rewrite <- H4 in H11. rewrite H3 in H11.
        apply add_3 in H11; try lia. apply add_3 in H11; try lia. assumption.
      * apply add_3 in H10; try lia. apply add_3 in H10; try lia.
        eapply drm_MapsTo in H10; eauto. lia.
Qed.

Lemma drm_add_loop_simple_injective: forall m m' n last1 last2,
    n > 0 ->
    drm m (Nat.pred n) -> drm m' (Nat.pred n) -> last1 = (Nat.pred n) -> last2 = n ->
    map_equiv (drm_add_loop_simple m last1 last2) (drm_add_loop_simple m' last1 last2) ->
    map_equiv m m'.
Proof.
  intros. unfold drm_add_loop_simple in *. rewrite map_equiv_MapsTo in H4.
  apply map_equiv_MapsTo. intros. destruct (lt_dec k (Nat.pred n)).
  - split; intros.
    + assert (MapsTo k v (add last1 last2 (add last2 last1 m))).
      { apply add_2; try lia. apply add_2; try lia. assumption. }
      apply H4 in H6. apply add_3 in H6; try lia. apply add_3 in H6; try lia. assumption.
    + assert (MapsTo k v (add last1 last2 (add last2 last1 m'))).
      { apply add_2; try lia. apply add_2; try lia. assumption. }
      apply H4 in H6. apply add_3 in H6; try lia. apply add_3 in H6; try lia. assumption.
  - split; intros.
    + eapply drm_MapsTo in H5. 2: apply H0. lia.
    + eapply drm_MapsTo in H5. 2: apply H1. lia.
Qed.

Lemma drm_add_loop_step_injective_kkv: forall m m' n last1 last2 k' k v k0' k0 v0,
    n > 0 ->
    drm m (Nat.pred n) -> drm m' (Nat.pred n) -> last1 = (Nat.pred n) -> last2 = n ->
    k' < (Nat.pred n) -> k < (Nat.pred n) -> v < (Nat.pred n) -> k' <> k -> k <> v ->
    k0' < (Nat.pred n) -> k0 < (Nat.pred n) -> v0 < (Nat.pred n) -> k0' <> k0 -> k0 <> v0 ->
    map_equiv (drm_add_loop_step m last1 last2 k' k v) (drm_add_loop_step m' last1 last2 k0' k0 v0) ->
    (k' = k0' /\ k = k0 /\ v = v0).
Proof.
  intros. rewrite map_equiv_MapsTo in H14. unfold drm_add_loop_step in *.
  destruct (eq_dec k' k0').
  - subst k0'. destruct (eq_dec k k0).
    + subst k0. destruct (eq_dec v v0); try lia.
      assert (MapsTo last1 v (add k' last1 (add last1 v (add k last2 (add last2 k m))))).
      { apply add_2; try lia. apply MapsTo_add_eq. }
      apply H14 in H15. apply add_3 in H15; try lia. apply MapsTo_add_eq_v in H15. lia.
    + assert (MapsTo k last2 (add k' last1 (add last1 v (add k last2 (add last2 k m))))).
      { apply add_2; try lia. apply add_2; try lia. apply MapsTo_add_eq. }
      apply H14 in H15. apply add_3 in H15; try lia. apply add_3 in H15; try lia.
      apply add_3 in H15; try lia. apply add_3 in H15; try lia.
      eapply drm_MapsTo in H15; eauto. lia.
  - assert (MapsTo k' last1 (add k' last1 (add last1 v (add k last2 (add last2 k m))))).
    apply MapsTo_add_eq. apply H14 in H15.
    apply add_3 in H15; try lia. apply add_3 in H15; try lia.
    apply MapsTo_add_neq in H15; try lia. apply add_3 in H15; try lia.
    eapply drm_MapsTo in H15; eauto. lia.
Qed.

Lemma drm_add_loop_step_injective: forall m m' n last1 last2 k' k v,
    n > 0 ->
    drm m (Nat.pred n) -> drm m' (Nat.pred n) -> last1 = (Nat.pred n) -> last2 = n ->
    MapsTo k' k m -> MapsTo k v m -> MapsTo k' k m' -> MapsTo k v m' ->
    map_equiv (drm_add_loop_step m last1 last2 k' k v) (drm_add_loop_step m' last1 last2 k' k v) ->
    map_equiv m m'.
Proof.
  intros. unfold drm_add_loop_step in H8. rewrite map_equiv_MapsTo in H8.
  apply map_equiv_MapsTo. intros. destruct (ge_dec k0 (Nat.pred n)).
  - split; intros.
    + eapply drm_MapsTo in H9; eauto. lia.
    + eapply drm_MapsTo in H9; eauto. lia.
  - assert (k0 < Nat.pred n). lia. clear n0.
    destruct (ge_dec v0 (Nat.pred n)).
    + split; intros.
      * eapply drm_MapsTo in H10; eauto. lia.
      * eapply drm_MapsTo in H10; eauto. lia.
    + assert (v0 < Nat.pred n). lia.
      destruct (eq_dec k0 k).
      * { subst k0. split; intros.
          - eapply MapsTo_eq_v in H11. 2: apply H5. subst v0. assumption.
          - eapply MapsTo_eq_v in H11. 2: apply H7. subst v0. assumption. }
      * { destruct (eq_dec k0 k').
          - subst k0. split; intros.
            + eapply MapsTo_eq_v in H11. 2: apply H4. subst v0. assumption.
            + eapply MapsTo_eq_v in H11. 2: apply H6. subst v0. assumption.
          - split; intros.
            + assert (MapsTo k0 v0 (add k' last1 (add last1 v (add k last2 (add last2 k m))))).
              { repeat (apply add_2; try lia). assumption. }
              apply H8 in H12. repeat (apply add_3 in H12; try lia). assumption.
            + assert (MapsTo k0 v0 (add k' last1 (add last1 v (add k last2 (add last2 k m'))))).
              { repeat (apply add_2; try lia). assumption. }
              apply H8 in H12. repeat (apply add_3 in H12; try lia). assumption. }
Qed.

Lemma drm_add_loop_simple_step_false: forall m m' n last1 last2 k' k v,
    n > 0 ->
    drm m (Nat.pred n) -> drm m' (Nat.pred n) -> last1 = (Nat.pred n) -> last2 = n ->
    k' < Nat.pred n -> k < Nat.pred n -> v < Nat.pred n ->
    map_equiv (drm_add_loop_simple m last1 last2) (drm_add_loop_step m' last1 last2 k' k v) ->
    False.
Proof.
  intros m m' n last1 last2 k' k v Hn Hdm Hdm' Hl1 Hl2 Hk' Hk Hv Heq.
  rewrite map_equiv_MapsTo in Heq.
  unfold drm_add_loop_simple, drm_add_loop_step in Heq.
  assert (MapsTo last1 last2 (add last1 last2 (add last2 last1 m))). apply MapsTo_add_eq.
  apply Heq in H. apply add_3 in H; try lia. apply MapsTo_add_eq_v in H. lia.
Qed.

Lemma drm_add_loop_fold_eq: forall m m' last1 last2 a,
    fold (drm_add_loop_fold_step m' last1 last2) m a =
    a ++ List.concat (List.map (fun p => match (find (snd p) m') with
                                         | Some v => [(drm_add_loop_step m' last1 last2 (fst p) (snd p) v)]
                                         | None => []
                                         end)
                               (elements m)).
Proof.
  destruct m. induction this0; intros.
  - unfold fold. simpl. rewrite app_nil_r. reflexivity.
  - unfold fold in *. simpl in *. destruct a as [k' k].
    pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    rewrite (IHthis0 H). unfold drm_add_loop_fold_step. simpl.
    rewrite app_assoc. reflexivity.
Qed.

Lemma InA_concat_map: forall {A B: Type} (eqA: A -> A -> Prop) x f (l: list B),
    (InA eqA x (concat (List.map f l))) <->
    (exists y, List.In y l /\ InA eqA x (f y)).
Proof.
  intros A B eqA x f l. induction l.
  - split; intros. easy. destruct H as [? [? ?]]. easy.
  - split; intros.
    + simpl in *. apply InA_app in H. destruct H.
      * exists a. split. left. reflexivity. assumption.
      * apply IHl in H. destruct H as [y [? ?]].
        exists y. split. right. assumption. assumption.
    + destruct H as [y [? ?]]. inversion H; subst.
      * simpl. apply InA_app_iff. left. assumption.
      * simpl. apply InA_app_iff. right. apply IHl.
        exists y. easy.
Qed.

Lemma InA_drm_add_loop_fold: forall m n last1 last2 x a,
    drm m n ->
    InA map_equiv x (fold (drm_add_loop_fold_step m last1 last2) m a) <->
    (InA map_equiv x a \/ exists k' k v, MapsTo k' k m /\ MapsTo k v m /\ map_equiv x (drm_add_loop_step m last1 last2 k' k v)).
Proof.
  intros. split; intros.
  - rewrite drm_add_loop_fold_eq in H0. apply InA_app in H0. destruct H0.
    + left. assumption.
    + apply InA_concat_map in H0. destruct H0 as [y [? ?]].
      destruct y as [k v]. simpl in *.
      assert (MapsTo k v m).
      { unfold MapsTo. unfold Raw.PX.MapsTo.
        apply In_InA. apply Raw.PX.eqke_equiv. apply H0. }
      pose proof H2.
      eapply drm_MapsTo in H2; eauto.
      assert (v < n). lia.
      eapply drm_lt_MapsTo_1 in H4; eauto.
      destruct H4 as [v' ?].
      pose proof H4.
      apply find_1 in H4. rewrite H4 in H1.
      inversion H1; try easy; subst. right.
      exists k, v, v'. easy.
  - rewrite drm_add_loop_fold_eq. apply InA_app_iff. destruct H0; try (left; easy).
    right. apply InA_concat_map. destruct H0 as [k' [k [v [? [? ?]]]]].
    exists (k', k). simpl.
    apply find_1 in H1. rewrite H1. split.
    unfold MapsTo in H0. unfold Raw.PX.MapsTo in H0.
    apply InA_eqke_In. apply H0.
    constructor. assumption.
Qed.

Lemma drm_construct_2_injective: forall m m' n x,
    n > 0 ->
    drm m (Nat.pred n) ->
    drm m' (Nat.pred n) ->
    InA map_equiv x (drm_construct_2 n m) ->
    InA map_equiv x (drm_construct_2 n m') ->
    map_equiv m m'.
Proof.
  intros. unfold drm_construct_2 in *. unfold drm_add_loop in *.
  inversion H2; subst.
  - inversion H3; subst.
    + eapply drm_add_loop_simple_injective; eauto. simpl. destruct n; try lia. simpl.
      etransitivity. symmetry. eassumption. assumption.
    + rewrite drm_add_loop_fold_eq in H6. simpl in H6.
      apply InA_concat_map in H6. destruct H6 as [y [? ?]].
      destruct y as [k' k]. simpl in *.
      assert (MapsTo k' k m'). unfold MapsTo. apply In_InA. apply Raw.PX.eqke_equiv.
      apply H4. eapply drm_MapsTo in H7; eauto. destruct H7 as [? [? ?]].
      eapply drm_lt_MapsTo_1 in H9; eauto. destruct H9 as [v ?].
      apply find_1 in H9. rewrite H9 in H6. inversion H6; try easy; subst.
      exfalso. eapply drm_add_loop_simple_step_false with (k':=k') (k:=k) (v:=v). apply H.
      apply H0. apply H1. reflexivity. reflexivity. apply H8.
      apply find_2 in H9. eapply drm_MapsTo in H9; eauto. lia.
      apply find_2 in H9. eapply drm_MapsTo in H9; eauto. lia.
      transitivity x. symmetry. apply H5. apply H11.
  - inversion H3; subst; clear H2 H3.
    + rewrite drm_add_loop_fold_eq in H5. simpl in H5.
      apply InA_concat_map in H5. destruct H5 as [y [? ?]].
      destruct y as [k' k]. simpl in *.
      assert (MapsTo k' k m). unfold MapsTo. apply In_InA. apply Raw.PX.eqke_equiv.
      apply H2. eapply drm_MapsTo in H4; eauto. destruct H4 as [? [? ?]].
      eapply drm_lt_MapsTo_1 in H7. 2: apply H0. destruct H7 as [v ?].
      apply find_1 in H7. rewrite H7 in H3. inversion H3; try easy; subst.
      exfalso. eapply drm_add_loop_simple_step_false with (k':=k') (k:=k) (v:=v). apply H.
      apply H1. apply H0. reflexivity. reflexivity. apply H5.
      apply find_2 in H7. eapply drm_MapsTo in H7; eauto. lia.
      apply find_2 in H7. eapply drm_MapsTo in H7; eauto. lia.
      transitivity x. symmetry. apply H6. apply H9.
    + rewrite drm_add_loop_fold_eq in H5. rewrite drm_add_loop_fold_eq in H6.
      simpl in *. rewrite InA_concat_map in H5. rewrite InA_concat_map in H6.
      destruct H5 as [y [? ?]]. destruct H6 as [y' [? ?]].
      destruct y as [k v]. destruct y' as [k' v'].
      assert (MapsTo k v m). apply In_InA. apply Raw.PX.eqke_equiv. apply H2. pose proof H6 as H6M.
      assert (MapsTo k' v' m'). apply In_InA. apply Raw.PX.eqke_equiv. apply H4. pose proof H7 as H7M.
      eapply drm_MapsTo in H6; eauto. eapply drm_MapsTo in H7; eauto.
      destruct H6 as [? [? ?]]. destruct H7 as [? [? ?]]. simpl in *.
      eapply drm_lt_MapsTo_1 in H9. 2: apply H0. destruct H9 as [v0 ?]. pose proof H9 as H9M.
      apply find_1 in H9. rewrite H9 in H3.
      eapply drm_lt_MapsTo_1 in H11. 2: apply H1. destruct H11 as [v0' ?]. pose proof H11 as H11M.
      apply find_1 in H11. rewrite H11 in H5.
      inversion H3; try easy; subst. inversion H5; try easy; subst.
      assert (k = k' /\ v = v' /\ v0 = v0').
      { eapply drm_MapsTo in H6M; eauto. eapply drm_MapsTo in H7M; eauto.
        eapply drm_MapsTo in H9M; eauto. eapply drm_MapsTo in H11M; eauto.
        eapply drm_add_loop_step_injective_kkv with (n:=n); try lia.
        apply H0. apply H1. reflexivity. reflexivity.
        transitivity x. symmetry. auto. auto. }
      destruct H12 as [? [? ?]]. subst k' v' v0'.
      eapply drm_add_loop_step_injective with (n:=n); auto.
      apply H6M. apply H9M. auto. auto.
      transitivity x. symmetry. apply H13. auto.
Qed.


Theorem PermutationA_ind_bis :
 forall {A} (eqA: A -> A -> Prop) (H: Equivalence eqA) (P : list A -> list A -> Prop),
   (P [] []) ->
   (forall x x' l l', PermutationA eqA l l' -> eqA x x' -> P l l' -> P (x :: l) (x' :: l')) ->
   (forall x y l l', PermutationA eqA l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', PermutationA eqA l l' -> P l l' -> PermutationA eqA l' l'' -> P l' l'' -> P l l'') ->
   forall l l', PermutationA eqA l l' -> P l l'.
Proof.
  intros A eqA HeqA P Hnil Hskip Hswap Htrans.
  induction 1; auto.
  apply Htrans with (x::y::l); auto.
  constructor 3.
  apply Hswap; auto.
  apply Permutation_PermutationA; auto.
  induction l; auto. apply Hskip.
  apply Permutation_PermutationA; auto. reflexivity. assumption.
  apply Permutation_PermutationA; auto.
  apply Hskip; auto. apply Permutation_PermutationA; auto. reflexivity.
  apply Hskip; auto. apply Permutation_PermutationA; auto. reflexivity.
  induction l; auto. apply Hskip.
  apply Permutation_PermutationA; auto. reflexivity. assumption.
  eauto.
Qed.

Lemma PermA_InA_decomp: forall {A: Type} (eqA: A -> A -> Prop) l l' x,
    Equivalence eqA ->
    InA eqA x l -> PermutationA eqA l l' -> exists rl rr x', eqA x x' /\ l' = rl ++ [x'] ++ rr.
Proof.
  intros A eqA l l' x HeqA HinA Hp. revert HinA. revert Hp. revert l l'.
  refine (PermutationA_ind_bis eqA HeqA _ _ _ _ _); intros; try easy.
  - inversion HinA; subst.
    + exists [], l', x'. split; auto. etransitivity; eauto.
    + apply H1 in H3. destruct H3 as [rl [rr [x_ [? ?]]]].
      subst l'. exists (x' :: rl), rr, x_. split; auto.
  - inversion HinA; subst.
    + exists [x0], l', y. split; auto.
    + inversion H2; subst.
      * exists [], (y :: l'), x0. split; auto.
      * apply H0 in H3. destruct H3 as [rl [rr [x' [? ?]]]].
        exists (x0 :: y :: rl), rr, x'. subst l'. split; auto.
  - assert (InA eqA x l'). eapply PermA_InA; auto. symmetry. apply H. apply HinA.
    apply H0 in HinA. apply H2 in H3.
    destruct HinA as [rl1 [rr1 [x'1 [? ?]]]].
    destruct H3 as [rl2 [rr2 [x'2 [? ?]]]].
    exists rl2, rr2, x'2. split; assumption.
Qed.

Lemma PermA_add_inv: forall {A: Type} (eqA: A -> A -> Prop) l l',
    Equivalence eqA ->
    PermutationA eqA l l' -> forall lr rr lr' rr' x x', eqA x x' -> l = lr ++ [x] ++ rr -> l' = lr' ++ [x'] ++ rr' -> PermutationA eqA (lr ++ rr) (lr' ++ rr').
Proof.
  intros A eqA l l' HeqA. revert l l'.
  refine (PermutationA_ind_bis eqA HeqA  _ _ _ _ _); intros.
  - destruct lr; easy.
  - destruct lr, lr'; simpl in *.
    + inversion H3; subst. inversion H4; subst. assumption.
    + inversion H3; subst. inversion H4; subst. rename x0 into x. rename x'0 into x'.
      clear H3 H4.
      assert (InA eqA x' rr). eapply PermA_InA; eauto.
      apply InA_app_iff. right. constructor. reflexivity.
      assert (InA eqA x' (lr' ++ x' :: rr')). apply InA_app_iff. right. constructor. reflexivity.
      eapply PermA_InA_decomp with (l':=rr) in H3; auto. 2: reflexivity.
      destruct H3 as [s_lr [s_rr [s_x' [? ?]]]]. pose proof H5.
      eapply H1 in H5. 3: reflexivity. 2: symmetry; assumption. subst rr.
      etransitivity. apply PermutationA_app_comm; auto. simpl.
      constructor. etransitivity. symmetry. apply H3. etransitivity. symmetry.
      apply H2. assumption. etransitivity. apply PermutationA_app_comm; auto.
      assumption.
    + inversion H3; subst. inversion H4; subst. rename x0 into x. rename x'0 into x'.
      clear H3 H4.
      assert (InA eqA x rr'). eapply PermA_InA; auto. symmetry. apply H.
      apply InA_app_iff. right. constructor. reflexivity.
      assert (InA eqA x (lr ++ x :: rr)). apply InA_app_iff. right. constructor. reflexivity.
      eapply PermA_InA_decomp with (l':=rr') in H4; auto.
      destruct H4 as [s_lr [s_rr [s_x' [? ?]]]]. pose proof H5.
      eapply H1 in H5. 3: reflexivity. 2: assumption. subst rr'.
      symmetry. etransitivity. apply PermutationA_app_comm; auto. simpl.
      constructor. etransitivity. symmetry. apply H4. etransitivity.
      apply H2. symmetry. assumption. etransitivity. apply PermutationA_app_comm; auto.
      symmetry. assumption.
    + assert (l = lr ++ x0 :: rr). inversion H3; subst. reflexivity.
      assert (l' = lr' ++ x'0 :: rr'). inversion H4; subst. reflexivity.
      assert (x = a). inversion H3; subst. reflexivity. subst a.
      assert (x' = a0). inversion H4; subst. reflexivity. subst a0.
      clear H3 H4. constructor. assumption. eapply H1; eauto.
  - destruct lr, lr'; simpl in H2, H3.
    + destruct rr, rr'; try easy.
      inversion H2. subst x0 a rr. inversion H3. subst x' a0 rr'.
      simpl. constructor. symmetry. assumption. assumption.
    + destruct rr; try easy. inversion H2. subst x0 a0 rr.
      destruct lr'.
      * simpl in H3. inversion H3. subst a x' rr'. simpl.
        constructor. reflexivity. assumption.
      * simpl in H3. inversion H3. subst a a0 l'.
        simpl. constructor. reflexivity. etransitivity. apply H.
        etransitivity. apply PermutationA_app_comm; auto. simpl.
        constructor. symmetry. assumption. etransitivity.
        apply PermutationA_app_comm; auto. reflexivity.
    + destruct rr'; try easy. inversion H3. subst x' a0 rr'.
      destruct lr.
      * simpl in H2. inversion H2. subst a x0 rr. simpl.
        constructor. reflexivity. assumption.
      * simpl in H2. inversion H2. subst a a0 l.
        simpl. constructor. reflexivity. etransitivity. 2: apply H.
        symmetry. etransitivity. apply PermutationA_app_comm; auto. simpl.
        constructor. assumption. etransitivity.
        apply PermutationA_app_comm; auto. reflexivity.
    + destruct lr, lr'; simpl in H2, H3.
      * inversion H2. subst a x0 rr. inversion H3. subst a0 x' rr'.
        constructor. symmetry. assumption. assumption.
      * inversion H2. subst a x0 rr. inversion H3. subst a0 a1 l'.
        simpl. transitivity (y :: x :: lr' ++ rr'). 2: constructor 3.
        constructor. reflexivity.
        etransitivity. apply H. etransitivity. apply PermutationA_app_comm; auto.
        simpl. constructor. symmetry. assumption. etransitivity.
        apply PermutationA_app_comm; auto. reflexivity.
      * inversion H2. subst a a1 l. inversion H3. subst a0 x' rr'.
        simpl. transitivity (x :: y :: lr ++ rr). constructor 3.
        constructor. reflexivity.
        etransitivity. 2: apply H. etransitivity. 2: apply PermutationA_app_comm; auto.
        simpl. constructor. symmetry. assumption. etransitivity.
        apply PermutationA_app_comm; auto. reflexivity.
      * inversion H2. subst a a1 l. inversion H3. subst a0 a2 l'.
        simpl. transitivity (x :: y :: lr ++ rr). constructor 3.
        constructor. reflexivity. constructor. reflexivity.
        eapply H0. apply H1. simpl. reflexivity. simpl. reflexivity.
  - assert (InA eqA x l). subst l. rewrite InA_app_iff. right. constructor. reflexivity.
    eapply PermA_InA_decomp in H6; auto. 2: apply H. destruct H6 as [lr'' [rr'' [x'' [? ?]]]].
    transitivity (lr'' ++ rr''). eapply H0. 3: apply H7. 2: apply H4. auto.
    eapply H2. 3: apply H5. 2: apply H7. etransitivity. symmetry. apply H6. assumption.
Qed.

Lemma PermA_cons_inv: forall {A: Type} (eqA: A -> A -> Prop) x x' l l',
    Equivalence eqA ->
    eqA x x' -> PermutationA eqA (x :: l) (x' :: l') -> PermutationA eqA l l'.
Proof.
  intros. change l with ([] ++ l). change l' with ([] ++ l').
  eapply PermA_add_inv; auto. 2: apply H0. simpl. assumption.
Qed.


Lemma drm_construct_2_well_behaved_helper: forall (m m' mx mx' : nmap nat) (n last1 last2 : nat),
    n > 0 -> last1 = Nat.pred n -> last2 = n ->
    map_equiv m m' ->
    map_equiv mx mx' ->
    (PermutationA map_equiv
                  ((drm_add_loop_simple mx last1 last2)
                     :: (fold (drm_add_loop_fold_step mx last1 last2) m []))
                  ((drm_add_loop_simple mx' last1 last2)
                     :: (fold (drm_add_loop_fold_step mx' last1 last2) m' []))).
Proof.
  assert (Hconcat: forall mx mx' last1 last2 l,
             map_equiv mx mx' ->
             PermutationA map_equiv
                          (concat
                             (List.map
                                (fun p : nat * key =>
                                   match find (snd p) mx with
                                   | Some v => [drm_add_loop_step mx last1 last2 (fst p) (snd p) v]
                                   | None => []
                                   end) l))
                          (concat
                             (List.map
                                (fun p : nat * key =>
                                   match find (snd p) mx' with
                                   | Some v => [drm_add_loop_step mx' last1 last2 (fst p) (snd p) v]
                                   | None => []
                                   end) l))).
    { intros. induction l. simpl. constructor.
      simpl. destruct a as [a0 a1]. simpl.
      destruct (find a1 mx) eqn:Ea1.
      - assert (find a1 mx' = Some n).
        { apply find_1. rewrite map_equiv_MapsTo in H. apply H. apply find_2. assumption. }
        rewrite H0. simpl. constructor.
        unfold drm_add_loop_step. repeat apply map_equiv_add. assumption.
        apply IHl.
      - assert (find a1 mx' = None).
        { destruct (find a1 mx') eqn:Ea1'; try easy.
          apply find_2 in Ea1'. rewrite map_equiv_MapsTo in H. apply H in Ea1'.
          apply find_1 in Ea1'. rewrite Ea1 in Ea1'. discriminate Ea1'. }
        rewrite H0. simpl. apply IHl. }

  intros m m' mx mx' n last1 last2 Hn Hlast1 Hlast2 Hm Hmx.
  unfold map_equiv in Hm. destruct m, m'. simpl in *.
  unfold drm_add_loop_simple. repeat rewrite drm_add_loop_fold_eq. simpl.
  induction Hm; simpl.
  - intros. constructor. 2: constructor. apply map_equiv_add.
    apply map_equiv_add. assumption.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup0).
    pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup1).
    apply IHHm in H0; auto. clear IHHm H.
    constructor. repeat apply map_equiv_add. assumption.
    transitivity (match find (snd x) mx' with
                  | Some v => [drm_add_loop_step mx' last1 last2 (fst x) (snd x) v]
                  | None => []
                  end ++
                      concat
                      (List.map
                         (fun p : nat * key =>
                            match find (snd p) mx with
                            | Some v => [drm_add_loop_step mx last1 last2 (fst p) (snd p) v]
                            | None => []
                            end) l)).
    + apply PermutationA_app_tail. apply map_equiv_Equivalence.
      destruct x as [x0 x1]. simpl. destruct (find x1 mx) eqn:E.
      * assert (MapsTo x1 n0 mx). apply find_2. assumption.
        rewrite map_equiv_MapsTo in Hmx. rewrite Hmx in H.
        apply find_1 in H. rewrite H. constructor; try constructor.
        unfold drm_add_loop_step. repeat apply map_equiv_add.
        rewrite map_equiv_MapsTo. assumption.
      * { destruct (find x1 mx') eqn:E'.
          + apply find_2 in E'. rewrite map_equiv_MapsTo in Hmx.
            apply Hmx in E'. apply find_1 in E'. rewrite E in E'. discriminate E'.
          + constructor. }
    + apply PermutationA_app_head. apply map_equiv_Equivalence.
      apply PermA_cons_inv in H0. 2: apply map_equiv_Equivalence.
      2: apply map_equiv_add. 2: apply map_equiv_add. 2: assumption.
      assumption.

  - constructor. repeat apply map_equiv_add. assumption.
    destruct y as [y0 y1]. destruct x as [x0 x1]. simpl.
    destruct (find y1 mx) eqn:Ey.
    + assert (find y1 mx' = Some n0).
      { apply find_1. rewrite map_equiv_MapsTo in Hmx. apply Hmx. apply find_2. assumption. }
      rewrite H. destruct (find x1 mx) eqn:Ex.
      * { assert (find x1 mx' = Some n1).
          { apply find_1. rewrite map_equiv_MapsTo in Hmx. apply Hmx. apply find_2. assumption. }
          rewrite H0. simpl. etransitivity. constructor 3.
          constructor. unfold drm_add_loop_step. repeat apply map_equiv_add. assumption.
          constructor. unfold drm_add_loop_step. repeat apply map_equiv_add. assumption.
          apply Hconcat; auto. }
      * assert (find x1 mx' = None).
        { destruct (find x1 mx') eqn:Ex'; try easy.
          apply find_2 in Ex'. rewrite map_equiv_MapsTo in Hmx. apply Hmx in Ex'.
          apply find_1 in Ex'. rewrite Ex in Ex'. discriminate Ex'. }
        rewrite H0. simpl. constructor. unfold drm_add_loop_step. repeat apply map_equiv_add. tauto.
        apply Hconcat; auto.
    + assert (find y1 mx' = None).
      { destruct (find y1 mx') eqn:Ey'; try easy.
        apply find_2 in Ey'. rewrite map_equiv_MapsTo in Hmx. apply Hmx in Ey'.
        apply find_1 in Ey'. rewrite Ey in Ey'. discriminate Ey'. }
      rewrite H. simpl. destruct (find x1 mx) eqn:Ex.
      * assert (find x1 mx' = Some n0).
        { apply find_1. rewrite map_equiv_MapsTo in Hmx. apply Hmx. apply find_2. assumption. }
        rewrite H0. simpl. constructor. unfold drm_add_loop_step. repeat apply map_equiv_add. tauto.
        apply Hconcat; auto.
      * assert (find x1 mx' = None).
        { destruct (find x1 mx') eqn:Ex'; try easy.
          apply find_2 in Ex'. rewrite map_equiv_MapsTo in Hmx. apply Hmx in Ex'.
          apply find_1 in Ex'. rewrite Ex in Ex'. discriminate Ex'. }
        rewrite H0. simpl. apply Hconcat; auto.
  - assert (NoDupA (Raw.PX.eqk (elt:=nat)) l').
    { eapply PermutationA_preserves_NoDupA. apply Raw.PX.eqk_equiv.
      apply Permutation_PermutationA. apply Raw.PX.eqk_equiv. apply Hm1. assumption. }
    pose proof (IHHm1 NoDup0 H) as IH1. clear IHHm1.
    pose proof (IHHm2 H NoDup1) as IH2. clear IHHm2.
    etransitivity. apply IH1. etransitivity. 2: apply IH2.
    constructor. repeat apply map_equiv_add. symmetry. assumption.
    apply Hconcat. symmetry. assumption.
Qed.

Corollary drm_construct_2_well_behaved: forall m m' n,
    n > 0 ->
    map_equiv m m' ->
    PermutationA map_equiv (drm_construct_2 n m) (drm_construct_2 n m').
Proof.
  intros. unfold drm_construct_2. unfold drm_add_loop.
  eapply drm_construct_2_well_behaved_helper with (n:=n); try lia; auto.
Qed.

Lemma map_equiv_add_v_inv: forall (k : key) (v v' : nat) (m m' : nmap nat),
    map_equiv (add k v m) (add k v' m') ->
    v = v'.
Proof.
  intros. rewrite map_equiv_MapsTo in H.
  assert (MapsTo k v (add k v m)). apply MapsTo_add_eq.
  apply H in H0. apply MapsTo_add_eq_v in H0. assumption.
Qed.

Lemma drm_construct_1_NoDupA_helper: forall (m: nmap nat) (n: nat) (mx: nmap nat),
    drm mx n ->
    (forall k v, List.In (k, v) (elements m) -> k < n /\ v < n) ->
    NoDupA map_equiv (drmcorrect.Map.fold (drm_inject_fold_step mx n) m []).
Proof.
  intros. rewrite drm_inject_fold_step_eq. simpl. destruct m. induction this0.
  - simpl. constructor.
  - simpl. constructor.
    + intro Hc. apply InA_map_iff in Hc. destruct Hc as [x [? ?]].
      destruct a as [a0 a1]. destruct x as [x0 x1].
      unfold drm_inject_step in *. simpl in *.
      assert (a1 = x1). eapply map_equiv_add_v_inv. apply H2. subst a1.
      assert (a0 = x0).
      { rewrite map_equiv_MapsTo in H2.
        assert (a0 < n).
        { pose proof (H0 a0 x1). apply H3. left. reflexivity. }
        assert (MapsTo a0 n (add n x1 (add a0 n mx))).
        { apply add_2; try lia. apply MapsTo_add_eq. }
        apply H2 in H4. apply add_3 in H4; try lia. destruct (eq_dec a0 x0); try easy.
        apply add_3 in H4; try lia.
        eapply drm_MapsTo in H4; eauto. lia. }
      subst a0. inversion NoDup0. contradict H5. apply In_InA. apply Raw.PX.eqk_equiv. tauto.
    + inversion NoDup0; subst. apply (IHthis0 H4). intros.
      simpl in *. apply H0. right. assumption.
Qed.

Lemma drm_construct_1_NoDupA: forall m n,
    drm m n ->
    NoDupA map_equiv (drm_construct_1 n m).
Proof.
  unfold drm_construct_1. unfold drm_inject.
  intros. apply drm_construct_1_NoDupA_helper; auto.
  intros.
  assert (MapsTo k v m).
  { unfold MapsTo. unfold Raw.PX.MapsTo. apply In_InA. apply Raw.PX.eqke_equiv. apply H0. }
  eapply drm_MapsTo in H1; eauto. lia.
Qed.

Lemma NoDupA_concat_map: forall {A B: Type} (eqA: A -> A -> Prop) (eqB: B -> B -> Prop) (l: list A) f,
    Equivalence eqA ->
    Equivalence eqB ->
    NoDupA eqA l ->
    (forall x, List.In x l -> NoDupA eqB (f x)) ->
    (forall x y m, List.In x l -> List.In y l -> InA eqB m (f x) -> InA eqB m (f y) -> eqA x y) ->
    NoDupA eqB (concat (List.map f l)).
Proof.
  intros A B eqA eqB l. induction l; intros.
  - constructor.
  - simpl. apply NoDupA_app; auto.
    + apply H2. constructor. reflexivity.
    + apply IHl; auto.
      * inversion H1; subst. assumption.
      * intros. apply H2. right. assumption.
      * { intros. eapply H3.
          - right. assumption.
          - right. assumption.
          - eassumption.
          - assumption. }
    + intros. rewrite InA_concat_map in H5. destruct H5 as [y [? ?]].
      eapply H3 in H6.
      * inversion H1; subst. apply H9. eapply InA_eqA; auto. symmetry. apply H6.
        apply In_InA; auto.
      * left. reflexivity.
      * right. assumption.
      * assumption.
Qed.

Lemma drm_construct_2_NoDupA: forall m n,
    n > 0 ->
    drm m (Nat.pred n) ->
    NoDupA map_equiv (drm_construct_2 n m).
Proof.
  intros. unfold drm_construct_2. unfold drm_add_loop. constructor.
  - intro. rewrite drm_add_loop_fold_eq in H1. simpl in H1.
    apply InA_concat_map in H1. destruct H1 as [[k v] [? ?]]. simpl in H2.
    destruct (find v m) eqn:E; try easy. apply find_2 in E.
    inversion H2; try easy; subst.
    assert (MapsTo k v m).
    { unfold MapsTo. unfold Raw.PX.MapsTo. apply In_InA. apply Raw.PX.eqke_equiv. apply H1. }
    pose proof E. eapply drm_MapsTo in H5; eauto.
    pose proof H3. eapply drm_MapsTo in H6; eauto.
    eapply drm_add_loop_simple_step_false; eauto; lia.
  - rewrite drm_add_loop_fold_eq. simpl. destruct m. simpl.
    eapply NoDupA_concat_map. apply Raw.PX.eqk_equiv. apply map_equiv_Equivalence.
    assumption. intros. destruct x. simpl.
    destruct (find k {| this := this0; NoDup := NoDup0 |}); try easy. constructor; easy.
    intros. destruct x, y. simpl in *.
    destruct (find k {| this := this0; NoDup := NoDup0 |}) eqn:E1; try easy.
    destruct (find k0 {| this := this0; NoDup := NoDup0 |}) eqn:E2; try easy.
    inversion H3; subst; try easy. inversion H4; subst; try easy. clear H3 H4.
    assert (map_equiv (drm_add_loop_step {| this := this0; NoDup := NoDup0 |} (Nat.pred n) n n0 k n2)
                      (drm_add_loop_step {| this := this0; NoDup := NoDup0 |} (Nat.pred n) n n1 k0 n3)).
    etransitivity. symmetry. eassumption. assumption.
    assert (MapsTo n0 k {| this := this0; NoDup := NoDup0 |}).
    { apply In_InA. apply Raw.PX.eqke_equiv. apply H1. }
    assert (MapsTo n1 k0 {| this := this0; NoDup := NoDup0 |}).
    { apply In_InA. apply Raw.PX.eqke_equiv. apply H2. }
    apply find_2 in E1. apply find_2 in E2.
    eapply drm_MapsTo in H4. 2: apply H0. eapply drm_MapsTo in H5. 2: apply H0.
    eapply drm_MapsTo in E1. 2: apply H0. eapply drm_MapsTo in E2. 2: apply H0.
    eapply drm_add_loop_step_injective_kkv in H3.
    3, 4: apply H0. 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14: lia.
    unfold Raw.PX.eqk. simpl. lia.
Qed.

Lemma InA_drm_construct_2: forall x n m,
    drm m (Nat.pred n) ->
    (InA map_equiv x (drm_construct_2 n m)) <->
    ((map_equiv x (drm_add_loop_simple m (Nat.pred n) n))
     \/ (exists k' k v, MapsTo k' k m /\ MapsTo k v m /\ map_equiv x (drm_add_loop_step m (Nat.pred n) n k' k v))).
Proof.
  intros. split; intros.
  - unfold drm_construct_2 in *. unfold drm_add_loop in H. inversion H0; subst.
    + left. assumption.
    + right. eapply InA_drm_add_loop_fold in H2. 2: apply H.
      destruct H2; easy.
  - unfold drm_construct_2 in *. unfold drm_add_loop in *. destruct H0.
    + constructor. assumption.
    + right. eapply InA_drm_add_loop_fold. apply H. right. assumption.
Qed.

Lemma drm_construct_1_2_false: forall m m' n x,
    n > 0 ->
    drm m n -> drm m' (Nat.pred n) ->
    InA map_equiv x (drm_construct_1 n m) ->
    InA map_equiv x (drm_construct_2 n m') ->
    False.
Proof.
  intros. rewrite InA_drm_construct_1 in H2.
  rewrite InA_drm_construct_2 in H3. 2: apply H1.
  destruct H2 as [k [v [? ?]]]. unfold drm_inject_step in *.
  rewrite map_equiv_MapsTo in H4.
  destruct H3.
  - unfold drm_add_loop_simple in H3.
    rewrite map_equiv_MapsTo in H3.
    destruct (eq_dec k (Nat.pred n)).
    + subst k. destruct (eq_dec v (Nat.pred n)).
      * subst v. eapply drm_MapsTo in H2; eauto. lia.
      * assert (MapsTo n (Nat.pred n) (add (Nat.pred n) n (add n (Nat.pred n) m'))).
        { apply add_2; try lia. apply MapsTo_add_eq. }
        apply H3 in H5. apply H4 in H5. apply MapsTo_add_eq_v in H5. lia.
    + assert (MapsTo (Nat.pred n) n (add (Nat.pred n) n (add n (Nat.pred n) m'))).
      { apply MapsTo_add_eq. }
      apply H3 in H5. apply H4 in H5. apply add_3 in H5; try lia.
      apply add_3 in H5; try lia. eapply drm_MapsTo in H5; eauto. lia.
  - unfold drm_add_loop_step in H3. destruct H3 as [_k' [_k [_v [? [? ?]]]]].
    rewrite map_equiv_MapsTo in H6.
    assert (_k' < Nat.pred n /\ _k < Nat.pred n /\ _v < Nat.pred n /\ _k' <> _k /\ _k <> _v).
    { eapply drm_MapsTo in H3; eauto. eapply drm_MapsTo in H5; eauto. lia. }
    assert (MapsTo _k n (add _k' (Nat.pred n) (add (Nat.pred n) _v (add _k n (add n _k m'))))).
    { apply add_2; try lia. apply add_2; try lia. apply MapsTo_add_eq. }
    apply H6 in H8. apply H4 in H8. apply add_3 in H8; try lia.
    destruct (eq_dec _k k).
    + subst _k.
      assert (MapsTo n k (add _k' (Nat.pred n) (add (Nat.pred n) _v (add k n (add n k m'))))).
      { apply add_2; try lia. apply add_2; try lia. apply add_2; try lia. apply MapsTo_add_eq. }
      apply H6 in H9. apply H4 in H9. eapply MapsTo_add_eq_v in H9. eapply drm_MapsTo in H2; eauto. lia.
    + apply add_3 in H8; try lia. eapply drm_MapsTo in H8; eauto. lia.
Qed.


Theorem drm_construct_NoDupA: forall n,
    NoDupA map_equiv (drm_construct n).
Proof.
  induction n using Wf_nat.lt_wf_ind.
  destruct n.
  - constructor. intro; easy. constructor.
  - simpl. destruct n.
    + constructor.
    + apply NoDupA_concat_map_app_drm with (n:=(S n)) (n':=(Nat.pred (S n))).
      * apply drm_construct_correct.
      * simpl. apply drm_construct_correct.
      * apply H. lia.
      * simpl. apply H. lia.
      * intros. apply drm_construct_1_NoDupA. assumption.
      * intros. apply drm_construct_2_NoDupA. lia. assumption.
      * intros. apply Forall_forall. intros. unfold drm_construct_1 in *.
        apply drm_inject_drms in H1. 2: assumption. exists (S (S n)).
        assumption.
      * intros. apply Forall_forall. intros. unfold drm_construct_2 in *.
        apply drm_add_loop_drms in H1. exists (S (S n)). assumption.
        simpl in *. assumption.
      * intros. apply drm_construct_1_well_behaved. assumption.
      * intros. apply drm_construct_2_well_behaved. lia. assumption.
      * intros. eapply drm_construct_1_injective; eauto.
      * intros. eapply drm_construct_2_injective. 2: apply H0.
        lia. assumption. eassumption. assumption.
      * intros. eapply drm_construct_1_2_false. 2: apply H0. lia.
        eassumption. eassumption. assumption.
Qed.
