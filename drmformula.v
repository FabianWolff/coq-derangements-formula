Require Import Exp_prop Rbase Rdefinitions Rfunctions Reals Lia.

Lemma lt_onehalf_if: forall a b: R,
    (0 < a)%R -> (0 < b)%R ->
    (b > 2 * a)%R -> ((a / b) < / 2)%R.
Proof.
  intros. apply Rmult_lt_reg_r with (r:=b); auto.
  apply Rmult_lt_reg_r with (r:=2%R). apply Rlt_0_2.
  unfold Rdiv. rewrite Rmult_comm.
  replace (a * / b * b)%R with (a * b * / b)%R.
  + rewrite Rinv_r_simpl_l. 2: apply Rgt_not_eq; auto.
    replace (/ 2 * b * 2)%R with (b * 2 * / 2)%R.
    * rewrite Rinv_r_simpl_l. 2: apply Rgt_not_eq; apply Rlt_0_2.
      apply H1.
    * rewrite Rmult_comm. rewrite Rmult_assoc. reflexivity.
  + rewrite Rmult_assoc. rewrite Rmult_assoc.
    replace (b * / b)%R with (/ b * b)%R. 2: apply Rmult_comm.
    reflexivity.
Qed.

Lemma INR_lt_onehalf_if: forall a b,
    (b > 2 * a) -> (((INR a) / (INR b)) < / 2)%R.
Proof.
  intros. destruct a, b.
  - inversion H.
  - simpl. unfold Rdiv. rewrite Rmult_0_l. apply Rinv_0_lt_compat. apply Rlt_0_2.
  - inversion H.
  - assert (b > 2*a + 1). lia. apply lt_onehalf_if.
    + apply lt_0_INR. lia.
    + apply lt_0_INR. lia.
    + change 2%R with (INR 2)%R. rewrite <- mult_INR. apply Rlt_gt.
      apply lt_INR. lia.
Qed.

Definition drm_count_as_sum (n: nat) := ((INR (fact n)) * (E1 (-1) n))%R.

Fixpoint fact_n_k (n k: nat): nat :=
  match k with
  | 0 => 1
  | S k' => ((Nat.max 1 n) + k - 1) * (fact_n_k n k')
  end.

Lemma fact_1_k: forall k, (fact_n_k 1 k) = (fact k).
Proof.
  induction k; simpl; auto.
Qed.

Lemma INR_S_neq_0: forall n, ((INR (S n)) <> 0)%R.
Proof.
  intro. change 0%R with (INR 0). apply not_INR. lia.
Qed.

Lemma INR_fact_n_k_gt_0: forall n k, ((INR (fact_n_k n k)) > 0)%R.
Proof.
  intros. apply Rlt_gt. change 0%R with (INR 0).
  apply lt_INR. revert n. induction k; intros; simpl.
  destruct n; try lia.
  replace (n + S k) with (S (n + k)). 2: lia.
  simpl. pose proof (IHk n).
  replace (n + k - 0) with (n + k). 2: lia.
  destruct n; lia.
Qed.

Corollary INR_fact_n_k_neq_0: forall n k, ((INR (fact_n_k n k)) <> 0)%R.
Proof.
  intros. apply Rgt_not_eq. apply INR_fact_n_k_gt_0.
Qed.

Lemma Rinv_eq_compat: forall r1 r2: R, r1 <> 0%R -> r2 <> 0%R -> (r1 = r2 <-> / r1 = / r2)%R.
Proof.
  intros. split; intros. subst r1. reflexivity.
  apply Rmult_eq_compat_r with (r:=r1) in H1.
  apply Rmult_eq_compat_r with (r:=r2) in H1.
  rewrite Rinv_l in H1; auto. rewrite Rmult_1_l in H1.
  rewrite Rmult_comm in H1. rewrite <- Rmult_assoc in H1.
  rewrite Rinv_r in H1; auto. rewrite Rmult_1_l in H1.
  subst r2. reflexivity.
Qed.

Lemma eq_INR: forall n m, n = m -> INR n = INR m.
Proof.
  intros. subst n. reflexivity.
Qed.

Lemma neg_1_mult_neg_1: ((-1) * (-1) = 1)%R.
Proof.
  rewrite <- mult_IZR. simpl. reflexivity.
Qed.

Lemma neg_1_mult: forall a, (((-1) * a) = - a)%R.
Proof.
  intros.
  change (-1)%R with (- IZR 1)%R.
  rewrite <- Ropp_mult_distr_l.
  rewrite Rmult_1_l. reflexivity.
Qed.

Definition inv_fact_n_k (n k: nat): R := (/ (INR (fact_n_k n k)))%R.

Lemma fact_fact_n_k: forall n k: nat, (((INR (fact n)) / (INR (fact (n + k)))) = (inv_fact_n_k (n + 1) k))%R.
Proof.
  unfold inv_fact_n_k.
  intros n k. revert n. induction k; intros.
  - simpl. rewrite plus_0_r. unfold Rdiv.
    replace (n + 1) with (S n). 2: lia. rewrite Rinv_r. 2: apply INR_fact_neq_0.
    symmetry. apply Rinv_1.
  - unfold Rdiv. replace (n + S k) with (S (n + k)). 2: lia.
    change (fact (S (n + k))) with ((S (n + k)) * (fact (n + k))).
    rewrite mult_INR. rewrite Rinv_mult_distr. 3: apply INR_fact_neq_0.
    2: change 0%R with (INR 0). 2: apply not_INR. 2: lia.
    rewrite Rmult_comm with (r1:=(/ INR (S (n + k)))%R).
    rewrite <- Rmult_assoc. unfold Rdiv in IHk. rewrite IHk.
    rewrite <- Rinv_mult_distr. 2: apply INR_fact_n_k_neq_0. 2: apply INR_S_neq_0.
    rewrite <- mult_INR.
    rewrite <- Rinv_eq_compat. 3: apply INR_fact_n_k_neq_0.
    + apply eq_INR. replace (S (n + k)) with ((n + 1) + k). 2: lia.
      rewrite Nat.mul_add_distr_l. simpl. replace (n + 1) with (S n); try lia.
    + change 0%R with (INR 0). apply not_INR. apply Nat.neq_mul_0. split.
      * apply INR_not_0. apply INR_fact_n_k_neq_0.
      * lia.
Qed.

Lemma fact_n_k_gt_0: forall n k, (fact_n_k n k) > 0.
Proof.
  intros.
  revert k n. induction k; intros; simpl; try lia.
  destruct n; simpl.
  - pose proof (IHk 0). lia.
  - replace (n + S k - 0) with (n + S k). 2: lia.
    rewrite Nat.mul_add_distr_r. pose proof (IHk (S n)).
    lia.
Qed.

Lemma fact_n_k_lt: forall n k k', k > k' -> n > 1 -> ((fact_n_k n k) > (fact_n_k n k')).
Proof.
  intros n k. revert n. induction k; intros; try lia.
  destruct (gt_dec k k').
  - eapply IHk in g. 2: apply H0. eapply gt_trans. 2: apply g.
    simpl. destruct n; try lia.
    destruct (fact_n_k (S n) k); try lia.
  - assert (k = k'). lia. subst k'.
    simpl. destruct n; try lia.
    assert (fact_n_k (S n) k > 0). apply fact_n_k_gt_0.
    destruct (fact_n_k (S n) k); try lia.
Qed.

Corollary INR_fact_n_k_lt: forall n k k', k > k' -> n > 1 -> (INR (fact_n_k n k) > INR (fact_n_k n k'))%R.
Proof.
  intros. apply lt_INR. apply fact_n_k_lt; lia.
Qed.

Lemma even_exists: forall n: nat, (Nat.even n = true) -> exists n': nat, 2 * n' = n.
Proof.    
  induction n using Wf_nat.lt_wf_ind. intros.
  destruct n.
  - exists 0. lia.
  - destruct n.
    + inversion H0.
    + assert (Nat.even n = true).
      { rewrite <- Nat.even_succ_succ. apply H0. }
      apply H in H1. 2: lia. destruct H1. exists (S x). lia.
Qed.

Lemma not_even_S_n: forall n: nat, (Nat.even n = false) -> Nat.even (S n) = true.
Proof.
  intros. rewrite Nat.even_succ. rewrite <- Nat.negb_odd in H.
  destruct (Nat.odd n); auto.
Qed.

Definition rest_sum (n N: nat) :=
  sum_f_R0 (fun k => (inv_fact_n_k (n + 1) (k + 1)) * ((-1) ^ k))%R (N - n - 1).

Lemma drm_count_rest_sum: forall N n, N > n ->
  ( (((INR (fact n)) * (E1 (-1) N)) - (drm_count_as_sum n)))%R =
  ( (rest_sum n N) * (if Nat.even n then (-1)%R else 1%R))%R.
Proof.
  unfold rest_sum.
  induction N; intros; try lia.
  destruct (Nat.eq_dec n N).
  - unfold drm_count_as_sum. rewrite <- Rmult_minus_distr_l.
    subst N. replace (S n - n) with 1. 2: lia. simpl.
    unfold E1. simpl. unfold Rminus. rewrite Rplus_comm.
    rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
    repeat rewrite Rmult_1_r.
    rewrite <- Rmult_assoc.
    replace (fact n + n * fact n) with (fact (n + 1)).
    2: replace (n + 1) with (S n); simpl; lia.
    replace (INR (fact n) * / INR (fact (n + 1)))%R with (INR (fact n) / INR (fact (n + 1)))%R.
    2: unfold Rdiv; tauto.
    rewrite fact_fact_n_k. destruct (Nat.even n) eqn:E.
    + apply even_exists in E. destruct E as [n' E]. subst n.
      rewrite pow_1_even. rewrite Rmult_1_r. reflexivity.
    + rewrite tech_pow_Rmult. apply not_even_S_n in E. apply even_exists in E.
      destruct E as [n' E]. rewrite <- E. rewrite pow_1_even. reflexivity.
  - assert (N > n). lia. apply IHN in H0.
    replace (S N - n - 1) with (S (N - n - 1)). 2: lia.
    simpl. rewrite Rmult_plus_distr_r. rewrite <- H0.
    unfold E1. simpl. unfold Rminus. rewrite Rmult_plus_distr_l.
    repeat rewrite -> Rplus_assoc. apply Rplus_eq_compat_l.
    rewrite Rplus_comm. apply Rplus_eq_reg_l with (r:=(drm_count_as_sum n)).
    repeat rewrite <- Rplus_assoc. repeat rewrite Rplus_opp_r.
    repeat rewrite Rplus_0_l. rewrite <- Rmult_assoc.
    replace (fact N + N * fact N) with (fact (S N)). 2: simpl; tauto.
    replace (S N) with (N + 1); try lia.
    replace (INR (fact n) * / INR (fact (N + 1)))%R with (INR (fact n) / INR (fact (N + 1)))%R.
    2: unfold Rdiv; tauto.
    assert (N > n). lia.
    assert (N + 1 = n + (N - n + 1)). lia. rewrite H2.
    rewrite fact_fact_n_k. replace (S (N - n - 1 + 1)) with (N - n + 1). 2: lia.
    repeat rewrite Rmult_assoc. repeat apply Rmult_eq_compat_l.
    assert (N = (N - n - 1) + (n + 1)). lia. rewrite H3.
    replace ((-1) ^ N)%R with ((-1) ^ ((N - n - 1 + (n + 1))))%R.
    2: rewrite <- H3; tauto.
    rewrite pow_add.
    replace (N - n - 1 + (n + 1) - n - 1) with ((N - n - 1)). 2: lia.
    apply Rmult_eq_compat_l. rewrite pow_add. rewrite pow_1.
    destruct (Nat.even n) eqn:E.
    + apply even_exists in E. destruct E as [n' E]. subst n.
      rewrite pow_1_even. rewrite Rmult_1_l. tauto.
    + rewrite Rmult_comm. rewrite tech_pow_Rmult.
      apply not_even_S_n in E. apply even_exists in E.
      destruct E as [n' E]. rewrite <- E. apply pow_1_even.
Qed.

Fact Rplus_mult_neg_1_r_gt_0: forall a b, (a + b * (-1) > 0)%R <-> (a > b)%R.
Proof.
  intros. rewrite Rmult_comm. change (-1)%R with (- IZR 1)%R.
  rewrite Ropp_mult_distr_l_reverse.
  rewrite Rmult_1_l. split; intros.
  - apply Rplus_gt_compat_r with (r:=(b)) in H.
    rewrite Rplus_assoc in H. rewrite Rplus_opp_l in H.
    rewrite Rplus_0_l in H. rewrite Rplus_0_r in H. exact H.
  - apply Rplus_lt_reg_r with (r:=(b)).
    rewrite Rplus_0_l. rewrite Rplus_assoc. rewrite Rplus_opp_l.
    rewrite Rplus_0_r. apply H.
Qed.

Fact Rplus_mult_neg_1_r_lt_0: forall a b, (a * (-1) + b < 0)%R <-> (a > b)%R.
Proof.
  intros. rewrite Rmult_comm. change (-1)%R with (- IZR 1)%R.
  rewrite Ropp_mult_distr_l_reverse.
  rewrite Rmult_1_l. split; intros.
  - apply Rplus_gt_compat_r with (r:=(-b)%R) in H.
    rewrite Rplus_assoc in H. rewrite Rplus_opp_r in H.
    rewrite Rplus_0_l in H. rewrite Rplus_0_r in H.
    apply Ropp_gt_cancel in H. exact H.
  - apply Rplus_lt_reg_r with (r:=(-b)%R).
    rewrite Rplus_0_l. rewrite Rplus_assoc. rewrite Rplus_opp_r.
    rewrite Rplus_0_r. apply Ropp_gt_contravar. apply H.
Qed.

Fact Rplus_neg_gt_0: forall a b, (a + - b > 0)%R <-> (a > b)%R.
Proof.
  intros. split; intros.
  - apply Rplus_lt_reg_r with (r:=(-b)%R).
    rewrite Rplus_opp_r. apply H.
  - apply Rplus_lt_reg_r with (r:=(b)%R).
    rewrite Rplus_0_l. rewrite Rplus_assoc.
    rewrite Rplus_opp_l. rewrite Rplus_0_r. apply H.
Qed.

Lemma inv_fact_n_k_gt: forall n k k', k < k' -> n > 1 -> (inv_fact_n_k n k > inv_fact_n_k n k')%R.
Proof.
  intros. unfold inv_fact_n_k. apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat. apply INR_fact_n_k_gt_0. apply INR_fact_n_k_gt_0.
  - apply lt_INR. apply fact_n_k_lt; lia.
Qed.

Lemma inv_fact_n_k_gt_0: forall n k, (inv_fact_n_k n k > 0)%R.
Proof.
  intros. unfold inv_fact_n_k. apply Rinv_0_lt_compat.
  change 0%R with (INR 0). apply lt_INR.
  apply fact_n_k_gt_0.
Qed.

Lemma rest_sum_gt_0_odd: forall n N,
    n > 0 -> N > n + 2 -> (Nat.odd (N - n - 1)) = true -> ((rest_sum n N) > (rest_sum n (n + 2)))%R.
Proof.
  unfold rest_sum.
  intros n N. revert n.
  induction N using Wf_nat.lt_wf_ind. intros.
  destruct N; try lia.
  destruct N; try lia.
  assert (N < S (S N)). lia.
  replace (S (S N) - n - 1) with (S (S (N - n - 1))). 2: simpl.
  2: destruct n; try lia. 2: destruct n; try lia.
  assert (Nat.odd (N - n - 1) = true).
  { replace (S (S N) - n - 1) with (S (S (N - n - 1))) in H2. 2: simpl.
    2: destruct n; try lia. 2: destruct n; try lia.
    rewrite Nat.odd_succ_succ in H2. apply H2. }
  destruct (gt_dec N (n + 2)).
  - pose proof (H N H3 n H0 g H4).
    eapply Rgt_trans. 2: apply H5. remember (N - n - 1) as N'.
    simpl. rewrite <- Rplus_0_r. rewrite Rplus_assoc. apply Rplus_gt_compat_l.
    rewrite tech_pow_Rmult.
    assert (Nat.even (S N') = true). rewrite Nat.even_succ. assumption.
    apply even_exists in H6. destruct H6 as [n' H6]. rewrite <- H6.
    rewrite pow_1_even. repeat rewrite Rmult_1_r.
    apply Rplus_mult_neg_1_r_gt_0.
    apply inv_fact_n_k_gt; lia.
  - destruct (Nat.eq_dec N (n + 2)).
    + subst N. replace (S (S (n + 2 - n - 1))) with 3. 2: lia.
      replace (n + 2 - n - 1) with 1. 2: lia. simpl.
      rewrite <- Rplus_0_r. repeat rewrite Rplus_assoc.
      repeat apply Rplus_gt_compat_l. repeat rewrite Rmult_1_r.
      replace (-1 * -1)%R with 1%R. 2: symmetry; apply neg_1_mult_neg_1.
      repeat rewrite Rmult_1_r. rewrite Rmult_comm.
      change (-1)%R with (- IZR 1)%R. rewrite Ropp_mult_distr_l_reverse.
      rewrite Rmult_1_l. apply Rplus_neg_gt_0.
      apply inv_fact_n_k_gt; lia.
    + assert (N < n + 2). lia. assert (N = n + 1). lia. subst N.
      replace (S (S (n + 1 - n - 1))) with 2. 2: lia.
      replace (n + 2 - n - 1) with 1. 2: lia. simpl.
      rewrite <- Rplus_0_r. apply Rplus_gt_compat_l.
      rewrite Rmult_1_r. rewrite neg_1_mult_neg_1. rewrite Rmult_1_r.
      apply inv_fact_n_k_gt_0.
Qed.

Lemma rest_sum_gt_0_even: forall n N,
    n > 0 -> N > n + 3 -> (Nat.even (N - n - 1)) = true -> ((rest_sum n N) > 0)%R.
Proof.
  intros. destruct N; try lia.
  assert (N > n + 2). lia.
  assert (Nat.odd (N - n - 1) = true).
  { rewrite <- Nat.even_succ. replace (S (N - n - 1)) with (S N - n - 1). 2: lia.
    assumption. }
  apply rest_sum_gt_0_odd in H3; auto.
  unfold rest_sum in *.
  replace (S N - n - 1) with (S (N - n - 1)). 2: lia.
  remember (N - n - 1) as Nn1.
  replace (n + 2 - n - 1) with 1 in H3. 2: lia.
  simpl in H3. simpl. rewrite <- Rplus_0_r.
  apply Rplus_gt_compat.
  - eapply Rgt_trans. apply H3. repeat rewrite Rmult_1_r.
    apply Rplus_mult_neg_1_r_gt_0. apply inv_fact_n_k_gt; lia.
  - rewrite tech_pow_Rmult. rewrite HeqNn1.
    replace (S N - n - 1) with (S (N - n - 1)) in H1. 2: lia.
    apply even_exists in H1. destruct H1 as [n' H1].
    rewrite <- H1. rewrite pow_1_even. rewrite Rmult_1_r.
    apply inv_fact_n_k_gt_0.
Qed.

Lemma rest_sum_gt_0: forall n N,
    n > 0 -> N > n + 3 -> ((rest_sum n N) > 0)%R.
Proof.
  intros. destruct (Nat.even (N - n - 1)) eqn:E.
  - apply rest_sum_gt_0_even; tauto.
  - destruct N; try lia.
    assert (N > n + 2). lia.
    rewrite <- Nat.negb_odd in E. rewrite Bool.negb_false_iff in E.
    apply rest_sum_gt_0_odd in E; try lia.
    eapply Rgt_trans. apply E.
    unfold rest_sum.
    replace (n + 2 - n - 1) with 1. 2: lia.
    simpl. repeat rewrite Rmult_1_r.
    apply Rplus_mult_neg_1_r_gt_0.
    apply inv_fact_n_k_gt; lia.
Qed.

Lemma rest_sum_even: forall n N,
    n > 0 -> N > n + 3 -> (Nat.even (N - n - 1)) = true -> ((rest_sum n N) < (rest_sum n (n + 3)))%R.
Proof.
  unfold rest_sum.
  intros n N. revert n.
  induction N using Wf_nat.lt_wf_ind. intros.
  destruct N; try lia.
  destruct N; try lia.
  assert (N < S (S N)). lia.
  replace (S (S N) - n - 1) with (S (S (N - n - 1))). 2: simpl.
  2: destruct n; try lia. 2: destruct n; try lia.
  assert (Nat.even (N - n - 1) = true).
  { replace (S (S N) - n - 1) with (S (S (N - n - 1))) in H2. 2: simpl.
    2: destruct n; try lia. 2: destruct n; try lia.
    rewrite Nat.even_succ_succ in H2. apply H2. }
  replace (n + 3 - n - 1) with 2. 2: lia.
  destruct (gt_dec N (n + 3)).
  - pose proof (H N H3 n H0 g H4).
    replace (n + 3 - n - 1) with 2 in H5. 2: lia.
    eapply Rlt_trans. 2: apply H5. remember (N - n - 1) as N'.
    simpl. rewrite <- Rplus_0_r. rewrite Rplus_assoc. apply Rplus_lt_compat_l.
    apply even_exists in H4. destruct H4 as [n' H4]. rewrite <- H4.
    rewrite pow_1_even. rewrite Rmult_1_r.
    apply Rplus_mult_neg_1_r_lt_0.
    rewrite neg_1_mult_neg_1. rewrite Rmult_1_r.
    apply inv_fact_n_k_gt; lia.
  - destruct (Nat.eq_dec N (n + 3)).
    + subst N. replace (S (S (n + 3 - n - 1))) with 4. 2: lia.
      simpl.
      rewrite <- Rplus_0_r. repeat rewrite Rplus_assoc.
      repeat apply Rplus_lt_compat_l. repeat rewrite Rmult_1_r.
      rewrite neg_1_mult_neg_1. rewrite Rmult_1_r.
      rewrite neg_1_mult_neg_1. rewrite Rmult_1_r.
      apply Rplus_mult_neg_1_r_lt_0.
      apply inv_fact_n_k_gt; lia.
    + assert (N < n + 3). lia. assert (N = n + 2). lia. subst N.
      replace (S (S (n + 2 - n - 1))) with 3. 2: lia.
      simpl.
      rewrite <- Rplus_0_r. apply Rplus_lt_compat_l.
      rewrite Rmult_1_r. rewrite neg_1_mult_neg_1.
      rewrite Rmult_1_r. rewrite Rmult_comm.
      rewrite neg_1_mult. rewrite <- Ropp_0.
      apply Ropp_lt_contravar. apply inv_fact_n_k_gt_0.
Qed.

Lemma rest_sum_odd: forall n N,
    n > 0 -> N > n + 4 -> (Nat.odd (N - n - 1)) = true -> ((rest_sum n N) < (rest_sum n (n + 3)))%R.
Proof.
  intros. destruct N; try lia.
  assert (N > n + 3). lia.
  assert (Nat.even (N - n - 1) = true).
  { rewrite <- Nat.odd_succ. replace (S (N - n - 1)) with (S N - n - 1). 2: lia. apply H1. }
  pose proof (rest_sum_even n N H H2 H3). unfold rest_sum in *.
  replace (S N - n - 1) with (S (N - n - 1)). 2: lia.
  remember (N - n - 1) as Nn1. remember (n + 3 - n - 1) as Nn2.
  replace (n + 3 - n - 1) with 2 in HeqNn2. 2: lia. simpl.
  eapply Rlt_trans. 2: apply H4. rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l.
  apply even_exists in H3. destruct H3 as [n' H3]. rewrite <- H3.
  rewrite pow_1_even. rewrite Rmult_1_r.
  rewrite Rmult_comm. rewrite neg_1_mult.
  rewrite <- Ropp_0. apply Ropp_lt_contravar.
  apply inv_fact_n_k_gt_0.
Qed.

Lemma rest_sum_lt: forall n N,
    n > 0 -> N > n + 4 -> ((rest_sum n N) < (rest_sum n (n + 1)))%R.
Proof.
  intros n N H.
  assert ((sum_f_R0 (fun k : nat => inv_fact_n_k (n + 1) (k + 1) * (-1) ^ k) 2 <=
           sum_f_R0 (fun k : nat => inv_fact_n_k (n + 1) (k + 1) * (-1) ^ k) 0)%R).
  { simpl. rewrite <- Rplus_0_r. repeat rewrite Rplus_assoc. apply Rplus_le_compat_l.
    repeat rewrite Rmult_1_r. rewrite neg_1_mult_neg_1. rewrite Rmult_1_r.
    apply Rlt_le. apply Rplus_mult_neg_1_r_lt_0.
    apply inv_fact_n_k_gt; lia. }
  intros.
  destruct (Nat.even (N - n - 1)) eqn:E.
  - apply rest_sum_even in E; try lia. unfold rest_sum in *.
    replace (n + 3 - n - 1) with 2 in E. 2: lia.
    replace (n + 1 - n - 1) with 0. 2: lia.
    eapply Rlt_le_trans. apply E. apply H0.
  - rewrite <- Nat.negb_odd in E. rewrite Bool.negb_false_iff in E.
    apply rest_sum_odd in E; try lia. unfold rest_sum in *.
    replace (n + 3 - n - 1) with 2 in E. 2: lia.
    replace (n + 1 - n - 1) with 0. 2: lia.
    eapply Rlt_le_trans. apply E. apply H0.
Qed.

Lemma R_dist_lt_swap: forall a b c eps, (R_dist a b < eps)%R -> ((Rabs (a + c)) < (Rabs (b + c)) + eps)%R.
Proof.
  intros a b c eps H. unfold R_dist in H.
  apply Rplus_lt_reg_r with (r:=(- Rabs (b + c))%R).
  rewrite Rplus_comm with (r2:=eps). rewrite Rplus_assoc.
  rewrite Rplus_opp_r. rewrite Rplus_0_r.
  unfold Rabs.
  destruct (Rcase_abs (a + c)); destruct (Rcase_abs (b + c)).
  - rewrite Ropp_involutive. rewrite Ropp_plus_distr.
    rewrite Rplus_comm with (r1:=b).
    rewrite <- Rplus_assoc. rewrite -> Rplus_assoc with (r1:=(-a)%R).
    rewrite Rplus_opp_l. rewrite Rplus_0_r. eapply Rle_lt_trans. 2: apply H.
    eapply Rle_trans. apply Rle_abs. pose proof (Rabs_Ropp (a - b)%R).
    rewrite <- H0. rewrite Ropp_minus_distr. unfold Rminus.
    rewrite Rplus_comm. apply Rle_refl.
  - assert (- c <= b)%R.
    { apply Rplus_ge_compat_r with (r:=(-c)%R) in r0.
      rewrite Rplus_0_l in r0. rewrite Rplus_assoc in r0.
      rewrite Rplus_opp_r in r0. rewrite Rplus_0_r in r0.
      apply Rge_le. assumption. }
    rewrite Ropp_plus_distr. rewrite Ropp_plus_distr.
    apply Rle_lt_trans with (r2:=(-a + b + -b + b)%R).
    + repeat rewrite Rplus_assoc. apply Rplus_le_compat_l.
      rewrite <- Rplus_assoc. rewrite <- Rplus_assoc.
      rewrite Rplus_comm with (r2:=(-b)%R). rewrite Rplus_comm with (r2:=(-b)%R).
      repeat rewrite Rplus_assoc. apply Rplus_le_compat_l.
      apply Rle_trans with (r2:=(- c + b)%R).
      * apply Rplus_le_compat_l. assumption.
      * apply Rplus_le_compat_r. assumption.
    + repeat rewrite Rplus_assoc. rewrite Rplus_opp_l.
      rewrite Rplus_0_r. eapply Rle_lt_trans. apply Rle_abs.
      rewrite <- Rabs_Ropp. rewrite Ropp_plus_distr.
      rewrite Ropp_involutive. apply H.
  - rewrite Ropp_involutive. assert (c < -b)%R.
    { apply Rplus_lt_reg_l with (r:=b). rewrite Rplus_opp_r. apply r0. }
    apply Rlt_trans with (r2:=(a + - b + (b + - b))%R).
    { repeat rewrite Rplus_assoc. apply Rplus_lt_compat_l.
      rewrite Rplus_opp_r. rewrite Rplus_0_r. eapply Rlt_trans. 2: apply H0.
      rewrite <- Rplus_0_r. apply Rplus_lt_compat_l. apply r0. }
    rewrite Rplus_opp_r. rewrite Rplus_0_r. unfold Rminus in H.
    eapply Rle_lt_trans. apply Rle_abs. apply H.
  - rewrite Ropp_plus_distr. rewrite Rplus_comm with (r1:=(-b)%R).
    rewrite <- Rplus_assoc. rewrite Rplus_assoc with (r1:=a).
    rewrite Rplus_opp_r. rewrite Rplus_0_r. unfold Rminus in H.
    eapply Rle_lt_trans. apply Rle_abs. apply H.
Qed.

Lemma inv_fact_n_k_le: forall n n' k, n >= n' -> n' > 0 -> (inv_fact_n_k n k <= inv_fact_n_k n' k)%R.
Proof.
  intros. unfold inv_fact_n_k. apply Rinv_le_contravar. apply INR_fact_n_k_gt_0.
  apply le_INR. generalize dependent n. generalize dependent n'. generalize dependent k.
  induction k; intros.
  - simpl. reflexivity.
  - pose proof H. apply IHk in H1; try lia. simpl. destruct n, n'; try lia.
    destruct (fact_n_k (S n') k); try lia. destruct (fact_n_k (S n) k); try lia.
    repeat rewrite <- Nat.add_sub_assoc; try lia.
    repeat rewrite Nat.mul_add_distr_r. apply plus_le_compat.
    apply mult_le_compat; lia. apply mult_le_compat; lia.
Qed.

Lemma Rinv_1_l: forall r, r <> 0%R -> (/ r * r = 1)%R.
Proof.
  intros. rewrite <- Rmult_1_l with (r:=(/ r * r)%R).
  rewrite Rmult_comm with (r2:=r). rewrite <- Rmult_assoc. rewrite Rinv_r_simpl_l.
  reflexivity. assumption.
Qed.

Corollary Rinv_1_r: forall r, r <> 0%R -> (r * / r = 1)%R.
Proof.
  intros. rewrite Rmult_comm. apply Rinv_1_l. assumption.
Qed.

Lemma drm_count_as_sum_e_diff_N: forall n: nat,
    n > 0 -> exists eps: R,
      (eps > 0)%R /\ exists N0: nat, forall N: nat,
        N > N0 ->
        ((Rabs (((INR (fact n)) * (E1 (-1) N)) - (drm_count_as_sum n))) + eps < (/ INR 2))%R.
Proof.
  intros. destruct (Nat.eq_dec n 1).
  - exists (/ INR 24)%R. split.
    { apply Rlt_gt. apply Rinv_0_lt_compat. change 0%R with (INR 0). apply lt_INR. lia. }
    remember (n + 10) as N0.
    exists N0. intros. rewrite drm_count_rest_sum; try lia.
    rewrite Rabs_mult. assert (Rabs (if Nat.even n then -1 else 1) = 1)%R.
    { destruct (Nat.even n). 2: apply Rabs_R1.
      replace (-1)%R with (- (1%R))%R. rewrite Rabs_Ropp. apply Rabs_R1.
      rewrite <- Ropp_Ropp_IZR. reflexivity. }
    rewrite H1. rewrite Rmult_1_r.
    remember (/ INR 24)%R as inv24. remember (/ INR 2)%R as inv2.
    rewrite Rabs_pos_eq. 2: apply Rlt_le. 2: apply rest_sum_gt_0; lia.
    assert ((inv_fact_n_k 2 1 + inv_fact_n_k 2 2 * -1 + inv_fact_n_k 2 3 + inv24 <= inv2)%R).
    { unfold inv_fact_n_k. subst inv2 inv24. change (fact_n_k 2 1) with 2.
      change (fact_n_k 2 2) with 6. change (fact_n_k 2 3) with 24.
      rewrite <- Rplus_0_r. repeat rewrite Rplus_assoc. apply Rplus_le_compat_l.
      apply Rmult_le_reg_l with (r:=(INR 6)). apply lt_0_INR; lia.
      repeat rewrite Rmult_plus_distr_l. rewrite Rmult_0_r.
      rewrite <- Rmult_assoc. rewrite Rinv_1_r. 2: apply not_0_INR; lia.
      rewrite Rmult_1_l. change 24 with (6 * 4). rewrite mult_INR.
      rewrite Rinv_mult_distr. 2, 3: apply not_0_INR; lia.
      rewrite <- Rmult_assoc. rewrite Rinv_1_r. 2: apply not_0_INR; lia.
      rewrite Rmult_1_l. apply Rmult_le_reg_l with (INR 4). apply lt_0_INR; lia.
      repeat rewrite Rmult_plus_distr_l. rewrite Rinv_1_r. 2: apply not_0_INR; lia.
      rewrite Rmult_0_r. rewrite <- plus_IZR.
      rewrite INR_IZR_INZ. rewrite <- mult_IZR. rewrite <- plus_IZR.
      apply IZR_le. simpl. lia. }
    destruct (Nat.even (N - n - 1)) eqn:E.
    + apply rest_sum_even in E; try lia.
      apply Rlt_le_trans with (r2:=(rest_sum n (n + 3) + inv24)%R).
      { apply Rplus_lt_compat_r. apply E. }
      unfold rest_sum in *.
      replace (n + 3 - n - 1) with 2. 2: lia. simpl.
      repeat rewrite Rmult_1_r. rewrite neg_1_mult_neg_1. rewrite Rmult_1_r.
      subst n. simpl. apply H2.
    + rewrite <- Nat.negb_odd in E. rewrite Bool.negb_false_iff in E.
      apply rest_sum_odd in E; try lia.
      apply Rlt_le_trans with (r2:=(rest_sum n (n + 3) + inv24)%R).
      { apply Rplus_lt_compat_r. apply E. }
      unfold rest_sum in *.
      replace (n + 3 - n - 1) with 2. 2: lia. simpl.
      repeat rewrite Rmult_1_r. rewrite neg_1_mult_neg_1. rewrite Rmult_1_r.
      subst n. simpl. apply H2.
  - exists (/ INR 24)%R. split.
    { apply Rlt_gt. apply Rinv_0_lt_compat. change 0%R with (INR 0). apply lt_INR. lia. }
    remember (n + 10) as N0.
    exists N0. intros. rewrite drm_count_rest_sum; try lia.
    rewrite Rabs_mult. assert (Rabs (if Nat.even n then -1 else 1) = 1)%R.
    { destruct (Nat.even n). 2: apply Rabs_R1.
      replace (-1)%R with (- (1%R))%R. rewrite Rabs_Ropp. apply Rabs_R1.
      rewrite <- Ropp_Ropp_IZR. reflexivity. }
    rewrite H1. rewrite Rmult_1_r.
    rewrite Rabs_pos_eq. 2: apply Rlt_le. 2: apply rest_sum_gt_0; lia.
    apply Rlt_le_trans with (r2:=(rest_sum n (n + 1) + / INR 24)%R).
    { apply Rplus_lt_compat_r. apply rest_sum_lt; lia. }
    unfold rest_sum. replace (n + 1 - n - 1) with 0. 2: lia.
    remember (/ INR 24)%R as inv24. remember (/ INR 2)%R as inv2. simpl.
    rewrite Rmult_1_r. apply Rle_trans with (r2:=(inv_fact_n_k 3 1 + inv24)%R).
    apply Rplus_le_compat_r. apply inv_fact_n_k_le; try lia.
    unfold inv_fact_n_k. change (fact_n_k 3 1) with 3.
    subst inv2 inv24.
    apply Rmult_le_reg_r with (r:=(INR 3)). apply lt_0_INR; lia.
    rewrite Rmult_plus_distr_r. rewrite Rinv_1_l. 2: apply not_0_INR; lia.
    change 24 with (8 * 3). rewrite mult_INR. rewrite Rinv_mult_distr. 2, 3: apply not_0_INR; lia.
    rewrite Rmult_assoc. rewrite Rinv_1_l. 2: apply not_0_INR; lia.
    rewrite Rmult_1_r. apply Rmult_le_reg_r with (r:=(INR 8)). apply lt_0_INR; lia.
    rewrite Rmult_plus_distr_r. rewrite Rinv_1_l. 2: apply not_0_INR; lia.
    rewrite Rmult_1_l. rewrite Rmult_assoc. rewrite Rmult_comm. rewrite Rmult_assoc.
    change (INR 8) with (INR (4 * 2)). rewrite mult_INR.
    rewrite Rmult_assoc. rewrite Rinv_1_r. 2: apply not_0_INR; lia.
    rewrite Rmult_1_r. repeat rewrite <- mult_INR. change 1%R with (INR 1).
    rewrite <- plus_INR. apply le_INR. lia.
Qed.

Lemma drm_count_as_sum_e_diff: forall n: nat, n > 0 ->
    ((Rabs (((INR (fact n)) * (exp (-1))) - (drm_count_as_sum n))) < (/ INR 2))%R.
Proof.
  intros n Hn.
  pose proof E1_cvg. unfold Un_cv in H.
  pose proof (drm_count_as_sum_e_diff_N n Hn). destruct H0 as [eps [? ?]].
  pose proof (H (-1)%R (eps / (INR (fact n)))%R).
  assert (eps / INR (fact n) > 0)%R.
  { apply Rlt_gt. apply Rdiv_lt_0_compat. apply H0.
    apply INR_fact_lt_0. }
  apply H2 in H3. destruct H3 as [N ?].
  destruct H1 as [N0 H1].
  remember (S (Nat.max N N0)) as N'.
  assert (N' > N0). lia. assert (N' >= N). lia.
  apply H1 in H4. apply H3 in H5.
  assert (R_dist ((INR (fact n)) * (E1 (-1) N')) ((INR (fact n)) * (exp (-1))) < eps)%R.
  { unfold R_dist in *. rewrite <- Rmult_minus_distr_l. rewrite Rabs_mult.
    assert (0 <= INR (fact n))%R.
    { apply Rlt_le. apply INR_fact_lt_0. }
    apply Rabs_pos_eq in H6. rewrite H6.
    apply Rmult_lt_compat_r with (r:=(INR (fact n))%R) in H5. 2: apply INR_fact_lt_0.
    unfold Rdiv in H5. rewrite Rmult_assoc in H5. rewrite Rinv_l in H5.
    2: apply INR_fact_neq_0. rewrite Rmult_1_r in H5. rewrite Rmult_comm in H5.
    exact H5. }
  clear H H0 H1 H2 H3.
  eapply Rle_lt_trans. 2: apply H4. clear H4 H5.
  apply Rlt_le. apply R_dist_lt_swap. rewrite R_dist_sym. assumption.
Qed.


Require Import drmcorrect drmnodup List SetoidList SetoidPermutation FMapWeakList OrderedTypeEx Compare_dec.
Import ListNotations.

Fixpoint drm_count (n: nat) :=
  match n with
  | 0 => 1
  | 1 => 0
  | S k => (n - 1) * ((drm_count k) + (drm_count (Nat.pred k)))
  end.


Lemma drm_construct_1_count: forall n m, length (drm_construct_1 n m) = (card m).
Proof.
  intros n m. revert n. destruct m. induction this; intros.
  - simpl. reflexivity.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup).
    pose proof (IHthis H). unfold card in *. simpl in *.
    unfold drm_construct_1. unfold drm_inject. rewrite drm_inject_fold_step_eq. simpl.
    unfold drm_inject_step. rewrite map_length. reflexivity.
Qed.

Lemma concat_map_length: forall {A B: Type} (l: list A) (f: A -> list B) c,
    (forall x, In x l -> (length (f x) = c)) ->
    (length (concat (List.map f l))) = (length l) * c.
Proof.
  intros A B. induction l; intros.
  - simpl. reflexivity.
  - simpl. rewrite app_length. rewrite IHl with (c:=c).
    + rewrite (H a). 2: left; tauto. reflexivity.
    + intros. apply H. right. assumption.
Qed.

Lemma drm_construct_2_count: forall n m,
    drm m (Nat.pred n) ->
    length (drm_construct_2 n m) = (card m) + 1.
Proof.
  intros n m. revert n. destruct m. induction this; intros n Hdrm.
  - simpl. reflexivity.
  - pose proof (SetoidList_NoDupA_cons_rev _ _ NoDup).
    pose proof (IHthis H). unfold card in *. simpl in *.
    rewrite drm_add_loop_fold_eq in *. rewrite app_nil_l.
    rewrite concat_map_length with (c:=1).
    + simpl. rewrite mult_1_r. rewrite plus_comm. simpl. reflexivity.
    + intros. destruct x as [x0 x1].
      assert (MapsTo x0 x1 {| Map.this := a :: this; Map.NoDup := NoDup |}).
      { apply In_InA. apply Map.Raw.PX.eqke_equiv. apply H1. }
      eapply drm_MapsTo in H2; eauto. destruct H2 as [? [? ?]].
      eapply drm_lt_MapsTo_1 in H4; eauto. destruct H4 as [v ?].
      apply Map.find_1 in H4. simpl. rewrite H4. simpl. reflexivity.
Qed.

Lemma drm_count_correct: forall n, (drm_count n) = length (drm_construct n).
Proof.
  induction n using Wf_nat.lt_wf_ind.
  destruct n.
  - simpl. reflexivity.
  - destruct n.
    + simpl. reflexivity.
    + change (drm_count (S (S n))) with (((S (S n)) - 1) * ((drm_count (S n)) + (drm_count (Nat.pred (S n))))).
      change (drm_construct (S (S n))) with
          ((concat (List.map (drm_construct_1 (S n)) (drm_construct (S n))))
             ++ (concat (List.map (drm_construct_2 (S n)) (drm_construct n)))).
      rewrite app_length.
      assert (length (concat (map (drm_construct_1 (S n)) (drm_construct (S n)))) = (S (S n) - 1) * (drm_count (S n))).
      { rewrite concat_map_length with (c:=(S n)).
        - rewrite <- H; lia.
        - intros. rewrite drm_construct_1_count.
          pose proof (drm_construct_correct (S n)). rewrite Forall_forall in H1.
          apply H1 in H0. apply card_drm in H0. lia. }
      rewrite H0.
      assert (length (concat (map (drm_construct_2 (S n)) (drm_construct n))) = (S (S n) - 1) * (drm_count n)).
      { rewrite concat_map_length with (c:=(S n)).
        - rewrite <- H; lia.
        - intros. rewrite drm_construct_2_count.
          + pose proof (drm_construct_correct n). rewrite Forall_forall in H2.
            apply H2 in H1. apply card_drm in H1. lia.
          + simpl. pose proof (drm_construct_correct n). rewrite Forall_forall in H2.
            apply H2 in H1. assumption. }
      rewrite H1. change (Nat.pred (S n)) with n.
      rewrite <- Nat.mul_add_distr_l. reflexivity.
Qed.

Lemma drm_count_closed_form: forall n,
    INR (drm_count n) = drm_count_as_sum n.
Proof.
  unfold drm_count_as_sum.
  induction n using Wf_nat.lt_wf_ind.
  destruct n.
  - unfold E1. simpl. rewrite Rmult_1_r. rewrite Rmult_1_l. rewrite Rinv_1. reflexivity.
  - destruct n.
    + unfold E1. simpl. rewrite Rinv_1. repeat rewrite Rmult_1_l. rewrite Rmult_1_r.
      rewrite <- plus_IZR. simpl. reflexivity.
    + change (drm_count (S (S n))) with (((S (S n)) - 1) * ((drm_count (S n)) + (drm_count (Nat.pred (S n))))).
      replace (E1 (-1) (S (S n))) with (E1 (-1) (S n) + / INR (fact (S (S n))) * (-1) ^ S (S n))%R.
      * rewrite mult_INR. rewrite plus_INR. rewrite H; try lia.
        change (Nat.pred (S n)) with n. rewrite H; try lia.
        replace (S (S n) - 1) with (S n). 2: lia.
        rewrite Rmult_plus_distr_l. rewrite Rmult_plus_distr_l.
        repeat rewrite <- Rmult_assoc. rewrite Rinv_r. 2: apply INR_fact_neq_0.
        rewrite Rmult_1_l. change (fact (S (S n))) with ((S (S n)) * fact (S n)).
        apply Rplus_eq_reg_l with (r:=(-(INR (S (S n) * fact (S n)) * E1 (-1) (S n)))%R).
        repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
        rewrite mult_INR. repeat rewrite Rmult_assoc. rewrite Ropp_mult_distr_l.
        rewrite <- Rmult_plus_distr_r.
        change (INR (S (S n))) with (INR (1 + S n)). rewrite plus_INR.
        rewrite Ropp_plus_distr. rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r.
        change (INR 1) with 1%R. rewrite <- Ropp_mult_distr_l. rewrite Rmult_1_l.
        replace (E1 (-1) (S n)) with ((E1 (-1) n) + / INR (fact (S n)) * (-1) ^ (S n))%R.
        {
          rewrite Rmult_plus_distr_l. repeat rewrite <- Rmult_assoc.
          rewrite Rinv_r. 2: apply INR_fact_neq_0. rewrite Rmult_1_l.
          rewrite <- mult_INR. change (S n * fact n) with (fact (S n)).
          rewrite Ropp_plus_distr. rewrite Rplus_comm. rewrite <- Rplus_assoc.
          rewrite Rplus_opp_r. rewrite Rplus_0_l.
          replace ((- (-1) ^ S n)%R) with (- (1 * (-1) ^ (S n)))%R.
          - rewrite Ropp_mult_distr_l. change (- (1))%R with (IZR (-1)).
            rewrite tech_pow_Rmult. reflexivity.
          - rewrite Rmult_1_l. reflexivity.
        }
        unfold E1. rewrite sum_N_predN with (N:=(S n)); try lia. simpl. reflexivity.
      * unfold E1. rewrite sum_N_predN; try lia. simpl. reflexivity.
Qed.


Definition round (r: R) :=
  if (Rlt_dec (R_dist r (IZR (Int_part r))) (/ INR 2)) then
    Some (Int_part r)
  else if (Rlt_dec (R_dist (IZR (up r)) r) (/ INR 2)) then
         Some (up r)
       else
         None.

Lemma round_dist: forall r n,
    (Rabs (r - INR n) < / INR 2)%R -> (round r) = Some (Z.of_nat n).
Proof.
  intros.
  rewrite INR_IZR_INZ in H. unfold round. unfold R_dist.
  unfold Rabs in H. destruct (Rcase_abs (r - IZR (Z.of_nat n))).
  - apply Rminus_lt in r0.
    pose proof (tech_up r (Z.of_nat n) r0). unfold Int_part.
    rewrite Ropp_minus_distr in H.
    assert (IZR (Z.of_nat n) <= r + 1)%R.
    { apply Rplus_lt_compat_r with (r:=r) in H.
      unfold Rminus in H. rewrite Rplus_assoc in H.
      rewrite Rplus_opp_l in H. rewrite Rplus_0_r in H. rewrite Rplus_comm in H.
      apply Rlt_le. eapply Rlt_le_trans. apply H.
      apply Rplus_le_compat_l. apply Rmult_le_reg_r with (r:=(INR 2)).
      change 0%R with (INR 0). apply lt_INR. lia.
      rewrite Rinv_l. rewrite Rmult_1_l.
      change 1%R with (INR 1). apply le_INR. lia.
      change 0%R with (INR 0). apply not_INR. lia. }
    pose proof H1.
    apply H0 in H1. rewrite <- H1.
    destruct (Rlt_dec (Rabs (r - IZR (Z.of_nat n - 1))) (/ INR 2)).
    + pose proof H2 as H2'.
      apply Rlt_le in r0. apply Rle_ge in r0. apply Rge_minus in r0. apply Rge_le in r0.
      apply Rle_ge in H2. apply Rge_minus in H2.
      unfold Rminus in H2. rewrite <- opp_IZR in H2.
      rewrite Rplus_assoc in H2. rewrite <- plus_IZR in H2.
      replace (1 + - Z.of_nat n)%Z with (- (Z.of_nat n - 1))%Z in H2. 2: lia.
      rewrite opp_IZR in H2. apply Rge_le in H2.
      pose proof H2. apply Rabs_pos_eq in H2.
      apply Rle_ge in H3. apply Rminus_ge in H3.
      unfold Rminus in r1. rewrite H2 in r1.
      unfold Zminus in r1. rewrite plus_IZR in r1.
      rewrite Ropp_plus_distr in r1. rewrite opp_IZR in r1.
      rewrite Ropp_involutive in r1.
      apply Ropp_lt_contravar in r1. rewrite Ropp_plus_distr in r1.
      rewrite Ropp_plus_distr in r1. rewrite Ropp_involutive in r1.
      rewrite <- Rplus_assoc in r1. rewrite Rplus_comm with (r1:=(- r)%R) in r1.
      apply Rplus_lt_compat_r with (r:=1%R) in r1.
      repeat rewrite Rplus_assoc in r1. rewrite Rplus_opp_l in r1.
      rewrite Rplus_0_r in r1.
      assert (- / INR 2 + 1 = / INR 2)%R.
      { rewrite <- Rinv_r with (r:=(INR 2)).
        replace (- (/ INR 2))%R with ((-1) * (/ INR 2))%R.
        rewrite <- Rmult_plus_distr_r. rewrite INR_IZR_INZ.
        rewrite <- plus_IZR.
        replace (-1 + Z.of_nat 2)%Z with 1%Z. rewrite Rmult_1_l.
        reflexivity. lia. change (-1)%Z with (- (1))%Z.
        rewrite opp_IZR. rewrite <- Ropp_mult_distr_l.
        rewrite Rmult_1_l. reflexivity.
        apply INR_S_neq_0. }
      rewrite H4 in r1.
      assert (IZR (Z.of_nat n) - r < IZR (Z.of_nat n) - r)%R.
      { eapply Rlt_trans. apply H. unfold Rminus. apply r1. }
      apply Rlt_irrefl in H5. contradiction.
    + destruct (Rlt_dec (Rabs (IZR (Z.of_nat n) - r)) (/ INR 2)); try easy.
      contradict n1. apply Rgt_minus in r0.
      apply Rgt_ge in r0. apply Rge_le in r0. apply Rabs_pos_eq in r0.
      rewrite r0. assumption.
  - apply Rminus_ge in r0. apply Rge_le in r0.
    pose proof (up_tech r (Z.of_nat n) r0).
    assert (r < IZR (Z.of_nat n + 1))%R.
    { rewrite plus_IZR. apply Rplus_lt_reg_r with (r:=(- IZR (Z.of_nat n))%R).
      rewrite Rplus_comm with (r2:=1%R). rewrite Rplus_assoc.
      rewrite Rplus_opp_r. rewrite Rplus_0_r. eapply Rlt_trans.
      unfold Rminus in H. apply H. apply Rmult_lt_reg_r with (r:=(INR 2)).
      change 0%R with (INR 0). apply lt_INR. lia.
      rewrite Rinv_l. rewrite Rmult_1_l. change 1%R with (INR 1).
      apply lt_INR. lia.
      change 0%R with (INR 0). apply not_INR. lia. }
    apply H0 in H1. unfold Int_part. rewrite <- H1.
    destruct (Rlt_dec (Rabs (r - IZR (Z.of_nat n + 1 - 1))) (/ INR 2)).
    + rewrite Z.add_simpl_r. reflexivity.
    + rewrite Z.add_simpl_r in n0. contradict n0.
      apply Rle_ge in r0. apply Rge_minus in r0.
      apply Rge_le in r0. apply Rabs_pos_eq in r0.
      rewrite r0. assumption.
Qed.

Theorem drm_formula: forall n,
    n > 0 ->
    round ((INR (fact n)) * (exp (-1))) = Some (Z.of_nat (length (drm_construct n))).
Proof.
  intros.
  pose proof (drm_count_as_sum_e_diff n H).
  rewrite <- drm_count_closed_form in H0.
  apply round_dist in H0. rewrite drm_count_correct in H0.
  assumption.
Qed.
