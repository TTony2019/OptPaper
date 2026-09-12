## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/lem_2.lean`

## Lean statement
```lean
theorem lemma_3_2_descent {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) (hnu : 0 < nu) (hmu : 0 < mu) :
    ∀ n, 2 <= n ->
      objectiveWithQuadratic P (A.M1 nu mu) (A.p n) (A.x n) <=
        objectiveWithQuadratic P (A.M2 nu mu) (A.p (n - 1)) (A.x (n - 1))
```

## Statement explanation
The theorem `lemma_3_2_descent` is a descent estimate for the inertial Tseng-type proximal algorithm. It fixes a dimension $m$, problem data $P$ for a problem in the Euclidean space of dimension $m$, algorithm data $A$ for $P$, and positive real parameters $\nu$ and $\mu$. For every natural number $n$ with $n\ge 2$, it asserts

$$
\operatorname{objectiveWithQuadratic}_P\bigl(A.M_1(\nu,\mu),\,A.p_n,\,A.x_n\bigr)
\le
\operatorname{objectiveWithQuadratic}_P\bigl(A.M_2(\nu,\mu),\,A.p_{n-1},\,A.x_{n-1}\bigr).
$$

Here $A.p_n$ denotes $A.p(n)$, $A.x_n$ denotes $A.x(n)$, and

$$
\operatorname{objectiveWithQuadratic}_P(M,y,z)
=
\operatorname{erealAddReal}\bigl(P.\mathrm{objective}(y),\,M\|y-z\|^2\bigr).
$$

Thus the left-hand side is the extended-real objective at the current proximal point $p_n$, plus the quadratic term $M_1(\nu,\mu)\|p_n-x_n\|^2$, while the right-hand side is the extended-real objective at the previous proximal point $p_{n-1}$, plus the quadratic term $M_2(\nu,\mu)\|p_{n-1}-x_{n-1}\|^2$. The constants $M_1(\nu,\mu)$ and $M_2(\nu,\mu)$ are algorithm constants depending on $\nu$ and $\mu$. The theorem says that the $M_1$-penalized value at step $n$ is bounded above by the $M_2$-penalized value at the previous step. This is the form of a decrease inequality: the theorem compares two penalized objective values rather than proving equality of objective values.

The only explicit hypotheses are $0<\nu$ and $0<\mu$, together with the structural assumptions contained in the data $P$ and $A$. The positivity of $\nu$ and $\mu$ is used in Young inequalities and in the index estimates for $M_1$ and $M_2$. The proof also uses the fact that $A.p_n$ minimizes a certain algorithm step objective, the update formula for $A.x_n$, the Lipschitz continuity of the gradient of $h$, Bregman distance bounds coming from strong convexity and gradient-Lipschitzness of $u$, and the descent lemma for the smooth part $h$.

## Lean proof
```lean
by
  intro n hn
  have hn1 : 1 <= n := by omega
  have hnpred : 1 <= n - 1 := by omega
  have hlam := A.lambda_bounds n hn1
  have hlamp := A.lambda_bounds (n - 1) hnpred
  have halpha := A.alpha_bounds n hn1
  have hlam_pos : 0 < A.lambda n := lt_of_lt_of_le A.lambdaLower_pos hlam.1
  have hlamp_pos : 0 < A.lambda (n - 1) := lt_of_lt_of_le A.lambdaLower_pos hlamp.1
  have hLh_nonneg : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
  have hLu_nonneg : 0 <= A.Lgrad_u := le_of_lt A.u_Lgrad_pos
  have hsigma_pos : 0 < A.sigma := A.u_strongly_convex.1
  have hmin :
      algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n (A.p n) <=
        algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n (A.p (n - 1)) :=
    argminSet_le (A.p_argmin n hn1)
  have hx_update :
      A.x n =
        A.p (n - 1) +
          A.lambda (n - 1) •
            (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))) := by
    have hx := A.x_update (n - 1) hnpred
    have hsucc : n - 1 + 1 = n := by omega
    simpa [hsucc] using hx
  have hx_sub :
      A.x n - A.p (n - 1) =
        A.lambda (n - 1) •
          (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))) := by
    rw [hx_update]
    abel
  have h13 :
      ‖A.x n - A.p (n - 1)‖ <=
        A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
    have hLip :=
      P.h_lipschitz_gradient.2.2 (A.x (n - 1)) (A.p (n - 1))
    calc
      ‖A.x n - A.p (n - 1)‖
          = ‖A.lambda (n - 1) •
              (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1)))‖ := by
              rw [hx_sub]
      _ = A.lambda (n - 1) *
            ‖gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))‖ := by
              rw [norm_smul]
              simp [Real.norm_eq_abs, abs_of_pos hlamp_pos]
      _ <= A.lambda (n - 1) *
            (P.Lgrad_h * ‖A.x (n - 1) - A.p (n - 1)‖) := by
              exact mul_le_mul_of_nonneg_left hLip (le_of_lt hlamp_pos)
      _ = A.lambda (n - 1) * P.Lgrad_h *
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
              ring
  have h14 :
      ‖A.x n - A.x (n - 1)‖ <=
        (1 + A.lambda (n - 1) * P.Lgrad_h) *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
    calc
      ‖A.x n - A.x (n - 1)‖
          = ‖(A.x n - A.p (n - 1)) +
              (A.p (n - 1) - A.x (n - 1))‖ := by
              congr 1
              abel
      _ <= ‖A.x n - A.p (n - 1)‖ +
            ‖A.p (n - 1) - A.x (n - 1)‖ := norm_add_le _ _
      _ <= A.lambda (n - 1) * P.Lgrad_h *
              ‖A.x (n - 1) - A.p (n - 1)‖ +
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
              exact add_le_add h13 (by rw [norm_sub_rev])
      _ = (1 + A.lambda (n - 1) * P.Lgrad_h) *
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
              ring
  have h15 :
      ‖A.p n - A.p (n - 1)‖ ^ 2 <=
        2 * (‖A.x n - A.p n‖ ^ 2 +
          A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
    have hbase := norm_sq_sub_le_two (A.p n) (A.p (n - 1)) (A.x n)
    have hrhs_nonneg :
        0 <= A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
      nlinarith [h13, norm_nonneg (A.x n - A.p (n - 1))]
    have h13sq :
        ‖A.x n - A.p (n - 1)‖ ^ 2 <=
          (A.lambda (n - 1) * P.Lgrad_h *
            ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2 := by
      exact sq_le_sq' (by
        have hnorm_nonneg : 0 <= ‖A.x n - A.p (n - 1)‖ := norm_nonneg _
        nlinarith) h13
    calc
      ‖A.p n - A.p (n - 1)‖ ^ 2
          <= 2 * (‖A.p n - A.x n‖ ^ 2 +
            ‖A.x n - A.p (n - 1)‖ ^ 2) := hbase
      _ <= 2 * (‖A.x n - A.p n‖ ^ 2 +
          (A.lambda (n - 1) * P.Lgrad_h *
            ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2) := by
            rw [norm_sub_rev (A.p n) (A.x n)]
            nlinarith [h13sq]
      _ = 2 * (‖A.x n - A.p n‖ ^ 2 +
          A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
            ring
  have h16 :
      inner Real
          (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
          (A.p n - A.p (n - 1)) <=
        (nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          (P.Lgrad_h ^ 2 / (2 * nu)) *
            ‖A.x n - A.p (n - 1)‖ ^ 2 := by
    have hLip := P.h_lipschitz_gradient.2.2 (A.p (n - 1)) (A.x n)
    calc
      inner Real
          (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
          (A.p n - A.p (n - 1))
          <= ‖gradient P.h (A.p (n - 1)) - gradient P.h (A.x n)‖ *
              ‖A.p n - A.p (n - 1)‖ := real_inner_le_norm _ _
      _ <= (P.Lgrad_h * ‖A.p (n - 1) - A.x n‖) *
              ‖A.p n - A.p (n - 1)‖ := by
              exact mul_le_mul_of_nonneg_right hLip (norm_nonneg _)
      _ = (P.Lgrad_h * ‖A.x n - A.p (n - 1)‖) *
              ‖A.p n - A.p (n - 1)‖ := by
              rw [norm_sub_rev (A.p (n - 1)) (A.x n)]
      _ <= (nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (1 / (2 * nu)) *
              (P.Lgrad_h * ‖A.x n - A.p (n - 1)‖) ^ 2 :=
              young_mul (a := P.Lgrad_h * ‖A.x n - A.p (n - 1)‖)
                (b := ‖A.p n - A.p (n - 1)‖) hnu
      _ = (nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (P.Lgrad_h ^ 2 / (2 * nu)) *
              ‖A.x n - A.p (n - 1)‖ ^ 2 := by
              ring
  have h17 :
      inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) <=
        (mu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          (1 / (2 * mu)) * ‖A.x n - A.x (n - 1)‖ ^ 2 :=
    inner_young hmu
  have h13sq :
      ‖A.x n - A.p (n - 1)‖ ^ 2 <=
        (A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2 := by
    have hrhs_nonneg :
        0 <= A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
      nlinarith [h13, norm_nonneg (A.x n - A.p (n - 1))]
    exact sq_le_sq' (by
      have hnorm_nonneg : 0 <= ‖A.x n - A.p (n - 1)‖ := norm_nonneg _
      nlinarith) h13
  have h14sq :
      ‖A.x n - A.x (n - 1)‖ ^ 2 <=
        ((1 + A.lambda (n - 1) * P.Lgrad_h) *
          ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2 := by
    have hlamp_nonneg : 0 <= A.lambda (n - 1) := le_of_lt hlamp_pos
    have hfactor_nonneg : 0 <= 1 + A.lambda (n - 1) * P.Lgrad_h := by
      nlinarith [mul_nonneg hlamp_nonneg hLh_nonneg]
    have hrhs_nonneg :
        0 <= (1 + A.lambda (n - 1) * P.Lgrad_h) *
          ‖A.x (n - 1) - A.p (n - 1)‖ :=
      mul_nonneg hfactor_nonneg (norm_nonneg _)
    exact sq_le_sq' (by
      have hnorm_nonneg : 0 <= ‖A.x n - A.x (n - 1)‖ := norm_nonneg _
      nlinarith) h14
  have hM1 :
      A.M1 nu mu <=
        A.sigma / (2 * A.lambda n) - P.Lgrad_h - nu -
          (A.alphaSeq n / A.lambda n) * mu :=
    m1_index_lower_bound A hmu hn1
  have hbpn :
      (A.sigma / 2) * ‖A.p n - A.x n‖ ^ 2 <=
        bregmanDistance A.u (A.p n) (A.x n) :=
    (algorithm_bregman_bounds A (A.p n) (A.x n)).1
  have hbprev :
      bregmanDistance A.u (A.p (n - 1)) (A.x n) <=
        (A.Lgrad_u / 2) * ‖A.p (n - 1) - A.x n‖ ^ 2 :=
    (algorithm_bregman_bounds A (A.p (n - 1)) (A.x n)).2
  have hbpn_scaled :
      A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2 <=
        (1 / A.lambda n) * bregmanDistance A.u (A.p n) (A.x n) := by
    calc
      A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2
          = (1 / A.lambda n) * ((A.sigma / 2) * ‖A.p n - A.x n‖ ^ 2) := by
              field_simp [ne_of_gt hlam_pos]
      _ <= (1 / A.lambda n) * bregmanDistance A.u (A.p n) (A.x n) := by
              exact mul_le_mul_of_nonneg_left hbpn (by positivity)
  have hbprev_scaled :
      (1 / A.lambda n) * bregmanDistance A.u (A.p (n - 1)) (A.x n) <=
        A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 := by
    calc
      (1 / A.lambda n) * bregmanDistance A.u (A.p (n - 1)) (A.x n)
          <= (1 / A.lambda n) * ((A.Lgrad_u / 2) *
              ‖A.p (n - 1) - A.x n‖ ^ 2) := by
              exact mul_le_mul_of_nonneg_left hbprev (by positivity)
      _ = A.Lgrad_u / (2 * A.lambda n) *
            ‖A.p (n - 1) - A.x n‖ ^ 2 := by
              field_simp [ne_of_gt hlam_pos]
  have hhdesc :
      P.h (A.p n) <=
        P.h (A.p (n - 1)) +
          inner Real (gradient P.h (A.p (n - 1))) (A.p n - A.p (n - 1)) +
          (P.Lgrad_h / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 :=
    lemma_3_1_descent P.h P.Lgrad_h P.h_lipschitz_gradient
      (A.p (n - 1)) (A.p n)
  let M1n : Real :=
    A.sigma / (2 * A.lambda n) - P.Lgrad_h - nu -
      (A.alphaSeq n / A.lambda n) * mu
  let M2n : Real :=
    A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
        (P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
          A.Lgrad_u / (2 * A.lambda n)) +
      (A.alphaSeq n / A.lambda n) *
        (mu * A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 +
          (1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu))
  let K : Real := P.Lgrad_h + nu + (A.alphaSeq n / A.lambda n) * mu
  have hc_nonneg : 0 <= A.alphaSeq n / A.lambda n :=
    div_nonneg halpha.1 (le_of_lt hlam_pos)
  have h12 :=
    algorithm_descent_ineq_12 A hn1 hlam_pos hmin hbpn_scaled hbprev_scaled hhdesc
  have h17_scaled :
      (A.alphaSeq n / A.lambda n) *
          inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) <=
        (A.alphaSeq n / A.lambda n) *
          ((mu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (1 / (2 * mu)) * ‖A.x n - A.x (n - 1)‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left h17 hc_nonneg
  have hdp_coeff_nonneg :
      0 <= P.Lgrad_h / 2 + nu / 2 + (A.alphaSeq n / A.lambda n) * (mu / 2) := by
    positivity
  have hdp_bound :
      (P.Lgrad_h / 2 + nu / 2 + (A.alphaSeq n / A.lambda n) * (mu / 2)) *
          ‖A.p n - A.p (n - 1)‖ ^ 2 <=
        K * ‖A.x n - A.p n‖ ^ 2 +
          K * (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
    calc
      (P.Lgrad_h / 2 + nu / 2 + (A.alphaSeq n / A.lambda n) * (mu / 2)) *
          ‖A.p n - A.p (n - 1)‖ ^ 2
          <= (P.Lgrad_h / 2 + nu / 2 + (A.alphaSeq n / A.lambda n) * (mu / 2)) *
            (2 * (‖A.x n - A.p n‖ ^ 2 +
              A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2)) := by
              exact mul_le_mul_of_nonneg_left h15 hdp_coeff_nonneg
      _ = K * ‖A.x n - A.p n‖ ^ 2 +
          K * (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
              simp [K]
              ring
  have ha_coeff_nonneg :
      0 <= A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu) := by
    positivity
  have h13sq_rev :
      ‖A.p (n - 1) - A.x n‖ ^ 2 <=
        (A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2 := by
    simpa [norm_sub_rev] using h13sq
  have ha_bound :
      (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
          ‖A.p (n - 1) - A.x n‖ ^ 2 <=
        (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
          (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
    calc
      (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
          ‖A.p (n - 1) - A.x n‖ ^ 2
          <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
            ((A.lambda (n - 1) * P.Lgrad_h *
              ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2) := by
              exact mul_le_mul_of_nonneg_left h13sq_rev ha_coeff_nonneg
      _ = (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
          (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
              ring
  have hdx_coeff_nonneg :
      0 <= (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) := by
    positivity
  have hdx_bound :
      (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
          ‖A.x n - A.x (n - 1)‖ ^ 2 <=
        (A.alphaSeq n / A.lambda n) *
          ((1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu)) *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
    calc
      (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
          ‖A.x n - A.x (n - 1)‖ ^ 2
          <= (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
            (((1 + A.lambda (n - 1) * P.Lgrad_h) *
              ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2) := by
              exact mul_le_mul_of_nonneg_left h14sq hdx_coeff_nonneg
      _ = (A.alphaSeq n / A.lambda n) *
          ((1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu)) *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
              ring
  have hRbound :
      A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
          P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          inner Real
            (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
            (A.p n - A.p (n - 1)) +
          (A.alphaSeq n / A.lambda n) *
            inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) <=
        K * ‖A.x n - A.p n‖ ^ 2 +
          M2n * ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
    have hyoung :
        A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
            P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            inner Real
              (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
              (A.p n - A.p (n - 1)) +
            (A.alphaSeq n / A.lambda n) *
              inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) <=
          (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              ‖A.p (n - 1) - A.x n‖ ^ 2 +
            (P.Lgrad_h / 2 + nu / 2 +
                (A.alphaSeq n / A.lambda n) * (mu / 2)) *
              ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := by
      calc
        A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
            P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            inner Real
              (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
              (A.p n - A.p (n - 1)) +
            (A.alphaSeq n / A.lambda n) *
              inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1))
            <= A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
              P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
              ((nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
                (P.Lgrad_h ^ 2 / (2 * nu)) *
                  ‖A.x n - A.p (n - 1)‖ ^ 2) +
              (A.alphaSeq n / A.lambda n) *
                inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) := by
                linarith [h16]
        _ <= A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
              P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
              ((nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
                (P.Lgrad_h ^ 2 / (2 * nu)) *
                  ‖A.x n - A.p (n - 1)‖ ^ 2) +
              (A.alphaSeq n / A.lambda n) *
                ((mu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
                  (1 / (2 * mu)) * ‖A.x n - A.x (n - 1)‖ ^ 2) := by
                linarith [h17_scaled]
        _ = (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              ‖A.p (n - 1) - A.x n‖ ^ 2 +
            (P.Lgrad_h / 2 + nu / 2 +
                (A.alphaSeq n / A.lambda n) * (mu / 2)) *
              ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := by
                rw [norm_sub_rev (A.x n) (A.p (n - 1))]
                ring
    calc
      A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
          P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          inner Real
            (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
            (A.p n - A.p (n - 1)) +
          (A.alphaSeq n / A.lambda n) *
            inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1))
          <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              ‖A.p (n - 1) - A.x n‖ ^ 2 +
            (P.Lgrad_h / 2 + nu / 2 +
                (A.alphaSeq n / A.lambda n) * (mu / 2)) *
              ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := hyoung
      _ <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) +
            (P.Lgrad_h / 2 + nu / 2 +
                (A.alphaSeq n / A.lambda n) * (mu / 2)) *
              ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := by
                linarith [ha_bound]
      _ <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) +
            (K * ‖A.x n - A.p n‖ ^ 2 +
              K * (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2)) +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := by
                linarith [hdp_bound]
      _ <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) +
            (K * ‖A.x n - A.p n‖ ^ 2 +
              K * (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2)) +
            (A.alphaSeq n / A.lambda n) *
              ((1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu)) *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
                linarith [hdx_bound]
      _ = K * ‖A.x n - A.p n‖ ^ 2 +
          M2n * ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
            simp [M2n, K]
            ring
  have hindexed :
      objectiveWithQuadratic P M1n (A.p n) (A.x n) <=
        objectiveWithQuadratic P M2n (A.p (n - 1)) (A.x (n - 1)) := by
    unfold objectiveWithQuadratic
    have h12_bound :
        erealAddReal (P.objective (A.p n))
            (A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2) <=
          erealAddReal (P.objective (A.p (n - 1)))
            (K * ‖A.x n - A.p n‖ ^ 2 +
              M2n * ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
      exact le_trans h12 (erealAddReal_le_of_le hRbound)
    have hcommon :
        erealAddReal (P.objective (A.p n))
            (M1n * ‖A.p n - A.x n‖ ^ 2 +
              K * ‖A.x n - A.p n‖ ^ 2) <=
          erealAddReal (P.objective (A.p (n - 1)))
            (M2n * ‖A.p (n - 1) - A.x (n - 1)‖ ^ 2 +
              K * ‖A.x n - A.p n‖ ^ 2) := by
      convert h12_bound using 2 <;>
        simp [M1n, K, norm_sub_rev] <;> ring
    exact erealAddReal_le_cancel_common (t := K * ‖A.x n - A.p n‖ ^ 2)
      (by simpa [norm_sub_rev, add_comm, add_left_comm, add_assoc] using hcommon)
  have hM2 : M2n <= A.M2 nu mu := by
    simpa [M2n] using m2_index_upper_bound A hnu hmu hn1 hnpred
  calc
    objectiveWithQuadratic P (A.M1 nu mu) (A.p n) (A.x n)
        <= objectiveWithQuadratic P M1n (A.p n) (A.x n) := by
            exact objectiveWithQuadratic_mono_coeff P (by simpa [M1n] using hM1)
              (A.p n) (A.x n)
    _ <= objectiveWithQuadratic P M2n (A.p (n - 1)) (A.x (n - 1)) := hindexed
    _ <= objectiveWithQuadratic P (A.M2 nu mu) (A.p (n - 1)) (A.x (n - 1)) := by
            exact objectiveWithQuadratic_mono_coeff P hM2 (A.p (n - 1)) (A.x (n - 1))
```

## Proof explanation
The proof begins with `intro n hn`, introducing an arbitrary index $n$ and the hypothesis $n\ge 2$. The tactic `omega` is then used twice to obtain the arithmetic facts $1\le n$ and $1\le n-1$. These are needed because several estimates in the proof require the algorithm-index bounds at both $n$ and $n-1$.

Next the proof extracts parameter and step-size information from the algorithm data. From `A.lambda_bounds n hn1` and `A.lambda_bounds (n-1) hnpred`, together with `A.lambdaLower_pos`, it obtains

$$
\lambda_n>0,\qquad \lambda_{n-1}>0,
$$

where $\lambda_k=A.\lambda(k)$. From `A.alpha_bounds n hn1` it obtains

$$
\alpha_n\ge 0,
$$

where $\alpha_n=A.\operatorname{alphaSeq}(n)$. It also records

$$
L_h=P.Lgrad_h\ge 0,\qquad L_u=A.Lgrad_u\ge 0,\qquad \sigma=A.\sigma>0.
$$

The nonnegativity of $L_h$ and $L_u$ is used later when multiplying inequalities by these constants; the positivity of $\lambda_n$ is used to form $1/\lambda_n$ and to divide by $\lambda_n$.

The first main inequality is the minimization property of $p_n$. The proof defines

$$
J_n(y)
=
\operatorname{erealAddReal}\Bigl(
P.f(y),\,
\frac1{\lambda_n}D_u(y,x_n)
+\langle y,\nabla h(x_n)\rangle
+c_n\langle y,x_{n-1}-x_n\rangle
\Bigr),
$$

where $c_n=\alpha_n/\lambda_n$, $D_u$ is the Bregman distance

$$
D_u(y,z)=u(y)-u(z)-\langle\nabla u(z),y-z\rangle,
$$

and $\langle\cdot,\cdot\rangle$ is the real inner product. This is the algorithm step objective. The fact `A.p_argmin n hn1` says that $p_n$ belongs to the argmin set of $J_n$. The cited lemma `argminSet_le` states that if a point belongs to the argmin set of a function $G$, then its value is no larger than the value at any other point:

$$
p\in\operatorname{argminSet}G \implies G(p)\le G(y).
$$

Specialized here to $G=J_n$, $p=p_n$, and $y=p_{n-1}$, it gives

$$
J_n(p_n)\le J_n(p_{n-1}).
$$

This is `hmin`. Mathematically, it expresses that the current proximal point $p_n$ gives no larger step-objective value than the previous point $p_{n-1}$.

The proof then analyzes the auxiliary point $x_n$. The field `A.x_update (n-1) hnpred` gives

$$
x_n
=
p_{n-1}
+\lambda_{n-1}\bigl(\nabla h(x_{n-1})-\nabla h(p_{n-1})\bigr).
$$

Subtracting $p_{n-1}$ yields

$$
x_n-p_{n-1}
=
\lambda_{n-1}\bigl(\nabla h(x_{n-1})-\nabla h(p_{n-1})\bigr).
$$

Using the Lipschitz estimate for $\nabla h$, namely

$$
\|\nabla h(x)-\nabla h(y)\|\le L_h\|x-y\|,
$$

the proof obtains

$$
\|x_n-p_{n-1}\|
\le
\lambda_{n-1}L_h\|x_{n-1}-p_{n-1}\|.
$$

This is the estimate called `h13`. It is obtained by taking norms:

$$
\|x_n-p_{n-1}\|
=
\lambda_{n-1}
\|\nabla h(x_{n-1})-\nabla h(p_{n-1})\|,
$$

and then applying the Lipschitz bound, using $\lambda_{n-1}>0$.

From this, the proof derives

$$
\|x_n-x_{n-1}\|
\le
(1+\lambda_{n-1}L_h)
\|x_{n-1}-p_{n-1}\|.
$$

This is `h14`. The argument inserts the intermediate point $p_{n-1}$:

$$
\|x_n-x_{n-1}\|
\le
\|x_n-p_{n-1}\|+\|p_{n-1}-x_{n-1}\|,
$$

then substitutes the bound for $\|x_n-p_{n-1}\|$ and simplifies using $\|p_{n-1}-x_{n-1}\|=\|x_{n-1}-p_{n-1}\|$.

The proof also needs a squared estimate for $\|p_n-p_{n-1}\|$. It invokes `norm_sq_sub_le_two`, which states that for all points $a,b,c$,

$$
\|a-b\|^2\le 2\bigl(\|a-c\|^2+\|c-b\|^2\bigr).
$$

Taking $a=p_n$, $b=p_{n-1}$, and $c=x_n$, this gives

$$
\|p_n-p_{n-1}\|^2
\le
2\bigl(\|p_n-x_n\|^2+\|x_n-p_{n-1}\|^2\bigr).
$$

Combining this with the square of the estimate $\|x_n-p_{n-1}\|\le \lambda_{n-1}L_h\|x_{n-1}-p_{n-1}\|$, the proof obtains

$$
\|p_n-p_{n-1}\|^2
\le
2\Bigl(
\|x_n-p_n\|^2
+
\lambda_{n-1}^2L_h^2
\|x_{n-1}-p_{n-1}\|^2
\Bigr).
$$

This is `h15`. The auxiliary facts `h13sq` and `h14sq` are the squared versions of `h13` and `h14`, obtained using `sq_le_sq'`, which is the elementary fact that for nonnegative quantities one may square an inequality.

The proof next applies two Young-type inequalities. For the gradient-difference inner product, it uses `young_mul`, which says that for $0<\varepsilon$,

$$
ab\le \frac{\varepsilon}{2}b^2+\frac1{2\varepsilon}a^2.
$$

Specialized with $\varepsilon=\nu$, $a=L_h\|x_n-p_{n-1}\|$, and $b=\|p_n-p_{n-1}\|$, it gives

$$
L_h\|x_n-p_{n-1}\|\|p_n-p_{n-1}\|
\le
\frac{\nu}{2}\|p_n-p_{n-1}\|^2
+
\frac{L_h^2}{2\nu}\|x_n-p_{n-1}\|^2.
$$

Together with the elementary bound

$$
\langle \nabla h(p_{n-1})-\nabla h(x_n),\,p_n-p_{n-1}\rangle
\le
\|\nabla h(p_{n-1})-\nabla h(x_n)\|
\|p_n-p_{n-1}\|
$$

and the Lipschitz estimate for $\nabla h$, this yields

$$
\langle \nabla h(p_{n-1})-\nabla h(x_n),\,p_n-p_{n-1}\rangle
\le
\frac{\nu}{2}\|p_n-p_{n-1}\|^2
+
\frac{L_h^2}{2\nu}\|x_n-p_{n-1}\|^2.
$$

This is `h16`.

For the inertial inner product, the proof uses `inner_young`, which states that for $0<\varepsilon$,

$$
\langle a,b\rangle
\le
\frac{\varepsilon}{2}\|a\|^2+\frac1{2\varepsilon}\|b\|^2.
$$

With $\varepsilon=\mu$, $a=p_n-p_{n-1}$, and $b=x_n-x_{n-1}$, it gives

$$
\langle p_n-p_{n-1},\,x_n-x_{n-1}\rangle
\le
\frac{\mu}{2}\|p_n-p_{n-1}\|^2
+
\frac1{2\mu}\|x_n-x_{n-1}\|^2.
$$

This is `h17`. Since $c_n=\alpha_n/\lambda_n\ge 0$, multiplying by $c_n$ gives the scaled version `h17_scaled`.

The proof then extracts the Bregman bounds. The theorem `algorithm_bregman_bounds` states that for every $x,y$,

$$
\frac{\sigma}{2}\|x-y\|^2
\le
D_u(x,y)
\le
\frac{L_u}{2}\|x-y\|^2.
$$

Applying this with $(x,y)=(p_n,x_n)$ gives

$$
\frac{\sigma}{2}\|p_n-x_n\|^2\le D_u(p_n,x_n),
$$

and applying it with $(x,y)=(p_{n-1},x_n)$ gives

$$
D_u(p_{n-1},x_n)\le \frac{L_u}{2}\|p_{n-1}-x_n\|^2.
$$

Multiplying these by $1/\lambda_n>0$ produces exactly the two scaled hypotheses

$$
\frac{\sigma}{2\lambda_n}\|p_n-x_n\|^2
\le
\frac1{\lambda_n}D_u(p_n,x_n),
$$

and

$$
\frac1{\lambda_n}D_u(p_{n-1},x_n)
\le
\frac{L_u}{2\lambda_n}\|p_{n-1}-x_n\|^2.
$$

These are `hbpn_scaled` and `hbprev_scaled`.

The proof also needs the descent inequality for $h$. It invokes `lemma_3_1_descent`, which says that if $h$ has Lipschitz-continuous gradient with constant $L_h$, then

$$
h(y)\le h(x)+\langle\nabla h(x),y-x\rangle+\frac{L_h}{2}\|y-x\|^2.
$$

With $x=p_{n-1}$ and $y=p_n$, this gives

$$
h(p_n)
\le
h(p_{n-1})
+\langle\nabla h(p_{n-1}),p_n-p_{n-1}\rangle
+\frac{L_h}{2}\|p_n-p_{n-1}\|^2.
$$

This is `hhdesc`.

At this point the proof has all ingredients for the main algorithmic inequality. It applies `algorithm_descent_ineq_12` with the index $n$, the positivity $\lambda_n>0$, the minimization inequality `hmin`, the two scaled Bregman inequalities, and the descent inequality `hhdesc`. The conclusion is

$$
\operatorname{erealAddReal}\left(P.\mathrm{objective}(p_n),
\frac{\sigma}{2\lambda_n}\|p_n-x_n\|^2\right)
\le
\operatorname{erealAddReal}\left(P.\mathrm{objective}(p_{n-1}),R_n\right),
$$

where

$$
R_n=
\frac{L_u}{2\lambda_n}\|p_{n-1}-x_n\|^2
+\frac{L_h}{2}\|p_n-p_{n-1}\|^2
+\langle \nabla h(p_{n-1})-\nabla h(x_n),\,p_n-p_{n-1}\rangle
+c_n\langle p_n-p_{n-1},\,x_n-x_{n-1}\rangle.
$$

This is the inequality called `h12`. It is the central estimate: it combines the proximal minimization property, the Bregman bounds, and the descent inequality for $h$ into one extended-real inequality.

The proof now bounds the right-hand side $R_n$. It defines local constants

$$
M_{1,n}
=
\frac{\sigma}{2\lambda_n}-L_h-\nu-c_n\mu,
$$

$$
M_{2,n}
=
\lambda_{n-1}^2L_h^2
\left(
\frac{L_h^2}{2\nu}+\nu+L_h+\frac{L_u}{2\lambda_n}
\right)
+
c_n\left(
\mu\lambda_{n-1}^2L_h^2+
\frac{(1+\lambda_{n-1}L_h)^2}{2\mu}
\right),
$$

and

$$
K=L_h+\nu+c_n\mu.
$$

The name `M1n` is the upper bound for $A.M_1(\nu,\mu)$ supplied by `m1_index_lower_bound`, and `M2n` is the lower bound for $A.M_2(\nu,\mu)$ supplied by `m2_index_upper_bound`. Indeed, `m1_index_lower_bound` gives

$$
A.M_1(\nu,\mu)\le M_{1,n},
$$

using $0<\mu$ and $1\le n$. Similarly, `m2_index_upper_bound` gives

$$
M_{2,n}\le A.M_2(\nu,\mu),
$$

using $0<\nu$, $0<\mu$, $1\le n$, and $1\le n-1$.

The proof proceeds to bound $R_n$. First, `h16` and `h17_scaled` are combined to show

$$
R_n
\le
\left(
\frac{L_u}{2\lambda_n}+\frac{L_h^2}{2\nu}
\right)\|p_{n-1}-x_n\|^2
+
\left(
\frac{L_h}{2}+\frac{\nu}{2}+\frac{c_n\mu}{2}
\right)\|p_n-p_{n-1}\|^2
+
c_n\frac1{2\mu}\|x_n-x_{n-1}\|^2.
$$

This is a direct application of the two Young bounds. Then:
- The squared estimate `h13sq` is used to replace

$$
\|p_{n-1}-x_n\|^2
$$

by at most

$$
\lambda_{n-1}^2L_h^2\|x_{n-1}-p_{n-1}\|^2.
$$

- The squared estimate `h15` is multiplied by the nonnegative coefficient

$$
\frac{L_h}{2}+\frac{\nu}{2}+\frac{c_n\mu}{2}
$$

to bound the $\|p_n-p_{n-1}\|^2$ term by

$$
K\|x_n-p_n\|^2
+
K\lambda_{n-1}^2L_h^2\|x_{n-1}-p_{n-1}\|^2.
$$

- The squared estimate `h14sq` is used to replace

$$
\|x_n-x_{n-1}\|^2
$$

by at most

$$
(1+\lambda_{n-1}L_h)^2\|x_{n-1}-p_{n-1}\|^2.
$$

Summing these three bounds and simplifying gives

$$
R_n
\le
K\|x_n-p_n\|^2
+
M_{2,n}\|x_{n-1}-p_{n-1}\|^2.
$$

This is `hRbound`. The proof uses `linarith` to combine the intermediate inequalities and `ring` to verify the algebraic identity matching the coefficients with $M_{2,n}$.

Now the proof converts `h12` into an inequality between `objectiveWithQuadratic` terms. Since `erealAddReal_le_of_le` states that for a fixed extended-real number $a$,

$$
r\le s \implies
\operatorname{erealAddReal}(a,r)\le \operatorname{erealAddReal}(a,s),
$$

the bound on $R_n$ allows the right-hand side of `h12` to be replaced by its upper bound:

$$
\operatorname{erealAddReal}\left(P.\mathrm{objective}(p_n),
\frac{\sigma}{2\lambda_n}\|p_n-x_n\|^2\right)
\le
\operatorname{erealAddReal}\left(P.\mathrm{objective}(p_{n-1}),
K\|x_n-p_n\|^2+M_{2,n}\|x_{n-1}-p_{n-1}\|^2\right).
$$

Using the identity

$$
M_{1,n}+K=\frac{\sigma}{2\lambda_n},
$$

and $\|x_n-p_n\|=\|p_n-x_n\|$, the left real part becomes

$$
M_{1,n}\|p_n-x_n\|^2+K\|x_n-p_n\|^2.
$$

The right real part is rearranged as

$$
M_{2,n}\|p_{n-1}-x_{n-1}\|^2+K\|x_n-p_n\|^2.
$$

Thus the inequality has the form

$$
\operatorname{erealAddReal}\left(P.\mathrm{objective}(p_n),r+t\right)
\le
\operatorname{erealAddReal}\left(P.\mathrm{objective}(p_{n-1}),s+t\right),
$$

with the common real term

$$
t=K\|x_n-p_n\|^2.
$$

The proof applies `erealAddReal_le_cancel_common`, which says that from

$$
\operatorname{erealAddReal}(a,r+t)\le \operatorname{erealAddReal}(b,s+t)
$$

one may cancel the common real summand $t$ and conclude

$$
\operatorname{erealAddReal}(a,r)\le \operatorname{erealAddReal}(b,s).
$$

Here this yields

$$
\operatorname{objectiveWithQuadratic}_P(M_{1,n},p_n,x_n)
\le
\operatorname{objectiveWithQuadratic}_P(M_{2,n},p_{n-1},x_{n-1}).
$$

This is `hindexed`.

Finally, the proof compares the local coefficients $M_{1,n}$ and $M_{2,n}$ to the algorithm coefficients $A.M_1(\nu,\mu)$ and $A.M_2(\nu,\mu)$. It uses `objectiveWithQuadratic_mono_coeff`, which states that for fixed $P,x,y$, if $M\le M'$, then

$$
\operatorname{objectiveWithQuadratic}_P(M,x,y)
\le
\operatorname{objectiveWithQuadratic}_P(M',x,y).
$$

From `hM1`, namely $A.M_1(\nu,\mu)\le M_{1,n}$, this gives

$$
\operatorname{objectiveWithQuadratic}_P(A.M_1(\nu,\mu),p_n,x_n)
\le
\operatorname{objectiveWithQuadratic}_P(M_{1,n},p_n,x_n).
$$

From `hM2`, namely $M_{2,n}\le A.M_2(\nu,\mu)$, it gives

$$
\operatorname{objectiveWithQuadratic}_P(M_{2,n},p_{n-1},x_{n-1})
\le
\operatorname{objectiveWithQuadratic}_P(A.M_2(\nu,\mu),p_{n-1},x_{n-1}).
$$

Combining these two monotonicity steps with `hindexed`, the final `calc` block proves

$$
\operatorname{objectiveWithQuadratic}_P(A.M_1(\nu,\mu),p_n,x_n)
\le
\operatorname{objectiveWithQuadratic}_P(A.M_2(\nu,\mu),p_{n-1},x_{n-1}),
$$

which is exactly the statement of `lemma_3_2_descent`. The tactics `simpa` and `ring` are used to rewrite the local constants and rearrange the expressions; `exact` closes the final goals by applying the previously established inequalities.

