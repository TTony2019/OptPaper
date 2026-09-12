## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/lem_3.lean`

## Lean statement
```lean
theorem lemma_3_3_parameter_choice
    (sigma Lh Lu lambdaLower alpha nu mu : Real)
    (hnu : 0 < nu) (hmu : 0 < mu) (hlambda : 0 < lambdaLower)
    (hineq : lemma33StrictInequality sigma Lh Lu lambdaLower alpha nu mu) :
    ∃ rho : Real, 0 < rho ∧
      ∀ lambdaUpper : Real,
        lambdaLower <= lambdaUpper ->
        lambdaUpper < lambdaLower + rho ->
        M2Value Lh Lu lambdaUpper alpha lambdaLower nu mu <
          M1Value sigma Lh lambdaUpper alpha lambdaLower nu mu
```

## Statement explanation
The declaration is a parameter-choice theorem for real numbers $\sigma, L_h, L_u, \lambda_{\mathrm{lower}}, \alpha, \nu, \mu$. Its hypotheses are that $\nu\gt 0$, $\mu\gt 0$, $\lambda_{\mathrm{lower}}\gt 0$, and that the predicate `lemma33StrictInequality` holds for the tuple $(\sigma, L_h, L_u, \lambda_{\mathrm{lower}}, \alpha, \nu, \mu)$. The concrete definition of `lemma33StrictInequality` is not expanded in the supplied source; in the proof it is used only as the hypothesis needed to invoke the auxiliary result `lemma33_base_scaled_inequality`.

The conclusion is that there exists a positive real number $\rho$ such that every real $\lambda_{\mathrm{upper}}$ satisfying

$$
\lambda_{\mathrm{lower}} \le \lambda_{\mathrm{upper}}
\quad\text{and}\quad
\lambda_{\mathrm{upper}} < \lambda_{\mathrm{lower}} + \rho
$$

also satisfies

$$
\mathrm{M2Value}(L_h,L_u,\lambda_{\mathrm{upper}},\alpha,\lambda_{\mathrm{lower}},\nu,\mu)
<
\mathrm{M1Value}(\sigma,L_h,\lambda_{\mathrm{upper}},\alpha,\lambda_{\mathrm{lower}},\nu,\mu).
$$

Here `M1Value` and `M2Value` are real-valued quantities depending on the displayed parameters; their internal definitions are not given in the provided source. Thus the theorem says that if the base strict inequality at $\lambda_{\mathrm{lower}}$ holds, then the comparison $\mathrm{M2Value}\lt \mathrm{M1Value}$ remains true for all $\lambda_{\mathrm{upper}}$ sufficiently close to $\lambda_{\mathrm{lower}}$ from the right. It is a local right-sided stability or parameter-selection statement.

## Lean proof
```lean
by
  have hbase :=
    lemma33_base_scaled_inequality sigma Lh Lu lambdaLower alpha nu mu hnu hmu hlambda hineq
  let F : Real -> Real := fun t =>
    2 * t *
      (Lh + nu + (alpha / lambdaLower) * mu +
        t ^ 2 * Lh ^ 2 *
          (Lh ^ 2 / (2 * nu) + nu + Lh + Lu / (2 * lambdaLower)) +
        alpha / lambdaLower *
          (mu * t ^ 2 * Lh ^ 2 +
            (1 + t * Lh) ^ 2 / (2 * mu)))
  have hcont : Continuous F := by
    unfold F
    continuity
  have hopen : IsOpen {t : Real | F t < sigma} := isOpen_lt hcont continuous_const
  have hmem : lambdaLower ∈ {t : Real | F t < sigma} := by
    simpa [F] using hbase
  rcases (Metric.isOpen_iff.mp hopen lambdaLower hmem) with ⟨eps, heps_pos, hball⟩
  refine ⟨eps, heps_pos, ?_⟩
  intro lambdaUpper hlower hlt
  have hdist : lambdaUpper ∈ Metric.ball lambdaLower eps := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith
  have hscaled : F lambdaUpper < sigma := hball hdist
  have hlu_pos : 0 < lambdaUpper := lt_of_lt_of_le hlambda hlower
  exact lemma33_m2_lt_m1_of_scaled sigma Lh Lu lambdaUpper alpha lambdaLower nu mu hlu_pos (by
    simpa [F] using hscaled)
```

## Proof explanation
The proof first applies the auxiliary lemma `lemma33_base_scaled_inequality` with the arguments $\sigma, L_h, L_u, \lambda_{\mathrm{lower}}, \alpha, \nu, \mu$, the positivity hypotheses $\nu\gt 0$, $\mu\gt 0$, $\lambda_{\mathrm{lower}}\gt 0$, and the hypothesis `hineq`. The result is the base scaled inequality

$$
2\lambda_{\mathrm{lower}}\left(
L_h+\nu+\frac{\alpha}{\lambda_{\mathrm{lower}}}\mu
+\lambda_{\mathrm{lower}}^2L_h^2\left(\frac{L_h^2}{2\nu}+\nu+L_h+\frac{L_u}{2\lambda_{\mathrm{lower}}}\right)
+\frac{\alpha}{\lambda_{\mathrm{lower}}}\left(\mu\lambda_{\mathrm{lower}}^2L_h^2+\frac{(1+\lambda_{\mathrm{lower}}L_h)^2}{2\mu}\right)
\right)<\sigma.
$$

This is stored as `hbase`.

Next the proof defines an auxiliary real function $F$ by

$$
F(t)=2t\left(
L_h+\nu+\frac{\alpha}{\lambda_{\mathrm{lower}}}\mu
+t^2L_h^2\left(\frac{L_h^2}{2\nu}+\nu+L_h+\frac{L_u}{2\lambda_{\mathrm{lower}}}\right)
+\frac{\alpha}{\lambda_{\mathrm{lower}}}\left(\mu t^2L_h^2+\frac{(1+tL_h)^2}{2\mu}\right)
\right).
$$

This is exactly the expression appearing in `hbase`, but with the variable $t$ in place of $\lambda_{\mathrm{lower}}$. Therefore `hbase` says precisely that $F(\lambda_{\mathrm{lower}})\lt \sigma$.

The proof then shows that $F$ is continuous. It does this by unfolding the local definition of $F$ and using the `continuity` tactic. Mathematically, $F$ is a polynomial in $t$ with coefficients involving fixed real constants such as $L_h, L_u, \alpha, \lambda_{\mathrm{lower}}, \nu, \mu$, so it is continuous. The denominators are fixed constants and do not introduce a discontinuity in the variable $t$.

Since $F$ is continuous and the constant function $t\mapsto\sigma$ is continuous, the set

```math
S=\{t\in\mathbb{R}:F(t)<\sigma\}
```

is open. This is the content of the invocation `isOpen_lt hcont continuous_const`. Because $F(\lambda_{\mathrm{lower}})\lt \sigma$, we have $\lambda_{\mathrm{lower}}\in S$. The proof records this as `hmem` by simplifying `hbase` using the definition of $F$.

The proof then uses the metric characterization of open sets, `Metric.isOpen_iff`. Since $S$ is open and $\lambda_{\mathrm{lower}}\in S$, there exists $\varepsilon\gt 0$ such that the metric ball $B(\lambda_{\mathrm{lower}},\varepsilon)$ is contained in $S$. In symbols, for every $t$ with $|t-\lambda_{\mathrm{lower}}|\lt \varepsilon$, one has $F(t)\lt \sigma$. The proof extracts this $\varepsilon$, its positivity, and the containment statement as `heps_pos` and `hball`.

The proof now chooses $\rho=\varepsilon$. It must show that every $\lambda_{\mathrm{upper}}$ satisfying $\lambda_{\mathrm{lower}}\le\lambda_{\mathrm{upper}}$ and $\lambda_{\mathrm{upper}}\lt \lambda_{\mathrm{lower}}+\varepsilon$ satisfies the desired comparison. After introducing such a $\lambda_{\mathrm{upper}}$ with the hypotheses `hlower` and `hlt`, the proof shows that $\lambda_{\mathrm{upper}}$ lies in the ball $B(\lambda_{\mathrm{lower}},\varepsilon)$. It rewrites metric-ball membership using `Metric.mem_ball` and `Real.dist_eq`, so the goal becomes $|\lambda_{\mathrm{upper}}-\lambda_{\mathrm{lower}}|\lt \varepsilon$. Since `hlower` says $\lambda_{\mathrm{lower}}\le\lambda_{\mathrm{upper}}$, the difference $\lambda_{\mathrm{upper}}-\lambda_{\mathrm{lower}}$ is nonnegative; this is obtained from `sub_nonneg.mpr hlower`. Therefore `abs_of_nonneg` replaces the absolute value by $\lambda_{\mathrm{upper}}-\lambda_{\mathrm{lower}}$. The hypothesis `hlt` says $\lambda_{\mathrm{upper}}\lt \lambda_{\mathrm{lower}}+\varepsilon$, so `linarith` concludes $\lambda_{\mathrm{upper}}-\lambda_{\mathrm{lower}}\lt \varepsilon$. Hence $\lambda_{\mathrm{upper}}\in B(\lambda_{\mathrm{lower}},\varepsilon)$, giving `hdist`.

Applying `hball` to `hdist` gives $F(\lambda_{\mathrm{upper}})\lt \sigma$, stored as `hscaled`. The proof also shows $0\lt \lambda_{\mathrm{upper}}$ by combining $0\lt \lambda_{\mathrm{lower}}$ with $\lambda_{\mathrm{lower}}\le\lambda_{\mathrm{upper}}$ using `lt_of_lt_of_le`. This is `hlu_pos`.

Finally, the proof applies `lemma33_m2_lt_m1_of_scaled` with arguments $\sigma, L_h, L_u, \lambda_{\mathrm{upper}}, \alpha, \lambda_{\mathrm{lower}}, \nu, \mu$. That lemma requires $0\lt \lambda_{\mathrm{upper}}$ and the scaled inequality

$$
2\lambda_{\mathrm{upper}}\left(
L_h+\nu+\frac{\alpha}{\lambda_{\mathrm{lower}}}\mu
+\lambda_{\mathrm{upper}}^2L_h^2\left(\frac{L_h^2}{2\nu}+\nu+L_h+\frac{L_u}{2\lambda_{\mathrm{lower}}}\right)
+\frac{\alpha}{\lambda_{\mathrm{lower}}}\left(\mu\lambda_{\mathrm{upper}}^2L_h^2+\frac{(1+\lambda_{\mathrm{upper}}L_h)^2}{2\mu}\right)
\right)<\sigma.
$$

The proof supplies $0\lt \lambda_{\mathrm{upper}}$ as `hlu_pos`. The scaled inequality is obtained from `hscaled` by `simpa [F]`, which unfolds the definition of $F$ at $t=\lambda_{\mathrm{upper}}$ and converts $F(\lambda_{\mathrm{upper}})\lt \sigma$ into exactly the displayed inequality. The lemma `lemma33_m2_lt_m1_of_scaled` then yields

$$
\mathrm{M2Value}(L_h,L_u,\lambda_{\mathrm{upper}},\alpha,\lambda_{\mathrm{lower}},\nu,\mu)
<
\mathrm{M1Value}(\sigma,L_h,\lambda_{\mathrm{upper}},\alpha,\lambda_{\mathrm{lower}},\nu,\mu),
$$

which is precisely the goal for this $\lambda_{\mathrm{upper}}$. Thus the existential choice $\rho=\varepsilon$ proves the theorem.

