## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_9.lean`

## Lean statement
```lean
theorem thm_9 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (A : M → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (V : Set M) (μbar : M) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ : M, CocoerciveOn α Set.univ (fun x : Set.univ => A μ x))
    (hγT : γ * T + T ^ 2 / α < 1)
    (hsol : ∀ μ : M,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hV : V ∈ nhds μbar) (hμbar : μbar ∈ V)
    (hD : M → ℝ) (hD_lim : Tendsto hD (nhds μbar) (nhds 0))
    (hDbound : ∀ μ : M, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖A μ (x μbar s) - A μbar (x μbar s)‖ ≤ hD μ)
    (hu₀ : Tendsto u₀ (nhds μbar) (nhds (u₀ μbar)))
    (hv₀ : Tendsto v₀ (nhds μbar) (nhds (v₀ μbar))) :
    Tendsto (fun μ : M => pathSupNorm T (fun t => x μ t - x μbar t))
      (nhds μbar) (nhds 0)
```

## Statement explanation
The declaration `thm_9` states a local uniform-stability result for a parametrized family of solutions of a damped second-order problem. The space \(H\) is a complete real inner product space, hence a real Hilbert space, and \(M\) is a normed additive commutative group, used as the parameter space. The data are an operator family \(A:M\to H\to H\), functions \(x,dx,ddx:M\to\mathbb R\to H\), initial data \(u_0,v_0:M\to H\), a set \(V\subseteq M\), a base parameter \(\bar\mu\in M\), and real numbers \(\alpha,\gamma,T\).

The standing assumptions are:

- \(\alpha>0\) and \(T>0\).
- For every \(\mu\in M\), the operator \(A_\mu:H\to H\) is \(\alpha\)-cocoercive on all of \(H\).
- The small-time/damping condition
  \[
  \gamma T+\frac{T^2}{\alpha}<1
  \]
  holds. Since \(\alpha>0\), this implies \(\alpha-\alpha\gamma T-T^2>0\), so the coefficient appearing later is a genuine positive constant.
- For every \(\mu\in M\), the triple \((x_\mu,dx_\mu,ddx_\mu)\) satisfies the predicate `ext_def_2` with operator \(A_\mu\), damping \(\gamma\), and initial data \(u_0(\mu),v_0(\mu)\). The provided source does not display the full definition of `ext_def_2`; the proof uses it exactly as the solution/Picard condition required by `thm_8_general`. The accompanying comment identifies the associated Picard operator as
  \[
  \Gamma_{A,u_0,v_0}(x)(t)
  =u_0+t v_0+\int_0^t (s-t)\bigl(\gamma \dot x(s)+A x(s)\bigr)\,ds,
  \]
  the Picard operator of the damped second-order system.
- \(V\) is a neighborhood of \(\bar\mu\), and \(\bar\mu\in V\).
- \(h_D:M\to\mathbb R\) satisfies \(h_D(\mu)\to0\) as \(\mu\to\bar\mu\).
- For every \(\mu\in M\) and every \(s\in[0,T]\),
  \[
  \|A_\mu(x_{\bar\mu}(s))-A_{\bar\mu}(x_{\bar\mu}(s))\|\le h_D(\mu).
  \]
  Thus the difference of the operators along the reference trajectory is controlled by a quantity tending to \(0\).
- The initial data are continuous at \(\bar\mu\):
  \[
  u_0(\mu)\to u_0(\bar\mu),\qquad
  v_0(\mu)\to v_0(\bar\mu).
  \]

The definition of `pathSupNorm` is
\[
\operatorname{pathSupNorm}_T(y)
=\sup\{q\in\mathbb R:\exists t\in[0,T],\,q=\|y(t)\|\}.
\]
So the conclusion
\[
\operatorname{Tendsto}\Bigl(\mu\mapsto
\operatorname{pathSupNorm}_T\bigl(x_\mu-x_{\bar\mu}\bigr)\Bigr)
\ \text{at }\bar\mu\ \text{to }0
\]
means
\[
\sup_{t\in[0,T]}\|x_\mu(t)-x_{\bar\mu}(t)\|\to0
\quad\text{as }\mu\to\bar\mu.
\]
In words: near the parameter \(\bar\mu\), the solution \(x_\mu\) converges uniformly on the time interval \([0,T]\) to the reference solution \(x_{\bar\mu}\).

## Lean proof
```lean
by
  -- The discrepancy bound required by `thm_8_general`, obtained from the
  -- Lipschitz continuity (cocoercivity) and the uniform bound along `x μbar`.
  have hdisc : ∀ μ ∈ V, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ v : H,
      ‖v - x μbar s‖ ≤ ‖u₀ μ - u₀ μbar‖ →
        ‖A μ v - A μbar v‖ ≤ 2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ := by
    intro μ _ s hs v hv
    have hLμ (a b : H) : ‖A μ a - A μ b‖ ≤ α⁻¹ * ‖a - b‖ := by
      have h := (cocoercive_implies_lipschitz (A μ) α (hcoco μ)).dist_le_mul a b
      simpa [dist_eq_norm, Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hα.le)] using h
    have hLbar (a b : H) : ‖A μbar a - A μbar b‖ ≤ α⁻¹ * ‖a - b‖ := by
      have h := (cocoercive_implies_lipschitz (A μbar) α (hcoco μbar)).dist_le_mul a b
      simpa [dist_eq_norm, Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hα.le)] using h
    have htri : ‖A μ v - A μbar v‖ ≤
        (α⁻¹ * ‖v - x μbar s‖ + hD μ) + α⁻¹ * ‖x μbar s - v‖ := by
      have h1 : ‖A μ v - A μbar v‖ ≤
          ‖A μ v - A μ (x μbar s)‖ + ‖A μ (x μbar s) - A μbar (x μbar s)‖ +
            ‖A μbar (x μbar s) - A μbar v‖ := by
        rw [show A μ v - A μbar v = (A μ v - A μ (x μbar s)) +
            (A μ (x μbar s) - A μbar (x μbar s)) + (A μbar (x μbar s) - A μbar v)
            by abel]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      have h2 := hLμ v (x μbar s)
      have h3 : ‖A μ (x μbar s) - A μbar (x μbar s)‖ ≤ hD μ := hDbound μ s hs
      have h4 := hLbar (x μbar s) v
      linarith
    refine htri.trans ?_
    have hsym : ‖x μbar s - v‖ = ‖v - x μbar s‖ := norm_sub_rev _ _
    have hpos : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
    rw [hsym]
    nlinarith [hv, norm_nonneg (v - x μbar s), hDbound μ s hs, norm_nonneg (A μ (x μbar s) - A μbar (x μbar s))]
  -- Theorem 7.1's estimate with that discrepancy bound
  have hest : ∀ᶠ μ in nhds μbar, pathSupNorm T (fun t => x μ t - x μbar t) ≤
      α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μbar‖ + T * ‖v₀ μ - v₀ μbar‖ +
          T ^ 2 * (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ)) := by
    filter_upwards [hV] with μ hμ
    exact thm_8_general V A x dx ddx u₀ v₀ α γ T hα hT (fun μ _ => hcoco μ)
      (fun μ _ => hsol μ) hγT μ hμ μbar hμbar
      (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ) (hdisc μ hμ)
  -- the right-hand side tends to 0
  have hRHS : Tendsto (fun μ : M =>
      α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μbar‖ + T * ‖v₀ μ - v₀ μbar‖ +
          T ^ 2 * (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ)))
      (nhds μbar) (nhds 0) := by
    have h1 : Tendsto (fun μ : M => ‖u₀ μ - u₀ μbar‖) (nhds μbar) (nhds 0) := by
      simpa using (hu₀.sub (tendsto_const_nhds : Tendsto (fun _ : M => u₀ μbar)
        (nhds μbar) (nhds (u₀ μbar)))).norm
    have h2 : Tendsto (fun μ : M => ‖v₀ μ - v₀ μbar‖) (nhds μbar) (nhds 0) := by
      simpa using (hv₀.sub (tendsto_const_nhds : Tendsto (fun _ : M => v₀ μbar)
        (nhds μbar) (nhds (v₀ μbar)))).norm
    have h3 : Tendsto (fun μ : M => T ^ 2 * (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ))
        (nhds μbar) (nhds 0) := by
      have h4 : Tendsto (fun μ : M => 2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ)
          (nhds μbar) (nhds 0) := by
        simpa using (h1.const_mul (2 * α⁻¹)).add hD_lim
      simpa using h4.const_mul (T ^ 2)
    have hsum : Tendsto (fun μ : M =>
        ‖u₀ μ - u₀ μbar‖ + T * ‖v₀ μ - v₀ μbar‖ +
          T ^ 2 * (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ)) (nhds μbar) (nhds 0) := by
      simpa using (h1.add (h2.const_mul T)).add h3
    simpa using hsum.const_mul (α / (α - α * γ * T - T ^ 2))
  refine squeeze_zero' ?_ hest hRHS
  filter_upwards with μ
  unfold pathSupNorm
  exact Real.sSup_nonneg fun q hq => by
    obtain ⟨t, _, rfl⟩ := hq
    exact norm_nonneg _
```

## Proof explanation
The proof first derives a discrepancy bound for \(A_\mu-A_{\bar\mu}\) on a tube around the reference trajectory. This is recorded as `hdisc`:

\[
\|A_\mu v-A_{\bar\mu}v\|
\le 2\alpha^{-1}\|u_0(\mu)-u_0(\bar\mu)\|+h_D(\mu)
\]

whenever \(\mu\in V\), \(s\in[0,T]\), and
\[
\|v-x_{\bar\mu}(s)\|\le \|u_0(\mu)-u_0(\bar\mu)\|.
\]

To prove this, the proof introduces \(\mu\), the hypothesis \(\mu\in V\), \(s\), \(s\in[0,T]\), \(v\), and the closeness hypothesis. It then proves two Lipschitz estimates. For \(A_\mu\), it applies `cocoercive_implies_lipschitz` to the cocoercivity hypothesis `hcoco μ`. That lemma says that if \(A\) is \(\beta\)-cocoercive on all of \(H\), then \(A\) is Lipschitz with constant \(\operatorname{toNNReal}(1/\beta)\). Here \(\beta=\alpha>0\), so \(\operatorname{toNNReal}(1/\alpha)=1/\alpha=\alpha^{-1}\). Using `dist_le_mul`, the proof obtains
\[
\|A_\mu a-A_\mu b\|\le \alpha^{-1}\|a-b\|
\]
for all \(a,b\in H\). The same argument for \(\bar\mu\) gives
\[
\|A_{\bar\mu}a-A_{\bar\mu}b\|\le \alpha^{-1}\|a-b\|.
\]
The `simpa` rewrites distance as norm, converts the nonnegative real constant \(\operatorname{toNNReal}(1/\alpha)\) into \(\alpha^{-1}\) using \(\alpha>0\), and simplifies the maximum with \(0\).

Next the proof inserts the telescoping decomposition
\[
A_\mu v-A_{\bar\mu}v
=
\bigl(A_\mu v-A_\mu(x_{\bar\mu}(s))\bigr)
+\bigl(A_\mu(x_{\bar\mu}(s))-A_{\bar\mu}(x_{\bar\mu}(s))\bigr)
+\bigl(A_{\bar\mu}(x_{\bar\mu}(s))-A_{\bar\mu}v\bigr).
\]
The identity is proved by `abel`. Applying the triangle inequality twice, using `norm_add_le` and `add_le_add`, gives
\[
\|A_\mu v-A_{\bar\mu}v\|
\le
\|A_\mu v-A_\mu(x_{\bar\mu}(s))\|
+\|A_\mu(x_{\bar\mu}(s))-A_{\bar\mu}(x_{\bar\mu}(s))\|
+\|A_{\bar\mu}(x_{\bar\mu}(s))-A_{\bar\mu}v\|.
\]
The first term is bounded by \(\alpha^{-1}\|v-x_{\bar\mu}(s)\|\) from the Lipschitz estimate for \(A_\mu\). The middle term is bounded by \(h_D(\mu)\) by the hypothesis `hDbound`. The third term is bounded by \(\alpha^{-1}\|x_{\bar\mu}(s)-v\|\) from the Lipschitz estimate for \(A_{\bar\mu}\). The tactic `linarith` combines these three inequalities with the triangle inequality to obtain
\[
\|A_\mu v-A_{\bar\mu}v\|
\le
\alpha^{-1}\|v-x_{\bar\mu}(s)\|+h_D(\mu)
+\alpha^{-1}\|x_{\bar\mu}(s)-v\|.
\]
Using `norm_sub_rev`, the proof replaces \(\|x_{\bar\mu}(s)-v\|\) by \(\|v-x_{\bar\mu}(s)\|\). Since \(\alpha^{-1}\ge0\) and
\[
\|v-x_{\bar\mu}(s)\|\le \|u_0(\mu)-u_0(\bar\mu)\|,
\]
the tactic `nlinarith` finishes the bound
\[
\|A_\mu v-A_{\bar\mu}v\|
\le 2\alpha^{-1}\|u_0(\mu)-u_0(\bar\mu)\|+h_D(\mu).
\]

The proof then applies the cited theorem `thm_8_general`. Specialized to the present setting with \(\mu'=\bar\mu\), that theorem says: if two parameters \(\mu,\mu'\in V\) satisfy the cocoercivity and solution hypotheses, if the small-time condition holds, and if there is a constant \(D\) such that for all \(s\in[0,T]\) and all \(v\in H\),
\[
\|v-x_{\mu'}(s)\|\le \|u_0(\mu)-u_0(\mu')\|
\implies
\|A_\mu v-A_{\mu'}v\|\le D,
\]
then
\[
\operatorname{pathSupNorm}_T(x_\mu-x_{\mu'})
\le
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\Bigl(
\|u_0(\mu)-u_0(\mu')\|
+T\|v_0(\mu)-v_0(\mu')\|
+T^2 D
\Bigr).
\]
In the proof, \(D\) is chosen as
\[
D=2\alpha^{-1}\|u_0(\mu)-u_0(\bar\mu)\|+h_D(\mu).
\]
The required discrepancy condition is exactly `hdisc`. Since \(V\) is a neighborhood of \(\bar\mu\), the proof uses `filter_upwards [hV]` to say that eventually \(\mu\in V\), and for such \(\mu\) it applies `thm_8_general`. This produces the eventual estimate `hext`:
\[
\operatorname{pathSupNorm}_T(x_\mu-x_{\bar\mu})
\le
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\Bigl(
\|u_0(\mu)-u_0(\bar\mu)\|
+T\|v_0(\mu)-v_0(\bar\mu)\|
+T^2\bigl(2\alpha^{-1}\|u_0(\mu)-u_0(\bar\mu)\|+h_D(\mu)\bigr)
\Bigr).
\]

The next step proves that the right-hand side tends to \(0\). The proof first uses `hu₀` to get
\[
u_0(\mu)\to u_0(\bar\mu).
\]
Subtracting the constant function \(\mu\mapsto u_0(\bar\mu)\) gives
\[
u_0(\mu)-u_0(\bar\mu)\to0.
\]
Since the norm is continuous, taking norms gives
\[
\|u_0(\mu)-u_0(\bar\mu)\|\to0.
\]
This is `h1`. Similarly, `hv₀` gives
\[
\|v_0(\mu)-v_0(\bar\mu)\|\to0,
\]
which is `h2`. Multiplying `h1` by the constant \(2\alpha^{-1}\) and adding \(h_D(\mu)\to0\) gives
\[
2\alpha^{-1}\|u_0(\mu)-u_0(\bar\mu)\|+h_D(\mu)\to0.
\]
This is `h4`. Multiplying by \(T^2\) gives `h3`:
\[
T^2\bigl(2\alpha^{-1}\|u_0(\mu)-u_0(\bar\mu)\|+h_D(\mu)\bigr)\to0.
\]
Combining `h1`, \(T\) times `h2`, and `h3` gives `hsum`:
\[
\|u_0(\mu)-u_0(\bar\mu)\|
+T\|v_0(\mu)-v_0(\bar\mu)\|
+T^2\bigl(2\alpha^{-1}\|u_0(\mu)-u_0(\bar\mu)\|+h_D(\mu)\bigr)
\to0.
\]
Finally, multiplying by the constant
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\]
gives `hRHS`, the statement that the entire upper bound in `hext` tends to \(0\). The tactics `.sub`, `.norm`, `.const_mul`, `.add`, and `simpa` are used to build these limit statements from the assumed limits and the continuity of scalar multiplication, addition, subtraction, and the norm.

It remains to squeeze the nonnegative quantity \(\operatorname{pathSupNorm}_T(x_\mu-x_{\bar\mu})\) between \(0\) and the upper bound. The proof supplies the lower bound by `filter_upwards` and then unfolding `pathSupNorm`:
\[
\operatorname{pathSupNorm}_T(x_\mu-x_{\bar\mu})
=
\sup\{q\in\mathbb R:\exists t\in[0,T],\,
q=\|x_\mu(t)-x_{\bar\mu}(t)\|\}.
\]
Every element \(q\) of this set is a norm, hence \(q\ge0\) by `norm_nonneg`. Therefore `Real.sSup_nonneg` gives
\[
0\le \operatorname{pathSupNorm}_T(x_\mu-x_{\bar\mu})
\]
for every \(\mu\), and in particular eventually as \(\mu\to\bar\mu\).

Finally, the proof applies `squeeze_zero'` with the lower bound \(0\), the eventual upper bound `hext`, and the limit `hRHS`. Since the upper bound tends to \(0\) and the quantity of interest is eventually nonnegative and bounded above by it, `squeeze_zero'` yields
\[
\operatorname{pathSupNorm}_T(x_\mu-x_{\bar\mu})\to0
\quad\text{as }\mu\to\bar\mu,
\]
which is exactly the conclusion of `thm_9`.

