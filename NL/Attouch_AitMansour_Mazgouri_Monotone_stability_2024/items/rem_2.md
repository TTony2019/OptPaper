## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/rem_2.lean`

## Lean statement
```lean
theorem rem_2 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α : M → ℝ) (μbar : M) (r T : ℝ)
    (hr : 0 < r) (hT : 0 < T)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hu₀ : Tendsto u₀ (nhds μbar) (nhds (u₀ μbar)))
    (hv₀ : Tendsto v₀ (nhds μbar) (nhds (v₀ μbar)))
    (hball : ∀ μ ∈ V, ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → ‖x μ t‖ ≤ r)
    (hV : V ∈ nhds μbar) (hμbar : μbar ∈ V)
    (hconv_A : Tendsto (fun μ : M => def_6 r hr (A μ) (A μbar)) (nhds μbar) (nhds 0))
    (hα_bound : ∀ᶠ μ in nhds μbar, α μbar ≤ α μ) :
    Tendsto (fun μ : M => pathSupNorm T (fun t => x μ t - x μbar t)) (nhds μbar) (nhds 0)
```

## Statement explanation
The theorem `rem_2` is a continuous-dependence, or stability, statement for a family of damped second-order problems indexed by a parameter \(\mu\) in a normed additive group \(M\). The state space is a real inner-product space \(H\), assumed complete, so \(H\) is a real Hilbert space. The set \(V\subseteq M\) is the admissible parameter set, and \(\bar\mu\in M\) is the reference parameter near which the limiting behavior is studied.

For each parameter \(\mu\), the data are an operator \(A_\mu=A(\mu):H\to H\), a real damping coefficient \(\gamma\), an initial position \(u_0(\mu)\in H\), an initial velocity \(v_0(\mu)\in H\), and three \(H\)-valued time functions \(x(\mu),dx(\mu),ddx(\mu):\mathbb R\to H\). The function \(x(\mu)\) is the trajectory whose stability is being measured; \(dx(\mu)\) and \(ddx(\mu)\) are the first and second derivative-type objects appearing in the solution predicate. The function \(\alpha:M\to\mathbb R\) supplies coercivity constants. The constants \(r,T>0\) are respectively a ball radius and a time horizon.

The hypothesis `hC₁` says that for every \(\mu\in V\), the number \(\alpha(\mu)\) is positive and the operator \(A_\mu\) satisfies the cocoercivity/monotonicity-type inequality

\[
\alpha(\mu)\|A_\mu u-A_\mu v\|^2
\le
\langle A_\mu u-A_\mu v,u-v\rangle_{\mathbb R}
\]

for all \(u,v\in H\). The hypothesis `hsol` says that for every admissible \(\mu\in V\), the triple \((x(\mu),dx(\mu),ddx(\mu))\) satisfies the predicate `ext_def_2` with operator \(A_\mu\), damping \(\gamma\), and initial data \(u_0(\mu),v_0(\mu)\). The definition of `ext_def_2` is not supplied in the given context, but in the proof it is used to obtain continuity of the first component \(x(\mu)\) on \( [0,T] \).

The hypotheses `hu₀` and `hv₀` state that the initial position and velocity data converge at \(\bar\mu\):

\[
u_0(\mu)\to u_0(\bar\mu),\qquad
v_0(\mu)\to v_0(\bar\mu)
\]

as \(\mu\to\bar\mu\). The hypothesis `hball` assumes that for every \(\mu\in V\), for almost every \(t\in [0,T]\) with respect to Lebesgue measure,

\[
\|x(\mu)(t)\|\le r.
\]

Thus the trajectories are uniformly bounded on the time interval, almost everywhere, by the radius \(r\). The hypothesis `hV` says that \(V\) is a neighborhood of \(\bar\mu\), and `hμbar` says that \(\bar\mu\) itself belongs to \(V\). The hypothesis `hconv_A` says that the discrepancy

\[
\operatorname{def}_6(r,h_r,A_\mu,A_{\bar\mu})
\]

tends to \(0\) as \(\mu\to\bar\mu\). Here `def_6` is defined as the supremum discrepancy on the ball of radius \(r\), so this is a convergence assumption on the operators \(A_\mu\) toward \(A_{\bar\mu}\). Finally, `hα_bound` says that eventually near \(\bar\mu\),

\[
\alpha(\bar\mu)\le \alpha(\mu).
\]

The conclusion is that

\[
\operatorname{pathSupNorm}_T\bigl(t\mapsto x(\mu)(t)-x(\bar\mu)(t)\bigr)\to 0
\]

as \(\mu\to\bar\mu\). Since

\[
\operatorname{pathSupNorm}_T f
=
\sup\{\|f(t)\|:t\in [0,T]\},
\]

this says that the trajectories \(x(\mu)\) converge to the reference trajectory \(x(\bar\mu)\) uniformly on the time interval \( [0,T] \), measured by the path supremum norm.

## Lean proof
```lean
by
  let m₀ : ℝ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μbar) ^ 2)
  have hm₀_pos : 0 < m₀ := by
    have hαbar : 0 < α μbar := (hC₁ μbar hμbar).1
    dsimp [m₀]
    apply Real.sqrt_pos.mpr
    have h2 : 0 < 2 / (α μbar) ^ 2 := by positivity
    nlinarith [sq_nonneg γ]
  -- the right-hand side of (3) tends to 0
  have hsqrt : Tendsto (fun μ : M =>
      Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2)) (nhds μbar) (nhds 0) := by
    have ha : Tendsto (fun μ : M => ‖u₀ μ - u₀ μbar‖) (nhds μbar) (nhds 0) := by
      simpa using (hu₀.sub (tendsto_const_nhds : Tendsto (fun _ : M => u₀ μbar)
        (nhds μbar) (nhds (u₀ μbar)))).norm
    have hb : Tendsto (fun μ : M => ‖v₀ μ - v₀ μbar‖) (nhds μbar) (nhds 0) := by
      simpa using (hv₀.sub (tendsto_const_nhds : Tendsto (fun _ : M => v₀ μbar)
        (nhds μbar) (nhds (v₀ μbar)))).norm
    simpa using ((ha.pow 2).add (hb.pow 2)).sqrt
  have hRHS : Tendsto (fun μ : M =>
      Real.exp (m₀ * T) * Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2) +
        m₀⁻¹ * (Real.exp (m₀ * T) - 1) * def_6 r hr (A μ) (A μbar))
      (nhds μbar) (nhds 0) := by
    have h1 : Tendsto (fun μ : M =>
        Real.exp (m₀ * T) * Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2))
        (nhds μbar) (nhds (Real.exp (m₀ * T) * 0)) := hsqrt.const_mul _
    have h2 : Tendsto (fun μ : M =>
        m₀⁻¹ * (Real.exp (m₀ * T) - 1) * def_6 r hr (A μ) (A μbar))
        (nhds μbar) (nhds (m₀⁻¹ * (Real.exp (m₀ * T) - 1) * 0)) :=
      hconv_A.const_mul _
    simpa using h1.add h2
  -- the uniform estimate of Theorem 5.1
  have hbound : ∀ᶠ μ in nhds μbar, pathSupNorm T (fun t => x μ t - x μbar t) ≤
      Real.exp (m₀ * T) * Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2) +
        m₀⁻¹ * (Real.exp (m₀ * T) - 1) * def_6 r hr (A μ) (A μbar) := by
    filter_upwards [hV, hα_bound] with μ hμV hαμ
    have hpt := thm_2 V A γ x dx ddx u₀ v₀ α r T hC₁ hsol hr hT hball μ hμV μbar hμbar
    have hαμ' : 0 < α μ := (hC₁ μ hμV).1
    have hαbar' : 0 < α μbar := (hC₁ μbar hμbar).1
    have hm : max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ) ^ 2))
        (Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μbar) ^ 2)) = m₀ := by
      have hle : Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ) ^ 2) ≤
          Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μbar) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hsq : (α μbar) ^ 2 ≤ (α μ) ^ 2 := by nlinarith
        have hdiv : 2 / (α μ) ^ 2 ≤ 2 / (α μbar) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
        linarith
      rw [max_eq_right hle]
    have hcont : ContinuousOn (fun t => ‖x μ t - x μbar t‖) (Set.Icc (0 : ℝ) T) := by
      have hμac := ((hsol μ hμV).2).1 T hT
      have hbarac := ((hsol μbar hμbar).2).1 T hT
      exact (((hμac.1.continuousOn).mono Set.Icc_subset_uIcc).sub
        ((hbarac.1.continuousOn).mono Set.Icc_subset_uIcc)).norm
    have hall : ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖x μ t - x μbar t‖ ≤ Real.exp (m₀ * T) *
            Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2) +
          m₀⁻¹ * (Real.exp (m₀ * T) - 1) * def_6 r hr (A μ) (A μbar) :=
      le_of_ae_le_const_of_continuousOn hT hcont (hpt.mono fun s hs hsT => by
        simpa only [hm] using hs hsT)
    exact pathSupNorm_le_of_forall hT.le hall
  refine squeeze_zero' ?_ hbound hRHS
  filter_upwards with μ
  unfold pathSupNorm
  exact Real.sSup_nonneg fun q hq => by
    obtain ⟨t, _, rfl⟩ := hq
    exact norm_nonneg _
```

## Proof explanation
The proof begins by introducing the auxiliary constant

\[
m_0=\sqrt{1+2\gamma^2+\frac{2}{\alpha(\bar\mu)^2}}.
\]

Since \(\bar\mu\in V\), the hypothesis `hC₁` gives \(\alpha(\bar\mu)>0\). The term \(2/\alpha(\bar\mu)^2\) is therefore positive, and \(1+2\gamma^2\) is nonnegative because \(\gamma^2\ge0\). Hence the radicand is positive, and `Real.sqrt_pos.mpr` proves \(m_0>0\). The Lean command `dsimp [m₀]` unfolds the local definition of \(m_0\), `positivity` proves the positivity of \(2/\alpha(\bar\mu)^2\), and `nlinarith [sq_nonneg γ]` combines the nonnegativity of \(\gamma^2\) with the positivity of the other term.

Next the proof shows that the initial-data term tends to zero. It first proves

\[
\|u_0(\mu)-u_0(\bar\mu)\|\to0.
\]

Indeed, `hu₀` says \(u_0(\mu)\to u_0(\bar\mu)\). Subtracting the constant map \(\mu\mapsto u_0(\bar\mu)\), whose limit is itself, gives \(u_0(\mu)-u_0(\bar\mu)\to0\). Since the norm map is continuous, the norm of this difference also tends to \(0\). The Lean expression `(hu₀.sub tendsto_const_nhds).norm` packages exactly that argument. The same reasoning with `hv₀` gives

\[
\|v_0(\mu)-v_0(\bar\mu)\|\to0.
\]

Then the proof applies the continuous operations \(z\mapsto z^2\), addition, and the square root at \(0\). Thus

\[
\sqrt{\|u_0(\mu)-u_0(\bar\mu)\|^2+\|v_0(\mu)-v_0(\bar\mu)\|^2}\to0.
\]

This is the auxiliary fact `hsqrt`.

Using `hsqrt` and the hypothesis `hconv_A`, the proof then shows that the whole right-hand side

\[
R(\mu)
=
e^{m_0T}
\sqrt{\|u_0(\mu)-u_0(\bar\mu)\|^2+\|v_0(\mu)-v_0(\bar\mu)\|^2}
+
m_0^{-1}(e^{m_0T}-1)\operatorname{def}_6(r,h_r,A_\mu,A_{\bar\mu})
\]

tends to \(0\). The first summand is a constant multiple of a quantity tending to \(0\), and the second summand is a constant multiple of \(\operatorname{def}_6(r,h_r,A_\mu,A_{\bar\mu})\), which tends to \(0\) by `hconv_A`. The Lean commands `hsqrt.const_mul`, `hconv_A.const_mul`, and `h1.add h2` implement these closure properties of limits. This is the auxiliary fact `hRHS`.

The central estimate is `hbound`, which asserts that eventually near \(\bar\mu\),

\[
\operatorname{pathSupNorm}_T\bigl(t\mapsto x(\mu)(t)-x(\bar\mu)(t)\bigr)
\le R(\mu).
\]

The proof uses `filter_upwards [hV, hα_bound]` to work with a parameter \(\mu\) for which \(\mu\in V\) and \(\alpha(\bar\mu)\le\alpha(\mu)\) hold. For such a \(\mu\), it invokes the previously established result `thm_2`. The supplied statement of `thm_2` is truncated at `let m_μ`, so its full conclusion is not visible here. What is visible and used in this proof is that `thm_2` provides an almost-everywhere pointwise estimate for \(\|x(\mu)(t)-x(\bar\mu)(t)\|\) whose exponential coefficient is the maximum of the two quantities

\[
\sqrt{1+2\gamma^2+\frac{2}{\alpha(\mu)^2}}
\quad\text{and}\quad
\sqrt{1+2\gamma^2+\frac{2}{\alpha(\bar\mu)^2}},
\]

together with the initial-data square-root term and the discrepancy term \(\operatorname{def}_6(r,h_r,A_\mu,A_{\bar\mu})\).

The proof then simplifies that maximum to \(m_0\). From \(\alpha(\bar\mu)\le\alpha(\mu)\) and the positivity of both quantities, it obtains

\[
(\alpha(\bar\mu))^2\le(\alpha(\mu))^2.
\]

Hence

\[
\frac{2}{(\alpha(\mu))^2}\le\frac{2}{(\alpha(\bar\mu))^2},
\]

so the radicand depending on \(\mu\) is at most the radicand depending on \(\bar\mu\). Since the square root is monotone on nonnegative reals, the corresponding square roots are ordered, and therefore the maximum equals the one involving \(\bar\mu\), namely \(m_0\). This is the auxiliary equality `hm`.

The proof also needs continuity of the difference norm on \( [0,T] \). From `hsol μ hμV` and `hsol μbar hμbar`, the solution predicate supplies absolute continuity, hence continuity, of \(x(\mu)\) and \(x(\bar\mu)\) on \( [0,T] \). The Lean code extracts this as `hμac` and `hbarac`, restricts the continuity to the interval \( [0,T] \) using `Set.Icc_subset_uIcc`, subtracts the two continuous functions, and takes the norm. Therefore

\[
t\mapsto \|x(\mu)(t)-x(\bar\mu)(t)\|
\]

is continuous on \( [0,T] \).

Now the proof upgrades the almost-everywhere bound to a pointwise bound. It uses `le_of_ae_le_const_of_continuousOn`: if \(T>0\), if \(f\) is continuous on \( [0,T] \), and if for almost every \(t\), \(t\in [0,T]\) implies \(f(t)\le M\), then for every \(t\in [0,T]\), \(f(t)\le M\). Here \(f(t)=\|x(\mu)(t)-x(\bar\mu)(t)\|\) and \(M=R(\mu)\). The almost-everywhere hypothesis comes from `hpt`, the estimate obtained from `thm_2`, after rewriting the maximum coefficient to \(m_0\) using `hm`. Thus the proof obtains

\[
\forall t\in [0,T],\qquad
\|x(\mu)(t)-x(\bar\mu)(t)\|\le R(\mu).
\]

This is the auxiliary fact `hall`.

Next, the proof converts the pointwise bound into a path-supremum bound. It invokes `pathSupNorm_le_of_forall`: if \(T\ge0\) and \(\|f(t)\|\le C\) for all \(t\in [0,T]\), then

\[
\operatorname{pathSupNorm}_T f\le C.
\]

Here \(T\ge0\) follows from `hT.le`, \(f(t)=x(\mu)(t)-x(\bar\mu)(t)\), and \(C=R(\mu)\). Therefore

\[
\operatorname{pathSupNorm}_T\bigl(t\mapsto x(\mu)(t)-x(\bar\mu)(t)\bigr)
\le R(\mu)
\]

eventually near \(\bar\mu\). This is `hbound`.

Finally, the proof applies the squeeze theorem for filters. The command `refine squeeze_zero' ?_ hbound hRHS` requires three ingredients: eventual nonnegativity of the quantity being bounded, the eventual upper bound `hbound`, and the convergence to zero of the upper bound `hRHS`. The remaining subgoal is that

\[
0\le
\operatorname{pathSupNorm}_T\bigl(t\mapsto x(\mu)(t)-x(\bar\mu)(t)\bigr).
\]

The proof proves this for every \(\mu\) using `unfold pathSupNorm`, which expands the definition as a supremum of the set of real numbers

\[
\{q:\exists t\in [0,T],\ q=\|x(\mu)(t)-x(\bar\mu)(t)\|\}.
\]

Every element of this set is the norm of some vector, hence is nonnegative. Therefore `Real.sSup_nonneg` gives that the supremum itself is nonnegative. Combining this nonnegativity, the eventual upper bound by \(R(\mu)\), and the fact \(R(\mu)\to0\), the squeeze theorem yields

\[
\operatorname{pathSupNorm}_T\bigl(t\mapsto x(\mu)(t)-x(\bar\mu)(t)\bigr)\to0
\]

as \(\mu\to\bar\mu\), which is the desired conclusion.

