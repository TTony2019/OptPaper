## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_10.lean`

## Lean statement
```lean
theorem approxSolutions_painleve_kuratowski {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M]
    (V : Set M) (A : M → H → H) (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun z : Set.univ => A μ z))
    (hsol : ∀ μ ∈ V, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hγT : γ * T + T ^ 2 / α < 1) :
    (∀ μ ∈ V, ∀ (εseq : ℕ → ℝ) (yseq : ℕ → ℝ → H), (∀ n, 0 < εseq n) →
        Tendsto εseq atTop (nhds 0) →
        (∀ n, yseq n ∈ approxSolutions A γ u₀ v₀ T (εseq n) μ) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun n => yseq n t) atTop (nhds (x μ t))) ∧
          Tendsto (fun n => pathSupNorm T (fun t => yseq n t - x μ t)) atTop (nhds 0)) ∧
      (∀ μ ∈ V, ∀ η > 0, ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε,
        ∃ y ∈ approxSolutions A γ u₀ v₀ T ε' μ,
          pathSupNorm T (fun t => y t - x μ t) < η)
```

## Statement explanation
The declaration `approxSolutions_painleve_kuratowski` is a convergence theorem for approximate solutions of a parameterized damped second-order equation. The space \(H\) is a real Hilbert space, and \(M\) is a normed additive commutative group whose elements are parameters. The set \(V\subseteq M\) is the admissible parameter set. For each parameter \(\mu\in M\), the operator \(A_\mu=A\mu\) maps \(H\) to \(H\), the curve \(x_\mu=x\mu:\mathbb R\to H\) is a candidate exact trajectory, \(dx_\mu\) and \(ddx_\mu\) are auxiliary trajectories, and \(u_{0,\mu},v_{0,\mu}\in H\) are initial data. The real parameters are \(\alpha,\gamma,T\), with \(\alpha>0\) and \(T>0\). The hypothesis \(hcoco\) states that for every \(\mu\in V\), \(A_\mu\) is \(\alpha\)-cocoercive on all of \(H\); the subtype notation `Set.univ` is only the Lean encoding of the whole space. The hypothesis \(hsol\) states that for every \(\mu\in V\), the tuple \((x_\mu,dx_\mu,ddx_\mu)\) satisfies the extended solution condition `ext_def_2` for the damped system with operator \(A_\mu\), damping \(\gamma\), and initial data \(u_{0,\mu},v_{0,\mu}\). The source does not expand `ext_def_2`, but the proof uses that it implies \(\gamma>0\), that \(x_\mu\) is continuous on \( [0,T] \), and that \(x_\mu\) is a fixed point of the centered integral map at nonnegative times. The smallness condition \(hγT\) is
\[
\gamma T+\frac{T^2}{\alpha}<1.
\]
Together with \(\alpha>0\), this makes the denominator
\[
D=\alpha-\alpha\gamma T-T^2
\]
positive. The set \(\operatorname{approxSolutions}(A,\gamma,u_0,v_0,T,\epsilon,\mu)\) is the set of approximate solutions at tolerance \(\epsilon\) for parameter \(\mu\). Its full definition is not shown, but the proof uses that membership entails continuity on \( [0,T] \) and a tolerance condition involving the centered integral map. The path-sup norm is
\[
\operatorname{pathSupNorm}_T(f)=\sup\{\|f(t)\|: t\in [0,T] \}.
\]

The conclusion is a conjunction of two statements. The first is sequential: for every \(\mu\in V\), every sequence \((\varepsilon_n)\) of positive reals with \(\varepsilon_n\to0\), and every sequence of curves \((y_n)\) such that
\[
y_n\in \operatorname{approxSolutions}(A,\gamma,u_0,v_0,T,\varepsilon_n,\mu)
\]
for every \(n\), one has pointwise convergence
\[
y_n(t)\to x_\mu(t)\qquad\text{for every }t\in [0,T],
\]
and uniform path-sup convergence
\[
\operatorname{pathSupNorm}_T(y_n-x_\mu)\to0.
\]
The second statement is epsilon-delta: for every \(\mu\in V\) and every \(\eta>0\), there exists \(\epsilon>0\) such that for every \(\epsilon'\in(0,\epsilon)\) there is a curve
\[
y\in \operatorname{approxSolutions}(A,\gamma,u_0,v_0,T,\epsilon',\mu)
\]
satisfying
\[
\operatorname{pathSupNorm}_T(y-x_\mu)<\eta.
\]
In words, as the approximation tolerance tends to zero, approximate solutions converge to the exact trajectory \(x_\mu\), both pointwise on \( [0,T] \) and uniformly in the path-sup norm, and arbitrarily small tolerances admit approximate solutions arbitrarily uniformly close to \(x_\mu\). This is the Painlevé-Kuratowski type convergence formulation for the solution sets.

## Lean proof
```lean
by
  have hxcont (μ : M) (hμ : μ ∈ V) : ContinuousOn (x μ) (Set.Icc (0 : ℝ) T) :=
    continuousOn_of_solution hT (hsol μ hμ).2
  have hbound (μ : M) (hμ : μ ∈ V) (ε : ℝ) {y : ℝ → H}
      (hy : y ∈ approxSolutions A γ u₀ v₀ T ε μ) :
      pathSupNorm T (fun t => y t - x μ t) ≤ (ε * α) / (α - α * γ * T - T ^ 2) :=
    approxSolutions_pathSupNorm_le V A x dx ddx u₀ v₀ α γ T ε hα (hsol μ hμ).1 hT hcoco hsol
      hγT hμ hy
  constructor
  · intro μ hμ εseq yseq _ hlim hyseq
    have hsup (n : ℕ) : pathSupNorm T (fun t => yseq n t - x μ t) ≤
        (εseq n * α) / (α - α * γ * T - T ^ 2) := hbound μ hμ _ (hyseq n)
    have hcont (n : ℕ) : ContinuousOn (fun t => yseq n t - x μ t) (Set.Icc (0 : ℝ) T) :=
      (hyseq n).1.sub (hxcont μ hμ)
    have hlim' : Tendsto (fun n => (εseq n * α) / (α - α * γ * T - T ^ 2))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun n => εseq n * α) atTop (nhds 0) := by
        simpa using hlim.mul_const α
      simpa using h1.div_const (α - α * γ * T - T ^ 2)
    refine ⟨?_, ?_⟩
    · intro t ht
      refine tendsto_iff_dist_tendsto_zero.mpr ?_
      have hb (n : ℕ) :
          dist (yseq n t) (x μ t) ≤ (εseq n * α) / (α - α * γ * T - T ^ 2) := by
        rw [dist_eq_norm]
        exact (norm_le_pathSupNorm_of_continuousOn (hcont n) ht).trans (hsup n)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
        (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall hb)
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
        (Eventually.of_forall fun n => pathSupNorm_nonneg_of_continuousOn hT.le (hcont n))
        (Eventually.of_forall hsup)
  · intro μ hμ η hη
    refine ⟨η, hη, ?_⟩
    intro ε' hε'
    refine ⟨x μ, ?_, ?_⟩
    · refine ⟨hxcont μ hμ, ?_⟩
      intro t ht
      have hfix := centeredIntegralMap_eq_of_solution (A μ) (x μ) (dx μ) (ddx μ)
        (u₀ μ) (v₀ μ) α γ (hcoco μ hμ) (hsol μ hμ) t ht.1
      rw [hfix, sub_self, norm_zero]
      exact hε'.1.le
    · have hzero : pathSupNorm T (fun t => x μ t - x μ t) ≤ η / 2 :=
        pathSupNorm_le_of_forall hT.le fun t _ => by rw [sub_self, norm_zero]; positivity
      linarith
```

## Proof explanation
The proof begins with two auxiliary facts. First, it proves that for every \(\mu\in V\), the exact curve \(x_\mu\) is continuous on \( [0,T] \). This is `hxcont`, defined by `continuousOn_of_solution hT (hsol μ hμ).2`. The term \(hsol μ hμ\) is the extended solution hypothesis; its second component is the solution condition `def_3`. The cited lemma `continuousOn_of_solution` says that if \(T>0\) and \((x,dx,ddx)\) satisfies `def_3 A γ u0 v0 x dx ddx`, then \(x\) is continuous on \([0,T]\). Applied to \(\mu\), it gives \(\operatorname{ContinuousOn}(x_\mu,[0,T])\).

Second, the proof establishes the quantitative error estimate `hbound`: for every \(\mu\in V\), every real \(\epsilon\), and every \(y\in\operatorname{approxSolutions}(A,\gamma,u_0,v_0,T,\epsilon,\mu)\),
\[
\operatorname{pathSupNorm}_T(y-x_\mu)\le \frac{\epsilon\alpha}{D}.
\]
This is exactly what `approxSolutions_pathSupNorm_le` provides. That theorem requires \(\alpha>0\), \(\gamma>0\), \(T>0\), the cocoercivity hypothesis, the solution hypothesis, and the smallness condition \(hγT\). The proof supplies \(\alpha>0\) from \(hα\), \(\gamma>0\) from the first component of \(hsol μ hμ\), \(T>0\) from \(hT\), and the remaining hypotheses directly. Its conclusion is the displayed uniform bound. This estimate is the main quantitative ingredient: it controls the whole path-sup error by the tolerance \(\epsilon\).

To prove the first conjunct of the conclusion, the proof splits the conjunction with `constructor` and works on the sequential statement. It introduces \(\mu\in V\), a sequence \(\varepsilon_n\), a sequence of curves \(y_n\), the positivity hypothesis on \(\varepsilon_n\) (which is discarded with `_` and not used), the limit hypothesis \(\varepsilon_n\to0\), and the hypothesis that
\[
y_n\in\operatorname{approxSolutions}(A,\gamma,u_0,v_0,T,\varepsilon_n,\mu)
\]
for every \(n\). Define
\[
U_n=\frac{\varepsilon_n\alpha}{D}.
\]
From `hbound`, the proof obtains `hsup`:
\[
\operatorname{pathSupNorm}_T(y_n-x_\mu)\le U_n
\]
for every \(n\).

Next, `hcont` proves that the difference \(y_n-x_\mu\) is continuous on \( [0,T] \). Indeed, membership of \(y_n\) in `approxSolutions` supplies continuity of \(y_n\) on \( [0,T] \) as its first component, and `hxcont μ hμ` supplies continuity of \(x_\mu\). The Lean operation `.sub` is the fact that the difference of two continuous functions is continuous.

The proof also shows `hlim'`, namely
\[
U_n\to0.
\]
Since \(\varepsilon_n\to0\), applying the theorem `Filter.Tendsto.mul_const` to \(hlim\) with constant \(\alpha\) gives \(\varepsilon_n\alpha\to0\). Then applying `Filter.Tendsto.div_const` with the constant \(D\) gives
\[
U_n=\frac{\varepsilon_n\alpha}{D}\to0.
\]
The `simpa` calls only simplify the function and arithmetic.

The proof then uses `refine ⟨?_, ?_⟩` to separate the pointwise convergence from the path-sup convergence. For pointwise convergence, fix \(t\in [0,T]\). The proof uses `tendsto_iff_dist_tendsto_zero.mpr`, so it is enough to show
\[
\operatorname{dist}(y_n(t),x_\mu(t))\to0.
\]
For each \(n\), `hb` proves
\[
\operatorname{dist}(y_n(t),x_\mu(t))
=\|y_n(t)-x_\mu(t)\|
\le \operatorname{pathSupNorm}_T(y_n-x_\mu)
\le U_n.
\]
The first equality is `dist_eq_norm`. The next inequality is `norm_le_pathSupNorm_of_continuousOn` applied to the continuous curve \(y_n-x_\mu\) and the point \(t\in [0,T]\). That lemma says that for a curve continuous on \( [0,T] \), its value at any point of \( [0,T] \) has norm at most the path-sup norm. The last inequality is `hsup n`.

Then the squeeze theorem `tendsto_of_tendsto_of_tendsto_of_le_of_le'` is applied. The lower comparison sequence is the constant \(0\), which tends to \(0\) by `tendsto_const_nhds`. The upper comparison sequence is \(U_n\), which tends to \(0\) by `hlim'`. The inequalities are
\[
0\le \operatorname{dist}(y_n(t),x_\mu(t))
\]
from `dist_nonneg`, and
\[
\operatorname{dist}(y_n(t),x_\mu(t))\le U_n
\]
from `hb`. Hence the distance tends to \(0\). By `tendsto_iff_dist_tendsto_zero`, this is exactly \(y_n(t)\to x_\mu(t)\).

For the path-sup convergence, let
\[
S_n=\operatorname{pathSupNorm}_T(y_n-x_\mu).
\]
The proof again uses the squeeze theorem. The lower bound \(0\le S_n\) is supplied by `pathSupNorm_nonneg_of_continuousOn`: since \(T\ge0\) from `hT.le` and \(y_n-x_\mu\) is continuous on \( [0,T] \), the path-sup norm is nonnegative. The upper bound \(S_n\le U_n\) is `hsup n`. Since \(U_n\to0\), the squeeze theorem gives \(S_n\to0\), i.e.
\[
\operatorname{pathSupNorm}_T(y_n-x_\mu)\to0.
\]
This completes the first conjunct.

The second conjunct is proved by `intro μ hμ η hη`, then `refine ⟨η, hη, ?_⟩`, so the proof chooses \(\epsilon=\eta\). It must show that for every \(\epsilon'\in(0,\eta)\) there exists an approximate solution at level \(\epsilon'\) with path-sup error less than \(\eta\). Fix \(\epsilon'\) with \(0<\epsilon'<\eta\). The proof chooses \(y=x_\mu\) with `refine ⟨x μ, ?_, ?_⟩`.

First it shows that
\[
x_\mu\in\operatorname{approxSolutions}(A,\gamma,u_0,v_0,T,\epsilon',\mu).
\]
The membership is established by `refine ⟨hxcont μ hμ, ?_⟩`. The first component is the already proved continuity of \(x_\mu\) on \( [0,T] \). For the remaining tolerance condition, fix \(t\in [0,T]\). Since \(t\ge0\), the cited theorem `centeredIntegralMap_eq_of_solution` applies to \(A_\mu,x_\mu,dx_\mu,ddx_\mu,u_{0,\mu},v_{0,\mu},\alpha,\gamma\), using \(hcoco μ hμ\) and \(hsol μ hμ\). It gives
\[
\Gamma_{A_\mu,u_{0,\mu},v_{0,\mu}}(x_\mu)(t)=x_\mu(t),
\]
where \(\Gamma\) is the centered integral map, the Picard operator described in the source by
\[
\Gamma_{A,u_0,v_0}(x)(t)
=u_0+t v_0+\int_0^t (s-t)\bigl(\gamma\dot x(s)+A x(s)\bigr)\,ds.
\]
The equality says that the exact solution \(x_\mu\) is a fixed point of the Picard operator at all nonnegative times. Rewriting with `rw [hfix, sub_self, norm_zero]` changes the tolerance goal into \(0\le\epsilon'\), which is exactly the positivity part of \(hε'\). Hence \(x_\mu\) satisfies the approximate-solution condition at level \(\epsilon'\).

Second, the proof shows
\[
\operatorname{pathSupNorm}_T(x_\mu-x_\mu)<\eta.
\]
Using `pathSupNorm_le_of_forall` with \(T\ge0\), it is enough to observe that for every \(t\in [0,T]\),
\[
\|x_\mu(t)-x_\mu(t)\|=0\le\frac{\eta}{2}.
\]
The equality is `sub_self` and `norm_zero`; the inequality is `positivity` from \(\eta>0\). Thus `hzero` gives
\[
\operatorname{pathSupNorm}_T(x_\mu-x_\mu)\le\frac{\eta}{2}.
\]
Since \(\eta>0\), we have \(\eta/2<\eta\), and `linarith` concludes the strict inequality. Therefore, with \(\epsilon=\eta\), every \(\epsilon'\in(0,\eta)\) has an approximate solution \(x_\mu\) whose path-sup error from \(x_\mu\) is less than \(\eta\), completing the second conjunct and the theorem.

