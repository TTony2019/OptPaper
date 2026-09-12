## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/ext_thm_3.lean`

## Lean statement
```lean
theorem weak_weighted_cesaro_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (v : ℝ → H) (vInfinity : H) (w : ℝ → ℝ) (t0 : ℝ)
    (hv : Tendsto (fun t => toWeakSpace ℝ H (v t)) atTop (nhds (toWeakSpace ℝ H vInfinity)))
    (hw_nonneg : ∀ t ≥ t0, 0 ≤ w t)
    (hw_integrable : ∀ a b, IntervalIntegrable w volume a b)
    (hwv_integrable : ∀ a b, IntervalIntegrable (fun s => w s • v s) volume a b)
    (hW : Tendsto (fun t => ∫ s in t0..t, w s) atTop atTop) :
    Tendsto (fun t => toWeakSpace ℝ H ((∫ s in t0..t, w s)⁻¹ • ∫ s in t0..t, w s • v s)) atTop
      (nhds (toWeakSpace ℝ H vInfinity))
```

## Statement explanation
The theorem `weak_weighted_cesaro_convergence` is a weak-convergence weighted Cesàro averaging statement in a complete real inner product space \(H\). The data are a function \(v:\mathbb R\to H\), a limit vector \(v_\infty\in H\), a real weight function \(w:\mathbb R\to\mathbb R\), and a starting time \(t_0\in\mathbb R\). Write

\[
W(t)=\int_{t_0}^{t} w(s)\,ds,
\qquad
A(t)=W(t)^{-1}\cdot \int_{t_0}^{t} w(s)\cdot v(s)\,ds,
\]

where the second integral is the \(H\)-valued interval integral of the vector-valued function \(s\mapsto w(s)\cdot v(s)\).

The hypotheses are:

- \(v(t)\) converges to \(v_\infty\) in the weak topology as \(t\to+\infty\), expressed by
  \[
  \operatorname{toWeakSpace}_{\mathbb R,H}(v(t))\to
  \operatorname{toWeakSpace}_{\mathbb R,H}(v_\infty).
  \]
- The weight is eventually nonnegative: \(w(t)\ge 0\) for every \(t\ge t_0\).
- For every real \(a,b\), the scalar function \(w\) is interval integrable on the interval with endpoints \(a\) and \(b\) with respect to Lebesgue measure.
- For every real \(a,b\), the vector-valued function \(s\mapsto w(s)\cdot v(s)\) is interval integrable on the interval with endpoints \(a\) and \(b\).
- The cumulative weight diverges:
  \[
  W(t)=\int_{t_0}^{t} w(s)\,ds \to +\infty
  \]
  as \(t\to+\infty\).

The conclusion is that the normalized weighted average \(A(t)\) converges weakly to the same limit:
\[
A(t)\rightharpoonup v_\infty
\quad\text{in the weak topology as }t\to+\infty.
\]

In ordinary mathematical language: if a curve \(v(t)\) converges weakly to \(v_\infty\), and \(w\) is an eventually nonnegative integrable weight whose cumulative integral tends to infinity, then the weighted Cesàro mean
\[
\frac{\int_{t_0}^{t} w(s)v(s)\,ds}{\int_{t_0}^{t} w(s)\,ds}
\]
also converges weakly to \(v_\infty\).

## Lean proof
```lean
by
  apply (weakConvergence_iff_forall_tendsto_inner_right _ vInfinity).2
  intro u
  have hv_coord := (weakConvergence_iff_forall_tendsto_inner_right v vInfinity).1 hv u
  have hcentered : ∀ a b, IntervalIntegrable (fun s => w s • (v s - vInfinity)) volume a b := by
    intro a b
    have hconst : IntervalIntegrable (fun s => w s • vInfinity) volume a b :=
      ⟨(hw_integrable a b).1.smul_const vInfinity, (hw_integrable a b).2.smul_const vInfinity⟩
    convert (hwv_integrable a b).sub hconst using 1
    · ext s
      module
  have hscalar : ∀ a b,
      IntervalIntegrable (fun s => w s * inner ℝ (v s - vInfinity) u) volume a b := by
    intro a b
    have h := hcentered a b
    constructor
    · simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left,
        real_inner_smul_right] using
        (innerSL ℝ u).integrableOn_comp h.1
    · simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left,
        real_inner_smul_right] using
        (innerSL ℝ u).integrableOn_comp h.2
  have hcoord : Tendsto (fun t => inner ℝ (v t - vInfinity) u) atTop (nhds 0) := by
    simpa only [inner_sub_left, sub_self] using
      hv_coord.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => inner ℝ vInfinity u) atTop
        (nhds (inner ℝ vInfinity u)))
  have havg := weighted_cesaro_real_tendsto_zero w
    (fun s => inner ℝ (v s - vInfinity) u) t0 hcoord hw_nonneg hw_integrable hscalar hW
  have hnonzero : ∀ᶠ t in atTop, (∫ s in t0..t, w s) ≠ 0 := by
    filter_upwards [(Filter.tendsto_atTop.1 hW 1)] with t ht
    linarith
  have hident : ∀ᶠ t in atTop,
      inner ℝ ((∫ s in t0..t, w s)⁻¹ • ∫ s in t0..t, w s • v s) u =
        inner ℝ vInfinity u + (∫ s in t0..t, w s)⁻¹ *
          ∫ s in t0..t, w s * inner ℝ (v s - vInfinity) u := by
    filter_upwards [hnonzero] with t ht
    have hconst : IntervalIntegrable (fun s => w s • vInfinity) volume t0 t :=
      ⟨(hw_integrable t0 t).1.smul_const vInfinity,
        (hw_integrable t0 t).2.smul_const vInfinity⟩
    have hdecomp : (∫ s in t0..t, w s • v s) =
        (∫ s in t0..t, w s • vInfinity) + ∫ s in t0..t, w s • (v s - vInfinity) := by
      rw [← intervalIntegral.integral_add hconst (hcentered t0 t)]
      apply intervalIntegral.integral_congr
      intro s hs
      module
    have hinter : inner ℝ (∫ s in t0..t, w s • (v s - vInfinity)) u =
        ∫ s in t0..t, w s * inner ℝ (v s - vInfinity) u := by
      simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left] using
        ((innerSL ℝ u).intervalIntegral_comp_comm (hcentered t0 t)).symm
    rw [hdecomp, intervalIntegral.integral_smul_const]
    simp only [smul_add, inner_add_left, real_inner_smul_left]
    rw [hinter]
    field_simp [ht]
  refine Tendsto.congr' ?_ (by simpa using tendsto_const_nhds.add havg)
  filter_upwards [hident] with t ht
  exact ht.symm
```

## Proof explanation
The proof first reduces weak convergence to convergence of all scalar inner-product coordinates, then applies a scalar weighted Cesàro lemma to each coordinate.

The cited theorem `weakConvergence_iff_forall_tendsto_inner_right` says that, in a complete real inner product space \(H\), a family \(\xi(a)\) converges weakly to \(x\) if and only if for every \(u\in H\),
\[
\langle \xi(a),u\rangle \to \langle x,u\rangle.
\]
The proof uses both directions of this equivalence.

First, the goal is to prove
\[
\operatorname{toWeakSpace}_{\mathbb R,H}(A(t))\to
\operatorname{toWeakSpace}_{\mathbb R,H}(v_\infty).
\]
The proof applies the reverse implication of the weak-convergence equivalence to the function \(t\mapsto A(t)\) and the limit \(v_\infty\). This reduces the goal to showing that for every \(u\in H\),
\[
\langle A(t),u\rangle \to \langle v_\infty,u\rangle.
\]
The tactic `intro u` fixes an arbitrary test vector \(u\).

Next, the proof applies the forward implication of the same equivalence to the original weak convergence hypothesis \(hv\) for \(v\). This gives
\[
\langle v(t),u\rangle \to \langle v_\infty,u\rangle.
\]
Subtracting the constant limit \(\langle v_\infty,u\rangle\), and using linearity of the inner product in its first argument, gives
\[
\langle v(t)-v_\infty,u\rangle \to 0.
\]
This is the centered scalar convergence needed for the scalar Cesàro theorem.

The proof then establishes integrability of the centered vector-valued function
\[
s\mapsto w(s)\cdot (v(s)-v_\infty).
\]
For each interval \( [a,b] \), the assumption `hwv_integrable` gives interval integrability of \(s\mapsto w(s)\cdot v(s)\). From `hw_integrable`, multiplying the scalar function \(w\) by the fixed vector \(v_\infty\) gives interval integrability of \(s\mapsto w(s)\cdot v_\infty\). Subtracting the latter from the former gives interval integrability of
\[
s\mapsto w(s)\cdot v(s)-w(s)\cdot v_\infty.
\]
By the vector identity
\[
w(s)\cdot v(s)-w(s)\cdot v_\infty
=
w(s)\cdot (v(s)-v_\infty),
\]
this proves the desired interval integrability. The `convert` step reduces the goal to that pointwise identity, and `module` proves the identity in the real vector space \(H\).

From this centered vector-valued integrability, the proof obtains interval integrability of the scalar function
\[
s\mapsto w(s)\langle v(s)-v_\infty,u\rangle.
\]
It applies the continuous linear functional \(x\mapsto \langle x,u\rangle\) to the interval-integrable vector-valued function \(s\mapsto w(s)\cdot(v(s)-v_\infty)\). A continuous linear functional preserves integrability, so the composition is integrable. Then the scalar is pulled out of the inner product using real bilinearity, yielding the stated scalar integrand. This is exactly the integrability hypothesis needed for the scalar weighted Cesàro theorem.

The cited scalar result `weighted_cesaro_real_tendsto_zero` says that if \(g:\mathbb R\to\mathbb R\) satisfies \(g(t)\to 0\), \(w\ge 0\) eventually, \(w\) and \(w g\) are interval integrable, and \(W(t)=\int_{t_0}^{t}w(s)\,ds\to+\infty\), then
\[
W(t)^{-1}\int_{t_0}^{t} w(s)g(s)\,ds \to 0.
\]
The proof applies this with
\[
g(s)=\langle v(s)-v_\infty,u\rangle.
\]
All hypotheses have just been verified: \(g\to 0\), \(w\ge0\) eventually, \(w\) is interval integrable, \(w g\) is interval integrable by the previous step, and \(W(t)\to+\infty\) is exactly `hW`. Therefore
\[
W(t)^{-1}\int_{t_0}^{t} w(s)\langle v(s)-v_\infty,u\rangle\,ds \to 0.
\]

The proof next records that \(W(t)\neq 0\) eventually. Since \(W(t)\to+\infty\), the filter characterization of convergence to \(+\infty\) gives that eventually \(1\le W(t)\). Hence \(W(t)\neq 0\) eventually. The tactic `linarith` closes this arithmetic implication.

The main algebraic step is an eventual identity for the scalar coordinate of the weighted average:
\[
\langle A(t),u\rangle
=
\langle v_\infty,u\rangle
+
W(t)^{-1}\int_{t_0}^{t} w(s)\langle v(s)-v_\infty,u\rangle\,ds.
\]
This is proved for all sufficiently large \(t\) with \(W(t)\neq 0\). First, the vector-valued integrand is decomposed pointwise:
\[
w(s)\cdot v(s)
=
w(s)\cdot v_\infty + w(s)\cdot(v(s)-v_\infty).
\]
Integrating both sides uses additivity of the interval integral, justified by interval integrability of the two summands. Then
\[
\int_{t_0}^{t} w(s)\cdot v_\infty\,ds
=
\left(\int_{t_0}^{t} w(s)\,ds\right)\cdot v_\infty
=
W(t)\cdot v_\infty.
\]
For the remaining integral, the continuous linear functional \(x\mapsto \langle x,u\rangle\) commutes with the interval integral:
\[
\left\langle \int_{t_0}^{t} w(s)\cdot(v(s)-v_\infty)\,ds,u\right\rangle
=
\int_{t_0}^{t}
\left\langle w(s)\cdot(v(s)-v_\infty),u\right\rangle\,ds
=
\int_{t_0}^{t}
w(s)\langle v(s)-v_\infty,u\rangle\,ds.
\]
Thus, after multiplying by \(W(t)^{-1}\), the inner product of the weighted average with \(u\) becomes
\[
W(t)^{-1}\left\langle W(t)\cdot v_\infty
+
\int_{t_0}^{t} w(s)\cdot(v(s)-v_\infty)\,ds,u\right\rangle.
\]
Using linearity of the inner product and the fact that \(W(t)\neq0\), this simplifies exactly to
\[
\langle v_\infty,u\rangle
+
W(t)^{-1}\int_{t_0}^{t} w(s)\langle v(s)-v_\infty,u\rangle\,ds.
\]
The tactic `field_simp [ht]` performs this final simplification using \(W(t)\neq0\).

Finally, the proof combines limits. The constant function \(t\mapsto \langle v_\infty,u\rangle\) tends to \(\langle v_\infty,u\rangle\), and the previously obtained Cesàro term tends to \(0\). Therefore their sum tends to \(\langle v_\infty,u\rangle\). Since \(\langle A(t),u\rangle\) is eventually equal to that sum, `Tendsto.congr'` transfers the limit to \(\langle A(t),u\rangle\). Thus for every \(u\in H\),
\[
\langle A(t),u\rangle \to \langle v_\infty,u\rangle.
\]
By the reverse direction of `weakConvergence_iff_forall_tendsto_inner_right`, this coordinatewise convergence is equivalent to weak convergence of \(A(t)\) to \(v_\infty\), which is the desired conclusion.

