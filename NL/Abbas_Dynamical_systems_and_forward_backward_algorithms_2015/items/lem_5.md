## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_5.lean`

## Lean statement
```lean
theorem subgradient_chain_rule {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ gammaZero H)
    (x v : ℝ → H) (b : ℝ) (hb : 0 < b)
    (hx_ac : AbsolutelyContinuousOnInterval x 0 b)
    (hsubgradient : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      v t ∈ subdifferential Phi (x t))
    (hdom : ∀ t ∈ Set.Icc 0 b, x t ∈ effectiveDomain Phi)
    (hx_deriv : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      HasDerivAt x (deriv x t) t)
    (hvL2 : MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b))) :
    AbsolutelyContinuousOnInterval (fun t ↦ (Phi (x t) : EReal).toReal) 0 b ∧
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      deriv (fun s ↦ (Phi (x s) : EReal).toReal) t = inner ℝ (v t) (deriv x t)
```

## Statement explanation
Statement: The theorem `subgradient_chain_rule` takes the following data.

- `H` is a type with a normed additive commutative group structure, equipped with an inner product space structure over `ℝ`, and is complete. In ordinary mathematical terms, `H` is a real Hilbert space, but only the norm, inner product, and completeness axioms needed for the argument are assumed.
- `Phi : H → Set.Ioi (⊥ : EReal)`: a function from `H` to the set of extended-real numbers strictly greater than `⊥` (bottom). Thus `Phi` takes values in extended real numbers that are not `-∞`; they may be finite or `+∞`.
- `hPhi : Phi ∈ gammaZero H`: the function `Phi` belongs to the class `gammaZero H`, described as a family of functions satisfying certain conditions used in the theory (e.g. weak convexity/regularity assumptions). No further properties are asserted in this theorem beyond membership.
- `x : ℝ → H` and `v : ℝ → H`: two functions of a real time variable, to be interpreted as a trajectory and a subgradient selection along that trajectory.
- `b : ℝ` and `hb : 0 < b`: an endpoint time, positive, with the interval under consideration being `[0, b]`.
- `hx_ac : AbsolutelyContinuousOnInterval x 0 b`: `x` is absolutely continuous on the interval `[0, b]`.
- `hsubgradient`: almost everywhere on `t ∈ [0, b]` with respect to the restricted volume measure, `v t ∈ subdifferential Phi (x t)`. That is, `v` is a measurable subgradient field along `x`.
- `hdom`: for every `t ∈ [0, b]`, `x t` belongs to the effective domain of `Phi`; that is, `Phi (x t)` is not `+∞` (and since values avoid `-∞`, it is finite at those points).
- `hx_deriv`: almost everywhere on `[0, b]`, the function `x` has derivative at `t` equal to `deriv x t`; this is the standard derivative function supplied by the derivative operator.
- `hvL2`: the function `v` is in `L²` on the interval `[0, b]` with respect to the restricted volume measure.
- `hdxL2`: the derivative function `deriv x` is in `L²` on the same interval.
- Conclusion: two statements hold simultaneously. First, the composed real-valued function `t ↦ (Phi (x t) : EReal).toReal` is absolutely continuous on `[0, b]`. Here the coercion `(Phi (x t) : EReal)` is the extended-real value, and `.toReal` sends a finite extended real to its real value; because `hdom` ensures `Phi (x t)` is finite almost everywhere, the real coercion is well-behaved. Second, almost everywhere on `[0, b]`, the derivative of that composed function at `t` equals the inner product `inner ℝ (v t) (deriv x t)`: the real inner product of the subgradient `v t` and the derivative of `x`.

In symbols:
\[
F(t) = \operatorname{toReal}(\Phi(x(t))),
\]
and the theorem asserts
\[
F \in AC([0,b]), \qquad
\dot F(t) = \langle v(t), \dot x(t)\rangle_{\mathbb R}
\quad \text{a.e. on } [0,b].
\]

## Lean proof
```lean
by
  let F : ℝ → ℝ := fun t ↦ (Phi (x t) : EReal).toReal
  have hF_ac : AbsolutelyContinuousOnInterval F 0 b := by
    let M : ℝ → ℝ := fun r ↦ ‖v r‖ * ‖deriv x r‖
    have hv_sq : IntegrableOn (fun r ↦ ‖v r‖ ^ 2) (Set.Icc 0 b) :=
      (memLp_two_iff_integrable_sq_norm hvL2.aestronglyMeasurable).mp hvL2
    have hdx_sq : IntegrableOn (fun r ↦ ‖deriv x r‖ ^ 2) (Set.Icc 0 b) :=
      (memLp_two_iff_integrable_sq_norm hdxL2.aestronglyMeasurable).mp hdxL2
    have hmajorant : IntegrableOn
        (fun r ↦ (‖v r‖ ^ 2 + ‖deriv x r‖ ^ 2) / 2) (Set.Icc 0 b) := by
      simpa [add_div] using (hv_sq.add hdx_sq).div_const 2
    have hM : IntegrableOn M (Set.Icc 0 b) := by
      apply Integrable.mono' hmajorant
      · exact hvL2.aestronglyMeasurable.norm.mul hdxL2.aestronglyMeasurable.norm
      · filter_upwards with r
        dsimp [M]
        rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        nlinarith [sq_nonneg (‖v r‖ - ‖deriv x r‖)]
    have hvol : volume (Set.Icc 0 b) ≠ 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    obtain ⟨r, hr, hsubr⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hvol hsubgradient
    let gamma : ℕ → PosReal := fun n ↦
      ⟨1 / ((n : ℝ) + 1), by positivity⟩
    have hgamma : Filter.Tendsto (fun n ↦ (gamma n : ℝ)) Filter.atTop (nhds 0) := by
      simpa [gamma] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0))
    let Fn : ℕ → ℝ → ℝ := fun n t ↦ (({}^[(gamma n)] Phi) (x t)).toReal
    have hlim : ∀ t, t ∈ Set.Icc 0 b →
        Filter.Tendsto (fun n ↦ Fn n t) Filter.atTop (nhds (F t)) := by
      intro t ht
      simpa [Fn, F] using
        moreauEnvelope_toReal_tendsto_of_mem_effectiveDomain Phi hPhi gamma hgamma
          (z := x r) (w := v r) hsubr (hdom t ht)
    have hinc : ∀ n {s t}, s ∈ Set.Icc 0 b → t ∈ Set.Icc 0 b → s ≤ t →
        abs (Fn n t - Fn n s) ≤ ∫ q in s..t, M q := by
      intro n s t hs ht hst
      have hsmooth := moreauEnvelope_comp_ac_and_increment_bound
        Phi hPhi (gamma n) x v hb.le hx_ac hsubgradient hx_deriv hM
      simpa [Fn, M] using hsmooth.2 hs ht hst
    exact absolutelyContinuousOnInterval_of_pointwise_limit_of_abs_sub_le_intervalIntegral
      hb.le hM hlim hinc
  constructor
  · exact hF_ac
  · simpa [F] using deriv_energy_eq_inner_of_absolutelyContinuous Phi hPhi x v b hb
      hsubgradient hdom hx_deriv hF_ac
```

## Proof explanation
The proof begins by defining the real-valued composition:
\[
F(t) = (\Phi(x(t)):\operatorname{EReal}).toReal.
\]
The goal is split into two assertions: absolute continuity of `F` and the pointwise a.e. derivative identity. The proof obtains absolute continuity first, then derives the derivative identity from a separate lemma.

1. Define `F : ℝ → ℝ := fun t ↦ (Phi (x t) : EReal).toReal`.
   This syntactic abbreviation makes the conclusion easier to state.

2. Prove `hF_ac : AbsolutelyContinuousOnInterval F 0 b`.
   - Define `M : ℝ → ℝ := fun r ↦ ‖v r‖ * ‖deriv x r‖`. This product will be the pointwise majorant for increments of approximations of `F`.
   - From `hvL2`, obtain `hv_sq`: the function `r ↦ ‖v r‖^2` is integrable on `[0,b]`. This uses the lemma `memLp_two_iff_integrable_sq_norm` applied to `hvL2`, extracting the integrability of the square of the norm because `v` is in `L²`.
   - Similarly, from `hdxL2`, obtain `hdx_sq`: the square of the norm of `deriv x` is integrable.
   - Define the majorant sum:
     \[
     r \mapsto \frac{\|v r\|^2 + \|deriv x r\|^2}{2}.
     \]
     Using `hv_sq.add hdx_sq` and division by the constant `2`, the tactic `simpa [add_div]` proves this function is integrable on `[0,b]`. This is `hmajorant`.
   - Prove `hM : IntegrableOn M (Set.Icc 0 b)`, i.e. the product `‖v‖ * ‖deriv x‖` is integrable.
     - `apply Integrable.mono' hmajorant` reduces the task to two facts: (a) the function `M` is measurable, and (b) `|M r|` is bounded pointwise by the integrable majorant.
     - Measurability comes from `hvL2.aestronglyMeasurable.norm.mul hdxL2.aestronglyMeasurable.norm`, since norms of strongly measurable functions are strongly measurable and products preserve this.
     - The pointwise bound is proved with `filter_upwards with r`, rewriting the absolute value using `abs_of_nonneg` because `M r` is a product of two norms, hence nonnegative. Then the inequality
       \[
       \|v r\| \|deriv x r\|
       \le \frac{\|v r\|^2 + \|deriv x r\|^2}{2}
       \]
       is deduced by `nlinarith` from the square inequality
       \[
       (\|v r\| - \|deriv x r\|)^2 \ge 0.
       \]
       This establishes `M` is integrable.

3. Show `hvol : volume (Set.Icc 0 b) ≠ 0`.
   - The interval `[0,b]` has positive Lebesgue measure because `b > 0`. The proof rewrites `Real.volume_Icc` and uses `ENNReal.ofReal_ne_zero_iff.mpr` after `linarith` from `hb`.
   - This nondegeneracy was needed to extract a point from the almost-everywhere subgradient condition: a.e. statement over a set of positive measure cannot be vacuous.

4. Obtain a particular point `r` in `[0,b]` where the subgradient condition holds.
   - `obtain ⟨r, hr, hsubr⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol hsubgradient`.
   - This gives a genuine point `r ∈ [0,b]` such that `v r ∈ subdifferential Phi (x r)`. Such a point will be used for approximating `Phi` by its Moreau envelope.

5. Define the approximation sequence of positive parameters:
   \[
   \gamma_n = \frac{1}{n+1}.
   \]
   - `gamma : ℕ → PosReal := fun n ↦ ⟨1 / ((n : ℝ) + 1), by positivity⟩` ensures each `gamma n` is a positive real number.
   - Prove `hgamma`: the real values of these parameters tend to `0` as `n → ∞`. This uses the known lemma `tendsto_one_div_add_atTop_nhds_zero_nat` and `simpa [gamma]`.

6. Define the Moreau-envelope approximations of the composition:
   \[
   F_n(t) = \operatorname{toReal}\left((\text{envelope of } \Phi \text{ with parameter } \gamma_n)(x(t))\right).
   \]
   In Lean, this is expressed with notation `(({}^{[(gamma n)]} Phi) (x t)).toReal`.

7. Prove that `F_n(t) → F(t)` for every `t ∈ [0,b]`:
   - `hlim : ∀ t, t ∈ Set.Icc 0 b → Filter.Tendsto (fun n ↦ Fn n t) Filter.atTop (nhds (F t))`.
   - Fix `t ∈ [0,b]`. The approximation result `moreauEnvelope_toReal_tendsto_of_mem_effectiveDomain Phi hPhi gamma hgamma (z := x r) (w := v r) hsubr (hdom t ht)` states that as the envelope parameter tends to `0`, the Moreau envelope of `Phi` evaluated at `x t` tends to the original extended-real value, provided one point from the subgradient condition is available and `x t` is in the effective domain. The `simpa [Fn, F]` command expands the definitions so the statement matches this goal.

8. Prove a uniform increment bound for each approximating function `F_n`:
   - `hinc : ∀ n {s t}, s ∈ [0,b] → t ∈ [0,b] → s ≤ t → abs (Fn n t - Fn n s) ≤ ∫ q in s..t, M q`.
   - Apply `moreauEnvelope_comp_ac_and_increment_bound Phi hPhi (gamma n) x v hb.le hx_ac hsubgradient hx_deriv hM`, which gives, for the same `M`, that along the absolutely continuous curve the variation of the Moreau envelope composition is controlled by the integral of `M` over subintervals. The second component of the returned pair is the needed bound; `simpa [Fn, M]` matches the notation.

9. Combine the limit and the increment bounds to conclude `F` itself is absolutely continuous:
   - Call
     \[
     \texttt{absolutelyContinuousOnInterval\_of\_pointwise\_limit\_of\_abs\_sub\_le\_intervalIntegral}
       \ hb.le\ hM\ hlim\ hinc.
     \]
   This standard criterion says: if a sequence of functions has pointwise limit `F`, each increment is bounded by the integral of an integrable majorant `M`, and the majorant is integrable, then the limit `F` is absolutely continuous. The output is `hF_ac`.

10. Now the second part of the conclusion.
    - Use `constructor` to split the final conjunction into absolute continuity and the a.e. derivative equality.
    - The first component is exactly `hF_ac`.
    - For the second component, the proof invokes the lemma:
      \[
      \texttt{deriv\_energy\_eq\_inner\_of\_absolutelyContinuous}
        \ Phi\ hPhi\ x\ v\ b\ hb\ hsubgradient\ hdom\ hx\_deriv\ hF\_ac.
      \]
      This lemma states that under the hypotheses already present and using the newly established absolute continuity of `F`, for almost every `t` the derivative of `F` is `inner ℝ (v t) (deriv x t)`. The final `simpa [F]` expands `F` so the stated conclusion matches exactly.

The proof therefore establishes absolute continuity of the real composition first, based on approximations by smooth Moreau envelopes and integrable majorants, and then the pointwise a.e. derivative formula follows from the absolute continuity together with the subgradient and derivative hypotheses.

