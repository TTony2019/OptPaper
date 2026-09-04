## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/lem_1.lean`

## Lean statement
```lean
theorem lemma_A_1 {s₀ α : ℝ} (hα : 1 < α) (a : ℝ → ℝ)
    (ha : ∀ s ∈ Set.Ici s₀, 0 < a s)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) (hs₀ : 0 ≤ s₀)
    (hInt : ∀ t : ℝ, IntervalIntegrable (fun u : ℝ => u ^ (α - 2) * a u) MeasureTheory.volume s₀ t) :
    Filter.Tendsto
      (fun s : ℝ => (s ^ (α - 1))⁻¹ * ∫ u in s₀..s, u ^ (α - 2) * a u)
      Filter.atTop (nhds 0)
```

## Statement explanation
The theorem assumes two real parameters \(s_0,\alpha\) with \(\alpha>1\), and a function \(a:\mathbb R\to\mathbb R\). The hypothesis
\[
\forall s\in \operatorname{Ici}(s_0),\quad 0<a(s)
\]
means \(a(s)>0\) for every \(s\ge s_0\). The hypothesis
\[
\operatorname{Filter.Tendsto}\ a\ \operatorname{Filter.atTop}\ (\operatorname{nhds}\ 0)
\]
means \(a(u)\to 0\) as \(u\to+\infty\). There is also the assumption \(0\le s_0\), and the integrability assumption that for every real \(t\), the function
\[
u\mapsto u^{\alpha-2}a(u)
\]
is interval-integrable on the interval between \(s_0\) and \(t\) with respect to Lebesgue measure.

The conclusion is that
\[
s\mapsto \frac{1}{s^{\alpha-1}}\int_{s_0}^{s} u^{\alpha-2}a(u)\,du
\]
tends to \(0\) as \(s\to+\infty\). In Lean notation,
\[
(s^{\alpha-1})^{-1}\int_{s_0}^{s} u^{\alpha-2}a(u)\,du \longrightarrow 0.
\]

## Lean proof
```lean
by
  let q : ℝ := α - 1
  have hq : 0 < q := by
    dsimp [q]
    linarith
  have hr : -1 < α - 2 := by linarith
  have hnonneg : ∀ᶠ s : ℝ in Filter.atTop,
      0 ≤ (s ^ q)⁻¹ * ∫ u in s₀..s, u ^ (α - 2) * a u := by
    filter_upwards [Filter.eventually_gt_atTop (max s₀ 0)] with s hs
    have hs₀s : s₀ ≤ s := le_trans (le_max_left _ _) hs.le
    have hsnonneg : 0 ≤ s := le_trans (le_max_right _ _) hs.le
    apply mul_nonneg
    · exact inv_nonneg.mpr (Real.rpow_nonneg hsnonneg _)
    · apply intervalIntegral.integral_nonneg hs₀s
      intro u hu
      exact mul_nonneg (Real.rpow_nonneg (le_trans hs₀ hu.1) _) (le_of_lt (ha u hu.1))
  rw [show α - 1 = q by rfl, tendsto_order]
  refine ⟨?_, ?_⟩
  · intro b hb
    filter_upwards [hnonneg] with s hs
    linarith
  · intro b hb
    let ε : ℝ := b * q / 2
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    have hea : ∀ᶠ u : ℝ in Filter.atTop, a u < ε :=
      ha0.eventually_lt tendsto_const_nhds hε
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hea
    let T : ℝ := max (max s₀ 0) T₀
    have hT : 0 ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
    have htail : ∀ u ≥ T, a u ≤ ε := by
      intro u hu
      exact (hT₀ u (le_trans (le_max_right _ _) hu)).le
    let f : ℝ → ℝ := fun u => u ^ (α - 2) * a u
    have hfix : Filter.Tendsto (fun s : ℝ => (s ^ q)⁻¹ * ∫ u in s₀..T, f u)
        Filter.atTop (nhds 0) := by
      have hpow := (tendsto_rpow_neg_atTop hq).congr' <| by
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with s hs
        rw [Real.rpow_neg hs.le]
      simpa using hpow.mul
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => ∫ u in s₀..T, f u) Filter.atTop
          (nhds (∫ u in s₀..T, f u)))
    have hfixlt : ∀ᶠ s : ℝ in Filter.atTop, (s ^ q)⁻¹ * ∫ u in s₀..T, f u < b / 2 :=
      hfix.eventually_lt tendsto_const_nhds (by linarith)
    filter_upwards [hfixlt, Filter.eventually_gt_atTop T] with s hsfix hs
    have hTs : T ≤ s := hs.le
    have hspos : 0 < s := lt_of_le_of_lt hT hs
    have hIntTs : IntervalIntegrable f MeasureTheory.volume T s := by
      exact ((hInt T).symm.trans (hInt s))
    have hWeightInt : IntervalIntegrable (fun u : ℝ => u ^ (α - 2) * ε) MeasureTheory.volume T s := by
      exact (intervalIntegral.intervalIntegrable_rpow' (a := T) (b := s) hr).mul_const ε
    have hmono : ∫ u in T..s, f u ∂MeasureTheory.volume ≤ ∫ u in T..s, u ^ (α - 2) * ε ∂MeasureTheory.volume := by
      apply intervalIntegral.integral_mono_on hTs hIntTs hWeightInt
      intro u hu
      exact mul_le_mul_of_nonneg_left (htail u hu.1) (Real.rpow_nonneg (le_trans hT hu.1) _)
    have htailbound : ∫ u in T..s, f u ≤ (ε / q) * s ^ q := by
      calc
        ∫ u in T..s, f u ≤ ∫ u in T..s, u ^ (α - 2) * ε := hmono
        _ = ε * ((s ^ q - T ^ q) / q) := by
          rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl hr)]
          dsimp [q]
          ring_nf
        _ ≤ (ε / q) * s ^ q := by
          have hsub' : s ^ q - T ^ q ≤ s ^ q := sub_le_self _ (Real.rpow_nonneg hT _)
          have hdiv : (s ^ q - T ^ q) / q ≤ s ^ q / q := (div_le_div_iff_of_pos_right hq).2 hsub'
          have hmul' : ε * ((s ^ q - T ^ q) / q) ≤ ε * (s ^ q / q) :=
            mul_le_mul_of_nonneg_left hdiv hε.le
          calc
            ε * ((s ^ q - T ^ q) / q) ≤ ε * (s ^ q / q) := hmul'
            _ = (ε / q) * s ^ q := by ring
    have hnormtail : (s ^ q)⁻¹ * ∫ u in T..s, f u ≤ b / 2 := by
      have hmul := mul_le_mul_of_nonneg_left htailbound
        (inv_nonneg.mpr (Real.rpow_nonneg hspos.le q))
      have hsq : s ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hspos _)
      calc
        (s ^ q)⁻¹ * ∫ u in T..s, f u ≤ (s ^ q)⁻¹ * ((ε / q) * s ^ q) := hmul
        _ = ε / q := by
          rw [← mul_assoc, mul_comm (s ^ q)⁻¹, mul_assoc, inv_mul_cancel₀ hsq, mul_one]
        _ = b / 2 := by
          dsimp [ε]
          field_simp [ne_of_gt hq]
    change (s ^ q)⁻¹ * ∫ u in s₀..s, f u < b
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hInt T) hIntTs
    simp only [f]
    rw [← hadd]
    change (s ^ q)⁻¹ * (_ + _) < b
    rw [mul_add]
    have hfix' : (s ^ q)⁻¹ * ∫ u in s₀..T, u ^ (α - 2) * a u < b / 2 := by simpa [f] using hsfix
    have hnormtail' : (s ^ q)⁻¹ * ∫ u in T..s, u ^ (α - 2) * a u ≤ b / 2 := by
      simpa [f] using hnormtail
    nlinarith
```

## Proof explanation
The proof begins by defining \(q=\alpha-1\), so that the denominator is \(s^q\). Since \(\alpha>1\), one has \(q>0\), proved using `dsimp` and `linarith`. It also notes that \(\alpha-2>-1\), which is useful later for integrability of real powers.

The first main step is to show that the expression
\[
(s^q)^{-1}\int_{s_0}^{s} u^{\alpha-2}a(u)\,du
\]
is eventually nonnegative as \(s\to+\infty\). This is done using `filter_upwards` with the fact that eventually \(s>\max(s_0,0)\). For such \(s\), one has \(s_0\le s\) and \(0\le s\). The inverse factor is nonnegative because \(s^q\ge0\) by real power nonnegativity. The integral is nonnegative because \(u\ge s_0\) on the interval, hence \(u^{\alpha-2}\ge0\) and \(a(u)>0\), so the integrand is nonnegative. Thus the whole product is nonnegative.

Next, the proof rewrites the goal using `tendsto_order`, which characterizes convergence to \(0\) in the order topology by two conditions: for every \(b<0\), eventually the expression is greater than \(b\); and for every \(b>0\), eventually the expression is less than \(b\).

The first condition is immediate from eventual nonnegativity: if the expression is eventually nonnegative and \(b<0\), then eventually \(b<\text{expression}\), proved by `linarith`.

The second condition is the main part. Fix \(b>0\). The proof chooses
\[
\varepsilon=\frac{bq}{2},
\]
which is positive because \(b>0\) and \(q>0\). Since \(a(u)\to0\) as \(u\to+\infty\), eventually \(a(u)<\varepsilon\). Thus there is some \(T_0\) such that \(a(u)<\varepsilon\) for all \(u\ge T_0\). The proof then chooses
\[
T=\max(\max(s_0,0),T_0),
\]
so \(T\ge0\), \(T\ge s_0\), and for all \(u\ge T\), one has \(a(u)\le\varepsilon\).

The integrand is named
\[
f(u)=u^{\alpha-2}a(u).
\]
The integral from \(s_0\) to \(s\) is split at \(T\). The part from \(s_0\) to \(T\) is a fixed finite integral multiplied by the decaying factor \((s^q)^{-1}\). Since \(q>0\), \((s^q)^{-1}\to0\) as \(s\to+\infty\), so the fixed part tends to \(0\). This uses `tendsto_rpow_neg_atTop` and `Real.rpow_neg`, followed by multiplying by a constant. Therefore, for large \(s\), the fixed part is less than \(b/2\).

For the tail part from \(T\) to \(s\), the proof estimates the integrand:
\[
u^{\alpha-2}a(u)\le u^{\alpha-2}\varepsilon
\]
because \(a(u)\le\varepsilon\) and \(u^{\alpha-2}\ge0\). By interval integral monotonicity,
\[
\int_T^s f(u)\,du
\le
\int_T^s u^{\alpha-2}\varepsilon\,du.
\]
The right-hand integral is evaluated using the real power integral formula:
\[
\int_T^s u^{\alpha-2}\varepsilon\,du
=
\varepsilon\frac{s^q-T^q}{q}.
\]
Since \(T^q\ge0\), this is at most
\[
\frac{\varepsilon}{q}s^q.
\]
Multiplying by the nonnegative factor \((s^q)^{-1}\) gives
\[
(s^q)^{-1}\int_T^s f(u)\,du
\le
\frac{\varepsilon}{q}
=
\frac{b}{2}.
\]
Here \(s>0\), so \(s^q>0\) and the inverse is valid.

Finally, using `intervalIntegral.integral_add_adjacent_intervals`, the whole integral is written as
\[
\int_{s_0}^s f(u)\,du
=
\int_{s_0}^T f(u)\,du
+
\int_T^s f(u)\,du.
\]
After distributing the inverse factor, the first summand is less than \(b/2\) and the second summand is at most \(b/2\). Combining these with `nlinarith` yields the desired inequality
\[
(s^q)^{-1}\int_{s_0}^s f(u)\,du < b.
\]
This proves the upper-bound condition, completing the proof of convergence to \(0\).

