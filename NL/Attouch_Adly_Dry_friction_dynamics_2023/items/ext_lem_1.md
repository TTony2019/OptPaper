## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_lem_1.lean`

## Lean statement
```lean
theorem lemma_3_1 {t₀ : ℝ} (h : ℝ → ℝ) (h_nonneg : ∀ t ∈ Set.Ici t₀, 0 ≤ h t)
    (h_mono : AntitoneOn h (Set.Ici t₀)) (h_int : MeasureTheory.IntegrableOn h (Set.Ici t₀)) :
    Filter.Tendsto (fun t : ℝ => t * h t) Filter.atTop (nhds 0)
```

## Statement explanation
Let \(t_0\in\mathbb R\) and \(h:\mathbb R\to\mathbb R\). The theorem assumes three facts:

1. \(h\) is nonnegative on the interval \([t_0,\infty)\): for every \(t\in[t_0,\infty)\), \(0\le h(t)\).
2. \(h\) is antitone on \([t_0,\infty)\): if \(t_0\le u\le t\), then \(h(t)\le h(u)\).
3. \(h\) is Lebesgue integrable on \([t_0,\infty)\).

Under these hypotheses, the conclusion is that \(t\,h(t)\to 0\) as \(t\to\infty\). In Lean filter notation, this is
\[
\operatorname{Tendsto}\left(\lambda t:\mathbb R,\ t\,h(t)\right)\quad
\mathrm{Filter.atTop}\quad(\mathrm{nhds}\ 0).
\]
That is, for every neighbourhood of \(0\) in \(\mathbb R\), eventually \(t\,h(t)\) lies in that neighbourhood as \(t\) becomes arbitrarily large.

## Lean proof
```lean
by
  have htail := tendsto_tail_setIntegral_Ici h_int
  have htail_half : Filter.Tendsto (fun t : ℝ => ∫ u in Set.Ici (t / 2), h u)
      Filter.atTop (nhds 0) := by
    convert htail.comp (Filter.tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)) using 1
  have htail_bound : Filter.Tendsto (fun t : ℝ => 2 * ∫ u in Set.Ici (t / 2), h u)
      Filter.atTop (nhds 0) := by
    simpa using htail_half.const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    htail_bound ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max (2 * t₀) 0)] with t ht
    have ht₀ : t₀ ≤ t / 2 := by
      have : 2 * t₀ ≤ t := le_trans (le_max_left _ _) ht
      linarith
    have ht_nonneg : 0 ≤ t := le_trans (le_max_right _ _) ht
    exact mul_nonneg ht_nonneg (h_nonneg t (ht₀.trans (by linarith)))
  · filter_upwards [Filter.eventually_ge_atTop (max (2 * t₀) 0)] with t ht
    have ht₀ : t₀ ≤ t / 2 := by
      have : 2 * t₀ ≤ t := le_trans (le_max_left _ _) ht
      linarith
    have ht_nonneg : 0 ≤ t := le_trans (le_max_right _ _) ht
    have hhalf : t / 2 ≤ t := by linarith
    have hconst_int : IntervalIntegrable (fun _ : ℝ => h t) MeasureTheory.volume (t / 2) t := by
      simp
    have hint : IntervalIntegrable h MeasureTheory.volume (t / 2) t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
      apply h_int.mono_set
      intro u hu
      exact ht₀.trans (le_of_lt hu.1)
    have hlower : (t / 2) * h t ≤ ∫ u in t / 2..t, h u := by
      have hmono : ∀ u ∈ Set.Icc (t / 2) t, h t ≤ h u := by
        intro u hu
        exact h_mono (ht₀.trans hu.1) (ht₀.trans (by linarith)) hu.2
      calc
        (t / 2) * h t = ∫ _u in t / 2..t, h t := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        _ ≤ ∫ u in t / 2..t, h u :=
          intervalIntegral.integral_mono_on hhalf hconst_int hint hmono
    have hupper := half_interval_le_tail ht₀ ht_nonneg h_nonneg h_int
    nlinarith [hlower, hupper]
```

## Proof explanation
The proof starts with the fact that the tail integral of an integrable function tends to zero. From \(h_{\mathrm{int}}\), the lemma `tendsto_tail_setIntegral_Ici` gives
\[
\int_{[t,\infty)} h(u)\,du \to 0 \quad\text{as } t\to\infty.
\]
The proof calls this `htail`.

Next, it replaces \(t\) by \(t/2\). Since \(t/2\to\infty\) as \(t\to\infty\), composing `htail` with the map \(t\mapsto t/2\) gives
\[
\int_{[t/2,\infty)} h(u)\,du \to 0.
\]
This is done using `convert`, `Filter.tendsto_id.atTop_div_const`, and the positivity of \(2\). Multiplying this convergent sequence by the constant \(2\), the proof obtains
\[
2\int_{[t/2,\infty)} h(u)\,du \to 0.
\]
This is called `htail_bound`.

The main argument is a sandwich argument. The proof uses
\[
\operatorname{tendsto\_of\_tendsto\_of\_tendsto\_of\_le\_of\_le'}
\]
with the constant zero sequence and `htail_bound`. It remains to show that, eventually in \(t\),
\[
0\le t\,h(t)
\]
and
\[
t\,h(t)\le 2\int_{[t/2,\infty)} h(u)\,du.
\]
Both eventual inequalities are proved for \(t\ge \max(2t_0,0)\).

For the lower bound, if \(t\ge\max(2t_0,0)\), then \(0\le t\) and \(t_0\le t/2\le t\), so \(t\in[t_0,\infty)\). Therefore \(h(t)\ge 0\) by the nonnegativity hypothesis. Since \(t\ge 0\), multiplication gives \(0\le t\,h(t)\).

For the upper bound, the proof first compares \(t\,h(t)\) with the interval integral on \([t/2,t]\). Since \(h\) is antitone and the interval \([t/2,t]\) lies in \([t_0,\infty)\), for every \(u\in[t/2,t]\) one has \(h(t)\le h(u)\). Integrating this pointwise inequality over \([t/2,t]\), and using that the integral of the constant \(h(t)\) over that interval is \((t-t/2)h(t)=\frac t2 h(t)\), gives
\[
\frac t2\,h(t)\le \int_{t/2}^{t} h(u)\,du.
\]
The proof establishes the necessary interval integrability of \(h\) by observing that \([t/2,t]\subseteq[t_0,\infty)\), so it follows from integrability of \(h\) on \([t_0,\infty)\).

Then the supplied lemma `half_interval_le_tail` is applied with \(t_0\le t/2\), \(0\le t\), the nonnegativity of \(h\), and the integrability of \(h\). It gives
\[
\int_{t/2}^{t} h(u)\,du
\le
\int_{[t/2,\infty)} h(u)\,du.
\]
Combining this with the previous inequality,
\[
\frac t2\,h(t)\le \int_{[t/2,\infty)} h(u)\,du.
\]
Multiplying by \(2\) yields
\[
t\,h(t)\le 2\int_{[t/2,\infty)} h(u)\,du.
\]
The final step `nlinarith` uses these algebraic inequalities to conclude the upper sandwich bound.

Thus, eventually,
\[
0\le t\,h(t)\le 2\int_{[t/2,\infty)} h(u)\,du,
\]
and the right-hand side tends to \(0\). By the sandwich principle, \(t\,h(t)\to 0\) as \(t\to\infty\).

