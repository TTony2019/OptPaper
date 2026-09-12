## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_lem_1.lean`

## Lean statement
```lean
theorem lemma_3_1 {t₀ : ℝ} (h : ℝ → ℝ) (h_nonneg : ∀ t ∈ Set.Ici t₀, 0 ≤ h t)
    (h_mono : AntitoneOn h (Set.Ici t₀)) (h_int : MeasureTheory.IntegrableOn h (Set.Ici t₀)) :
    Filter.Tendsto (fun t : ℝ => t * h t) Filter.atTop (nhds 0)
```

## Statement explanation
The declaration `lemma_3_1` states the following. Let $t_0$ be a real number and let $h:\mathbb R\to\mathbb R$. Assume that:

1. $h$ is nonnegative on the half-line $[t_0,\infty)$: for every $t\in[t_0,\infty)$, $0\le h(t)$.
2. $h$ is nonincreasing on $[t_0,\infty)$: if $t_0\le x\le y$, then $h(y)\le h(x)$. In Lean this is `AntitoneOn h (Set.Ici t₀)`.
3. $h$ is integrable on $[t_0,\infty)$ with respect to Lebesgue measure.

Under these hypotheses, the conclusion is that the product $t h(t)$ tends to $0$ as $t\to+\infty$:

```math
\lim_{t\to+\infty} t\,h(t)=0.
```

Equivalently, the function $h$ must decay faster than $1/t$ asymptotically. The theorem does not assume continuity; it uses only nonnegativity, monotonicity, and integrability on the half-line.

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
The proof starts from the integrability hypothesis. The theorem `tendsto_tail_setIntegral_Ici`, applied to $h_{\text{int}}$, says that because $h$ is integrable on $[t_0,\infty)$, the tail set integral

```math
a\mapsto \int_{[a,\infty)} h(u)\,du
```

converges to $0$ as $a\to+\infty$. This is recorded as `htail`. The mathematical point is that an integrable function has vanishing tail integrals; here this is used without any nonnegativity or monotonicity assumption.

Next, the proof defines `htail_half`, the assertion that

```math
t\mapsto \int_{[t/2,\infty)} h(u)\,du
```

also tends to $0$ as $t\to+\infty$. Since $t\mapsto t/2$ tends to $+\infty$ when $2\gt 0$, composing the previous tail limit with $t\mapsto t/2$ gives this result. The command `convert ... using 1` is only handling the fact that the composition is definitionally the displayed function. Thus the tail integral beginning at $t/2$ vanishes asymptotically.

Then `htail_bound` records that the scaled expression

```math
t\mapsto 2\int_{[t/2,\infty)} h(u)\,du
```

tends to $0$. This follows from the previous limit by multiplying by the constant $2$: the command `htail_half.const_mul 2` gives convergence of the scaled function to $2\cdot 0=0$, and `simpa` simplifies the result.

The main conclusion is then obtained by a squeeze argument. The proof invokes `tendsto_of_tendsto_of_tendsto_of_le_of_le'` with the lower bounding function $0$, whose convergence to $0$ is supplied by `tendsto_const_nhds`, and the upper bounding function $2\int_{[t/2,\infty)}h$, whose convergence to $0$ is supplied by `htail_bound`. The remaining two goals are the eventual inequalities

```math
0\le t\,h(t)
```

and

```math
t\,h(t)\le 2\int_{[t/2,\infty)} h(u)\,du.
```

For the lower bound, the proof uses `filter_upwards` with the eventual condition $t\ge \max(2t_0,0)$. For such $t$, one has $2t_0\le t$, hence $t_0\le t/2$ by linear arithmetic (`linarith`). Also $0\le t$ because $t\ge\max(2t_0,0)\ge0$. Since $t_0\le t/2$ and $0\le t$, we get $t_0\le t$. The nonnegativity hypothesis then gives $0\le h(t)$. Multiplying the inequalities $0\le t$ and $0\le h(t)$ gives $`0\le t\,h(t)`$. This proves the required eventual lower bound.

For the upper bound, the proof again restricts to eventually $t\ge \max(2t_0,0)$, so that $t_0\le t/2$, $0\le t$, and $t/2\le t$. The constant function $u\mapsto h(t)$ is interval integrable on $[t/2,t]$ by `simp`. The function $h$ itself is interval integrable on $[t/2,t]$: using `intervalIntegrable_iff_integrableOn_Ioc_of_le` with $t/2\le t$, it suffices to show $h$ is integrable on $(t/2,t]$. Every $u\in(t/2,t]$ satisfies $u\gt t/2\ge t_0$, so $(t/2,t]\subseteq[t_0,\infty)$. Since $h$ is integrable on $[t_0,\infty)$, the subset monotonicity statement `h_int.mono_set` gives integrability on $(t/2,t]$.

Now the proof uses monotonicity of $h$ on the interval. Since $h$ is nonincreasing on $[t_0,\infty)$, for every $u\in[t/2,t]$, both $u$ and $t$ lie in $[t_0,\infty)$, and $u\le t$, so

$$
h(t)\le h(u).
$$

This is the pointwise inequality `hmono`. Applying the interval integral monotonicity theorem `intervalIntegral.integral_mono_on`, the constant function $u\mapsto h(t)$ is below $h$ on $[t/2,t]$, hence

```math
\int_{t/2}^{t} h(t)\,du \le \int_{t/2}^{t} h(u)\,du.
```

The left side equals

```math
(t-t/2)\,h(t)=\frac t2\,h(t).
```

The equality between $(t/2)h(t)$ and the constant integral is handled by `intervalIntegral.integral_const`, `smul_eq_mul`, and `ring`. Therefore

```math
\frac t2\,h(t)\le \int_{t/2}^{t} h(u)\,du.
```

Next, the cited lemma `half_interval_le_tail` gives

```math
\int_{t/2}^{t} h(u)\,du \le \int_{[t/2,\infty)} h(u)\,du.
```

Its hypotheses are exactly $t_0\le t/2$, $0\le t$, nonnegativity of $h$ on $[t_0,\infty)$, and integrability of $h$ on $[t_0,\infty)$. Mathematically, $[t/2,t]\subseteq[t/2,\infty)$, and since $h\ge0$ on that tail, the integral over the larger set is at least the integral over the subinterval.

Combining the two inequalities yields

```math
\frac t2\,h(t)\le \int_{[t/2,\infty)} h(u)\,du.
```

Multiplying by $2$ gives

```math
t\,h(t)\le 2\int_{[t/2,\infty)} h(u)\,du.
```

The final `nlinarith` step performs exactly this combination of the lower interval estimate and the tail estimate.

Thus, eventually,

```math
0\le t\,h(t)\le 2\int_{[t/2,\infty)} h(u)\,du.
```

Both bounding functions, the constant $0$ and $2\int_{[t/2,\infty)}h$, tend to $0$ as $t\to+\infty$. By the squeeze theorem invoked through `tendsto_of_tendsto_of_tendsto_of_le_of_le'`, the sandwiched function $`t\,h(t)`$also tends to$0$. This proves the theorem.

