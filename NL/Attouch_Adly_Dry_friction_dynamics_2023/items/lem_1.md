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
The declaration concerns a real starting point $s_0$, a real exponent $\alpha$, and a function $a:\mathbb R\to\mathbb R$. It assumes:

- $1<\alpha$, so $\alpha-1>0$ and $\alpha-2>-1$;
- $a(s)>0$ for every $s\ge s_0$;
- $\lim_{s\to+\infty}a(s)=0$;
- $s_0\ge 0$;
- for every real $t$, the function

  $$
  u\mapsto u^{\alpha-2}a(u)
  $$

  is interval integrable on the interval from $s_0$ to $t$ with respect to Lebesgue measure.

The conclusion is

$$
\lim_{s\to+\infty}\frac{1}{s^{\alpha-1}}
\int_{s_0}^{s}u^{\alpha-2}a(u)\,du=0.
$$

In ordinary language, if $a$ is positive on the half-line $[s_0,\infty)$, tends to $0$ at infinity, and the weighted function $u^{\alpha-2}a(u)$ is locally interval integrable, then the primitive of $u^{\alpha-2}a(u)$ grows more slowly than $s^{\alpha-1}$. Since $\alpha>1$, the normalizing factor $s^{\alpha-1}$ grows without bound, and the theorem says that the normalized integral still tends to $0$. This is an Abelian-type estimate: the part of the integral before any fixed threshold is killed by the factor $s^{-(\alpha-1)}$, while the tail after a large threshold is made small using $a(u)\to0$.

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
The proof is an epsilon-threshold argument. It first proves that the normalized integral is eventually nonnegative, then uses the order characterization of convergence to $0$ to prove a lower eventual bound and an upper eventual bound.

First, the proof sets

$$
q:=\alpha-1.
$$

Since $1<\alpha$, `linarith` gives

$$
0<q.
$$

Also, again from $1<\alpha$,

$$
-1<\alpha-2.
$$

These two facts are crucial: $q>0$ makes $s^{-q}\to0$ as $s\to+\infty$, and $\alpha-2>-1$ makes $u^{\alpha-2}$ interval integrable and gives the usual power antiderivative formula.

Next, the proof establishes eventual nonnegativity of the normalized integral. It uses `filter_upwards` with the fact that eventually $s>\max(s_0,0)$. For such an $s$, one has $s_0\le s$ and $0\le s$. Then

$$
(s^q)^{-1}\int_{s_0}^{s}u^{\alpha-2}a(u)\,du\ge0.
$$

Indeed, $s\ge0$ implies $s^q\ge0$, so $(s^q)^{-1}\ge0$. For the integral, if $u\in[s_0,s]$, then $u\ge s_0\ge0$, hence $u^{\alpha-2}\ge0$; also $a(u)>0$ by the hypothesis on $a$. Therefore the integrand $u^{\alpha-2}a(u)$ is nonnegative on $[s_0,s]$, so its interval integral is nonnegative by `intervalIntegral.integral_nonneg`. This gives the eventual inequality

$$
0\le (s^q)^{-1}\int_{s_0}^{s}u^{\alpha-2}a(u)\,du.
$$

The proof then rewrites the goal using `tendsto_order`. This converts convergence to $0$ into two eventual order conditions: for every $b<0$, eventually

$$
b<\frac{1}{s^q}\int_{s_0}^{s}u^{\alpha-2}a(u)\,du,
$$

and for every $b>0$, eventually

$$
\frac{1}{s^q}\int_{s_0}^{s}u^{\alpha-2}a(u)\,du<b.
$$

The first of these follows immediately from the eventual nonnegativity: if $b<0$ and the expression is at least $0$, then $b<$ the expression. This is the `linarith` step after `filter_upwards [hnonneg]`.

For the upper bound, fix $b>0$. The proof defines

$$
\varepsilon:=\frac{bq}{2}.
$$

Since $b>0$ and $q>0$, `positivity` shows $\varepsilon>0$. Because $a(u)\to0$ as $u\to+\infty$, for this positive $\varepsilon$ one eventually has $a(u)<\varepsilon$. In Lean this is obtained from `ha0.eventually_lt tendsto_const_nhds hε`. The fact `Filter.eventually_atTop.1 hea` then extracts a threshold $T_0$ such that

$$
u\ge T_0 \implies a(u)<\varepsilon.
$$

The proof sets

$$
T:=\max(\max(s_0,0),T_0).
$$

Thus $T\ge s_0$, $T\ge0$, and $T\ge T_0$. Consequently, for every $u\ge T$, one has $a(u)\le\varepsilon$.

Now define

$$
f(u):=u^{\alpha-2}a(u).
$$

The proof handles the fixed part of the integral, namely

$$
(s^q)^{-1}\int_{s_0}^{T}f(u)\,du.
$$

Since $q>0$, the standard limit

$$
s^{-q}\to0\qquad(s\to+\infty)
$$

holds. For $s>0$, $s^{-q}=(s^q)^{-1}$. Therefore

$$
(s^q)^{-1}\to0.
$$

Multiplying by the constant $\int_{s_0}^{T}f(u)\,du$, one obtains

$$
\lim_{s\to+\infty}(s^q)^{-1}\int_{s_0}^{T}f(u)\,du=0.
$$

This is the `hfix` step. Hence, since $b/2>0$, eventually

$$
(s^q)^{-1}\int_{s_0}^{T}f(u)\,du<\frac b2.
$$

This is `hfixlt`.

The proof now restricts to $s$ satisfying both this fixed-part inequality and $s>T$. Then $s>0$, so $s^q>0$. It also proves that $f$ is interval integrable on $T..s$: from the hypothesis `hInt T` and `hInt s`, reversing and concatenating intervals gives interval integrability on $T..s$. The comparison function $u\mapsto u^{\alpha-2}\varepsilon$ is also interval integrable on $T..s$, because $\alpha-2>-1$ and multiplication by the constant $\varepsilon$ preserves interval integrability; this uses `intervalIntegral.intervalIntegrable_rpow'` and `.mul_const ε`.

Next comes the monotonicity estimate. For $u\in[T,s]$, one has $u\ge T\ge0$, so $u^{\alpha-2}\ge0$. Also, by the choice of $T$, $a(u)\le\varepsilon$. Hence

$$
f(u)=u^{\alpha-2}a(u)\le u^{\alpha-2}\varepsilon.
$$

Applying `intervalIntegral.integral_mono_on` gives

$$
\int_T^s f(u)\,du
\le
\int_T^s u^{\alpha-2}\varepsilon\,du.
$$

This is `hmono`.

The comparison integral is then evaluated. Using the power antiderivative formula for exponent $\alpha-2>-1$,

$$
\int_T^s u^{\alpha-2}\,du
=\frac{s^{\alpha-1}-T^{\alpha-1}}{\alpha-1}
=\frac{s^q-T^q}{q}.
$$

Thus

$$
\int_T^s u^{\alpha-2}\varepsilon\,du
=\varepsilon\frac{s^q-T^q}{q}.
$$

Since $T\ge0$, we have $T^q\ge0$, so $s^q-T^q\le s^q$. Dividing by $q>0$ and multiplying by $\varepsilon\ge0$ gives

$$
\varepsilon\frac{s^q-T^q}{q}
\le
\varepsilon\frac{s^q}{q}
=\frac{\varepsilon}{q}s^q.
$$

Therefore

$$
\int_T^s f(u)\,du
\le
\frac{\varepsilon}{q}s^q.
$$

This is `htailbound`.

Multiplying by $(s^q)^{-1}$, which is nonnegative, yields

$$
(s^q)^{-1}\int_T^s f(u)\,du
\le
(s^q)^{-1}\frac{\varepsilon}{q}s^q
=\frac{\varepsilon}{q}.
$$

Since $s>0$, $s^q>0$, so cancellation is valid. Finally, because $\varepsilon=bq/2$ and $q\ne0$,

$$
\frac{\varepsilon}{q}=\frac b2.
$$

Thus

$$
(s^q)^{-1}\int_T^s f(u)\,du\le\frac b2.
$$

This is `hnormtail`.

The final step splits the integral:

$$
\int_{s_0}^{s}f(u)\,du
=\int_{s_0}^{T}f(u)\,du
+\int_T^{s}f(u)\,du.
$$

This uses `intervalIntegral.integral_add_adjacent_intervals`, for which interval integrability on $s_0..T$ and $T..s$ has already been established. Multiplying by $(s^q)^{-1}$ and distributing gives

$$
(s^q)^{-1}\int_{s_0}^{s}f(u)\,du
=(s^q)^{-1}\int_{s_0}^{T}f(u)\,du
+(s^q)^{-1}\int_T^{s}f(u)\,du.
$$

The first summand is strictly less than $b/2$ by `hfixlt`, while the second is at most $b/2$ by `hnormtail`. Hence their sum is less than $b$. The tactic `nlinarith` performs exactly this final arithmetic. Since $q=\alpha-1$ and $f(u)=u^{\alpha-2}a(u)$, this proves the desired eventual upper bound. Together with the earlier eventual lower bound and `tendsto_order`, it proves

$$
\lim_{s\to+\infty}
(s^{\alpha-1})^{-1}
\int_{s_0}^{s}u^{\alpha-2}a(u)\,du
=0.
$$

