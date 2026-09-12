## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/ext_lem_1.lean`

## Lean statement
```lean
abbrev ext_lem_1 {w a b : ℝ → ℝ} {t₀ T α : ℝ} (hT : 0 < T) (hα₁ : 0 ≤ α) (hα₂ : α < 1)
    (hac : AbsolutelyContinuousOnInterval w t₀ (t₀ + T))
    (hw_nonneg : ∀ t, t ∈ Set.Icc t₀ (t₀ + T) → 0 ≤ w t)
    (ha_int : MeasureTheory.IntegrableOn a (Set.Icc t₀ (t₀ + T)) MeasureTheory.volume)
    (hb_int : MeasureTheory.IntegrableOn b (Set.Icc t₀ (t₀ + T)) MeasureTheory.volume)
    (hb_nonneg : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc t₀ (t₀ + T) → 0 ≤ b t)
    (hineq : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc t₀ (t₀ + T) →
      (1 - α) * deriv w t ≤ a t * w t + b t * (w t) ^ α) :
    ∀ t : ℝ, t₀ ≤ t → t ≤ t₀ + T →
      w t ^ (1 - α) ≤ w t₀ ^ (1 - α) * Real.exp (∫ τ in t₀..t, a τ) +
        ∫ s in t₀..t, Real.exp (∫ τ in s..t, a τ) * b s :=
  nonlinear_gronwall_inequality hT hα₁ hα₂ hac hw_nonneg ha_int hb_int hb_nonneg hineq
```

## Statement explanation
`ext_lem_1` is an abbreviation packaging a nonlinear Gronwall comparison estimate. Its data are three real-valued functions $w,a,b:\mathbb R\to\mathbb R$ and three real parameters $t_0,T,\alpha$. The explicit hypotheses are:

- $0<T$, so the interval $[t_0,t_0+T]$ has positive length;
- $0\le \alpha$ and $\alpha<1$, hence $0\le \alpha<1$;
- $w$ is absolutely continuous on the interval from $t_0$ to $t_0+T$;
- $w$ is nonnegative on $[t_0,t_0+T]$, i.e. for every real $t$, if $t\in [t_0,t_0+T]$, then $0\le w(t)$;
- $a$ is integrable on $[t_0,t_0+T]$ with respect to Lebesgue measure;
- $b$ is integrable on $[t_0,t_0+T]$ with respect to Lebesgue measure;
- $b$ is almost everywhere nonnegative on $[t_0,t_0+T]$, i.e. for almost every $t$ with respect to Lebesgue measure, if $t\in [t_0,t_0+T]$, then $0\le b(t)$;
- the nonlinear differential inequality holds almost everywhere: for almost every $t$, if $t\in [t_0,t_0+T]$, then

  $$
  (1-\alpha)\operatorname{deriv} w(t)
  \le a(t)w(t)+b(t)(w(t))^\alpha .
  $$

The conclusion is that for every real $t$ with $t_0\le t\le t_0+T$,

$$
w(t)^{1-\alpha}
\le w(t_0)^{1-\alpha}
  \exp\!\left(\int_{t_0}^{t} a(\tau)\,d\tau\right)
+ \int_{t_0}^{t}
  \exp\!\left(\int_{s}^{t} a(\tau)\,d\tau\right)b(s)\,ds .
$$

Thus the declaration says: under the positivity, absolute-continuity, integrability, nonnegativity, and almost-everywhere differential-inequality assumptions above, the function $w^{1-\alpha}$ satisfies an explicit Gronwall-type upper bound on $[t_0,t_0+T]$. The bound consists of the initial term $w(t_0)^{1-\alpha}$ multiplied by the exponential of the integral of $a$, plus a forcing term in which $b(s)$ is weighted by the exponential of the integral of $a$ from $s$ to $t$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is an `abbrev`, and its body is the term

$$
\texttt{nonlinear\_gronwall\_inequality hT hα₁ hα₂ hac hw\_nonneg ha\_int hb\_int hb\_nonneg hineq}.
$$

So the proof field is not a tactic proof; it is a direct term-level application of the imported result `nonlinear_gronwall_inequality`.

The arguments supplied to that result are exactly the hypotheses of `ext_lem_1`: the positivity $0<T$, the two assumptions $0\le\alpha$ and $\alpha<1$, absolute continuity of $w$, nonnegativity of $w$ on $[t_0,t_0+T]$, integrability of $a$ and $b$ on $[t_0,t_0+T]$, almost-everywhere nonnegativity of $b$ on that interval, and the almost-everywhere inequality

$$
(1-\alpha)\operatorname{deriv} w(t)
\le a(t)w(t)+b(t)(w(t))^\alpha .
$$

The full statement of `nonlinear_gronwall_inequality` is not included in the provided source, but the visible consequence of applying it with these arguments is precisely the displayed conclusion of `ext_lem_1`: for every $t$ with $t_0\le t\le t_0+T$,

$$
w(t)^{1-\alpha}
\le w(t_0)^{1-\alpha}
  \exp\!\left(\int_{t_0}^{t} a(\tau)\,d\tau\right)
+ \int_{t_0}^{t}
  \exp\!\left(\int_{s}^{t} a(\tau)\,d\tau\right)b(s)\,ds .
$$

Thus the mathematical role of the body is to name that nonlinear Gronwall estimate under the abbreviation `ext_lem_1`. Since `abbrev` is transparent, later uses of `ext_lem_1` can be unfolded to this application. No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and there are no intermediate proof steps to explain beyond this term-level packaging.

