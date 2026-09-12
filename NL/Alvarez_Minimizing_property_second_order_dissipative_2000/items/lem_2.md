## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/lem_2.lean`

## Lean statement
```lean
theorem positive_part_integrable_of_damped_inequality (omega g : ℝ → ℝ) (gamma : ℝ)
    (hDiff : ContDiffOn ℝ 1 omega (Set.Ici 0)) (hgamma : 0 < gamma)
    (hIneq : ∀ t ∈ Set.Ici 0, deriv omega t + gamma * omega t ≤ g t)
    (hg : IntegrableOn g (Set.Ici 0)) :
    IntegrableOn (fun t => max (omega t) 0) (Set.Ici 0)
```

## Statement explanation
The declaration states the following. Let $\omega:\mathbb R\to\mathbb R$, $g:\mathbb R\to\mathbb R$, and $\gamma\in\mathbb R$. Assume that $\omega$ is $C^1$ on the ray $[0,\infty)$, in the sense of one-sided differentiability on that set; that $\gamma>0$; that for every $t\ge 0$,

$$
\mathrm{deriv}\omega(t)+\gamma\,\omega(t)\le g(t);
$$

and that $g$ is Lebesgue integrable on $[0,\infty)$. The conclusion is that the positive part of $\omega$,

$$
t\mapsto \max(\omega(t),0),
$$

is integrable on $[0,\infty)$.

Mathematically, this says that a function satisfying a first-order damped differential inequality with right-hand side bounded above by an integrable function has an integrable positive part. No integrability of $\omega$ itself is assumed. The damping term $\gamma>0$ is essential: it produces exponential decay in the comparison estimates, which makes both the initial exponential factor and the causal convolution of $|g|$ integrable. The proof first converts the inequality against $g$ into an inequality against $|g|$, then applies a damped Gronwall-type comparison estimate to bound $\omega(t)$, and finally dominates $\max(\omega(t),0)$ by an explicit integrable majorant.

## Lean proof
```lean
by
  have hG : IntegrableOn (fun t : ℝ => |g t|) (Set.Ici 0) := hg.abs
  have hineq_abs : ∀ t ∈ Set.Ici 0, deriv omega t + gamma * omega t ≤ |g t| :=
    fun t ht => (hIneq t ht).trans (le_abs_self (g t))
  have hcomparison := damped_le_causal_exp_convolution omega g gamma hDiff hineq_abs hg
  have hconvolution := causal_exp_convolution_integrable g gamma hgamma hg
  have hkernel : IntegrableOn (fun t : ℝ => Real.exp ((-gamma) * t)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) 0
  have hinitial : IntegrableOn
      (fun t : ℝ => Real.exp (-gamma * t) * max (omega 0) 0) (Set.Ici 0) := by
    simpa only [neg_mul] using hkernel.mul_const (max (omega 0) 0)
  have hmajorant : IntegrableOn (fun t : ℝ =>
      Real.exp (-gamma * t) * max (omega 0) 0 +
        ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s|) (Set.Ici 0) :=
    hinitial.add hconvolution
  have hconvolution_nonneg : ∀ t ∈ Set.Ici 0,
      0 ≤ ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := by
    intro t ht
    exact intervalIntegral.integral_nonneg_of_forall ht fun s =>
      mul_nonneg (le_of_lt (Real.exp_pos _)) (abs_nonneg _)
  have hpointwise : ∀ t ∈ Set.Ici 0,
      max (omega t) 0 ≤ Real.exp (-gamma * t) * max (omega 0) 0 +
        ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := by
    intro t ht
    apply max_le
    · calc
        omega t ≤ Real.exp (-gamma * t) * omega 0 +
            ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := hcomparison t ht
        _ ≤ Real.exp (-gamma * t) * max (omega 0) 0 +
            ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| :=
          add_le_add
            (mul_le_mul_of_nonneg_left (le_max_left _ _)
              (le_of_lt (Real.exp_pos _))) le_rfl
    · exact add_nonneg
        (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_max_right _ _))
        (hconvolution_nonneg t ht)
  have htarget_measurable : AEStronglyMeasurable (fun t : ℝ => max (omega t) 0)
      (volume.restrict (Set.Ici 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ici
    intro t ht
    exact (hDiff t ht).continuousWithinAt.max continuousWithinAt_const
  have hnorm_bound : ∀ᵐ t ∂(volume.restrict (Set.Ici 0)),
      ‖max (omega t) 0‖ ≤ Real.exp (-gamma * t) * max (omega 0) 0 +
  ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hpointwise t ht
  exact hmajorant.mono' htarget_measurable hnorm_bound
```

## Proof explanation
The proof is an integrable-dominance argument. It constructs an explicit integrable function $M(t)$ such that

$$
\max(\omega(t),0)\le M(t)
$$

for almost every $t\ge 0$, and then invokes the standard comparison theorem for integrability.

First, the proof records that $|g|$ is integrable on $[0,\infty)$. Indeed, if $g$ is integrable on $[0,\infty)$, then so is $t\mapsto |g(t)|$. This is not directly used later in the displayed invocation chain, but it is the natural preliminary fact corresponding to the absolute value appearing in the convolution.

Next, the hypothesis

$$
\mathrm{deriv}\omega(t)+\gamma\,\omega(t)\le g(t)
$$

is strengthened to

$$
\mathrm{deriv}\omega(t)+\gamma\,\omega(t)\le |g(t)|
$$

for every $t\ge 0$. This uses the elementary inequality $g(t)\le |g(t)|$. The proof introduces an arbitrary $t\ge0$, applies the assumed inequality at $t$, and then transits to $|g(t)|$. The resulting hypothesis is exactly the absolute-value form required by the damped comparison lemma.

The damped comparison lemma is then applied with $\omega$, $g$, and $\gamma$. Its content, specialized here, is: if $\omega$ is $C^1$ on $[0,\infty)$, if

$$
\mathrm{deriv}\omega(t)+\gamma\,\omega(t)\le |g(t)|
$$

for all $t\ge0$, and if $g$ is integrable on $[0,\infty)$, then for every $t\ge0$,

$$
\omega(t)\le e^{-\gamma t}\omega(0)
+\int_0^t e^{-\gamma(t-s)}|g(s)|\,ds.
$$

This is the damped Gronwall estimate: the value $\omega(t)$ is bounded by the exponentially decayed initial value plus the causal convolution of the absolute forcing. It supplies a pointwise upper bound on $\omega(t)$.

The causal-convolution integrability lemma is applied next. Its content, specialized to $g$ and $\gamma$, is: if $\gamma>0$ and $g$ is integrable on $[0,\infty)$, then

$$
t\mapsto \int_0^t e^{-\gamma(t-s)}|g(s)|\,ds
$$

is integrable on $[0,\infty)$. Thus the convolution part of the comparison estimate is itself an integrable function of $t$.

The proof then shows that the exponential decay factor $t\mapsto e^{-\gamma t}$ is integrable on $[0,\infty)$. It first rewrites integrability on the closed ray $[0,\infty)$ as integrability on the open ray $(0,\infty)$, since the single point $0$ has Lebesgue measure zero. Then it uses the standard fact that for $a<0$, the function $x\mapsto e^{a x}$ is integrable on a ray $(b,\infty)$. Here $a=-\gamma$, and $a<0$ follows from $\gamma>0$ by linear arithmetic. Taking $b=0$ gives integrability of $t\mapsto e^{-\gamma t}$ on $(0,\infty)$, hence on $[0,\infty)$.

Multiplying this integrable function by the constant $\max(\omega(0),0)$ gives another integrable function:

$$
t\mapsto e^{-\gamma t}\max(\omega(0),0).
$$

The simplification only rewrites $(-\gamma)t$ as $-\gamma t$. This is the initial-value term in the comparison bound, and it is integrable because a constant multiple of an integrable function is integrable.

Adding the integrable initial term and the integrable causal convolution gives the majorant

$$
M(t)=e^{-\gamma t}\max(\omega(0),0)
+\int_0^t e^{-\gamma(t-s)}|g(s)|\,ds,
$$

which is integrable on $[0,\infty)$. This function is the explicit dominating function for the positive part of $\omega$.

The proof also verifies that the convolution term is nonnegative for every $t\ge0$:

$$
0\le \int_0^t e^{-\gamma(t-s)}|g(s)|\,ds.
$$

Indeed, for $s\in[0,t]$, the exponential factor is positive and $|g(s)|\ge0$, so the integrand is nonnegative. Since $t\ge0$, the interval integral from $0$ to $t$ is therefore nonnegative. This fact is used to show that the majorant $M(t)$ is nonnegative.

The key pointwise estimate is then

$$
\max(\omega(t),0)\le M(t)
$$

for every $t\ge0$. To prove an inequality of the form $\max(a,0)\le B$, it suffices to prove both $a\le B$ and $0\le B$. The first part follows from the comparison estimate:

$$
\omega(t)\le e^{-\gamma t}\omega(0)
+\int_0^t e^{-\gamma(t-s)}|g(s)|\,ds.
$$

Since $\omega(0)\le \max(\omega(0),0)$ and $e^{-\gamma t}\ge0$, the product increases when $\omega(0)$ is replaced by $\max(\omega(0),0)$. The convolution term is unchanged. Hence

$$
\omega(t)\le e^{-\gamma t}\max(\omega(0),0)
+\int_0^t e^{-\gamma(t-s)}|g(s)|\,ds=M(t).
$$

The second part, $0\le M(t)$, follows because both summands are nonnegative: the product $e^{-\gamma t}\max(\omega(0),0)$ is nonnegative, and the convolution integral was shown to be nonnegative. Therefore the maximum is at most $M(t)$.

Next, the proof establishes the measurability requirement for the positive part. Since $\omega$ is $C^1$ on $[0,\infty)$, it is continuous within $[0,\infty)$ at every point of that set. The constant function $0$ is also continuous, so the pointwise maximum $\max(\omega(t),0)$ is continuous on $[0,\infty)$. A function continuous on a measurable set is almost-everywhere strongly measurable with respect to the Lebesgue measure restricted to that set. Thus the positive part is AEStronglyMeasurable on $[0,\infty)$.

The pointwise estimate is then upgraded to an almost-everywhere norm estimate. For almost every $t$ with respect to the restricted measure, one has $t\in[0,\infty)$. At such $t$,

$$
\|\max(\omega(t),0)\|=\max(\omega(t),0),
$$

because the maximum is nonnegative. The proof rewrites the norm as an absolute value and uses nonnegativity of $\max(\omega(t),0)$. Combining this with the pointwise estimate gives

$$
\|\max(\omega(t),0)\|\le M(t)
$$

almost everywhere on $[0,\infty)$.

Finally, the integrability comparison theorem is applied: if a function is almost-everywhere strongly measurable and its norm is almost-everywhere bounded by an integrable function, then it is integrable. Here the integrable majorant is $M(t)$, and the function being dominated is $t\mapsto \max(\omega(t),0)$. Therefore

$$
t\mapsto \max(\omega(t),0)
$$

is integrable on $[0,\infty)$, which is exactly the desired conclusion.

