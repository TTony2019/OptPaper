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
The declaration `subgradient_chain_rule` is a subgradient chain rule for an extended-real-valued convex function along an absolutely continuous path.

Let $H$ be a complete real inner product space. Let

$$
\Phi : H \to \{\,y \in \overline{\mathbb R} \mid -\infty < y\,\}
$$

be an extended-real function whose values are never $-\infty$. The hypothesis `hPhi : Phi ∈ gammaZero H` is the Gamma-zero regularity assumption on $\Phi$; in the supplied context the gamma class is defined by convexity and lower semicontinuity, so this is the convexity/lower-semicontinuity content available for $\Phi$.

Let $x,v:\mathbb R\to H$ be two paths and let $b\in\mathbb R$. The assumptions are:

- `hb : 0 < b`, so the interval $[0,b]$ is nondegenerate.
- `hx_ac : AbsolutelyContinuousOnInterval x 0 b`, so $x$ is absolutely continuous on $[0,b]$.
- `hsubgradient : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), v t ∈ subdifferential Phi (x t)`, so for almost every $t\in[0,b]$, the vector $v(t)$ is a subgradient of $\Phi$ at $x(t)$.
- `hdom : ∀ t ∈ Set.Icc 0 b, x t ∈ effectiveDomain Phi`, so the path stays in the effective domain of $\Phi$ on the whole interval; in this extended-real setting this is the finite-domain condition for $\Phi$.
- `hx_deriv : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), HasDerivAt x (deriv x t) t`, so $x$ is differentiable at almost every $t\in[0,b]$, with derivative $\mathrm{deriv}x(t)$.
- `hvL2 : MemLp v 2 (volume.restrict (Set.Icc 0 b))`, so $v\in L^2([0,b])$.
- `hdxL2 : MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b))`, so $\mathrm{deriv}x\in L^2([0,b])$.

The conclusion is the conjunction of two facts. First,

$$
t\mapsto (\Phi(x(t)):\overline{\mathbb R}).toReal
$$

is absolutely continuous on $[0,b]$. Second, for almost every $t\in[0,b]$,

$$
\mathrm{deriv}\!\left(t\mapsto (\Phi(x(t)):\overline{\mathbb R}).toReal\right)(t)
=\langle v(t), \mathrm{deriv}x(t)\rangle_{\mathbb R}.
$$

Thus the energy $t\mapsto \Phi(x(t))$, viewed as a real-valued function on the interval, is absolutely continuous and satisfies the expected chain rule almost everywhere.

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
The proof first proves the absolute continuity of the real-valued energy, and then uses a separate cited theorem to obtain the almost-everywhere derivative formula.

At the start, the proof introduces

$$
F(t)=(\Phi(x(t)):\overline{\mathbb R}).toReal.
$$

The goal is to prove that $F$ is absolutely continuous on $[0,b]$, and then that its derivative is $\langle v(t),\mathrm{deriv}x(t)\rangle$ almost everywhere.

To prove absolute continuity, the proof introduces the majorant

$$
M(r)=\|v(r)\|\,\|\mathrm{deriv}x(r)\|.
$$

It first shows that $M$ is integrable on $[0,b]$. From `hvL2` and `hdxL2`, using `memLp_two_iff_integrable_sq_norm`, the proof obtains integrability of

$$
r\mapsto \|v(r)\|^2
\qquad\text{and}\qquad
r\mapsto \|\mathrm{deriv}x(r)\|^2
$$

on $[0,b]$. That theorem says that for an almost-everywhere strongly measurable function, membership in $L^2$ is equivalent to integrability of the square of its norm. The proof supplies the almost-everywhere strong measurability coming from `hvL2.aestronglyMeasurable` and `hdxL2.aestronglyMeasurable`.

Adding these two integrable functions and dividing by $2$, the proof gets integrability of

$$
r\mapsto \frac{\|v(r)\|^2+\|\mathrm{deriv}x(r)\|^2}{2}.
$$

This is used as an integrable upper bound for $M$. Indeed, for every $r$,

$$
\|v(r)\|\,\|\mathrm{deriv}x(r)\|
\le
\frac{\|v(r)\|^2+\|\mathrm{deriv}x(r)\|^2}{2},
$$

which follows from

$$
0\le (\|v(r)\|-\|\mathrm{deriv}x(r)\|)^2
=\|v(r)\|^2-2\|v(r)\|\,\|\mathrm{deriv}x(r)\|+\|\mathrm{deriv}x(r)\|^2.
$$

The proof uses `Integrable.mono'` with this majorant and with the measurability of the product of the norm functions to conclude

$$
M\in L^1([0,b]).
$$

The tactic `filter_upwards with r` proves the pointwise almost-everywhere domination, `rw [abs_of_nonneg ...]` removes the absolute value because $M(r)\ge0$, and `nlinarith [sq_nonneg (...)]` proves the displayed inequality.

Next, the proof notes that the interval $[0,b]$ has nonzero Lebesgue measure because $0<b$. It rewrites the volume of the interval using `Real.volume_Icc` and applies `ENNReal.ofReal_ne_zero_iff`, reducing the claim to $b>0$. Since `hsubgradient` holds almost everywhere on a set of nonzero measure, `Measure.exists_mem_of_measure_ne_zero_of_ae` gives a point

$$
r\in[0,b]
$$

such that

$$
v(r)\in\partial\Phi(x(r)).
$$

This point is used as a witness that a subgradient exists somewhere on the interval.

The proof then defines positive Moreau parameters

$$
\gamma_n=\frac{1}{n+1}.
$$

The statement `hgamma` records that $\gamma_n\to0$ as $n\to\infty$, using the standard limit `tendsto_one_div_add_atTop_nhds_zero_nat`.

For those parameters, the proof defines

$$
F_n(t)=\bigl({}^{\gamma_n}\Phi\bigr)(x(t)).toReal,
$$

the real-valued Moreau envelope of $\Phi$ along the path $x(t)$.

It next proves pointwise convergence $F_n(t)\to F(t)$ for every $t\in[0,b]$. This uses `moreauEnvelope_toReal_tendsto_of_mem_effectiveDomain`. That cited result says that if $\Phi$ is in the Gamma-zero class, if $\gamma_n>0$ tends to $0$, if $w\in\partial\Phi(z)$ for some point $z$, and if $y$ belongs to the effective domain of $\Phi$, then

$$
\bigl({}^{\gamma_n}\Phi\bigr)(y).toReal
\longrightarrow
(\Phi(y):\overline{\mathbb R}).toReal.
$$

The proof applies this with $z=x(r)$, $w=v(r)$, using the previously obtained subgradient witness $v(r)\in\partial\Phi(x(r))$, and with $y=x(t)$, using `hdom t ht` to know $x(t)$ is in the effective domain. Thus for each $t\in[0,b]$, $F_n(t)\to F(t)$.

The proof then establishes the increment estimate

$$
|F_n(t)-F_n(s)|\le \int_s^t M(q)\,dq
$$

whenever $s,t\in[0,b]$ and $s\le t$. This comes from `moreauEnvelope_comp_ac_and_increment_bound`. That cited theorem states that, under the Gamma-zero assumption on $\Phi$, for a positive Moreau parameter $\gamma$, if $x$ is absolutely continuous on $[0,b]$, if the subgradient inclusion holds almost everywhere, if $x$ is differentiable almost everywhere with derivative $\mathrm{deriv}x$, and if $M$ is integrable on $[0,b]$, then the composed Moreau envelope $t\mapsto({}^\gamma\Phi)(x(t)).toReal$ is absolutely continuous on $[0,b]$ and satisfies exactly the displayed increment bound. The proof applies this with $\gamma=\gamma_n$, using `hb.le`, `hx_ac`, `hsubgradient`, `hx_deriv`, and the previously proved integrability of $M$, and then extracts the second component of the conclusion.

At this point the proof has pointwise convergence $F_n\to F$ on $[0,b]$ and uniform interval-integral increment bounds for the $F_n$ by the integrable function $M$. It applies
`absolutelyContinuousOnInterval_of_pointwise_limit_of_abs_sub_le_intervalIntegral`. The visible content of that lemma is that if $0\le b$, if $M$ is integrable on $[0,b]$, if $F_n\to F$ pointwise on $[0,b]$, and if each $F_n$ satisfies an estimate of the form above, then the limit function $F$ is absolutely continuous on $[0,b]$. This gives the desired absolute continuity of

$$
F(t)=(\Phi(x(t)):\overline{\mathbb R}).toReal.
$$

Finally, `constructor` splits the desired conjunction. The first branch is closed by the already proved absolute continuity of $F$. The second branch uses `deriv_energy_eq_inner_of_absolutelyContinuous`. That cited theorem says that under the same hypotheses on $\Phi$, $x$, $v$, $b$, the almost-everywhere subgradient condition, the effective-domain condition, the almost-everywhere differentiability of $x$, and the absolute continuity of $F(t)=(\Phi(x(t))).toReal$ on $[0,b]$, one has, for almost every $t\in[0,b]$,

$$
\mathrm{deriv} F(t)=\langle v(t),\mathrm{deriv}x(t)\rangle_{\mathbb R}.
$$

The proof supplies exactly those hypotheses, including the just-established absolute continuity of $F$, and then uses `simpa [F]` to unfold the local definition of $F$ so that the cited conclusion matches the required goal. This completes the proof of the subgradient chain rule.

