## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_1.lean`

## Lean statement
```lean
theorem theorem_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ)
    (z dz : ℝ → H) (hf : ContDiff ℝ 1 f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x)
    (hgradient_lip : LocallyLipschitz (gradient f))
    (hinitial : r < ‖gradient f (z t₀)‖)
    (hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (gradient f (z t)) (dz t)) t)
    (hcomp_cont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀))
    (hsol : IsDrygradTrajectory r hr f (hf.differentiable (by norm_num)) z dz t₀)
    (V : H → H) (hV_lip : LocallyLipschitz V)
    (hV_zero : ∀ x, V x = 0 ↔ ‖gradient f x‖ ≤ r)
    (hvelocity : ∀ t ∈ Set.Ici t₀, dz t = V (z t))
    (hvelocity_limit : Filter.Tendsto dz Filter.atTop (nhds 0))
    (hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 →
      ∀ t ∈ Set.Ici S, z t = z S) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀) ∧
      MeasureTheory.IntegrableOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀) ∧
      MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ici t₀) ∧
      ∃ zLimit, Filter.Tendsto z Filter.atTop (nhds zLimit) ∧ ‖gradient f zLimit‖ = r ∧
        ((∃ T ∈ Set.Ici t₀, ∀ t ∈ Set.Ici T, z t = zLimit) ∨
          ∀ t ∈ Set.Ici t₀, r < ‖gradient f (z t)‖)
```

## Statement explanation
The theorem assumes a type \(H\) equipped with a normed additive commutative group structure, a real inner product space structure, and completeness. There are real parameters \(t_0\) and \(r\), with \(r>0\). The data include a function \(f:H\to\mathbb R\), a trajectory \(z:\mathbb R\to H\), and a velocity \(dz:\mathbb R\to H\). The hypotheses are:

- \(f\) is \(C^1\), i.e. `ContDiff ℝ 1 f`.
- \(f\) is bounded below: there exists \(m\in\mathbb R\) such that \(m\le f(x)\) for all \(x\in H\).
- The gradient \(\nabla f\) is locally Lipschitz.
- Initially the gradient norm is larger than \(r\): \(r<\|\nabla f(z(t_0))\|\).
- For every \(t\ge t_0\), the derivative of \(s\mapsto f(z(s))\) at \(t\) is the inner product \(\langle \nabla f(z(t)), dz(t)\rangle\).
- The composition \(t\mapsto f(z(t))\) is continuous on \([t_0,\infty)\).
- The trajectory \(z\) is a dry-gradient trajectory with threshold \(r\), velocity \(dz\), and initial time \(t_0\), expressed by the predicate `IsDrygradTrajectory`.
- There is a velocity field \(V:H\to H\), locally Lipschitz, such that \(V(x)=0\) if and only if \(\|\nabla f(x)\|\le r\).
- For all \(t\ge t_0\), \(dz(t)=V(z(t))\).
- The velocity tends to zero at infinity: \(dz(t)\to 0\) as \(t\to\infty\).
- If for some \(S\ge t_0\) one has \(V(z(S))=0\), then the trajectory is constant from \(S\) onward: for all \(t\ge S\), \(z(t)=z(S)\).

The conclusion has four parts:

1. The energy \(t\mapsto f(z(t))\) is nonincreasing on \([t_0,\infty)\).
2. The function \(t\mapsto \|dz(t)\|^2\) is Lebesgue integrable on \([t_0,\infty)\).
3. The function \(t\mapsto \|dz(t)\|\) is Lebesgue integrable on \([t_0,\infty)\).
4. The trajectory \(z(t)\) has a limit \(z_{\mathrm{limit}}\) as \(t\to\infty\), and \(\|\nabla f(z_{\mathrm{limit}})\|=r\). Moreover, either the trajectory is eventually constant equal to \(z_{\mathrm{limit}}\), or \(\|\nabla f(z(t))\|>r\) for every \(t\ge t_0\).

## Lean proof
```lean
by
  have hanti : AntitoneOn (fun t => f (z t)) (Set.Ici t₀) :=
    drygrad_energy_antitone f z dz hr (hf.differentiable (by norm_num)) hsol hchain hcomp_cont
  have hVcont : Continuous V := hV_lip.continuous
  have hzcont : ContinuousOn z (Set.Ici t₀) := by
    intro t ht
    exact (hsol t ht).1.continuousAt.continuousWithinAt
  have hdzcont : ContinuousOn dz (Set.Ici t₀) := by
    have hVz : ContinuousOn (fun t => V (z t)) (Set.Ici t₀) :=
      hVcont.comp_continuousOn hzcont
    exact hVz.congr (by
      intro t ht
      exact hvelocity t ht)
  have hnormcont : ContinuousOn (fun t => ‖dz t‖) (Set.Ici t₀) := hdzcont.norm
  have hsqcont : ContinuousOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀) :=
    hnormcont.pow 2
  obtain ⟨m, hm⟩ := hf_lower
  have hprefix : ∀ T : ℝ, t₀ ≤ T →
      ∫ t in t₀..T, (‖dz t‖ ^ 2 + r * ‖dz t‖) ≤ f (z t₀) - m := by
    intro T hT
    have hfgcont : ContinuousOn (fun t => gradient f (z t)) (Set.Icc t₀ T) :=
      hgradient_lip.continuous.comp_continuousOn (hzcont.mono Set.Icc_subset_Ici_self)
    have hdzIcc : ContinuousOn dz (Set.Icc t₀ T) := hdzcont.mono Set.Icc_subset_Ici_self
    have hintercont : ContinuousOn (fun t => inner ℝ (gradient f (z t)) (dz t))
        (Set.Icc t₀ T) := hfgcont.inner hdzIcc
    have hderivcont : ContinuousOn (deriv (fun s => f (z s))) (Set.Icc t₀ T) :=
      hintercont.congr (by
        intro t ht
        exact (hchain t (Set.Icc_subset_Ici_self ht)).deriv)
    have hleftint : IntervalIntegrable (fun t => ‖dz t‖ ^ 2 + r * ‖dz t‖)
        MeasureTheory.volume t₀ T := by
      apply ContinuousOn.intervalIntegrable_of_Icc hT
      exact hsqcont.mono Set.Icc_subset_Ici_self |>.add
        ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)))
    have hrightint : IntervalIntegrable (fun t => - deriv (fun s => f (z s)) t)
        MeasureTheory.volume t₀ T :=
      (hderivcont.neg).intervalIntegrable_of_Icc hT
    have hpoint : ∀ t ∈ Set.Icc t₀ T,
        ‖dz t‖ ^ 2 + r * ‖dz t‖ ≤ - deriv (fun s => f (z s)) t := by
      intro t ht
      have h := drygrad_energy_deriv_le f z dz hr (hf.differentiable (by norm_num)) hsol hchain
        (Set.Icc_subset_Ici_self ht)
      linarith
    have hint := intervalIntegral.integral_mono_on hT hleftint hrightint hpoint
    have hftc : ∫ t in t₀..T, deriv (fun s => f (z s)) t = f (z T) - f (z t₀) :=
      intervalIntegral.integral_deriv_eq_sub
        (fun t ht => by
          rw [Set.uIcc_of_le hT] at ht
          exact (hchain t (Set.Icc_subset_Ici_self ht)).differentiableAt)
        (hderivcont.intervalIntegrable_of_Icc hT)
    rw [intervalIntegral.integral_neg, hftc] at hint
    have hbound : f (z t₀) - f (z T) ≤ f (z t₀) - m := by linarith [hm (z T)]
    calc
      ∫ t in t₀..T, (‖dz t‖ ^ 2 + r * ‖dz t‖) ≤
          -(f (z T) - f (z t₀)) := hint
      _ = f (z t₀) - f (z T) := by ring
      _ ≤ f (z t₀) - m := hbound
  have hsqprefix : ∀ T : ℝ, t₀ ≤ T → ∫ t in t₀..T, ‖dz t‖ ^ 2 ≤ f (z t₀) - m := by
    intro T hT
    have hnonneg : 0 ≤ ∫ t in t₀..T, r * ‖dz t‖ :=
      intervalIntegral.integral_nonneg hT (fun t _ => mul_nonneg hr.le (norm_nonneg _))
    have hadd := hprefix T hT
    have hadd' : (∫ t in t₀..T, ‖dz t‖ ^ 2) +
        (∫ t in t₀..T, r * ‖dz t‖) ≤ f (z t₀) - m := by
      calc
        (∫ t in t₀..T, ‖dz t‖ ^ 2) + (∫ t in t₀..T, r * ‖dz t‖) =
            ∫ t in t₀..T, (‖dz t‖ ^ 2 + r * ‖dz t‖) :=
          (intervalIntegral.integral_add
            ((hsqcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)
            ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)).symm
        _ ≤ f (z t₀) - m := hadd
    linarith
  have hnormprefix : ∀ T : ℝ, t₀ ≤ T → ∫ t in t₀..T, ‖dz t‖ ≤ (f (z t₀) - m) / r := by
    intro T hT
    have hnonneg : 0 ≤ ∫ t in t₀..T, ‖dz t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
    have hadd := hprefix T hT
    have hadd' : (∫ t in t₀..T, ‖dz t‖ ^ 2) +
        r * (∫ t in t₀..T, ‖dz t‖) ≤ f (z t₀) - m := by
      rw [← intervalIntegral.integral_const_mul]
      calc
        (∫ t in t₀..T, ‖dz t‖ ^ 2) + (∫ t in t₀..T, r * ‖dz t‖) =
            ∫ t in t₀..T, (‖dz t‖ ^ 2 + r * ‖dz t‖) :=
          (intervalIntegral.integral_add
            ((hsqcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)
            ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)).symm
        _ ≤ f (z t₀) - m := hadd
    exact (le_div_iff₀ hr).mpr (by linarith)
  have hsqint : MeasureTheory.IntegrableOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀) :=
    integrableOn_Ici_of_nonneg_prefix_bound hsqcont (fun _ _ => sq_nonneg _) hsqprefix
  have hnormint : MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ici t₀) :=
    integrableOn_Ici_of_nonneg_prefix_bound hnormcont (fun _ _ => norm_nonneg _) hnormprefix
  refine ⟨hanti, hsqint, hnormint, ?_⟩
  let zLimit := Filter.atTop.limUnder z
  have hnormint' : MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ioi t₀) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    exact hnormint
  have hdzint' : MeasureTheory.IntegrableOn dz (Set.Ioi t₀) := by
    rw [MeasureTheory.IntegrableOn]
    apply (MeasureTheory.integrable_norm_iff
      ((hdzcont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)).mp
    exact hnormint'.integrable
  have hzlim : Filter.Tendsto z Filter.atTop (nhds zLimit) :=
    MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
      (f := z) (f' := dz) (a := t₀)
      (fun t ht => (hsol t (show t ∈ Set.Ici t₀ from
        le_of_lt (show t₀ < t from ht))).1) hdzint'
  have hVzlim : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds (V zLimit)) :=
    (hVcont.tendsto zLimit).comp hzlim
  have hdzV : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds 0) := by
    apply hvelocity_limit.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨t₀, fun t ht => ht⟩] with t ht
    exact hvelocity t ht
  have hVzero : V zLimit = 0 := tendsto_nhds_unique hVzlim hdzV
  have hball : ‖gradient f zLimit‖ ≤ r := (hV_zero zLimit).mp hVzero
  have hqcont : Continuous (fun x : H => ‖gradient f x‖) := hgradient_lip.continuous.norm
  have hqlim : Filter.Tendsto (fun t => ‖gradient f (z t)‖) Filter.atTop
      (nhds ‖gradient f zLimit‖) := (hqcont.tendsto zLimit).comp hzlim
  by_cases hhit : ∃ T ∈ Set.Ici t₀, ‖gradient f (z T)‖ ≤ r
  · rcases hhit with ⟨T, hT, hTball⟩
    have hqIcc : ContinuousOn (fun t => ‖gradient f (z t)‖) (Set.Icc t₀ T) :=
      hqcont.comp_continuousOn (hzcont.mono Set.Icc_subset_Ici_self)
    have hrmem : r ∈ Set.Icc (‖gradient f (z T)‖) (‖gradient f (z t₀)‖) :=
      ⟨hTball, hinitial.le⟩
    rcases intermediate_value_Icc' hT hqIcc hrmem with ⟨S, hS, hqS⟩
    have hVSzero : V (z S) = 0 := (hV_zero (z S)).mpr (le_of_eq hqS)
    have hev : z =ᶠ[Filter.atTop] fun _ : ℝ => z S := by
      filter_upwards [Filter.eventually_atTop.2 ⟨S, fun t ht => ht⟩] with t ht
      exact hstationary S hS.1 hVSzero t ht
    have hzS : Filter.Tendsto z Filter.atTop (nhds (z S)) :=
      tendsto_const_nhds.congr' hev.symm
    have hzEq : zLimit = z S := tendsto_nhds_unique hzlim hzS
    refine ⟨zLimit, hzlim, ?_, Or.inl ⟨S, hS.1, ?_⟩⟩
    · rw [hzEq]
      exact hqS
    · intro t ht
      rw [hzEq]
      exact hstationary S hS.1 hVSzero t ht
  · have hexterior : ∀ t ∈ Set.Ici t₀, r < ‖gradient f (z t)‖ := by
      intro t ht
      exact lt_of_not_ge (fun h => hhit ⟨t, ht, h⟩)
    have hlower : r ≤ ‖gradient f zLimit‖ := by
      by_contra hnot
      have hless : ‖gradient f zLimit‖ < r := lt_of_not_ge hnot
      have hevent : ∀ᶠ t in Filter.atTop, ‖gradient f (z t)‖ < r :=
        (tendsto_order.1 hqlim).2 r hless
      have htail : ∀ᶠ t in Filter.atTop, t ∈ Set.Ici t₀ :=
        Filter.eventually_atTop.2 ⟨t₀, fun t ht => ht⟩
      rcases (hevent.and htail).exists with ⟨t, ht, ht0⟩
      exact (not_lt_of_ge (le_of_lt (hexterior t ht0))) ht
    refine ⟨zLimit, hzlim, le_antisymm hball hlower, Or.inr hexterior⟩
```

## Proof explanation
The proof first obtains the monotonicity of the energy along the trajectory. This is done by applying the earlier lemma `drygrad_energy_antitone` to the assumptions `hsol`, `hchain`, and `hcomp_cont`. This yields that \(t\mapsto f(z(t))\) is antitone on \([t_0,\infty)\).

Next, the proof establishes continuity facts. Since \(V\) is locally Lipschitz, it is continuous. The dry-gradient trajectory assumption gives continuity of \(z\) at every point \(t\ge t_0\), hence \(z\) is continuous on \([t_0,\infty)\). Since \(dz(t)=V(z(t))\) on \([t_0,\infty)\), and both \(V\) and \(z\) are continuous, \(dz\) is continuous on \([t_0,\infty)\). Consequently \(\|dz\|\) and \(\|dz\|^2\) are also continuous there.

The proof then takes a lower bound \(m\) for \(f\) from `hf_lower`. The main technical step is to prove a uniform integral bound over finite intervals \([t_0,T]\). For any \(T\ge t_0\), it shows

\[
\int_{t_0}^{T} \bigl(\|dz(t)\|^2 + r\|dz(t)\|\bigr)\,dt
\le f(z(t_0))-m.
\]

To prove this, the proof uses the chain-rule hypothesis `hchain` to identify the derivative of \(t\mapsto f(z(t))\) with the inner product \(\langle \nabla f(z(t)), dz(t)\rangle\). Continuity of the gradient and of \(z\) gives continuity of this derivative on \([t_0,T]\). A separate dry-gradient derivative lemma, `drygrad_energy_deriv_le`, supplies the pointwise inequality

\[
\|dz(t)\|^2+r\|dz(t)\|\le -\frac{d}{dt} f(z(t)).
\]

The proof then integrates this pointwise inequality over \([t_0,T]\) using `intervalIntegral.integral_mono_on`. The fundamental theorem of calculus, applied through `intervalIntegral.integral_deriv_eq_sub`, gives

\[
\int_{t_0}^{T} \frac{d}{dt} f(z(t))\,dt
=
f(z(T))-f(z(t_0)).
\]

Therefore the integral of the negative derivative is \(f(z(t_0))-f(z(T))\). Since \(m\le f(z(T))\), this is at most \(f(z(t_0))-m\). The command `calc` chains these inequalities, and `linarith` handles linear arithmetic.

From this combined integral bound, two separate bounds are extracted. Because \(r\|dz\|\) is nonnegative, the integral of \(\|dz\|^2\) over \([t_0,T]\) is also bounded by \(f(z(t_0))-m\). Because \(\|dz\|^2\) is nonnegative, the integral of \(r\|dz\|\) is bounded by the same constant, so

\[
\int_{t_0}^{T} \|dz(t)\|\,dt
\le
\frac{f(z(t_0))-m}{r}.
\]

Here positivity of \(r\) is used. The proof uses `linarith` to combine inequalities and the lemma `le_div_iff₀` to divide by the positive number \(r\).

These finite-interval bounds, together with continuity and nonnegativity, are then passed to a lemma `integrableOn_Ici_of_nonneg_prefix_bound`. This proves the two desired integrability statements on \([t_0,\infty)\).

The proof then turns to the existence of a limit for \(z(t)\). It defines

\[
z_{\mathrm{limit}} := \lim_{\mathcal F_{\mathrm{atTop}}} z,
\]

where Lean uses `Filter.atTop.limUnder`. The integrability of \(\|dz\|\) on \([t_0,\infty)\) is transferred to the open interval \((t_0,\infty)\). Since \(dz\) is continuous and \(\|dz\|\) is integrable, \(dz\) itself is integrable on \((t_0,\infty)\). The proof applies the lemma `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi` to conclude that \(z(t)\to z_{\mathrm{limit}}\) as \(t\to\infty\).

Next, the proof compares two limits of \(V(z(t))\). On one hand, because \(V\) is continuous and \(z(t)\to z_{\mathrm{limit}}\),

\[
V(z(t))\to V(z_{\mathrm{limit}}).
\]

On the other hand, since \(dz(t)\to 0\) and \(dz(t)=V(z(t))\) eventually for all large \(t\),

\[
V(z(t))\to 0.
\]

By uniqueness of limits, \(V(z_{\mathrm{limit}})=0\). The equivalence `hV_zero` then gives

\[
\|\nabla f(z_{\mathrm{limit}})\|\le r.
\]

It remains to prove equality with \(r\). The norm of the gradient is continuous because the gradient is locally Lipschitz, so

\[
\|\nabla f(z(t))\|\to \|\nabla f(z_{\mathrm{limit}})\|.
\]

The proof splits into two cases.

In the first case, there exists some time \(T\ge t_0\) with \(\|\nabla f(z(T))\|\le r\). Since initially \(\|\nabla f(z(t_0))\|>r\) and the gradient norm along \(z\) is continuous on \([t_0,T]\), the intermediate value theorem gives a time \(S\in[t_0,T]\) such that

\[
\|\nabla f(z(S))\|=r.
\]

Then \(V(z(S))=0\). By the stationary assumption, \(z(t)=z(S)\) for every \(t\ge S\). Therefore the trajectory is eventually constant, so its limit \(z_{\mathrm{limit}}\) equals \(z(S)\). Hence \(\|\nabla f(z_{\mathrm{limit}})\|=r\), and the first alternative of the conclusion holds.

In the second case, no such time \(T\) exists. Then for every \(t\ge t_0\),

\[
r<\|\nabla f(z(t))\|.
\]

The proof argues by contradiction that \(r\le \|\nabla f(z_{\mathrm{limit}})\|\). If instead \(\|\nabla f(z_{\mathrm{limit}})\|<r\), then eventually \(\|\nabla f(z(t))\|<r\), because the gradient norm tends to the limit norm. But this contradicts the fact that for all large \(t\ge t_0\), the gradient norm is greater than \(r\). Therefore

\[
r\le \|\nabla f(z_{\mathrm{limit}})\|.
\]

Combining this with the earlier inequality \(\|\nabla f(z_{\mathrm{limit}})\|\le r\) gives equality. The second alternative of the conclusion holds in this case. The proof uses `by_contra` for the contradiction, `tendsto_order` to extract the eventual inequality, and `filter_upwards` to combine eventually-at-top properties. The final `refine` assembles the four parts of the conclusion.

