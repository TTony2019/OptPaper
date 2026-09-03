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
The theorem is stated in a complete real inner-product space. Concretely, the variables and assumptions are:

- `H : Type*` is a type equipped with `[NormedAddCommGroup H]`, `[InnerProductSpace ℝ H]`, and `[CompleteSpace H]`; thus `H` is a real Hilbert space, with norm and inner product denoted by `‖·‖` and `inner ℝ · ·`.
- `t₀` and `r` are real numbers, and `hr : 0 < r` says the radius parameter `r` is strictly positive.
- `f : H → ℝ` is a real-valued function on `H`. The assumption `hf : ContDiff ℝ 1 f` means `f` is continuously differentiable. `hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x` says `f` is bounded below.
- `hgradient_lip : LocallyLipschitz (gradient f)` says the gradient of `f` is locally Lipschitz.
- `z dz : ℝ → H` are time-dependent curves in `H`. Here `z` is the position curve and `dz` is its velocity-like curve.
- `hinitial : r < ‖gradient f (z t₀)‖` says that at the initial time `t₀`, the norm of the gradient of `f` at the initial position is strictly larger than `r`.
- `hchain` states that for every `t` with `t ≥ t₀`, the derivative at `t` of the scalar function `s ↦ f (z s)` is exactly `inner ℝ (gradient f (z t)) (dz t)`, i.e. the time derivative of `f ∘ z` is given by the inner product of the spatial gradient and the velocity.
- `hcomp_cont` says `f (z t)` is continuous as a function of `t` on the set `Set.Ici t₀ = {t : ℝ | t₀ ≤ t}`.
- `hsol : IsDrygradTrajectory r hr f (hf.differentiable (by norm_num)) z dz t₀` is an assumption using the custom predicate `IsDrygradTrajectory`; in the surrounding formalization this encodes that `(z,dz)` is a drygrad trajectory for `f` starting at `t₀` with parameter `r`.
- `V : H → H` is a vector field, and `hV_lip : LocallyLipschitz V` says it is locally Lipschitz.
- `hV_zero : ∀ x, V x = 0 ↔ ‖gradient f x‖ ≤ r` identifies the zero set of `V` with the set of points where the gradient norm is at most `r`.
- `hvelocity` says that for every `t ≥ t₀`, `dz t = V (z t)`, so the velocity is the vector field evaluated along the trajectory.
- `hvelocity_limit` says `dz` tends to `0` as `t → +∞`, i.e. `Filter.Tendsto dz Filter.atTop (nhds 0)`.
- `hstationary` says that if at some time `S ≥ t₀` the vector field vanishes at `z S`, i.e. `V (z S) = 0`, then the trajectory is frozen forever after: `z t = z S` for every `t ≥ S`.

The conclusion is a conjunction of four statements:

1. `AntitoneOn (fun t => f (z t)) (Set.Ici t₀)`: the function `t ↦ f (z t)` is antitone, hence nonincreasing, on `[t₀, ∞)`.
2. `MeasureTheory.IntegrableOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀)`: the function `‖dz t‖²` is Lebesgue integrable over `[t₀, ∞)`.
3. `MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ici t₀)`: the norm `‖dz t‖` is integrable over `[t₀, ∞)`.
4. There exists a limit point `zLimit` in `H` such that:
   - `z t` tends to `zLimit` as `t → +∞`;
   - `‖gradient f zLimit‖ = r`;
   - and either the trajectory reaches this limit in finite time and remains there — there is `T ≥ t₀` such that `z t = zLimit` for all `t ≥ T` — or the trajectory never enters the region where the gradient norm is at most `r`: for every `t ≥ t₀`, one has `r < ‖gradient f (z t)‖`.

Thus the theorem says that under a drygrad dynamics with a locally Lipschitz damping field whose zero set is the gradient-n

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
No proof explanation was returned by the model.

