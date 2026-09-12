## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_1.lean`

## Lean statement
```lean
theorem theorem_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ)
    (z : ℝ → H) (hf : ContDiff ℝ 1 f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x)
    (hgradient_lip : LocallyLipschitz (gradient f))
    (hz_diff : Differentiable ℝ z)
    (hinitial : r < ‖gradient f (z t₀)‖)
    (hsol : IsDrygradTrajectory r f z t₀) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀) ∧
      MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖ ^ 2) (Set.Ici t₀) ∧
      MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖) (Set.Ici t₀) ∧
      ∃ zLimit, Filter.Tendsto z Filter.atTop (nhds zLimit) ∧ ‖gradient f zLimit‖ = r ∧
        ((∃ T ∈ Set.Ici t₀, ∀ t ∈ Set.Ici T, z t = zLimit) ∨
          ∀ t ∈ Set.Ici t₀, r < ‖gradient f (z t)‖)
```

## Statement explanation
This declaration is a convergence and energy-dissipation theorem for a dry-gradient trajectory in a real Hilbert space.

The ambient space \(H\) is a complete real inner-product space, hence a real Hilbert space. The real number \(r\) is the dry-friction/threshold parameter, and the hypothesis \(0<r\) says that this threshold is strictly positive. The real number \(t_0\) is the initial time. The function \(f:H\to\mathbb R\) is a real-valued energy on \(H\), and \(z:\mathbb R\to H\) is a trajectory in \(H\).

The assumptions on \(f\) and \(z\) are: \(f\) is \(C^1\), expressed by `ContDiff ℝ 1 f`; \(f\) is bounded below, so there exists \(m\in\mathbb R\) such that
\[
m\le f(x)\qquad\text{for all }x\in H;
\]
the gradient \(\nabla f\) is locally Lipschitz; \(z\) is differentiable; and the initial gradient satisfies
\[
r<\|\nabla f(z(t_0))\|.
\]
Finally, `IsDrygradTrajectory r f z t₀` says that \(z\) is a dry-gradient trajectory for \(f\) with parameter \(r\) starting at time \(t_0\). In the proof, this hypothesis is used to obtain the velocity relation
\[
\operatorname{deriv}z(t)=-\operatorname{softThresholder}_r(\nabla f(z(t)))
\]
for \(t\ge t_0\).

The conclusion is a conjunction of four assertions.

First, the energy \(t\mapsto f(z(t))\) is antitone on \([t_0,\infty)\), meaning that it is nonincreasing there: if \(t_0\le s\le t\), then \(f(z(t))\le f(z(s))\).

Second, the squared speed is integrable on the half-line:
\[
t\mapsto \|\operatorname{deriv}z(t)\|^2
\]
is integrable on \([t_0,\infty)\).

Third, the speed itself is integrable on the half-line:
\[
t\mapsto \|\operatorname{deriv}z(t)\|
\]
is integrable on \([t_0,\infty)\).

Fourth, there exists a limit point \(z_\infty\) such that
\[
z(t)\to z_\infty\quad\text{as }t\to\infty,
\]
and at that limit the gradient norm equals the threshold:
\[
\|\nabla f(z_\infty)\|=r.
\]
Moreover, the trajectory has one of two possible asymptotic behaviors: either it stabilizes in finite time, meaning that there exists \(T\ge t_0\) such that
\[
z(t)=z_\infty\qquad\text{for all }t\ge T,
\]
or the gradient norm remains strictly above the threshold for all time:
\[
r<\|\nabla f(z(t))\|\qquad\text{for all }t\ge t_0.
\]

In ordinary mathematical language, the theorem says that a dry-gradient trajectory with initial gradient norm above the dry-friction threshold dissipates energy, has integrable speed and squared speed, converges to a limit point where the gradient norm exactly equals the threshold, and either reaches that limit in finite time or never enters the region where the gradient norm is at most \(r\).

## Lean proof
```lean
by
  let V : H → H := fun x => -softThresholder r (gradient f x)
  have hsoft_lip : LipschitzWith 1 (softThresholder r : H → H) :=
    lipschitzWith_one_of_firmlyNonexpansive (softThresholder_firmlyNonexpansive r hr)
  have hV_lip : LocallyLipschitz V := by
    have hneg : LocallyLipschitz (fun x : H => -x) :=
      LipschitzWith.id.neg.locallyLipschitz
    simpa [V, Function.comp_def] using
      hneg.comp (hsoft_lip.locallyLipschitz.comp hgradient_lip)
  have hV_zero : ∀ x, V x = 0 ↔ ‖gradient f x‖ ≤ r := by
    intro x
    constructor
    · intro hx
      by_contra hnot
      have hlt : r < ‖gradient f x‖ := lt_of_not_ge hnot
      have hgrad : gradient f x ≠ 0 := by
        exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans hr hlt))
      have hcoef : 1 - r / ‖gradient f x‖ ≠ 0 := by
        apply ne_of_gt
        rw [sub_pos, div_lt_one (lt_trans hr hlt)]
        exact hlt
      change -softThresholder r (gradient f x) = 0 at hx
      rw [softThresholder_apply, if_pos hlt] at hx
      exact (neg_ne_zero.mpr (smul_ne_zero hcoef hgrad)) hx
    · intro hx
      simp [V, softThresholder_apply, if_neg (not_lt_of_ge hx)]
  have hvelocity : ∀ t ∈ Set.Ici t₀, deriv z t = V (z t) := by
    intro t ht
    exact drygrad_velocity_formula hr (hsol t ht)
  have hV_ode_lip : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ w ∈ U, ‖V y - V w‖ ≤ L * ‖y - w‖ := by
    intro x
    rcases hV_lip x with ⟨K, U, hU, hKU⟩
    refine ⟨U, hU, K, K.coe_nonneg, ?_⟩
    intro y hy w hw
    simpa [dist_eq_norm] using hKU.dist_le_mul y hy w hw
  have hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 →
      ∀ t ∈ Set.Ici S, z t = z S := by
    intro S hS hVS t ht
    have hSstrict : t₀ < S := by
      have hSne : t₀ ≠ S := by
        intro heq
        subst S
        have hball := (hV_zero (z t₀)).mp hVS
        exact (not_lt_of_ge hball) hinitial
      exact lt_of_le_of_ne hS hSne
    have hzode : ∀ s ∈ Set.Ioo t₀ (t + 1), HasDerivAt z (V (z s)) s := by
      intro s hs
      rw [← hvelocity s hs.1.le]
      exact (hz_diff s).hasDerivAt
    have hconstode : ∀ s ∈ Set.Ioo t₀ (t + 1),
        HasDerivAt (fun _ : ℝ => z S) (V (z S)) s := by
      intro s _
      simpa [hVS] using (hasDerivAt_const s (z S))
    have heq := ode_eqOn_Ioo_of_locally_lipschitz V hV_ode_lip
      (show S ∈ Set.Ioo t₀ (t + 1) by
        exact ⟨hSstrict, lt_of_le_of_lt ht (by linarith)⟩)
      z (fun _ : ℝ => z S) hzode hconstode rfl
    exact heq ⟨lt_of_lt_of_le hSstrict ht, by linarith⟩
  have hanti : AntitoneOn (fun t => f (z t)) (Set.Ici t₀) :=
    drygrad_energy_antitone f z hr (hf.differentiable (by norm_num)) hz_diff hsol
  have hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (gradient f (z t)) (deriv z t)) t := by
    intro t _
    exact hasDerivAt_comp_gradient (hf.differentiable (by norm_num)) hz_diff t
  have hVcont : Continuous V := hV_lip.continuous
  have hzcont : ContinuousOn z (Set.Ici t₀) := by
    intro t ht
    exact (hz_diff t).continuousAt.continuousWithinAt
  have hdzcont : ContinuousOn (deriv z) (Set.Ici t₀) := by
    have hVz : ContinuousOn (fun t => V (z t)) (Set.Ici t₀) :=
      hVcont.comp_continuousOn hzcont
    exact hVz.congr (by
      intro t ht
      exact hvelocity t ht)
  have hnormcont : ContinuousOn (fun t => ‖deriv z t‖) (Set.Ici t₀) := hdzcont.norm
  have hsqcont : ContinuousOn (fun t => ‖deriv z t‖ ^ 2) (Set.Ici t₀) :=
    hnormcont.pow 2
  obtain ⟨m, hm⟩ := hf_lower
  have hprefix : ∀ T : ℝ, t₀ ≤ T →
      ∫ t in t₀..T, (‖deriv z t‖ ^ 2 + r * ‖deriv z t‖) ≤ f (z t₀) - m := by
    intro T hT
    have hfgcont : ContinuousOn (fun t => gradient f (z t)) (Set.Icc t₀ T) :=
      hgradient_lip.continuous.comp_continuousOn (hzcont.mono Set.Icc_subset_Ici_self)
    have hdzIcc : ContinuousOn (deriv z) (Set.Icc t₀ T) := hdzcont.mono Set.Icc_subset_Ici_self
    have hintercont : ContinuousOn (fun t => inner ℝ (gradient f (z t)) (deriv z t))
        (Set.Icc t₀ T) := hfgcont.inner hdzIcc
    have hderivcont : ContinuousOn (deriv (fun s => f (z s))) (Set.Icc t₀ T) :=
      hintercont.congr (by
        intro t ht
        exact (hchain t (Set.Icc_subset_Ici_self ht)).deriv)
    have hleftint : IntervalIntegrable (fun t => ‖deriv z t‖ ^ 2 + r * ‖deriv z t‖)
        MeasureTheory.volume t₀ T := by
      apply ContinuousOn.intervalIntegrable_of_Icc hT
      exact hsqcont.mono Set.Icc_subset_Ici_self |>.add
        ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)))
    have hrightint : IntervalIntegrable (fun t => - deriv (fun s => f (z s)) t)
        MeasureTheory.volume t₀ T :=
      (hderivcont.neg).intervalIntegrable_of_Icc hT
    have hpoint : ∀ t ∈ Set.Icc t₀ T,
        ‖deriv z t‖ ^ 2 + r * ‖deriv z t‖ ≤ - deriv (fun s => f (z s)) t := by
      intro t ht
      have h := drygrad_energy_deriv_le f z hr (hf.differentiable (by norm_num)) hz_diff hsol
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
      ∫ t in t₀..T, (‖deriv z t‖ ^ 2 + r * ‖deriv z t‖) ≤
          -(f (z T) - f (z t₀)) := hint
      _ = f (z t₀) - f (z T) := by ring
      _ ≤ f (z t₀) - m := hbound
  have hsqprefix : ∀ T : ℝ, t₀ ≤ T → ∫ t in t₀..T, ‖deriv z t‖ ^ 2 ≤ f (z t₀) - m := by
    intro T hT
    have hnonneg : 0 ≤ ∫ t in t₀..T, r * ‖deriv z t‖ :=
      intervalIntegral.integral_nonneg hT (fun t _ => mul_nonneg hr.le (norm_nonneg _))
    have hadd := hprefix T hT
    have hadd' : (∫ t in t₀..T, ‖deriv z t‖ ^ 2) +
        (∫ t in t₀..T, r * ‖deriv z t‖) ≤ f (z t₀) - m := by
      calc
        (∫ t in t₀..T, ‖deriv z t‖ ^ 2) + (∫ t in t₀..T, r * ‖deriv z t‖) =
            ∫ t in t₀..T, (‖deriv z t‖ ^ 2 + r * ‖deriv z t‖) :=
          (intervalIntegral.integral_add
            ((hsqcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)
            ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)).symm
        _ ≤ f (z t₀) - m := hadd
    linarith
  have hnormprefix : ∀ T : ℝ, t₀ ≤ T → ∫ t in t₀..T, ‖deriv z t‖ ≤ (f (z t₀) - m) / r := by
    intro T hT
    have hnonneg : 0 ≤ ∫ t in t₀..T, ‖deriv z t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
    have hadd := hprefix T hT
    have hadd' : (∫ t in t₀..T, ‖deriv z t‖ ^ 2) +
        r * (∫ t in t₀..T, ‖deriv z t‖) ≤ f (z t₀) - m := by
      rw [← intervalIntegral.integral_const_mul]
      calc
        (∫ t in t₀..T, ‖deriv z t‖ ^ 2) + (∫ t in t₀..T, r * ‖deriv z t‖) =
            ∫ t in t₀..T, (‖deriv z t‖ ^ 2 + r * ‖deriv z t‖) :=
          (intervalIntegral.integral_add
            ((hsqcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)
            ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)).symm
        _ ≤ f (z t₀) - m := hadd
    exact (le_div_iff₀ hr).mpr (by linarith)
  have hsqint : MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖ ^ 2) (Set.Ici t₀) :=
    integrableOn_Ici_of_nonneg_prefix_bound hsqcont (fun _ _ => sq_nonneg _) hsqprefix
  have hnormint : MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖) (Set.Ici t₀) :=
    integrableOn_Ici_of_nonneg_prefix_bound hnormcont (fun _ _ => norm_nonneg _) hnormprefix
  refine ⟨hanti, hsqint, hnormint, ?_⟩
  let zLimit := Filter.atTop.limUnder z
  have hnormint' : MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖) (Set.Ioi t₀) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    exact hnormint
  have hdzint' : MeasureTheory.IntegrableOn (deriv z) (Set.Ioi t₀) := by
    rw [MeasureTheory.IntegrableOn]
    apply (MeasureTheory.integrable_norm_iff
      ((hdzcont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)).mp
    exact hnormint'.integrable
  have hzlim : Filter.Tendsto z Filter.atTop (nhds zLimit) :=
    MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
      (f := z) (f' := deriv z) (a := t₀)
        (fun t ht => (hz_diff t).hasDerivAt) hdzint'
  have hVzlim : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds (V zLimit)) :=
    (hVcont.tendsto zLimit).comp hzlim
  have hVnormint : MeasureTheory.IntegrableOn (fun t => ‖V (z t)‖) (Set.Ici t₀) :=
    hnormint.congr_fun (fun t ht => congrArg norm (hvelocity t ht)) measurableSet_Ici
  have hVzero_from_integrability : V zLimit = 0 := by
    by_contra hne
    let c : ℝ := ‖V zLimit‖ / 2
    have hc : 0 < c := by
      dsimp [c]
      exact half_pos (norm_pos_iff.mpr hne)
    have hVnormlim : Filter.Tendsto (fun t => ‖V (z t)‖) Filter.atTop
        (nhds ‖V zLimit‖) := hVzlim.norm
    have hevent : ∀ᶠ t in Filter.atTop, c < ‖V (z t)‖ :=
      (tendsto_order.1 hVnormlim).1 c (by dsimp [c]; linarith [norm_pos_iff.mpr hne])
    rcases Filter.eventually_atTop.1 hevent with ⟨T, hT⟩
    let A := max t₀ T
    have htailint : MeasureTheory.IntegrableOn (fun t => ‖V (z t)‖) (Set.Ici A) :=
      hVnormint.mono_set (Set.Ici_subset_Ici.mpr (le_max_left t₀ T))
    have hconstint : MeasureTheory.IntegrableOn (fun _ : ℝ => c) (Set.Ici A) := by
      rw [MeasureTheory.IntegrableOn] at htailint ⊢
      apply MeasureTheory.Integrable.mono' htailint
      · exact MeasureTheory.aestronglyMeasurable_const
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_of_nonneg hc.le]
        exact (hT t (le_trans (le_max_right t₀ T) ht)).le
    exact (by
      simp [MeasureTheory.integrableOn_const_iff, hc.ne'] :
        ¬ MeasureTheory.IntegrableOn (fun _ : ℝ => c) (Set.Ici A)) hconstint
  have hvelocity_limit : Filter.Tendsto (deriv z) Filter.atTop (nhds 0) := by
    have hVlimit : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds 0) := by
      simpa [hVzero_from_integrability] using hVzlim
    apply hVlimit.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨t₀, fun t ht => ht⟩] with t ht
    exact (hvelocity t ht).symm
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
The proof begins by defining the vector field
\[
V(x)=-\operatorname{softThresholder}_r(\nabla f(x)).
\]
The soft thresholder is
\[
\operatorname{softThresholder}_r(x)=
\begin{cases}
\left(1-\dfrac r{\|x\|}\right)x, & r<\|x\|,\\
0, & \|x\|\le r.
\end{cases}
\]
The cited theorem `softThresholder_firmlyNonexpansive` says that for \(r>0\), this map is firmly nonexpansive on all of \(H\). The cited lemma `lipschitzWith_one_of_firmlyNonexpansive` converts firm nonexpansiveness into the Lipschitz bound \(\|S_r(x)-S_r(y)\|\le\|x-y\|\). Hence the proof obtains that \(\operatorname{softThresholder}_r\) is \(1\)-Lipschitz. The negation map \(x\mapsto -x\) is locally Lipschitz, and the assumed local Lipschitzness of \(\nabla f\) implies that the composition
\[
x\mapsto -\operatorname{softThresholder}_r(\nabla f(x))
\]
is locally Lipschitz. This is the assertion `hV_lip`.

Next the proof identifies the zeros of \(V\). It proves
\[
V(x)=0\quad\Longleftrightarrow\quad \|\nabla f(x)\|\le r.
\]
Indeed, if \(\|\nabla f(x)\|>r\), then the soft thresholder is a nonzero scalar multiple of the nonzero vector \(\nabla f(x)\), so it cannot vanish after applying the minus sign. Conversely, if \(\|\nabla f(x)\|\le r\), then the soft thresholder is zero by its definition. This equivalence is important because it says that stationary points of the vector field are exactly the points where the gradient norm is at most the dry-friction threshold.

The trajectory hypothesis is then used through the cited theorem `drygrad_velocity_formula`. That theorem states that if for some \(v,g\in H\) there exists \(u\) in the subdifferential of the dry-friction potential with parameter \(r\) at \(v\), such that
\[
v+u+g=0,
\]
then
\[
v=-\operatorname{softThresholder}_r(g).
\]
Specialized to the current setting, the trajectory condition gives the inclusion for \(v=\operatorname{deriv}z(t)\) and \(g=\nabla f(z(t))\), and therefore yields
\[
\operatorname{deriv}z(t)=V(z(t))
\]
for every \(t\ge t_0\). This is the differential equation satisfied by the trajectory.

The proof then converts the local Lipschitz property of \(V\) into the explicit local form required by the ODE uniqueness theorem. It shows that for each \(x\in H\), there is a neighborhood \(U\) of \(x\) and a constant \(L\ge 0\) such that
\[
\|V(y)-V(w)\|\le L\|y-w\|
\]
for all \(y,w\in U\).

This is used to prove that once \(V(z(S))=0\) at some time \(S\ge t_0\), the trajectory is constant from \(S\) onward. First, \(S\) cannot equal \(t_0\), because \(V(z(t_0))=0\) would imply \(\|\nabla f(z(t_0))\|\le r\), contradicting the strict initial hypothesis \(r<\|\nabla f(z(t_0))\|\). Thus \(t_0<S\). For any \(t\ge S\), on the interval \((t_0,t+1)\), both \(z\) and the constant function \(s\mapsto z(S)\) satisfy the same ODE
\[
\dot u=V(u).
\]
The function \(z\) satisfies it by the velocity formula, and the constant function satisfies it because \(V(z(S))=0\). The cited theorem `ode_eqOn_Ioo_of_locally_lipschitz` says that locally Lipschitz ODEs have unique solutions on an interval: if two functions satisfy \(\dot u=F(u)\) and \(\dot v=F(v)\) on \((a,b)\), and they agree at one point \(t_0\in(a,b)\), then they agree on all of \((a,b)\). Applying this with \(F=V\), \(a=t_0\), \(b=t+1\), and initial point \(S\), the proof concludes \(z(t)=z(S)\) for all \(t\ge S\). This is the finite-time stabilization mechanism.

The energy monotonicity is obtained directly from the cited theorem `drygrad_energy_antitone`, which says that under the differentiability, positivity, and trajectory assumptions, the function \(t\mapsto f(z(t))\) is antitone on \([t_0,\infty)\). This gives the first conclusion of the theorem.

Next, the cited theorem `hasDerivAt_comp_gradient` gives the chain rule for the energy:
\[
\frac{d}{dt}f(z(t))=\left\langle \nabla f(z(t)),\operatorname{deriv}z(t)\right\rangle.
\]
The proof then records the pointwise energy-dissipation inequality from `drygrad_energy_deriv_le`: for every \(t\ge t_0\),
\[
\|\operatorname{deriv}z(t)\|^2
+r\|\operatorname{deriv}z(t)\|
+\frac{d}{dt}f(z(t))\le 0.
\]
Equivalently,
\[
\|\operatorname{deriv}z(t)\|^2+r\|\operatorname{deriv}z(t)\|
\le -\frac{d}{dt}f(z(t)).
\]

To integrate this inequality, the proof establishes continuity of the relevant functions on \([t_0,\infty)\). Since \(V\) is continuous and \(z\) is continuous, the composition \(t\mapsto V(z(t))\) is continuous; because \(\operatorname{deriv}z(t)=V(z(t))\) on \([t_0,\infty)\), the derivative \(\operatorname{deriv}z\) is continuous there. Therefore \(t\mapsto \|\operatorname{deriv}z(t)\|\) and \(t\mapsto \|\operatorname{deriv}z(t)\|^2\) are continuous on \([t_0,\infty)\).

Let \(m\) be the lower bound for \(f\) supplied by `hf_lower`. For every finite \(T\ge t_0\), integration of the pointwise inequality gives
\[
\int_{t_0}^{T}\left(\|\operatorname{deriv}z(t)\|^2
+r\|\operatorname{deriv}z(t)\|\right)\,dt
\le \int_{t_0}^{T}-\frac{d}{dt}f(z(t))\,dt.
\]
By the fundamental theorem of calculus, the right-hand side is
\[
-\bigl(f(z(T))-f(z(t_0))\bigr)
=f(z(t_0))-f(z(T)).
\]
Since \(f(z(T))\ge m\), this is at most
\[
f(z(t_0))-m.
\]
Thus
\[
\int_{t_0}^{T}\left(\|\operatorname{deriv}z(t)\|^2
+r\|\operatorname{deriv}z(t)\|\right)\,dt
\le f(z(t_0))-m.
\]

Because the integrand is nonnegative, the proof drops the nonnegative term \(r\|\operatorname{deriv}z\|\) and obtains
\[
\int_{t_0}^{T}\|\operatorname{deriv}z(t)\|^2\,dt
\le f(z(t_0))-m.
\]
Likewise, dropping the nonnegative squared term and using \(r>0\), it obtains
\[
r\int_{t_0}^{T}\|\operatorname{deriv}z(t)\|\,dt
\le f(z(t_0))-m,
\]
hence
\[
\int_{t_0}^{T}\|\operatorname{deriv}z(t)\|\,dt
\le \frac{f(z(t_0))-m}{r}.
\]

Now the cited theorem `integrableOn_Ici_of_nonneg_prefix_bound` is applied. It says that if a continuous nonnegative function on \([t_0,\infty)\) has uniformly bounded finite integrals \(\int_{t_0}^{T}g\le B\), then it is integrable on \([t_0,\infty)\). The squared speed and the speed satisfy these hypotheses, so the proof obtains
\[
\operatorname{IntegrableOn}(\|\operatorname{deriv}z\|^2,[t_0,\infty))
\]
and
\[
\operatorname{IntegrableOn}(\|\operatorname{deriv}z\|,[t_0,\infty)).
\]
These are the second and third conclusions of the theorem.

For the limit, the proof defines the candidate
\[
z_\infty:=\operatorname{Filter.atTop.limUnder}z.
\]
It converts integrability on \([t_0,\infty)\) to integrability on \((t_0,\infty)\). Since \(\|\operatorname{deriv}z\|\) is integrable on \((t_0,\infty)\), the integrability of the norm implies the integrability of \(\operatorname{deriv}z\) itself on \((t_0,\infty)\). The proof then invokes `MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi` with \(z\) as the function, \(\operatorname{deriv}z\) as its derivative, and \(t_0\) as the left endpoint. The visible conclusion is exactly
\[
z(t)\to z_\infty\quad\text{as }t\to\infty.
\]

Because \(V\) is continuous and \(z(t)\to z_\infty\), the proof obtains
\[
V(z(t))\to V(z_\infty).
\]
It also knows that \(\|V(z(t))\|=\|\operatorname{deriv}z(t)\|\) is integrable on \([t_0,\infty)\). To prove \(V(z_\infty)=0\), the proof argues by contradiction. If \(V(z_\infty)\ne 0\), let
\[
c=\frac{\|V(z_\infty)\|}{2}>0.
\]
Since \(\|V(z(t))\|\to\|V(z_\infty)\|\), eventually \(\|V(z(t))\|>c\). On a tail \([A,\infty)\), the integrable function \(\|V(z(t))\|\) dominates the positive constant \(c\). But the constant function \(c>0\) is not integrable on an infinite half-line. This contradiction forces
\[
V(z_\infty)=0.
\]
From \(V(z_\infty)=0\), the proof also derives
\[
\operatorname{deriv}z(t)\to 0
\]
and, using \(\operatorname{deriv}z(t)=V(z(t))\) eventually, again \(V(z(t))\to0\). By uniqueness of limits, this is consistent with \(V(z(t))\to V(z_\infty)\), so \(V(z_\infty)=0\). Applying the earlier equivalence for the zeros of \(V\), the proof obtains
\[
\|\nabla f(z_\infty)\|\le r.
\]
Since \(\nabla f\) is locally Lipschitz, it is continuous, and hence \(x\mapsto \|\nabla f(x)\|\) is continuous. Therefore
\[
\|\nabla f(z(t))\|\to \|\nabla f(z_\infty)\|.
\]

The proof now splits into two cases.

In the first case, there exists \(T\ge t_0\) such that
\[
\|\nabla f(z(T))\|\le r.
\]
At time \(t_0\), the strict hypothesis gives
\[
r<\|\nabla f(z(t_0))\|.
\]
Thus \(r\) lies between \(\|\nabla f(z(T))\|\) and \(\|\nabla f(z(t_0))\|\). Since \(t\mapsto \|\nabla f(z(t))\|\) is continuous on \([t_0,T]\), the intermediate value theorem gives some \(S\in[t_0,T]\) with
\[
\|\nabla f(z(S))\|=r.
\]
Then \(V(z(S))=0\). By the earlier stationary-trajectory argument, \(z(t)=z(S)\) for all \(t\ge S\). Hence \(z(t)\) converges to both \(z_\infty\) and \(z(S)\), so uniqueness of limits gives \(z_\infty=z(S)\). Therefore
\[
\|\nabla f(z_\infty)\|=\|\nabla f(z(S))\|=r,
\]
and \(z(t)=z_\infty\) for all sufficiently large \(t\). This proves the finite-time stabilization alternative.

In the second case, there is no \(T\ge t_0\) with \(\|\nabla f(z(T))\|\le r\). Thus for every \(t\ge t_0\),
\[
r<\|\nabla f(z(t))\|.
\]
It remains to prove that equality holds at the limit. The proof already has \(\|\nabla f(z_\infty)\|\le r\). If instead \(\|\nabla f(z_\infty)\|<r\), then by convergence \(\|\nabla f(z(t))\|<r\) eventually, contradicting the strict inequality \(r<\|\nabla f(z(t))\|\) for all \(t\ge t_0\). Hence
\[
r\le \|\nabla f(z_\infty)\|.
\]
Together with \(\|\nabla f(z_\infty)\|\le r\), this gives
\[
\|\nabla f(z_\infty)\|=r.
\]
The strict inequality \(r<\|\nabla f(z(t))\|\) for all \(t\ge t_0\) is exactly the second alternative in the theorem.

Throughout, tactics such as `intro` introduce variables or assumptions into the local context, `rw` replaces expressions by equal definitions or previously proved equalities, `simp` simplifies definitions such as the soft thresholder and elementary logical reductions, `exact` closes a goal by supplying the required proof term, `linarith` solves linear inequalities, `ring` performs algebraic simplification, `by_contra` begins a proof by contradiction, `rcases` destructs existential or conjunctive hypotheses, `filter_upwards` proves eventually statements along the filter \(\operatorname{atTop}\), and `refine` assembles the final conjunction and existential conclusions.

