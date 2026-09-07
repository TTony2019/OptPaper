import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_4
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_5
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_6
namespace Alvarez2002
open Filter
open scoped RealInnerProductSpace
open scoped Topology

/-- Cancelling a nonzero distance in the strong-monotonicity estimate. -/
private theorem distance_le_grad_difference {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (β : ℝ) (gxy dxy : H)
    (hmono : β * ‖dxy‖ ^ 2 ≤ inner ℝ gxy dxy) : β * ‖dxy‖ ≤ ‖gxy‖ := by
  have hcs : inner ℝ gxy dxy ≤ ‖gxy‖ * ‖dxy‖ := real_inner_le_norm _ _
  have hsq : β * ‖dxy‖ ^ 2 ≤ ‖gxy‖ * ‖dxy‖ := hmono.trans hcs
  by_cases hzero : ‖dxy‖ = 0
  · rw [hzero]
    simp
  · have hpos : 0 < ‖dxy‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

/-- A differentiable strongly monotone map has nonnegative directional derivative. -/
private theorem strong_mono_hessian_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (gradΦ : H → H) (hessΦ : H → H →L[ℝ] H)
    (hstrong : StronglyMonotoneOnBoundedSubsets H gradΦ)
    (hderiv : ∀ z, HasFDerivAt gradΦ (hessΦ z) z) (z w : H) :
    0 ≤ inner ℝ (hessΦ z w) w := by
  let R : ℝ := ‖z‖ + ‖w‖ + 1
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [norm_nonneg z, norm_nonneg w]
  rcases hstrong R hR with ⟨β, hβ, hmono⟩
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r hr hrone
    exact ⟨hr, hrone.le⟩
  have hquot : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      β * ‖w‖ ^ 2 ≤ inner ℝ (r⁻¹ • (gradΦ (z + r • w) - gradΦ z)) w := by
    filter_upwards [hsmall] with r hr
    have hzrw : ‖z + r • w‖ < R := by
      calc
        ‖z + r • w‖ ≤ ‖z‖ + ‖r • w‖ := norm_add_le _ _
        _ = ‖z‖ + r * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1.le]
        _ ≤ ‖z‖ + ‖w‖ := by gcongr; nlinarith [norm_nonneg w]
        _ < R := by dsimp [R]; linarith
    have hz : ‖z‖ < R := by dsimp [R]; nlinarith [norm_nonneg w]
    have hball : max ‖z + r • w‖ ‖z‖ < R := max_lt hzrw hz
    have hm := hmono (z + r • w) z hball
    have hr0 : r ≠ 0 := ne_of_gt hr.1
    rw [show z + r • w - z = r • w by abel, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr.1] at hm
    have hinner : inner ℝ (gradΦ (z + r • w) - gradΦ z) (r • w) =
        r * inner ℝ (gradΦ (z + r • w) - gradΦ z) w := by
      rw [inner_smul_right]
    rw [hinner] at hm
    have hfactor : β * (r * ‖w‖) ^ 2 = r * (β * ‖w‖ ^ 2 * r) := by ring
    rw [hfactor] at hm
    have hdiv : β * ‖w‖ ^ 2 ≤ r⁻¹ * inner ℝ (gradΦ (z + r • w) - gradΦ z) w := by
      rw [← div_eq_inv_mul]
      apply (le_div_iff₀ hr.1).mpr
      exact le_of_mul_le_mul_left (by simpa [mul_assoc, mul_left_comm] using hm) hr.1
    simpa [inner_smul_left, smul_eq_mul] using hdiv
  have hline := (hderiv z).hasLineDerivAt w
  have htend := hline.tendsto_slope_zero_right
  have hscalar : Tendsto
      (fun r : ℝ => inner ℝ (r⁻¹ • (gradΦ (z + r • w) - gradΦ z)) w) (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (hessΦ z w) w)) :=
    ((continuous_inner.comp (continuous_id.prodMk continuous_const)).tendsto _).comp htend
  have hneg := le_of_tendsto hscalar.neg (hquot.mono fun r hr => neg_le_neg hr)
  nlinarith [mul_nonneg hβ.le (sq_nonneg ‖w‖)]

/-- The differential form of the perturbed energy calculation. -/
private theorem epsilon_energy_deriv {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (gradΦ : H → H)
    (hessΦ : H → H →L[ℝ] H)
    (ε : ℝ) (x v a : ℝ → H) (hgrad : ∀ z, HasGradientAt Φ (gradΦ z) z)
    (hx : ∀ s, HasDerivAt x (v s) s) (hv : ∀ s, HasDerivAt v (a s) s)
    (heq : ∀ s, 0 < s → ε • a s + hessΦ (x s) (v s) + gradΦ (x s) = 0)
    (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun r => ε / 2 * ‖v r‖ ^ 2 + Φ (x r))
      (-inner ℝ (hessΦ (x s) (v s)) (v s)) s := by
  have hkin := ((hv s).norm_sq).const_mul (ε / 2)
  have hpot0 := (hgrad (x s)).hasFDerivAt.comp_hasDerivAt s (hx s)
  have hpot : HasDerivAt (fun r => Φ (x r)) (inner ℝ (gradΦ (x s)) (v s)) s := by
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hpot0
  have hsum := hkin.add hpot
  convert hsum using 1
  have hi := congrArg (fun q : H => inner ℝ q (v s)) (heq s hs)
  simp [inner_add_left, inner_smul_left] at hi
  have hinner : inner ℝ (v s) (a s) = inner ℝ (a s) (v s) := real_inner_comm _ _
  rw [hinner]
  linarith

/-- The variation-of-constants formula for the scalar damping equation in a Banach space. -/
private theorem variation_of_constants {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] (q f : ℝ → H)
    (hf : Continuous f) (hqcont : Continuous q)
    (hq : ∀ r : ℝ, 0 < r → HasDerivAt q (-q r + f r) r) :
    ∀ s : ℝ, 0 ≤ s →
      q s = Real.exp (-s) • q 0 + ∫ r in (0)..s, Real.exp (-(s - r)) • f r := by
  intro s hs
  by_cases hs0 : s = 0
  · simp [hs0]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hderiv : ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) s →
      HasDerivAt (fun u : ℝ => Real.exp u • q u) (Real.exp r • f r) r := by
    intro r hr
    convert (Real.hasDerivAt_exp r).smul (hq r hr.1) using 1
    simp [smul_add, smul_neg]
  have hint : IntervalIntegrable (fun r : ℝ => Real.exp r • f r)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0 s := by
    exact (Real.continuous_exp.smul hf).intervalIntegrable 0 s
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := s) (f := fun r => Real.exp r • q r)
    (f' := fun r => Real.exp r • f r) hs
    ((Real.continuous_exp.smul hqcont).continuousOn) hderiv hint
  have hscaled := congrArg (fun z : H => Real.exp (-s) • z) hfund
  have hkernel : (∫ r in (0)..s, Real.exp (-(s - r)) • f r) =
      Real.exp (-s) • ∫ r in (0)..s, Real.exp r • f r := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro r _
    change Real.exp (-(s - r)) • f r = Real.exp (-s) • (Real.exp r • f r)
    rw [← mul_smul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have hsub : q s - Real.exp (-s) • q 0 =
      ∫ r in (0)..s, Real.exp (-(s - r)) • f r := by
    rw [hkernel]
    have hexp : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add]
      simp
    simpa [smul_sub, smul_smul, hexp] using hscaled.symm
  simpa [add_comm] using eq_add_of_sub_eq hsub

/--
Proposition 3.1:
Uniform `O(√ε)` convergence of `(ε-DIN)` to continuous Newton.
-/
theorem epsilon_din_uniform_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (x₀ v₀ : H) (xε : ℝ → ℝ → H) (x : ℝ → H)
    (hΦ : AssumptionH H Φ)
    (hcoercive : ∀ A : ℝ, ∃ R : ℝ, 0 < R ∧ ∀ z : H, Φ z ≤ A → ‖z‖ < R)
    (hstrong : StronglyMonotoneOnBoundedSubsets H (gradient Φ))
    (hε : ∀ ε : ℝ, 0 < ε → IsEpsilonDINTrajectory ε Φ x₀ v₀ (xε ε))
    (hcn : IsContinuousNewtonTrajectory x₀ x Φ)
    (hεreg : ∀ ε : ℝ, 0 < ε → Differentiable ℝ (xε ε) ∧ Differentiable ℝ (deriv (xε ε)))
    (hx : Differentiable ℝ x) :
    (∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      ‖xε ε t - x t‖ ≤ C * Real.sqrt ε) ∧
    TendstoUniformlyOn xε x (nhdsWithin 0 (Set.Ioi 0)) (Set.Ici 0) := by
  let gradΦ : H → H := gradient Φ
  let hessΦ : H → H →L[ℝ] H := fderiv ℝ (gradient Φ)
  have hΦC1 : ContDiff ℝ 1 Φ :=
    hΦ.twice_continuously_differentiable.of_le (by norm_num)
  have hgradC1 : ContDiff ℝ 1 gradΦ := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by
          simpa using hΦ.twice_continuously_differentiable)).2.2
    simpa [gradΦ, gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
  have hgrad : ∀ z, HasGradientAt Φ (gradΦ z) z := by
    intro z
    simpa [gradΦ, gradient, Function.comp_def] using
      ((hΦC1.differentiable (by norm_num) z).hasGradientAt)
  have hess_deriv : ∀ z, HasFDerivAt gradΦ (hessΦ z) z := by
    intro z
    exact (hgradC1.differentiable (by norm_num) z).hasFDerivAt
  let vε : ℝ → ℝ → H := fun ε s => deriv (xε ε) s
  let aε : ℝ → ℝ → H := fun ε s => deriv (deriv (xε ε)) s
  have hεdata : ∀ ε : ℝ, 0 < ε →
      0 < ε ∧ xε ε 0 = x₀ ∧ vε ε 0 = v₀ ∧
        (∀ s, HasDerivAt (xε ε) (vε ε s) s) ∧
        (∀ s, HasDerivAt (vε ε) (aε ε s) s) ∧
        ∀ s, 0 < s →
          ε • aε ε s + hessΦ (xε ε s) (vε ε s) + gradΦ (xε ε s) = 0 := by
    intro ε hεpos
    rcases hε ε hεpos with ⟨hεpos', hxε0, hvε0, _⟩
    rcases hεreg ε hεpos with ⟨hxε, hvε⟩
    refine ⟨hεpos', hxε0, ?_, ?_, ?_, ?_⟩
    · simpa [vε] using hvε0
    · intro s
      exact (hxε s).hasDerivAt
    · intro s
      simpa [vε, aε] using (hvε s).hasDerivAt
    · intro s hs
      rcases hε ε hεpos with ⟨_, _, _, heqε⟩
      simpa [vε, aε, hessΦ, gradΦ] using heqε s hs
  have hess_nonneg : ∀ z w : H, 0 ≤ inner ℝ ((fderiv ℝ (gradient Φ)) z w) w :=
    fun z w =>
    strong_mono_hessian_nonneg (gradient Φ) (fderiv ℝ (gradient Φ)) hstrong hess_deriv z w
  rcases hcn with ⟨hx0, hcn_eq_from_hcn⟩
  let v : ℝ → H := fun s => deriv x s
  have hxv : ∀ s, HasDerivAt x (v s) s := by
    intro s
    simpa [v] using (hx s).hasDerivAt
  have heq : ∀ s, 0 < s → hessΦ (x s) (deriv x s) + gradΦ (x s) = 0 := by
    intro s hs
    simpa [hessΦ, gradΦ] using hcn_eq_from_hcn s hs
  have henergy : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ t →
      ε / 2 * ‖vε ε t‖ ^ 2 + Φ (xε ε t) ≤ ε / 2 * ‖v₀‖ ^ 2 + Φ x₀ := by
    intro ε hεpos t ht
    rcases hεdata ε hεpos with ⟨_, hxε0, hvε0, hxε, hvε, heqε⟩
    let U : ℝ → ℝ := fun s => ε / 2 * ‖vε ε s‖ ^ 2 + Φ (xε ε s)
    have hUanti : AntitoneOn U (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · intro s hs
        have hxεcont : Continuous (xε ε) :=
          continuous_iff_continuousAt.mpr (fun r => (hxε r).continuousAt)
        have hvεcont : Continuous (vε ε) :=
          continuous_iff_continuousAt.mpr (fun r => (hvε r).continuousAt)
        have hkincont : Continuous (fun r => ε / 2 * ‖vε ε r‖ ^ 2) := by
          exact continuous_const.mul ((continuous_norm.comp hvεcont).pow 2)
        have hpotcont : Continuous (fun r => Φ (xε ε r)) :=
          hΦC1.continuous.comp hxεcont
        simpa [U] using (hkincont.add hpotcont).continuousAt.continuousWithinAt
      · intro s hs
        have hspos : 0 < s := by simpa using hs
        simpa [U] using
          (epsilon_energy_deriv Φ gradΦ hessΦ ε (xε ε) (vε ε) (aε ε) hgrad hxε hvε
            heqε s hspos).differentiableAt.differentiableWithinAt
      · intro s hs
        have hspos : 0 < s := by simpa using hs
        have hder := epsilon_energy_deriv Φ gradΦ hessΦ ε (xε ε) (vε ε) (aε ε)
          hgrad hxε hvε heqε s hspos
        simpa [U, hder.deriv] using neg_nonpos.mpr (hess_nonneg _ _)
    have := hUanti (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 0)) (Set.mem_Ici.mpr ht) ht
    simpa [U, hxε0, hvε0] using this
  let α : ℝ := ‖v₀‖ ^ 2 / 2 + Φ x₀
  rcases hΦ.bounded_below with ⟨m, hm⟩
  have hpert : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      Φ (xε ε t) ≤ α ∧ ε * ‖vε ε t‖ ≤ Real.sqrt (2 * ε * (α - m)) := by
    intro ε hεpos hεone t ht
    have hE := henergy ε hεpos t ht
    have hα : ε / 2 * ‖v₀‖ ^ 2 + Φ x₀ ≤ α := by
      dsimp [α]
      nlinarith [sq_nonneg ‖v₀‖]
    have hEα : ε / 2 * ‖vε ε t‖ ^ 2 + Φ (xε ε t) ≤ α := hE.trans hα
    have hphi : Φ (xε ε t) ≤ α := by
      nlinarith [sq_nonneg ‖vε ε t‖, hεpos.le]
    have hgap : 0 ≤ α - m := by linarith [hm (xε ε t)]
    have hvelsq : (ε * ‖vε ε t‖) ^ 2 ≤ 2 * ε * (α - m) := by
      nlinarith [hm (xε ε t)]
    have hrad : 0 ≤ 2 * ε * (α - m) := mul_nonneg (mul_nonneg (by norm_num) hεpos.le) hgap
    have hsqrt : (Real.sqrt (2 * ε * (α - m))) ^ 2 = 2 * ε * (α - m) :=
      Real.sq_sqrt hrad
    refine ⟨hphi, ?_⟩
    nlinarith [mul_nonneg hεpos.le (norm_nonneg (vε ε t)), Real.sqrt_nonneg (2 * ε * (α - m))]
  have hcont : ∀ t : ℝ, 0 ≤ t → Φ (x t) ≤ Φ x₀ := by
    intro t ht
    let V : ℝ → ℝ := fun s => Φ (x s)
    have hVcont : Continuous V := hΦC1.continuous.comp hx.continuous
    have hVderiv : ∀ s : ℝ, 0 < s →
        HasDerivAt V (-inner ℝ (hessΦ (x s) (v s)) (v s)) s := by
      intro s hs
      have hd := (hgrad (x s)).hasFDerivAt.comp_hasDerivAt s (hxv s)
      have hd' : HasDerivAt V (inner ℝ (gradΦ (x s)) (v s)) s := by
        simpa [V, Function.comp_def, InnerProductSpace.toDual_apply_apply] using hd
      convert hd' using 1
      have hi := congrArg (fun q : H => inner ℝ q (v s)) (heq s hs)
      simp [inner_add_left] at hi
      linarith
    have hVanti : AntitoneOn V (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · intro s hs
        simpa [V] using hVcont.continuousAt.continuousWithinAt
      · intro s hs
        have hspos : 0 < s := by simpa using hs
        simpa [V] using (hVderiv s hspos).differentiableAt.differentiableWithinAt
      · intro s hs
        have hspos : 0 < s := by simpa using hs
        simpa [V, (hVderiv s hspos).deriv] using neg_nonpos.mpr (hess_nonneg _ _)
    have := hVanti (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 0)) (Set.mem_Ici.mpr ht) ht
    simpa [V, hx0] using this
  rcases hcoercive α with ⟨R, hRpos, hsub⟩
  have hball : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      max ‖xε ε t‖ ‖x t‖ < R := by
    intro ε hεpos hεone t ht
    apply max_lt
    · exact hsub _ (hpert ε hεpos hεone t ht).1
    · apply hsub
      have hα0 : Φ x₀ ≤ α := by
        dsimp [α]
        nlinarith [sq_nonneg ‖v₀‖]
      exact (hcont t ht).trans hα0
  rcases hstrong R hRpos with ⟨β, hβpos, hmono⟩
  have hdist : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      β * ‖xε ε t - x t‖ ≤ ‖gradΦ (xε ε t) - gradΦ (x t)‖ := by
    intro ε hεpos hεone t ht
    apply distance_le_grad_difference
    exact hmono _ _ (hball ε hεpos hεone t ht)
  have hgrad_diff : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ t →
      gradΦ (xε ε t) - gradΦ (x t) =
        Real.exp (-t) • (ε • v₀) - ε • vε ε t +
          ∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r) := by
    intro ε hεpos t ht
    rcases hεdata ε hεpos with ⟨_, hxε0, hvε0, hxε, hvε, heqε⟩
    have hq : ∀ r : ℝ, 0 < r →
        HasDerivAt (fun s => gradΦ (x s)) (-gradΦ (x r)) r := by
      intro r hr
      have hd := (hess_deriv (x r)).comp_hasDerivAt r (hxv r)
      have hH : hessΦ (x r) (v r) = -gradΦ (x r) :=
        eq_neg_of_add_eq_zero_left (heq r hr)
      simpa [Function.comp_def, hH] using hd
    have hqcont : Continuous (fun s => gradΦ (x s)) :=
      hgradC1.continuous.comp hx.continuous
    have hqsol := variation_of_constants (fun s => gradΦ (x s)) (fun _ : ℝ => (0 : H))
      continuous_const hqcont (fun r hr => by simpa using hq r hr) t ht
    have hfε : Continuous (fun s : ℝ => ε • vε ε s) :=
      continuous_const.smul (continuous_iff_continuousAt.mpr fun s => (hvε s).continuousAt)
    let ω : ℝ → H := fun s => ε • vε ε s + gradΦ (xε ε s)
    have hω : ∀ r : ℝ, 0 < r → HasDerivAt ω (-ω r + ε • vε ε r) r := by
      intro r hr
      have hv' := (hvε r).const_smul ε
      have hx' := (hess_deriv (xε ε r)).comp_hasDerivAt r (hxε r)
      have hd := hv'.add hx'
      have hsum : ε • aε ε r + hessΦ (xε ε r) (vε ε r) = -gradΦ (xε ε r) :=
        eq_neg_of_add_eq_zero_left (heqε r hr)
      convert hd using 1
      rw [hsum]
      dsimp [ω]
      abel
    have hωcont : Continuous ω := by
      have hxεcont : Continuous (xε ε) :=
        continuous_iff_continuousAt.mpr (fun r => (hxε r).continuousAt)
      have hgradcomp : Continuous (fun s => gradΦ (xε ε s)) :=
        hgradC1.continuous.comp hxεcont
      simpa [ω] using hfε.add hgradcomp
    have hωsol := variation_of_constants ω (fun s : ℝ => ε • vε ε s) hfε hωcont hω t ht
    have hqsol' : gradΦ (x t) = Real.exp (-t) • gradΦ x₀ := by
      simpa [hx0] using hqsol
    have hω0 : ω 0 = ε • v₀ + gradΦ x₀ := by simp [ω, hxε0, hvε0]
    rw [hω0] at hωsol
    calc
      gradΦ (xε ε t) - gradΦ (x t) = (ω t - ε • vε ε t) - gradΦ (x t) := by
        dsimp [ω]
        abel
      _ = Real.exp (-t) • (ε • v₀) - ε • vε ε t +
          ∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r) := by
        rw [hωsol, hqsol']
        rw [smul_add]
        abel
  have hgrad_bound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      ‖gradΦ (xε ε t) - gradΦ (x t)‖ ≤
        ε * ‖v₀‖ + 2 * Real.sqrt (2 * ε * (α - m)) := by
    intro ε hεpos hεone t ht
    let B : ℝ := Real.sqrt (2 * ε * (α - m))
    have hB : 0 ≤ B := Real.sqrt_nonneg _
    have hinit : ‖Real.exp (-t) • (ε • v₀)‖ ≤ ε * ‖v₀‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs, abs_of_pos hεpos]
      have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      exact mul_le_of_le_one_left (mul_nonneg hεpos.le (norm_nonneg _)) he
    have hinst : ‖ε • vε ε t‖ ≤ B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
      exact (hpert ε hεpos hεone t ht).2
    have hkernel : ‖∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ ≤ B := by
      have hecont : Continuous (fun r : ℝ => Real.exp (-(t - r))) :=
        Real.continuous_exp.comp ((continuous_const.sub continuous_id).neg)
      have hvcont : Continuous (fun r : ℝ => ε • vε ε r) := by
        rcases hεdata ε hεpos with ⟨_, _, _, _, hvε', _⟩
        exact continuous_const.smul
          (continuous_iff_continuousAt.mpr fun r => (hvε' r).continuousAt)
      have hfint : IntervalIntegrable (fun r : ℝ => ‖Real.exp (-(t - r)) • (ε • vε ε r)‖)
          MeasureTheory.volume 0 t := (hecont.smul hvcont).norm.intervalIntegrable 0 t
      have hgint : IntervalIntegrable (fun r : ℝ => Real.exp (-(t - r)) * B)
          MeasureTheory.volume 0 t := (hecont.mul continuous_const).intervalIntegrable 0 t
      have hmono := intervalIntegral.integral_mono_on ht hfint hgint (fun r hr => by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.norm_eq_abs, abs_of_pos hεpos]
        exact mul_le_mul_of_nonneg_left (hpert ε hεpos hεone r hr.1).2 (Real.exp_pos _).le)
      have hscalar : (∫ r in (0)..t, Real.exp (-(t - r)) * B) =
          B * (1 - Real.exp (-t)) := by
        calc
          (∫ r in (0)..t, Real.exp (-(t - r)) * B) =
              B * Real.exp (-t) * (∫ r in (0)..t, Real.exp r) := by
            rw [show (fun r : ℝ => Real.exp (-(t - r)) * B) =
              fun r => (B * Real.exp (-t)) * Real.exp r by
                funext r
                rw [show -(t - r) = -t + r by ring, Real.exp_add]
                ring]
            rw [intervalIntegral.integral_const_mul, mul_assoc]
          _ = B * (1 - Real.exp (-t)) := by
            rw [integral_exp, Real.exp_zero]
            have heq : Real.exp (-t) * Real.exp t = 1 := by
              rw [← Real.exp_add]
              simp
            calc
              B * Real.exp (-t) * (Real.exp t - 1) =
                  B * (Real.exp (-t) * Real.exp t - Real.exp (-t)) := by ring
              _ = B * (1 - Real.exp (-t)) := by rw [heq]
      calc
        ‖∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ ≤
            ∫ r in (0)..t, ‖Real.exp (-(t - r)) • (ε • vε ε r)‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
        _ ≤ ∫ r in (0)..t, Real.exp (-(t - r)) * B := hmono
        _ = B * (1 - Real.exp (-t)) := hscalar
        _ ≤ B := by
          have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
          nlinarith [Real.exp_pos (-t)]
    rw [hgrad_diff ε hεpos t ht]
    calc
      ‖Real.exp (-t) • (ε • v₀) - ε • vε ε t +
          ∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ ≤
          ‖Real.exp (-t) • (ε • v₀)‖ + ‖ε • vε ε t‖ +
            ‖∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ := by
              calc
                _ ≤ ‖Real.exp (-t) • (ε • v₀) - ε • vε ε t‖ +
                    ‖∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ := norm_add_le _ _
                _ ≤ _ := by gcongr; exact norm_sub_le _ _
      _ ≤ ε * ‖v₀‖ + 2 * B := by linarith
      _ = ε * ‖v₀‖ + 2 * Real.sqrt (2 * ε * (α - m)) := rfl
  let K : ℝ := ‖v₀‖ + 2 * Real.sqrt (2 * (α - m))
  let C : ℝ := (K + 1) / β
  have hgap : 0 ≤ α - m := by
    dsimp [α]
    linarith [hm x₀, sq_nonneg ‖v₀‖]
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (by linarith) hβpos
  have herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      ‖xε ε t - x t‖ ≤ C * Real.sqrt ε := by
    intro ε hεpos hεone t ht
    have hsqrteps : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
    have hsqrteps_sq : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hεpos.le
    have hsqrteps_le_one : Real.sqrt ε ≤ 1 := by
      rw [← sq_le_sq₀ hsqrteps (by norm_num : (0 : ℝ) ≤ 1)]
      simpa [hsqrteps_sq] using hεone
    have heps_le_sqrt : ε ≤ Real.sqrt ε := by
      nlinarith
    have hsqrtfac : Real.sqrt (2 * ε * (α - m)) =
        Real.sqrt ε * Real.sqrt (2 * (α - m)) := by
      rw [show 2 * ε * (α - m) = ε * (2 * (α - m)) by ring,
        Real.sqrt_mul hεpos.le]
    have hgrad := hgrad_bound ε hεpos hεone t ht
    rw [hsqrtfac] at hgrad
    have hgradK : ε * ‖v₀‖ + 2 * (Real.sqrt ε * Real.sqrt (2 * (α - m))) ≤
        Real.sqrt ε * K := by
      dsimp [K]
      nlinarith [norm_nonneg v₀, Real.sqrt_nonneg (2 * (α - m))]
    have hβdist : β * ‖xε ε t - x t‖ ≤ Real.sqrt ε * K :=
      (hdist ε hεpos hεone t ht).trans (hgrad.trans hgradK)
    have hdiv : ‖xε ε t - x t‖ ≤ (Real.sqrt ε * K) / β :=
      (le_div_iff₀ hβpos).mpr (by simpa [mul_comm] using hβdist)
    calc
      ‖xε ε t - x t‖ ≤ (Real.sqrt ε * K) / β := hdiv
      _ ≤ ((K + 1) / β) * Real.sqrt ε := by
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff_of_pos_right hβpos).mpr
        have : Real.sqrt ε * K ≤ Real.sqrt ε * (K + 1) := by
          gcongr
          linarith
        nlinarith
      _ = C * Real.sqrt ε := rfl
  refine ⟨⟨C, hCpos, herror⟩, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  let η : ℝ := min 1 ((δ / C) ^ 2)
  have hδC : 0 < δ / C := div_pos hδ hCpos
  have hη : 0 < η := by
    dsimp [η]
    exact (lt_min_iff).mpr ⟨by norm_num, sq_pos_of_pos hδC⟩
  filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
  intro t ht
  have hεpos : 0 < ε := hε.1
  have hεη : ε < η := hε.2
  have hεη' : ε < min 1 ((δ / C) ^ 2) := by simpa [η] using hεη
  have hεone : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hεη' (min_le_left _ _))
  have hεsq : ε < (δ / C) ^ 2 := lt_of_lt_of_le hεη' (min_le_right _ _)
  have hsqrt_lt : Real.sqrt ε < δ / C := (Real.sqrt_lt' hδC).mpr hεsq
  have hrate := herror ε hεpos hεone t ht
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖xε ε t - x t‖ ≤ C * Real.sqrt ε := hrate
    _ < C * (δ / C) := mul_lt_mul_of_pos_left hsqrt_lt hCpos
    _ = δ := by field_simp [ne_of_gt hCpos]
end Alvarez2002
