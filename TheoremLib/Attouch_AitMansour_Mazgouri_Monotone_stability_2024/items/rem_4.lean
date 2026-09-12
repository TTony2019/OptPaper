import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.rem_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_4

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set

/-- Remark 7.2(i): an interval-uniform instance of the estimate (3) of
  Theorem 3.1 gives the sup-norm estimate (28) in `C([0,T]; H)`.

  This auxiliary form takes the a.e. estimate of Theorem 3.1 (`thm_1`) as a
  hypothesis; `rem_4_estimate28` below instantiates it with the solutions
  whose existence and uniqueness are given by that theorem, so that (28) is
  derived and not assumed. -/
theorem rem_4_estimate28_aux {H : Type*} [NormedAddCommGroup H]
    (x x' : ℝ → H) (u₀ v₀ u₀' v₀' : H) (m T θ₁ _θ₂ c : ℝ) (hT : 0 < T) (hm : 0 ≤ m)
    (h₁ : 0 ≤ θ₁) (hc : 0 ≤ c)
    (hcont : ContinuousOn (fun t => x t - x' t) (Set.Icc (0 : ℝ) T))
    (hae : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      ‖x t - x' t‖ ≤
        Real.exp (m * t) * Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
          (θ₁ / m) * (Real.exp (m * t) - 1) * c) :
    pathSupNorm T (fun t => x t - x' t) ≤
      Real.exp (m * T) * Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
        (θ₁ / m) * (Real.exp (m * T) - 1) * c := by
  have haeT : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      ‖x t - x' t‖ ≤
        Real.exp (m * T) * Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
          (θ₁ / m) * (Real.exp (m * T) - 1) * c := by
    filter_upwards [hae] with s hs hsT
    refine (hs hsT).trans ?_
    have hexp : Real.exp (m * s) ≤ Real.exp (m * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT.2 hm)
    have hcoef : Real.exp (m * s) - 1 ≤ Real.exp (m * T) - 1 := by linarith
    have h1e : Real.exp (m * s) * Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) ≤
        Real.exp (m * T) * Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _)
    have h2e : (θ₁ / m) * (Real.exp (m * s) - 1) * c ≤
        (θ₁ / m) * (Real.exp (m * T) - 1) * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (div_nonneg h₁ hm)) hc
    linarith [h1e, h2e]
  exact pathSupNorm_le_of_forall hT.le
    (le_of_ae_le_const_of_continuousOn (M := Real.exp (m * T) *
        Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
          (θ₁ / m) * (Real.exp (m * T) - 1) * c)
      hT hcont.norm haeT)

/-- Remark 7.2: in the Banach space `(C([0,T];H), ‖·‖_∞)` the estimate (3) of
  Theorem 3.1 takes the form (28): for all `μ,μ'` in the parameter set, the
  sup-norm distance between the unique strong global solutions is bounded by
  `e^{mT}√(‖u₀^μ−u₀^{μ'}‖²+‖v₀^μ−v₀^{μ'}‖²) + (θ₁/m)(e^{mT}−1)‖μ−μ'‖^{θ₂}`,
  where `m = max(m_μ, m_{μ'})` and `m_μ = (1+2γ²+2/α_μ²)^{1/2}`.

  Both the existence and uniqueness of the solutions `x_μ` and the a.e.
  estimate (3) come from Theorem 3.1 (`thm_1`); the sup-norm form (28) follows
  by taking the supremum over `[0,T]` of that estimate. -/
theorem rem_4_estimate28 {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup M]
    (V : Set M) (A : M → H → H) (γ : ℝ) (u₀ v₀ : M → H) (α : M → ℝ)
    (θ₁ θ₂ T : ℝ) (hγ : 0 < γ) (hT : 0 < T)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H,
      α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧
      ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂) :
    (∀ μ ∈ V, ∃ x dx ddx : ℝ → H,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) x dx ddx ∧
        ∀ y dy ddy : ℝ → H, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) y dy ddy →
          Set.EqOn x y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V, ∀ sol sol' dsol dsol' ddsol ddsol' : ℝ → H,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) sol dsol ddsol →
      ext_def_2 (A μ') γ (u₀ μ') (v₀ μ') sol' dsol' ddsol' →
      let m := max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2)))
        (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2)))
      pathSupNorm T (fun t => sol t - sol' t) ≤
        Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          (θ₁ / m) * (Real.exp (m * T) - 1) * ‖μ - μ'‖ ^ θ₂) := by
  have hmain := thm_1 V A γ u₀ v₀ α θ₁ θ₂ hγ hC₁ hC₂
  constructor
  · exact hmain.1
  · intro μ hμ μ' hμ' s u ds du ds' du' hs hu
    obtain ⟨z, dz, ddz, hzext, hzu⟩ := hmain.1 μ hμ
    obtain ⟨z', dz', ddz', hzext', hzu'⟩ := hmain.1 μ' hμ'
    obtain ⟨y, y', ⟨dy, ddy, hy⟩, ⟨dy', ddy', hy'⟩, hb'⟩ := hmain.2 μ hμ μ' hμ'
    have hzAeq_s : z =ᵐ[MeasureTheory.volume.restrict (Set.Ici 0)] s := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with r hr
      exact (hzu s ds ds' hs) hr
    have hzAeq_y : z =ᵐ[MeasureTheory.volume.restrict (Set.Ici 0)] y := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with r hr
      exact (hzu y dy ddy hy) hr
    have hzAeq_u : z' =ᵐ[MeasureTheory.volume.restrict (Set.Ici 0)] u := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with r hr
      exact (hzu' u du du' hu) hr
    have hzAeq_y' : z' =ᵐ[MeasureTheory.volume.restrict (Set.Ici 0)] y' := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with r hr
      exact (hzu' y' dy' ddy' hy') hr
    have hbound : ∀ᵐ r ∂MeasureTheory.volume.restrict (Set.Ici 0),
        r ∈ Set.Icc (0 : ℝ) T →
          ‖s r - u r‖ ≤
            Real.exp (max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2)))
                (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))) * r) *
              Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
            (θ₁ / max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2)))
                (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2)))) *
              (Real.exp (max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2)))
                  (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))) * r) - 1) *
                ‖μ - μ'‖ ^ θ₂ := by
      filter_upwards [MeasureTheory.ae_restrict_of_ae hb', hzAeq_y, hzAeq_s,
        hzAeq_y', hzAeq_u] with r hbr hyr hsr hy'r hur
      intro hrT
      have hsame : ‖s r - u r‖ = ‖y r - y' r‖ := by
        rw [← hsr, ← hur, hyr, hy'r]
      rw [hsame]
      exact hbr hrT.1
    have hpoint : ∀ᵐ r ∂MeasureTheory.volume, r ∈ Set.Icc (0 : ℝ) T →
        ‖s r - u r‖ ≤
          Real.exp (max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2)))
              (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))) * r) *
            Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          (θ₁ / max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2)))
              (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2)))) *
            (Real.exp (max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2)))
                (Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))) * r) - 1) *
              ‖μ - μ'‖ ^ θ₂ :=
      (MeasureTheory.ae_imp_of_ae_restrict hbound).mono
        fun r hr hrT => hr hrT.1 hrT
    exact rem_4_estimate28_aux s u (u₀ μ) (v₀ μ) (u₀ μ') (v₀ μ')
      _ T θ₁ θ₂ (‖μ - μ'‖ ^ θ₂) hT (le_max_of_le_left (Real.sqrt_nonneg _)) hC₂.1.le
      (Real.rpow_nonneg (norm_nonneg _) _)
      (((hs.2.1 T hT).1.continuousOn.mono Set.Icc_subset_uIcc).sub
        ((hu.2.1 T hT).1.continuousOn.mono Set.Icc_subset_uIcc))
      (hpoint.mono fun r hr hrT => hr ⟨hrT.1, hrT.2⟩)

/-- Remark 7.2(ii): the small-horizon regime `γT + T²/α < 1` makes the
  denominator `α − αγT − T²` of the fixed-point estimate (25) positive, so
  (25) is available as a refinement of (28) on short horizons. -/
theorem rem_4_refinement (α γ T : ℝ) (hα : 0 < α)
    (hγT : γ * T + T ^ 2 / α < 1) :
    0 < α - α * γ * T - T ^ 2 := by
  have hcore : α * γ * T + T ^ 2 < α := by
    calc
      α * γ * T + T ^ 2 = α * (γ * T + T ^ 2 / α) := by
        field_simp [hα.ne']
      _ < α * 1 := mul_lt_mul_of_pos_left hγT hα
      _ = α := by ring
  nlinarith

/-! ### Remark 7.2(ii): (25) refines (28) on short horizons

The paper claims that for every `T > 0` with `γT + T²/α ∈ [0,1)` the
fixed-point estimate (25) is a refinement of the sup-norm estimate (28).  As
stated for *all* such `T` this is false: for `α = 1`, `γ = 0`, `T = 0.9` the
leading coefficient `α/(α-αγT-T²)` of (25) times `√(1+T²)` equals `7.08`,
larger than `e^{mT} = 4.76`.  The comparison is therefore proved for
sufficiently small `T` (which is the regime the paper's "sharp error bounds"
refers to), in the coefficient form that implies `(25) ≤ (28)`:

* `(α/(α-αγT-T²))·√(1+T²) ≤ e^{mT}` (the initial-data coefficients, via
  Cauchy–Schwarz `‖Δu‖ + T‖Δv‖ ≤ √(1+T²)√(‖Δu‖²+‖Δv‖²)`),
* `(α/(α-αγT-T²))·T² ≤ (e^{mT}-1)/m` (the `‖μ-μ'‖^{θ₂}` coefficients),

where `m = √(1+2γ²+2/α²)`. -/

/-- Auxiliary estimate: under the quadratic smallness condition
`T²/2 + T²/α + γmT² + mT³/α ≤ (m-γ)T` (which holds for small `T > 0` because
`γ < m`), the first coefficient of (25) is dominated by the first coefficient
of (28). -/
private theorem sqrt_coeff_le_exp {α γ m T : ℝ} (hα : 0 < α) (hT : 0 < T)
    (hquad : T ^ 2 / 2 + T ^ 2 / α + γ * m * T ^ 2 + m * T ^ 3 / α ≤ (m - γ) * T)
    (hs : γ * T + T ^ 2 / α < 1) :
    Real.sqrt (1 + T ^ 2) / (1 - (γ * T + T ^ 2 / α)) ≤ Real.exp (m * T) := by
  have h1s : 0 < 1 - (γ * T + T ^ 2 / α) := by linarith
  have hsq : Real.sqrt (1 + T ^ 2) ≤ 1 + T ^ 2 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg T]
  have hexp : 1 + m * T ≤ Real.exp (m * T) := by
    have := Real.add_one_le_exp (m * T)
    linarith
  have hkey : 1 + T ^ 2 / 2 ≤ Real.exp (m * T) * (1 - (γ * T + T ^ 2 / α)) := by
    have h2 : (1 + m * T) * (1 - (γ * T + T ^ 2 / α)) ≤
        Real.exp (m * T) * (1 - (γ * T + T ^ 2 / α)) :=
      mul_le_mul_of_nonneg_right hexp h1s.le
    have h3 : 1 + T ^ 2 / 2 ≤ (1 + m * T) * (1 - (γ * T + T ^ 2 / α)) := by
      have hexpand : (1 + m * T) * (1 - (γ * T + T ^ 2 / α)) =
          1 + (m * T - (γ * T + T ^ 2 / α) - (γ * m * T ^ 2 + m * T ^ 3 / α)) := by
        field_simp [hα.ne']
        ring
      rw [hexpand]
      linarith [hquad]
    linarith
  rw [div_le_iff₀ h1s]
  exact hsq.trans hkey

/-- Auxiliary estimate: under `T(1+γ) + T²/α ≤ 1` the second coefficient of
  (25) is dominated by the second coefficient of (28), using
  `e^{mT} - 1 ≥ mT`. -/
private theorem t_sq_coeff_le_exp {α γ m T : ℝ} (hm : 0 < m) (hT : 0 < T)
    (hsmall : T * (1 + γ) + T ^ 2 / α ≤ 1) (hs : γ * T + T ^ 2 / α < 1) :
    T ^ 2 / (1 - (γ * T + T ^ 2 / α)) ≤ (Real.exp (m * T) - 1) / m := by
  have h1s : 0 < 1 - (γ * T + T ^ 2 / α) := sub_pos.mpr hs
  have hexp : 1 + m * T ≤ Real.exp (m * T) := by
    have := Real.add_one_le_exp (m * T)
    linarith
  have hge : T ≤ (Real.exp (m * T) - 1) / m := by
    rw [le_div_iff₀ hm]
    nlinarith
  have hle : T ^ 2 / (1 - (γ * T + T ^ 2 / α)) ≤ T := by
    rw [div_le_iff₀ h1s]
    nlinarith
  linarith

/-- Remark 7.2(ii), short-horizon form: there is `T₀ > 0` such that for every
  `T ∈ (0,T₀)` both coefficients of the fixed-point estimate (25) are at most
  the corresponding coefficients of the sup-norm estimate (28):
  `(α/(α-αγT-T²))·√(1+T²) ≤ e^{mT}` and
  `(α/(α-αγT-T²))·T² ≤ (e^{mT}-1)/m`, with `m = √(1+2γ²+2/α²)`.  This is the
  precise form of the paper's "refinement" claim (see the section comment for
  why it cannot hold for all `T` with `γT + T²/α ∈ [0,1)`). -/
theorem rem_4_refinement_threshold (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ∈ Set.Ioo (0 : ℝ) T₀,
      γ * T + T ^ 2 / α < 1 ∧
      (α / (α - α * γ * T - T ^ 2)) * Real.sqrt (1 + T ^ 2) ≤
        Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) ∧
      (α / (α - α * γ * T - T ^ 2)) * T ^ 2 ≤
        (Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) - 1) /
          Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) := by
  set m : ℝ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) with hm
  have hm_sq : m ^ 2 = 1 + 2 * γ ^ 2 + 2 / α ^ 2 := by
    rw [hm]
    exact Real.sq_sqrt (by positivity)
  have hm_one : 1 ≤ m := by
    have hα2 : 0 < 2 / α ^ 2 := by positivity
    rw [hm, Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg γ, hα2.le]
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_one
  have hγm : γ < m := by
    have hα2 : 0 < 2 / α ^ 2 := by positivity
    rw [hm, Real.lt_sqrt hγ]
    nlinarith [sq_nonneg γ, hα2.le]
  have hε : 0 < m - γ := sub_pos.mpr hγm
  set C : ℝ := 1 / 2 + 1 / α + m * γ + m / α with hC
  have hC_pos : 0 < C := by
    rw [hC]
    have h1 : 0 < 1 / α := one_div_pos.mpr hα
    have h2 : 0 < m / α := div_pos hm_pos hα
    have h3 : 0 ≤ m * γ := mul_nonneg hm_pos.le hγ
    linarith
  have hden_pos : 0 < 1 + γ + 1 / α := by
    have h1 : 0 < 1 / α := one_div_pos.mpr hα
    linarith
  refine ⟨min 1 (min ((m - γ) / C) (1 / (1 + γ + 1 / α))), ?_, ?_⟩
  · refine lt_min zero_lt_one (lt_min (div_pos hε hC_pos) ?_)
    exact one_div_pos.mpr hden_pos
  · intro T hT
    obtain ⟨hTpos, hTlt⟩ := hT
    have hTle1 : T ≤ 1 := (lt_min_iff.mp hTlt).1.le
    have hTlt' : T < min ((m - γ) / C) (1 / (1 + γ + 1 / α)) := (lt_min_iff.mp hTlt).2
    have hTC : T * C ≤ m - γ := by
      have h := (lt_min_iff.mp hTlt').1
      rw [lt_div_iff₀ hC_pos] at h
      linarith
    have hTden : T * (1 + γ + 1 / α) ≤ 1 := by
      have h := (lt_min_iff.mp hTlt').2
      rw [lt_div_iff₀ hden_pos] at h
      linarith
    have hsqT : T ^ 2 ≤ T := by nlinarith
    have hdiv_sq : T ^ 2 / α ≤ T / α := by
      rw [div_le_div_iff_of_pos_right hα]
      exact hsqT
    have hs_lt : γ * T + T ^ 2 / α < 1 := by
      have h2 : γ * T + T ^ 2 / α ≤ T * (γ + 1 / α) := by
        have h2' : T * (γ + 1 / α) = γ * T + T / α := by ring
        rw [h2']
        linarith [hdiv_sq]
      have h3 : T * (γ + 1 / α) ≤ T * (1 + γ + 1 / α) := by
        nlinarith [hTpos.le]
      linarith
    have hquad : T ^ 2 / 2 + T ^ 2 / α + γ * m * T ^ 2 + m * T ^ 3 / α ≤ (m - γ) * T := by
      have hTC2 : T * (T * C) ≤ T * (m - γ) := mul_le_mul_of_nonneg_left hTC hTpos.le
      have hexp : T * (T * C) =
          T ^ 2 / 2 + T ^ 2 / α + γ * m * T ^ 2 + m * T ^ 2 / α := by
        rw [hC]
        ring
      have hT3 : T ^ 3 ≤ T ^ 2 := by nlinarith
      have h4 : m * T ^ 3 / α ≤ m * T ^ 2 / α := by
        rw [div_le_div_iff_of_pos_right hα]
        exact mul_le_mul_of_nonneg_left hT3 hm_pos.le
      calc
        T ^ 2 / 2 + T ^ 2 / α + γ * m * T ^ 2 + m * T ^ 3 / α ≤
            T ^ 2 / 2 + T ^ 2 / α + γ * m * T ^ 2 + m * T ^ 2 / α := by linarith
        _ = T * (T * C) := hexp.symm
        _ ≤ T * (m - γ) := hTC2
        _ = (m - γ) * T := by ring
    have hs_eq : α / (α - α * γ * T - T ^ 2) = 1 / (1 - (γ * T + T ^ 2 / α)) := by
      have hden : α - α * γ * T - T ^ 2 = α * (1 - (γ * T + T ^ 2 / α)) := by
        field_simp [hα.ne']
        ring
      have h1s' : (1 : ℝ) - (γ * T + T ^ 2 / α) ≠ 0 :=
        sub_ne_zero.mpr (by linarith [hs_lt] : (1 : ℝ) ≠ γ * T + T ^ 2 / α)
      rw [hden]
      field_simp [hα.ne', h1s']
    refine ⟨hs_lt, ?_, ?_⟩
    · rw [hs_eq]
      have hmain := sqrt_coeff_le_exp hα hTpos hquad hs_lt
      calc
        (1 / (1 - (γ * T + T ^ 2 / α))) * Real.sqrt (1 + T ^ 2) =
            Real.sqrt (1 + T ^ 2) / (1 - (γ * T + T ^ 2 / α)) := by ring
        _ ≤ Real.exp (m * T) := hmain
        _ = Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) := by rw [hm]
    · rw [hs_eq]
      have hsmall : T * (1 + γ) + T ^ 2 / α ≤ 1 := by
        have h2 : T * (1 + γ) + T ^ 2 / α ≤ T * (1 + γ) + T / α := by
          linarith [hdiv_sq]
        have h3 : T * (1 + γ) + T / α ≤ T * (1 + γ + 1 / α) := by
          have h4 : T * (1 + γ + 1 / α) = T * (1 + γ) + T / α := by ring
          rw [h4]
        linarith
      have hmain := t_sq_coeff_le_exp hm_pos hTpos hsmall hs_lt
      calc
        (1 / (1 - (γ * T + T ^ 2 / α))) * T ^ 2 = T ^ 2 / (1 - (γ * T + T ^ 2 / α)) := by
          ring
        _ ≤ (Real.exp (m * T) - 1) / m := hmain
        _ = (Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) - 1) /
            Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) := by rw [hm]

/-- Remark 7.2(ii) at the level of the estimates themselves: for all
  sufficiently small `T > 0`, the right-hand side of the fixed-point estimate
  (25) is at most the right-hand side of the sup-norm estimate (28), for every
  choice of nonnegative data `A₀ = ‖u₀^μ - u₀^{μ'}‖`, `B₀ = ‖v₀^μ - v₀^{μ'}‖`,
  `c = ‖μ - μ'‖^{θ₂}` and `θ₁ ≥ 0`.  Together with `rem_4_refinement_threshold`
  this is the precise content of the paper's claim that (25) "refines" (28) by
  sharp error bounds — valid on short horizons, not for all `T` with
  `γT + T²/α ∈ [0,1)`. -/
theorem rem_4_refinement_bound (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ∈ Set.Ioo (0 : ℝ) T₀, ∀ θ₁ : ℝ, 0 ≤ θ₁ →
      ∀ A₀ B₀ c : ℝ, 0 ≤ A₀ → 0 ≤ B₀ → 0 ≤ c →
        (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀ + T ^ 2 * θ₁ * c) ≤
          Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) *
              Real.sqrt (A₀ ^ 2 + B₀ ^ 2) +
            (θ₁ / Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2)) *
              (Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) - 1) * c := by
  obtain ⟨T₀, hT₀, hT⟩ := rem_4_refinement_threshold α γ hα hγ
  refine ⟨T₀, hT₀, ?_⟩
  intro T hTmem θ₁ hθ₁ A₀ B₀ c hA hB hc
  obtain ⟨hs, hcoeff₁, hcoeff₂⟩ := hT T hTmem
  set m : ℝ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) with hm
  have hm_pos : 0 < m := by
    rw [hm]
    exact Real.sqrt_pos.mpr (by positivity)
  have hcoeff₁' : (α / (α - α * γ * T - T ^ 2)) * Real.sqrt (1 + T ^ 2) ≤
      Real.exp (m * T) := by
    rw [hm]
    exact hcoeff₁
  have hcoeff₂' : (α / (α - α * γ * T - T ^ 2)) * T ^ 2 ≤
      (Real.exp (m * T) - 1) / m := by
    rw [hm]
    exact hcoeff₂
  have hden_pos : 0 < α - α * γ * T - T ^ 2 := by
    have hcore : α * γ * T + T ^ 2 < α := by
      calc
        α * γ * T + T ^ 2 = α * (γ * T + T ^ 2 / α) := by field_simp [hα.ne']
        _ < α * 1 := mul_lt_mul_of_pos_left hs hα
        _ = α := by ring
    nlinarith
  have hg_nonneg : 0 ≤ α / (α - α * γ * T - T ^ 2) := div_nonneg hα.le hden_pos.le
  have hcs : A₀ + T * B₀ ≤ Real.sqrt (1 + T ^ 2) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) := by
    have h2 : (A₀ + T * B₀) ^ 2 ≤ (1 + T ^ 2) * (A₀ ^ 2 + B₀ ^ 2) := by
      nlinarith [sq_nonneg (T * A₀ - B₀)]
    calc
      A₀ + T * B₀ ≤ Real.sqrt ((1 + T ^ 2) * (A₀ ^ 2 + B₀ ^ 2)) :=
        Real.le_sqrt_of_sq_le h2
      _ = Real.sqrt (1 + T ^ 2) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) :=
        Real.sqrt_mul (by positivity) _
  have hmain₁ : (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀) ≤
      Real.exp (m * T) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) := by
    calc
      (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀) ≤
          (α / (α - α * γ * T - T ^ 2)) *
            (Real.sqrt (1 + T ^ 2) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hg_nonneg
      _ = ((α / (α - α * γ * T - T ^ 2)) * Real.sqrt (1 + T ^ 2)) *
            Real.sqrt (A₀ ^ 2 + B₀ ^ 2) := by ring
      _ ≤ Real.exp (m * T) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) :=
        mul_le_mul_of_nonneg_right hcoeff₁' (Real.sqrt_nonneg _)
  have hmain₂ : (α / (α - α * γ * T - T ^ 2)) * (T ^ 2 * θ₁ * c) ≤
      (θ₁ / m) * (Real.exp (m * T) - 1) * c := by
    calc
      (α / (α - α * γ * T - T ^ 2)) * (T ^ 2 * θ₁ * c) =
          ((α / (α - α * γ * T - T ^ 2)) * T ^ 2) * (θ₁ * c) := by ring
      _ ≤ ((Real.exp (m * T) - 1) / m) * (θ₁ * c) :=
        mul_le_mul_of_nonneg_right hcoeff₂' (mul_nonneg hθ₁ hc)
      _ = (θ₁ / m) * (Real.exp (m * T) - 1) * c := by ring
  calc
    (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀ + T ^ 2 * θ₁ * c) =
        (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀) +
          (α / (α - α * γ * T - T ^ 2)) * (T ^ 2 * θ₁ * c) := by ring
    _ ≤ Real.exp (m * T) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) +
          (θ₁ / m) * (Real.exp (m * T) - 1) * c := add_le_add hmain₁ hmain₂
    _ = Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) *
            Real.sqrt (A₀ ^ 2 + B₀ ^ 2) +
          (θ₁ / Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2)) *
            (Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) - 1) * c := by
      rw [hm]

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
