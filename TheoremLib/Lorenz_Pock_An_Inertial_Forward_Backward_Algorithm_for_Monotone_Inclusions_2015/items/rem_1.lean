import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_2

open Filter

open scoped Pointwise

namespace LorenzPock

private theorem scalar_alpha_bound_implies_condition (g e a : ℝ)
    (hg_pos : 0 < g) (hg_lt_two : g < 2) (he_pos : 0 < e)
    (he_upper : e < (9 - 4 * g) / (2 * g)) (ha_nonneg : 0 ≤ a)
    (ha_bound : a ≤ 1 + (Real.sqrt (9 - 4 * g - 2 * e * g) - 3) / g) :
    0 ≤ 1 - 3 * a - e - (1 - a)^2 * g / 2 := by
  let D : ℝ := 9 - 4 * g - 2 * e * g
  let r : ℝ := 1 + (Real.sqrt D - 3) / g
  have htg_pos : 0 < 2 * g := by positivity
  have hD_pos : 0 < D := by
    have h := (lt_div_iff₀ htg_pos).mp he_upper
    dsimp [D]
    nlinarith
  have hsqrt_sq : (Real.sqrt D)^2 = D := Real.sq_sqrt (le_of_lt hD_pos)
  have hroot : 1 - 3 * r - e - (1 - r)^2 * g / 2 = 0 := by
    dsimp [r]
    field_simp [ne_of_gt hg_pos]
    nlinarith [hsqrt_sq]
  have ha_le_r : a ≤ r := by
    simpa [r, D] using ha_bound
  have hr_nonneg : 0 ≤ r := le_trans ha_nonneg ha_le_r
  have hfactor_nonneg : 0 ≤ 3 - g + g * (a + r) / 2 := by
    have : 0 ≤ g * (a + r) / 2 := by positivity
    nlinarith
  have hdiff : 0 ≤ (r - a) * (3 - g + g * (a + r) / 2) :=
    mul_nonneg (sub_nonneg.mpr ha_le_r) hfactor_nonneg
  have hfactor :
      (1 - 3 * a - e - (1 - a)^2 * g / 2) -
        (1 - 3 * r - e - (1 - r)^2 * g / 2) =
      (r - a) * (3 - g + g * (a + r) / 2) := by ring
  rw [← hfactor, hroot] at hdiff
  simpa using hdiff

private theorem scalar_id_quadratic {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (c : ℝ) (u : H) :
    inner ℝ ((c • ContinuousLinearMap.id ℝ H) u) u = c * ‖u‖ ^ 2 := by
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_smul_left,
    real_inner_self_eq_norm_sq]
  simp

/-- The scalar-metric form of condition (17) from Remark 3. -/
theorem scalar_metric_inertial_condition {H : Type*} [NormedAddCommGroup H] [Nontrivial H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : SetValuedOperator H H) (B : H → H)
    (M L Linv : H →L[ℝ] H) (m l step : ℝ) (α ε γ ell : ℕ → ℝ)
    (it : InertialForwardBackwardIteration H A B M α ell)
    (S : Set H) (hsolution : S = {z | ∃ a ∈ A z, a + B z = 0})
    (hS_nonempty : S.Nonempty)
    (hmaxA : SetValuedOperator.IsMaximalMonotone A)
    (hmaxB : SetValuedOperator.IsMaximalMonotone
      (SetValuedOperator.ofFunction Set.univ (fun x ↦ B x)))
    (hM_selfadjoint : ∀ u v, inner ℝ (M u) v = inner ℝ u (M v))
    (hM_positive_definite : ∀ u, u ≠ 0 → 0 < inner ℝ (M u) u)
    (hL_selfadjoint : ∀ u v, inner ℝ (L u) v = inner ℝ u (L v))
    (hL_positive_definite : ∀ u, u ≠ 0 → 0 < inner ℝ (L u) u)
    (hLinv : Linv.comp L = ContinuousLinearMap.id ℝ H)
    (hM_scalar : M = m • ContinuousLinearMap.id ℝ H)
    (hL_scalar : L = l • ContinuousLinearMap.id ℝ H)
    (hB_lipschitz : ∃ cB : ℝ, 0 < cB ∧ ∀ u v, ‖B u - B v‖ ≤ cB * ‖u - v‖)
    (hcocoercive : IsCocoerciveWithInverseMetric B Linv S)
    (hγ : 0 < γ 0 ∧ γ 0 < 2)
    (hγ_definition : γ 0 = l * step / m)
    (hγ_constant : ∀ k, γ k = γ 0)
    (hstep_constant : ∀ k, ell k = step)
    (hε : 0 < ε 0 ∧ ε 0 < (9 - 4 * γ 0) / (2 * γ 0))
    (hε_constant : ∀ k, ε k = ε 0)
    (hα_mono : Monotone α)
    (hα_bound : ∀ k, 0 ≤ α k ∧ α k ≤ 1 + (Real.sqrt (9 - 4 * γ k - 2 * ε k * γ k) - 3) / γ k)
    (hconvergence_conditions : ∀ k, 0 < ell k)
    (hsummax : SetValuedOperator.IsMaximalMonotone
      (A + SetValuedOperator.ofFunction Set.univ
        (fun x : (Set.univ : Set H) ↦ B x.1))) :
    (∀ k, 0 ≤ 1 - 3 * α k - ε k - (1 - α k)^2 * γ k / 2) ∧
    ∃ z ∈ S, Tendsto (fun k ↦ toWeakSpace ℝ H (it.x k)) Filter.atTop
      (nhds (toWeakSpace ℝ H z)) := by
  let g : ℝ := γ 0
  let e : ℝ := ε 0
  have hg_pos : 0 < g := hγ.1
  have hg_lt_two : g < 2 := hγ.2
  have he_pos : 0 < e := hε.1
  have he_upper : e < (9 - 4 * g) / (2 * g) := hε.2
  have hscalar : ∀ k, 0 ≤ 1 - 3 * α k - ε k - (1 - α k)^2 * γ k / 2 := by
    intro k
    have hk := hα_bound k
    rw [hγ_constant k, hε_constant k] at hk
    rw [hε_constant k, hγ_constant k]
    exact scalar_alpha_bound_implies_condition g e (α k) hg_pos hg_lt_two he_pos he_upper
      hk.1 (by simpa [g, e] using hk.2)
  have hm_pos : 0 < m := by
    obtain ⟨u, hu⟩ := exists_ne (0 : H)
    have hpos := hM_positive_definite u hu
    rw [hM_scalar, scalar_id_quadratic] at hpos
    have hnorm : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    nlinarith
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hgamma_mul : m * g = l * step := by
    rw [show g = γ 0 by rfl, hγ_definition]
    field_simp [hm_ne]
  have hε_for_thm2 : ∃ e : ℝ, 0 < e ∧ ∀ k u, 0 ≤ inner ℝ
      ((((1 - 3 * α k) • M) - (((1 - α k)^2 * ell k / 2) • L) - e • M) u) u := by
    refine ⟨e, he_pos, ?_⟩
    intro k u
    have hq : 0 ≤ 1 - 3 * α k - e - (1 - α k)^2 * g / 2 := by
      simpa [g, e, hε_constant k, hγ_constant k] using hscalar k
    have hop :
        ((1 - 3 * α k) • M - ((1 - α k)^2 * ell k / 2) • L - e • M) =
          ((m * (1 - 3 * α k - e - (1 - α k)^2 * g / 2)) •
            ContinuousLinearMap.id ℝ H) := by
      rw [hM_scalar, hL_scalar, hstep_constant k]
      ext v
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      have hcoeff :
          (1 - 3 * α k) * m - ((1 - α k)^2 * step / 2) * l - e * m =
            m * (1 - 3 * α k - e - (1 - α k)^2 * g / 2) := by
        linear_combination ((1 - α k)^2 / 2) * hgamma_mul
      rw [← hcoeff]
      module
    rw [hop, scalar_id_quadratic]
    exact mul_nonneg (mul_nonneg (le_of_lt hm_pos) hq) (sq_nonneg ‖u‖)
  have hl_pos : 0 < l := by
    obtain ⟨u, hu⟩ := exists_ne (0 : H)
    have hpos := hL_positive_definite u hu
    rw [hL_scalar, scalar_id_quadratic] at hpos
    have hnorm : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    nlinarith
  have hl_ne : l ≠ 0 := ne_of_gt hl_pos
  have hlinv_smul : ∀ v, Linv (l • v) = v := by
    intro v
    rw [hL_scalar] at hLinv
    have hc : (Linv.comp (l • ContinuousLinearMap.id ℝ H)) v = v := by
      rw [hLinv]
      rfl
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] using hc
  have hu' : ∀ u, Linv u = l⁻¹ • u := by
    intro u
    calc
      Linv u = Linv (l • (l⁻¹ • u)) := by
        congr 1
        rw [smul_inv_smul₀ hl_ne]
      _ = l⁻¹ • u := hlinv_smul (l⁻¹ • u)
  have hLcomp : L.comp Linv = ContinuousLinearMap.id ℝ H := by
    rw [hL_scalar]
    ext u
    calc
      ((l • ContinuousLinearMap.id ℝ H).comp Linv) u = l • Linv u := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply]
      _ = u := by
        rw [hu', smul_smul, mul_inv_cancel₀ hl_ne, one_smul]
  have hdecomp : ∀ k,
      (M - (ell k / 2) • L) = ((m - ell k * l / 2) • ContinuousLinearMap.id ℝ H) := by
    intro k
    rw [hM_scalar, hL_scalar]
    ext v
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    have hcoeff : ell k / 2 * l = ell k * l / 2 := by ring
    rw [← hcoeff, ← sub_smul]
  have hα : ∃ αbar : ℝ, αbar < 1 ∧ ∀ k, 0 ≤ α k ∧ α k ≤ αbar := by
    refine ⟨1 / 3, by norm_num, ?_⟩
    intro k
    constructor
    · exact (hα_bound k).1
    · have hq : 0 ≤ 1 - 3 * α k - e - (1 - α k)^2 * g / 2 := by
        simpa [g, e, hε_constant k, hγ_constant k] using hscalar k
      have hαk_le : α k ≤ (1 - e) / 3 := by
        nlinarith [hq, hg_pos, he_pos, sq_nonneg (1 - α k)]
      nlinarith
  have hmetric : ∀ k u, u ≠ 0 → 0 < inner ℝ ((M - (ell k / 2) • L) u) u := by
    intro k u hu
    have hγk : γ k < 2 := by simpa [hγ_constant k] using hγ.2
    have hγk_def : γ k = l * ell k / m := by
      rw [hγ_constant k, hγ_definition, hstep_constant k]
    have hle2 : l * ell k < 2 * m := by
      rw [hγk_def] at hγk
      exact (div_lt_iff₀ hm_pos).mp hγk
    have hpos_coeff : 0 < m - ell k * l / 2 := by
      nlinarith
    rw [hdecomp k, scalar_id_quadratic]
    exact mul_pos hpos_coeff (sq_pos_of_pos (norm_pos_iff.mpr hu))
  have hM_coercive : ∃ cM : ℝ, 0 < cM ∧ ∀ u,
      cM * ‖u‖ ^ 2 ≤ inner ℝ (M u) u := by
    refine ⟨m / 2, by positivity, ?_⟩
    intro u
    rw [hM_scalar, scalar_id_quadratic]
    nlinarith [sq_nonneg ‖u‖, hm_pos]
  have hS_coercive : ∃ cS : ℝ, 0 < cS ∧ ∀ k u,
      cS * ‖u‖ ^ 2 ≤ inner ℝ ((M - (ell k / 2) • L) u) u := by
    have hγstep : l * step < 2 * m := by
      have hlt : l * step / m < 2 := by simpa [hγ_definition] using hγ.2
      nlinarith [hm_pos]
    have hcoeff_pos : 0 < m - l * step / 2 := by
      nlinarith
    refine ⟨(m - l * step / 2) / 2, by positivity, ?_⟩
    intro k u
    rw [hdecomp k, hstep_constant k, scalar_id_quadratic]
    nlinarith [hcoeff_pos, sq_nonneg ‖u‖]
  have hell_lower : ∃ l0 : ℝ, 0 < l0 ∧ ∀ k, l0 ≤ ell k := by
    have hstep_pos : 0 < step := by
      simpa [hstep_constant 0] using hconvergence_conditions 0
    refine ⟨step / 2, by positivity, ?_⟩
    intro k
    rw [hstep_constant k]
    nlinarith
  have hell_mono : Monotone ell := by
    intro i j hij
    rw [hstep_constant i, hstep_constant j]
  refine ⟨hscalar, ?_⟩
  exact inertial_lyapunov_condition_implies_weak_convergence A B M L Linv α ell it S
    hmaxA hmaxB hsolution hS_nonempty hLinv hLcomp hB_lipschitz
    hL_selfadjoint hL_positive_definite hcocoercive hconvergence_conditions hα
    hmetric hM_coercive hS_coercive hsummax hell_lower hα_mono hell_mono hε_for_thm2

end LorenzPock
