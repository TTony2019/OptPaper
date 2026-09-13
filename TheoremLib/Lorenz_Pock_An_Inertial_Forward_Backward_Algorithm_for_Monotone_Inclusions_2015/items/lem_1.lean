import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_5
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_3

open Filter

open ERealFunction

namespace LorenzPock

/-- Lemma 6: the parameter choice (25) verifies the numerical conditions
(22) and (24). -/
private theorem inertial_cap_quadratic (m ε a : ℝ) (hm : 0 < m)
    (hε : 0 < ε ∧ ε < (9 - 4 * m) / (2 * m))
    (ha : 0 ≤ a ∧ a ≤
      1 + (Real.sqrt (9 - 4 * m - 2 * ε * m) - 3) / m) :
    0 ≤ 1 - 3 * a - ε - (1 - a)^2 * m / 2 := by
  let D : ℝ := 9 - 4 * m - 2 * ε * m
  have htwo_m : 0 < 2 * m := by positivity
  have hD : 0 < D := by
    have h := (lt_div_iff₀ htwo_m).mp hε.2
    dsimp [D]
    nlinarith
  have hnum : 0 < 9 - 4 * m := by
    have hdiv : 0 < (9 - 4 * m) / (2 * m) := lt_trans hε.1 hε.2
    rcases (div_pos_iff.mp hdiv) with h | h
    · exact h.1
    · nlinarith [htwo_m, h.2]
  have hbase : 0 ≤ m * a - (m - 3) := by
    nlinarith [ha.1]
  have hsq : (Real.sqrt D)^2 = D := Real.sq_sqrt hD.le
  have hcap : (a - 1) * m ≤ Real.sqrt D - 3 := by
    apply (le_div_iff₀ hm).mp
    nlinarith [ha.2]
  have hsqrt : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  dsimp [D] at hsq hsqrt hcap ⊢
  nlinarith

theorem primal_dual_steps_feasible {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (p : SaddlePointProblem X Y) (γ δ r ε : ℝ) (α : ℕ → ℝ)
    (it : InertialPrimalDualIteration X Y p.gradQ p.gradPStar p.K
      (subdifferential p.G) (subdifferential p.FStar)
      α (‖p.K‖ * r + p.LQ / γ)⁻¹ (‖p.K‖ / r + p.LP / δ)⁻¹)
    (hγ : 0 < γ ∧ γ < 2) (hδ : 0 < δ ∧ δ < 2) (hr : 0 < r)
    (hLQ : 0 < p.LQ) (hLP : 0 < p.LP)
    (hε : 0 < ε ∧ ε < (9 - 4 * max γ δ) / (2 * max γ δ))
    (hα_mono : Monotone α)
    (hα : ∀ k, 0 ≤ α k ∧ α k ≤
      1 + (Real.sqrt (9 - 4 * max γ δ - 2 * ε * max γ δ) - 3) / max γ δ) :
    let τ := (‖p.K‖ * r + p.LQ / γ)⁻¹
    let σ := (‖p.K‖ / r + p.LP / δ)⁻¹
    (0 < τ ∧ τ < 2 / p.LQ) ∧ (0 < σ ∧ σ < 2 / p.LP) ∧
    ‖p.K‖ ^ 2 < (τ⁻¹ - p.LQ / 2) * (σ⁻¹ - p.LP / 2) ∧
    (∀ k, ((1 - 3 * α k - ε) / τ - (1 - α k)^2 * p.LQ / 2) *
      ((1 - 3 * α k - ε) / σ - (1 - α k)^2 * p.LP / 2) ≥
        (1 - 3 * α k - ε)^2 * ‖p.K‖^2) ∧
    (∀ k, (1 - 3 * α k - ε) / τ ≥ (1 - α k)^2 * p.LQ / 2) ∧
    (∀ k, (1 - 3 * α k - ε) / σ ≥ (1 - α k)^2 * p.LP / 2) := by
  dsimp
  let m : ℝ := max γ δ
  have hm : 0 < m := lt_max_of_lt_left hγ.1
  have hq : ∀ k, 0 ≤ 1 - 3 * α k - ε - (1 - α k)^2 * m / 2 := fun k =>
    inertial_cap_quadratic m ε (α k) hm (by simpa [m] using hε) (by simpa [m] using hα k)
  have hA : ∀ k, 0 ≤ 1 - 3 * α k - ε := by
    intro k
    have := hq k
    have hm0 : 0 ≤ m := hm.le
    nlinarith [sq_nonneg (1 - α k)]
  have hu : 0 < ‖p.K‖ * r + p.LQ / γ := by
    have : 0 < p.LQ / γ := div_pos hLQ hγ.1
    exact add_pos_of_nonneg_of_pos (mul_nonneg (norm_nonneg _) hr.le) this
  have hv : 0 < ‖p.K‖ / r + p.LP / δ := by
    have : 0 < p.LP / δ := div_pos hLP hδ.1
    exact add_pos_of_nonneg_of_pos (div_nonneg (norm_nonneg _) hr.le) this
  have hτ : (0 < (‖p.K‖ * r + p.LQ / γ)⁻¹ ∧
      (‖p.K‖ * r + p.LQ / γ)⁻¹ < 2 / p.LQ) := by
    constructor
    · exact inv_pos.mpr hu
    · have hden : p.LQ / 2 < ‖p.K‖ * r + p.LQ / γ := by
        have hfrac : 0 < p.LQ * (2 - γ) / (2 * γ) :=
          div_pos (mul_pos hLQ (sub_pos.mpr hγ.2)) (mul_pos (by norm_num) hγ.1)
        have hid : p.LQ / γ - p.LQ / 2 = p.LQ * (2 - γ) / (2 * γ) := by
          field_simp [hγ.1.ne']
        have hkr : 0 ≤ ‖p.K‖ * r := mul_nonneg (norm_nonneg _) hr.le
        nlinarith [hid, hfrac]
      rw [show 2 / p.LQ = 1 / (p.LQ / 2) by field_simp,
        show (‖p.K‖ * r + p.LQ / γ)⁻¹ = 1 / (‖p.K‖ * r + p.LQ / γ) by rw [one_div]]
      exact one_div_lt_one_div_of_lt (by positivity) hden
  have hσ : (0 < (‖p.K‖ / r + p.LP / δ)⁻¹ ∧
      (‖p.K‖ / r + p.LP / δ)⁻¹ < 2 / p.LP) := by
    constructor
    · exact inv_pos.mpr hv
    · have hden : p.LP / 2 < ‖p.K‖ / r + p.LP / δ := by
        have hfrac : 0 < p.LP * (2 - δ) / (2 * δ) :=
          div_pos (mul_pos hLP (sub_pos.mpr hδ.2)) (mul_pos (by norm_num) hδ.1)
        have hid : p.LP / δ - p.LP / 2 = p.LP * (2 - δ) / (2 * δ) := by
          field_simp [hδ.1.ne']
        have hkr : 0 ≤ ‖p.K‖ / r := div_nonneg (norm_nonneg _) hr.le
        nlinarith [hid, hfrac]
      rw [show 2 / p.LP = 1 / (p.LP / 2) by field_simp,
        show (‖p.K‖ / r + p.LP / δ)⁻¹ = 1 / (‖p.K‖ / r + p.LP / δ) by rw [one_div]]
      exact one_div_lt_one_div_of_lt (by positivity) hden
  refine ⟨hτ, hσ, ?_, ?_, ?_, ?_⟩
  · rw [inv_inv, inv_inv]
    have hqγ : 0 < p.LQ * (2 - γ) / (2 * γ) :=
      div_pos (mul_pos hLQ (sub_pos.mpr hγ.2)) (mul_pos (by norm_num) hγ.1)
    have hqδ : 0 < p.LP * (2 - δ) / (2 * δ) :=
      div_pos (mul_pos hLP (sub_pos.mpr hδ.2)) (mul_pos (by norm_num) hδ.1)
    have hmid : 0 ≤ ‖p.K‖ * (r * (p.LP * (2 - δ) / (2 * δ)) +
        (p.LQ * (2 - γ) / (2 * γ)) / r) := by
      exact mul_nonneg (norm_nonneg _) (add_nonneg (mul_nonneg hr.le hqδ.le) (div_nonneg hqγ.le hr.le))
    have hlast : 0 < (p.LQ * (2 - γ) / (2 * γ)) *
        (p.LP * (2 - δ) / (2 * δ)) := mul_pos hqγ hqδ
    have hexpand :
        (‖p.K‖ * r + p.LQ / γ - p.LQ / 2) *
          (‖p.K‖ / r + p.LP / δ - p.LP / 2) =
          ‖p.K‖ ^ 2 + ‖p.K‖ * (r * (p.LP * (2 - δ) / (2 * δ)) +
            (p.LQ * (2 - γ) / (2 * γ)) / r) +
          (p.LQ * (2 - γ) / (2 * γ)) * (p.LP * (2 - δ) / (2 * δ)) := by
      field_simp [hγ.1.ne', hδ.1.ne', hr.ne']
      ring
    rw [hexpand]
    nlinarith
  · intro k
    let A : ℝ := 1 - 3 * α k - ε
    have hγm : γ ≤ m := by simp [m]
    have hδm : δ ≤ m := by simp [m]
    have hqγ : 0 ≤ A - (1 - α k)^2 * γ / 2 := by
      have hrest : 0 ≤ (1 - α k)^2 * (m - γ) / 2 :=
        div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hγm)) (by norm_num)
      calc
        A - (1 - α k)^2 * γ / 2 =
            (A - (1 - α k)^2 * m / 2) + (1 - α k)^2 * (m - γ) / 2 := by ring
        _ ≥ 0 := add_nonneg (by simpa [A] using hq k) hrest
    have hqδ : 0 ≤ A - (1 - α k)^2 * δ / 2 := by
      have hrest : 0 ≤ (1 - α k)^2 * (m - δ) / 2 :=
        div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hδm)) (by norm_num)
      calc
        A - (1 - α k)^2 * δ / 2 =
            (A - (1 - α k)^2 * m / 2) + (1 - α k)^2 * (m - δ) / 2 := by ring
        _ ≥ 0 := add_nonneg (by simpa [A] using hq k) hrest
    have hU : A * ‖p.K‖ * r ≤
        A / (‖p.K‖ * r + p.LQ / γ)⁻¹ - (1 - α k)^2 * p.LQ / 2 := by
      have : 0 ≤ p.LQ / γ * (A - (1 - α k)^2 * γ / 2) :=
        mul_nonneg (div_nonneg hLQ.le hγ.1.le) hqγ
      have hid : A / (‖p.K‖ * r + p.LQ / γ)⁻¹ - (1 - α k)^2 * p.LQ / 2 =
          A * ‖p.K‖ * r + p.LQ / γ * (A - (1 - α k)^2 * γ / 2) := by
        simp only [div_eq_mul_inv, inv_inv]
        field_simp [hγ.1.ne']
        ring
      rw [hid]
      linarith
    have hV : A * ‖p.K‖ / r ≤
        A / (‖p.K‖ / r + p.LP / δ)⁻¹ - (1 - α k)^2 * p.LP / 2 := by
      have : 0 ≤ p.LP / δ * (A - (1 - α k)^2 * δ / 2) :=
        mul_nonneg (div_nonneg hLP.le hδ.1.le) hqδ
      have hid : A / (‖p.K‖ / r + p.LP / δ)⁻¹ - (1 - α k)^2 * p.LP / 2 =
          A * ‖p.K‖ / r + p.LP / δ * (A - (1 - α k)^2 * δ / 2) := by
        simp only [div_eq_mul_inv, inv_inv]
        field_simp [hδ.1.ne', hr.ne']
        ring
      rw [hid]
      linarith
    have hUnonneg : 0 ≤ A / (‖p.K‖ * r + p.LQ / γ)⁻¹ -
        (1 - α k)^2 * p.LQ / 2 := by
      have hAn : 0 ≤ A := by simpa [A] using hA k
      have : 0 ≤ A * ‖p.K‖ * r := mul_nonneg (mul_nonneg hAn (norm_nonneg _)) hr.le
      exact this.trans hU
    have hVnonneg : 0 ≤ A / (‖p.K‖ / r + p.LP / δ)⁻¹ -
        (1 - α k)^2 * p.LP / 2 := by
      have hAn : 0 ≤ A := by simpa [A] using hA k
      have : 0 ≤ A * ‖p.K‖ / r := div_nonneg (mul_nonneg hAn (norm_nonneg _)) hr.le
      exact this.trans hV
    have hleft : 0 ≤ A * ‖p.K‖ / r := by
      exact div_nonneg (mul_nonneg (by simpa [A] using hA k) (norm_nonneg _)) hr.le
    have hprod := mul_le_mul hU hV hleft hUnonneg
    have heq : (A * ‖p.K‖ * r) * (A * ‖p.K‖ / r) = A^2 * ‖p.K‖^2 := by
      field_simp [hr.ne']
    dsimp [A] at hprod heq ⊢
    nlinarith [hprod, heq]
  · intro k
    let A : ℝ := 1 - 3 * α k - ε
    have hγm : γ ≤ m := by simp [m]
    have hqγ : 0 ≤ A - (1 - α k)^2 * γ / 2 := by
      have hrest : 0 ≤ (1 - α k)^2 * (m - γ) / 2 :=
        div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hγm)) (by norm_num)
      calc
        A - (1 - α k)^2 * γ / 2 =
            (A - (1 - α k)^2 * m / 2) + (1 - α k)^2 * (m - γ) / 2 := by ring
        _ ≥ 0 := add_nonneg (by simpa [A] using hq k) hrest
    have : 0 ≤ p.LQ / γ * (A - (1 - α k)^2 * γ / 2) :=
      mul_nonneg (div_nonneg hLQ.le hγ.1.le) hqγ
    have hid : A / (‖p.K‖ * r + p.LQ / γ)⁻¹ - (1 - α k)^2 * p.LQ / 2 =
        A * ‖p.K‖ * r + p.LQ / γ * (A - (1 - α k)^2 * γ / 2) := by
      simp only [div_eq_mul_inv, inv_inv]
      field_simp [hγ.1.ne']
      ring
    apply sub_nonneg.mp
    change 0 ≤ A / (‖p.K‖ * r + p.LQ / γ)⁻¹ - (1 - α k)^2 * p.LQ / 2
    rw [hid]
    exact add_nonneg (mul_nonneg (mul_nonneg (by simpa [A] using hA k) (norm_nonneg _)) hr.le) this
  · intro k
    let A : ℝ := 1 - 3 * α k - ε
    have hδm : δ ≤ m := by simp [m]
    have hqδ : 0 ≤ A - (1 - α k)^2 * δ / 2 := by
      have hrest : 0 ≤ (1 - α k)^2 * (m - δ) / 2 :=
        div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hδm)) (by norm_num)
      calc
        A - (1 - α k)^2 * δ / 2 =
            (A - (1 - α k)^2 * m / 2) + (1 - α k)^2 * (m - δ) / 2 := by ring
        _ ≥ 0 := add_nonneg (by simpa [A] using hq k) hrest
    have : 0 ≤ p.LP / δ * (A - (1 - α k)^2 * δ / 2) :=
      mul_nonneg (div_nonneg hLP.le hδ.1.le) hqδ
    have hid : A / (‖p.K‖ / r + p.LP / δ)⁻¹ - (1 - α k)^2 * p.LP / 2 =
        A * ‖p.K‖ / r + p.LP / δ * (A - (1 - α k)^2 * δ / 2) := by
      simp only [div_eq_mul_inv, inv_inv]
      field_simp [hδ.1.ne', hr.ne']
      ring
    apply sub_nonneg.mp
    change 0 ≤ A / (‖p.K‖ / r + p.LP / δ)⁻¹ - (1 - α k)^2 * p.LP / 2
    rw [hid]
    exact add_nonneg (div_nonneg (mul_nonneg (by simpa [A] using hA k) (norm_nonneg _)) hr.le) this

end LorenzPock
