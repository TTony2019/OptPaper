import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.algo_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_2
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.lem_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.cor_2

open Filter

namespace BurachikSvaiterRobustnessHPE2001

private theorem hpe_tendsto_norm_of_sq_le {u b : ℕ → ℝ}
    (hu : ∀ k, 0 ≤ u k) (hb0 : Tendsto b Filter.atTop (nhds 0))
    (hle : ∀ k, u k ^ 2 ≤ b k) : Tendsto u Filter.atTop (nhds 0) := by
  have hsq : Tendsto (fun k => u k ^ 2) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb0
      (fun k => sq_nonneg (u k)) hle
  rw [← Real.sqrt_zero]
  convert hsq.sqrt using 1
  ext k
  exact (Real.sqrt_sq (hu k)).symm

private theorem hpe_tendsto_of_le_div_const {u b : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hu : ∀ k, 0 ≤ u k) (hb0 : Tendsto b Filter.atTop (nhds 0))
    (hle : ∀ k, c * u k ≤ b k) : Tendsto u Filter.atTop (nhds 0) := by
  have hdiv : Tendsto (fun k => b k / c) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      hb0.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => c⁻¹) Filter.atTop (nhds c⁻¹))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv hu
    (fun k => (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hle k))

/-- Corollary 3.3: asymptotic properties of HPE iterates when a zero exists. -/
theorem hpe_asymptotics {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T)
    (hzero : ∃ xStar, (0 : H) ∈ T xStar) :
    Bornology.IsBounded (Set.range A.x) ∧
    Tendsto (fun k ↦ ‖A.y k - A.x k‖) Filter.atTop (nhds 0) ∧
    Tendsto A.ε Filter.atTop (nhds 0) ∧
    Tendsto (fun k ↦ ‖A.v k‖) Filter.atTop (nhds 0) ∧
    Tendsto (fun k ↦ ‖A.c k • A.v k‖) Filter.atTop (nhds 0) := by
  rcases hzero with ⟨xStar, hxStar⟩
  rcases hpe_distance_converges A hxStar with ⟨L, hL0, hDist⟩
  have hδ0 : Tendsto A.δ Filter.atTop (nhds 0) := A.summable_delta.tendsto_atTop_zero
  have hα0 : Tendsto A.α Filter.atTop (nhds 0) := A.summable_alpha.tendsto_atTop_zero
  have hxBounded : Bornology.IsBounded (Set.range A.x) := by
    rcases isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ hDist) with ⟨C, hC⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖xStar‖, ?_⟩
    rintro z ⟨k, rfl⟩
    have hk : ‖A.x k - xStar‖ ≤ C := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC _ ⟨k, rfl⟩
    calc
      ‖A.x k‖ = ‖(A.x k - xStar) + xStar‖ := congrArg norm (by abel)
      _ ≤ ‖A.x k - xStar‖ + ‖xStar‖ := norm_add_le _ _
      _ ≤ C + ‖xStar‖ := add_le_add_left hk _
  have hDistSucc : Tendsto (fun k ↦ ‖A.x (k + 1) - xStar‖) Filter.atTop (nhds L) := by
    exact hDist.comp (Filter.tendsto_add_atTop_nat 1)
  have hExactDist : Tendsto (fun k ↦ ‖extragradientStep A k - xStar‖)
      Filter.atTop (nhds L) := by
    have herr0 : Tendsto (fun k ↦ ‖extragradientStep A k - xStar‖ -
        ‖A.x (k + 1) - xStar‖) Filter.atTop (nhds 0) := by
      have hneg0 : Tendsto (fun k ↦ -A.α k) Filter.atTop (nhds 0) := by
        simpa using hα0.neg
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg0 hα0
        (fun k => by
          have h := A.update_error k
          have hrev := abs_norm_sub_norm_le (extragradientStep A k - xStar)
            (A.x (k + 1) - xStar)
          rw [show (extragradientStep A k - xStar) - (A.x (k + 1) - xStar) =
              extragradientStep A k - A.x (k + 1) by abel, norm_sub_rev] at hrev
          have h' : ‖extragradientStep A k - A.x (k + 1)‖ ≤ A.α k := by
            simpa [extragradientStep, norm_sub_rev] using h
          simpa [norm_sub_rev] using (abs_le.mp (hrev.trans h')).1)
        (fun k => by
          have h := A.update_error k
          have hrev := abs_norm_sub_norm_le (extragradientStep A k - xStar)
            (A.x (k + 1) - xStar)
          rw [show (extragradientStep A k - xStar) - (A.x (k + 1) - xStar) =
              extragradientStep A k - A.x (k + 1) by abel, norm_sub_rev] at hrev
          have h' : ‖extragradientStep A k - A.x (k + 1)‖ ≤ A.α k := by
            simpa [extragradientStep, norm_sub_rev] using h
          simpa [norm_sub_rev] using (abs_le.mp (hrev.trans h')).2)
    simpa [sub_add_cancel] using herr0.add hDistSucc
  rcases A.sigma_bound with ⟨σbar, hσbar_pos, hσbar_lt_one, hσ⟩
  let q : ℝ := 1 - σbar ^ 2
  have hq : 0 < q := by dsimp [q]; nlinarith
  have hdispSqLe : ∀ k, q * ‖A.y k - A.x k‖ ^ 2 ≤
      ‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 + A.δ k := by
    intro k
    have hs := hσ k
    have hsSq : A.σ k ^ 2 ≤ σbar ^ 2 :=
      (sq_le_sq₀ (A.σ_nonneg k) hσbar_pos.le).mpr hs.2
    have hd := hpe_descent A hxStar k
    dsimp [q]
    nlinarith
  have hright0 : Tendsto (fun k ↦
      ‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 + A.δ k)
      Filter.atTop (nhds 0) := by
    have h1 : Tendsto (fun k ↦ ‖xStar - A.x k‖ ^ 2) Filter.atTop (nhds (L ^ 2)) := by
      simpa [norm_sub_rev] using hDist.pow 2
    have h2 : Tendsto (fun k ↦ ‖xStar - extragradientStep A k‖ ^ 2)
        Filter.atTop (nhds (L ^ 2)) := by
      simpa [norm_sub_rev] using hExactDist.pow 2
    simpa using (h1.sub h2).add hδ0
  have hdisp : Tendsto (fun k ↦ ‖A.y k - A.x k‖) Filter.atTop (nhds 0) := by
    refine hpe_tendsto_norm_of_sq_le (u := fun k => ‖A.y k - A.x k‖)
      (b := fun k => (‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 + A.δ k) / q)
      (fun k => norm_nonneg _) ?_ ?_
    · simpa [div_eq_mul_inv] using hright0.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => q⁻¹) Filter.atTop (nhds q⁻¹))
    · intro k
      exact (le_div_iff₀ hq).mpr (by simpa [mul_comm] using hdispSqLe k)
  have hprod0 : Tendsto (fun k ↦ (A.σ k) ^ 2 * ‖A.y k - A.x k‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hr0 : Tendsto (fun k ↦ ‖A.y k - A.x k‖ ^ 2) Filter.atTop (nhds 0) :=
      by simpa using hdisp.pow 2
    have hupper : Tendsto (fun k ↦ σbar ^ 2 * ‖A.y k - A.x k‖ ^ 2)
        Filter.atTop (nhds 0) := by simpa using tendsto_const_nhds.mul hr0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; positivity
    · intro k
      have hs := hσ k
      have hsSq : A.σ k ^ 2 ≤ σbar ^ 2 :=
        (sq_le_sq₀ (A.σ_nonneg k) hσbar_pos.le).mpr hs.2
      exact mul_le_mul_of_nonneg_right hsSq (sq_nonneg _)
  have hb0 : Tendsto (fun k ↦ A.δ k + (A.σ k) ^ 2 * ‖A.y k - A.x k‖ ^ 2)
      Filter.atTop (nhds 0) := by simpa using hδ0.add hprod0
  let R : ℕ → H := fun k => A.c k • A.v k + A.y k - A.x k
  have hRSqLe : ∀ k, ‖R k‖ ^ 2 ≤ A.δ k + (A.σ k) ^ 2 * ‖A.y k - A.x k‖ ^ 2 := by
    intro k
    have hr := A.residual_bound k
    dsimp [R]
    nlinarith [mul_nonneg (le_of_lt (A.c_pos k)) (A.ε_nonneg k)]
  have hR0 : Tendsto (fun k ↦ ‖R k‖) Filter.atTop (nhds 0) :=
    hpe_tendsto_norm_of_sq_le (fun k => norm_nonneg _) hb0 hRSqLe
  rcases A.c_lower_bound with ⟨cbar, hcbar_pos, hcbar_le⟩
  have hε0 : Tendsto A.ε Filter.atTop (nhds 0) := by
    refine hpe_tendsto_of_le_div_const (c := 2 * cbar) (by nlinarith) A.ε_nonneg hb0 ?_
    intro k
    have hr := A.residual_bound k
    have hc := hcbar_le k
    nlinarith [sq_nonneg ‖R k‖, mul_nonneg (le_of_lt (A.c_pos k)) (A.ε_nonneg k)]
  have hcv0 : Tendsto (fun k ↦ ‖A.c k • A.v k‖) Filter.atTop (nhds 0) := by
    have hsum : Tendsto (fun k ↦ ‖R k‖ + ‖A.y k - A.x k‖) Filter.atTop (nhds 0) := by
      simpa using hR0.add hdisp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    · intro k; exact norm_nonneg _
    · intro k
      have htri := norm_sub_le (R k) (A.y k - A.x k)
      have heq : A.c k • A.v k = R k - (A.y k - A.x k) := by
        dsimp [R]; abel
      change ‖A.c k • A.v k‖ ≤ ‖R k‖ + ‖A.y k - A.x k‖
      rw [heq]
      exact htri
  have hv0 : Tendsto (fun k ↦ ‖A.v k‖) Filter.atTop (nhds 0) := by
    refine hpe_tendsto_of_le_div_const (c := cbar) hcbar_pos (fun k => norm_nonneg _) hcv0 ?_
    intro k
    calc
      cbar * ‖A.v k‖ ≤ A.c k * ‖A.v k‖ :=
        mul_le_mul_of_nonneg_right (hcbar_le k) (norm_nonneg _)
      _ = ‖A.c k • A.v k‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (A.c_pos k)]
  exact ⟨hxBounded, hdisp, hε0, hv0, hcv0⟩

end BurachikSvaiterRobustnessHPE2001
