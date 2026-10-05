import TheoremLib.Dual_guided_2026.SDOTEmpiricalProcess

/-!
# Quantitative grids for potential balls

Rounding each coordinate down on a lattice gives a finite cover of a potential
ball. Its cardinality is bounded explicitly, rather than using compactness
without a covering-size estimate.
-/

namespace DualGuided2026

open scoped BigOperators

noncomputable def coordinateGrid {n : ℕ} (gStar : Fin n → ℝ) (r δ : ℝ) :
    Finset (Fin n → ℝ) := by
  classical
  exact Finset.univ.image (fun k : Fin n → Fin (Nat.ceil (2 * r / δ) + 1) =>
    fun j => gStar j - r + δ * (k j : ℝ))

theorem coordinateGrid_card_le {n : ℕ} (gStar : Fin n → ℝ) (r δ : ℝ) :
    (coordinateGrid gStar r δ).card ≤ (Nat.ceil (2 * r / δ) + 1) ^ n := by
  classical
  unfold coordinateGrid
  exact (Finset.card_image_le).trans_eq (by simp)

private theorem ceil_ratio_le {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    (Nat.ceil (2 * r / δ) : ℝ) ≤ 2 * r / δ + 1 := by
  have hc : (Nat.ceil (2 * r / δ) : ℝ) ≤ (Nat.floor (2 * r / δ) : ℝ) + 1 := by
    exact_mod_cast Nat.ceil_le_floor_add_one (2 * r / δ)
  exact hc.trans (add_le_add (Nat.floor_le (by positivity)) le_rfl)

theorem coordinateGrid_card_real_le {n : ℕ} (gStar : Fin n → ℝ)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    ((coordinateGrid gStar r δ).card : ℝ) ≤ (2 * r / δ + 2) ^ n := by
  have hc : ((coordinateGrid gStar r δ).card : ℝ) ≤
      ((Nat.ceil (2 * r / δ) : ℝ) + 1) ^ n := by
    exact_mod_cast coordinateGrid_card_le gStar r δ
  have hceil := ceil_ratio_le hr hδ
  exact hc.trans (pow_le_pow_left₀ (by positivity) (by linarith) n)

theorem coordinateGrid_norm_le {n : ℕ} (gStar : Fin n → ℝ)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) {g : Fin n → ℝ}
    (hg : g ∈ coordinateGrid gStar r δ) : ‖g - gStar‖ ≤ r + δ := by
  classical
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hg
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hk : (k j : ℝ) ≤ (Nat.ceil (2 * r / δ) : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ (k j).isLt
  have hbound := hk.trans (ceil_ratio_le hr hδ)
  have hmul := mul_le_mul_of_nonneg_left hbound hδ.le
  have heq : δ * (2 * r / δ + 1) = 2 * r + δ := by field_simp
  rw [heq] at hmul
  have hk0 : 0 ≤ (k j : ℝ) := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith

theorem coordinateGrid_covers {n : ℕ} (gStar : Fin n → ℝ)
    {r δ : ℝ} (_hr : 0 ≤ r) (hδ : 0 < δ) (h : Fin n → ℝ) (hh : ‖h - gStar‖ ≤ r) :
    ∃ g ∈ coordinateGrid gStar r δ, ∀ j, |h j - g j| ≤ δ := by
  classical
  let q : Fin n → ℝ := fun j => (h j - gStar j + r) / δ
  have hclose (j : Fin n) : |h j - gStar j| ≤ r := by
    have hj : |h j - gStar j| ≤ ‖h - gStar‖ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (h - gStar) j
    exact hj.trans hh
  have hq0 (j : Fin n) : 0 ≤ q j := by
    apply div_nonneg _ hδ.le
    linarith [(abs_le.mp (hclose j)).1]
  have hqle (j : Fin n) : q j ≤ 2 * r / δ := by
    apply div_le_div_of_nonneg_right _ hδ.le
    linarith [(abs_le.mp (hclose j)).2]
  let k : Fin n → Fin (Nat.ceil (2 * r / δ) + 1) := fun j =>
    ⟨Nat.floor (q j), Nat.lt_succ_iff.mpr
      ((Nat.floor_mono (hqle j)).trans (Nat.floor_le_ceil (2 * r / δ)))⟩
  let g : Fin n → ℝ := fun j => gStar j - r + δ * (k j : ℝ)
  refine ⟨g, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, ?_⟩
  intro j
  have hf := Nat.floor_le (hq0 j)
  have hf' := Nat.lt_floor_add_one (q j)
  have hlo := (le_div_iff₀ hδ).mp hf
  have hhi := (div_lt_iff₀ hδ).mp hf'
  change |h j - (gStar j - r + δ * (Nat.floor (q j) : ℝ))| ≤ δ
  rw [abs_of_nonneg (by linarith)]
  linarith

open MeasureTheory

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem shiftPotentialCoordinate_close (data : HELLOSDOTData X Ω)
    (gStar g : Fin data.n → ℝ) {r δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ‖g - gStar‖ ≤ r) (j : Fin data.n) {t : ℝ} (ht : |t| ≤ 2 * δ) :
    ∀ k, |shiftPotentialCoordinate g j t k - gStar k| ≤ r + 2 * δ := by
  classical
  intro k
  have hk : |g k - gStar k| ≤ r := by
    have hcoord := norm_le_pi_norm (g - gStar) k
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
    exact hcoord.trans hg
  by_cases hkj : k = j
  · subst k
    simp only [shiftPotentialCoordinate, Function.update_self]
    calc
      |g j + t - gStar j| = |(g j - gStar j) + t| := by congr 1; ring
      _ ≤ |g j - gStar j| + |t| := abs_add_le _ _
      _ ≤ r + 2 * δ := add_le_add hk ht
  · simp only [shiftPotentialCoordinate, Function.update_of_ne hkj]
    exact hk.trans (by linarith)

/-- Both endpoints of each coordinate bracket have a small second moment.
Summing these bounds over the finite grid makes the estimate applicable to
the sample-dependent potential. -/
theorem gridEndpointEnergy_integral_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gStar : Fin data.n → ℝ) {m : ℕ}, 0 < m →
        ∀ (grid : Finset (Fin data.n → ℝ)) {r δ : ℝ}, 0 < r → 0 ≤ δ →
          (∀ g ∈ grid, ‖g - gStar‖ ≤ r) →
          (∫ samples, gridEndpointEnergy data gStar grid δ samples
            ∂sourceBatchMeasure data m) ≤ (grid.card : ℝ) * C * (r + 2 * δ) / (m : ℝ) := by
  classical
  obtain ⟨C, hC, hmass⟩ := movingCellEnvelope_measure_le data hregular
  let B := ∑ j, 1 / data.b j
  have hB : 0 ≤ B :=
    Finset.sum_nonneg fun j _ => div_nonneg (by norm_num) (data.b_pos j).le
  refine ⟨2 * C * B, by positivity, ?_⟩
  intro gStar m hm grid r δ hr hδ hgrid
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hρ : 0 < r + 2 * δ := by linarith
  have hmassReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass gStar _ hρ)
  rw [ENNReal.toReal_ofReal (mul_nonneg hC hρ.le)] at hmassReal
  have hfixed (g : Fin data.n → ℝ) (hg : g ∈ grid) (j : Fin data.n)
      (t : ℝ) (ht : |t| ≤ 2 * δ) :
      (∫ samples, movingCellEmpiricalRemainder data gStar samples
          (shiftPotentialCoordinate g j t) j ^ 2 ∂sourceBatchMeasure data m) ≤
        C * (r + 2 * δ) / (m : ℝ) := by
    rw [integral_fixedMovingCellEmpiricalRemainder_sq data _ _ hm]
    exact div_le_div_of_nonneg_right
      ((variance_cellIndicator_difference_le_envelope data _ _ _
        (shiftPotentialCoordinate_close data gStar g hδ (hgrid g hg) j ht) j).trans
          hmassReal) hmreal.le
  have hneg : |-2 * δ| ≤ 2 * δ := by rw [abs_of_nonpos (by linarith)]; linarith
  have hpos : |2 * δ| ≤ 2 * δ := by rw [abs_of_nonneg (by positivity)]
  have hterm (g : Fin data.n → ℝ) (j : Fin data.n) :
      Integrable (fun samples : Fin m → X =>
        (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j ^ 2 +
          movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j ^ 2) / data.b j)
        (sourceBatchMeasure data m) :=
    (((memLp_fixedMovingCellEmpiricalRemainder data gStar
      (shiftPotentialCoordinate g j (-2 * δ)) j).integrable_sq).add
        ((memLp_fixedMovingCellEmpiricalRemainder data gStar
          (shiftPotentialCoordinate g j (2 * δ)) j).integrable_sq)).div_const _
  unfold gridEndpointEnergy
  rw [integral_finset_sum grid
    (fun g _ => integrable_finset_sum Finset.univ fun j _ => hterm g j)]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hterm _ j), integral_div,
    integral_add (memLp_fixedMovingCellEmpiricalRemainder data gStar
      (shiftPotentialCoordinate _ _ (-2 * δ)) _).integrable_sq
      (memLp_fixedMovingCellEmpiricalRemainder data gStar
        (shiftPotentialCoordinate _ _ (2 * δ)) _).integrable_sq]
  calc
    _ ≤ ∑ g ∈ grid, ∑ j,
        (C * (r + 2 * δ) / (m : ℝ) + C * (r + 2 * δ) / (m : ℝ)) / data.b j := by
      apply Finset.sum_le_sum
      intro g hg
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_right
        (add_le_add (hfixed g hg j _ hneg) (hfixed g hg j _ hpos)) (data.b_pos j).le
    _ = (grid.card : ℝ) * (2 * C * B) * (r + 2 * δ) / (m : ℝ) := by
      simp only [B, div_eq_mul_inv, one_mul, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
      ring

end DualGuided2026
