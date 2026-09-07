import Mathlib.Tactic

/-!
# Lemma 2.1
-/

open scoped InnerProductSpace

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Lemma 2.1: an error bound relating `u`, `v`, and `eta`. -/
lemma lemma_2_1
    {sigma : ℝ} (hsigma : 0 ≤ sigma ∧ sigma < 1)
    {u v eta : H}
    (hv : v = u + eta)
    (heta : ‖eta‖ ≤ sigma * max ‖u‖ ‖v‖) :
    ‖v‖ ≤ ‖u‖ / (1 - sigma) ∧
      (1 - sigma) * ‖u‖ * ‖v‖ ≤ ⟪v, u⟫_ℝ := by
  rcases hsigma with ⟨hsig0, hsigl1⟩
  have hpos : 0 < 1 - sigma := sub_pos.mpr hsigl1
  have h1sub_nonneg : 0 ≤ 1 - sigma := le_of_lt hpos
  have part_i : ‖v‖ ≤ ‖u‖ / (1 - sigma) := by
    by_cases hcase : ‖v‖ ≤ ‖u‖
    · have hineq : ‖v‖ * (1 - sigma) ≤ ‖u‖ := by
        have hle1 : 1 - sigma ≤ 1 := by nlinarith
        have hmul₁ : ‖v‖ * (1 - sigma) ≤ ‖u‖ * (1 - sigma) :=
          mul_le_mul_of_nonneg_right hcase h1sub_nonneg
        have hmul₂ : ‖u‖ * (1 - sigma) ≤ ‖u‖ * 1 :=
          mul_le_mul_of_nonneg_left hle1 (norm_nonneg u)
        nlinarith
      exact (le_div_iff₀' hpos).mpr (by simpa [mul_comm] using hineq)
    · have hlt : ‖u‖ < ‖v‖ := lt_of_not_ge hcase
      have hmax : max ‖u‖ ‖v‖ = ‖v‖ := max_eq_right (le_of_lt hlt)
      have heta' : ‖eta‖ ≤ sigma * ‖v‖ := by
        simpa [hmax] using heta
      have htri : ‖v‖ ≤ ‖u‖ + ‖eta‖ := by
        calc
          ‖v‖ = ‖u + eta‖ := by rw [hv]
          _ ≤ ‖u‖ + ‖eta‖ := norm_add_le u eta
      have hchain : ‖v‖ ≤ ‖u‖ + sigma * ‖v‖ := by nlinarith
      have hineq : ‖v‖ * (1 - sigma) ≤ ‖u‖ := by nlinarith
      exact (le_div_iff₀' hpos).mpr (by simpa [mul_comm] using hineq)
  have part_ii : (1 - sigma) * ‖u‖ * ‖v‖ ≤ ⟪v, u⟫_ℝ := by
    by_cases hcase : ‖v‖ ≤ ‖u‖
    · have hmax : max ‖u‖ ‖v‖ = ‖u‖ := max_eq_left hcase
      have heta_bound : ‖eta‖ ≤ sigma * ‖u‖ := by
        simpa [hmax] using heta
      have h_inner_expand : ⟪v, u⟫_ℝ = ‖u‖ ^ 2 + ⟪eta, u⟫_ℝ := by
        calc
          ⟪v, u⟫_ℝ = ⟪u + eta, u⟫_ℝ := by rw [hv]
          _ = ⟪u, u⟫_ℝ + ⟪eta, u⟫_ℝ := by rw [inner_add_left]
          _ = ‖u‖ ^ 2 + ⟪eta, u⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
      have hlow : -‖eta‖ * ‖u‖ ≤ ⟪eta, u⟫_ℝ := by
        have hcs := abs_real_inner_le_norm eta u
        have hlow' := (abs_le.mp hcs).1
        nlinarith
      rw [h_inner_expand]
      have h_nonneg_u : 0 ≤ ‖u‖ := norm_nonneg u
      have h_nonneg_v : 0 ≤ ‖v‖ := norm_nonneg v
      calc
        (1 - sigma) * ‖u‖ * ‖v‖ ≤ (1 - sigma) * ‖u‖ * ‖u‖ := by
          exact mul_le_mul_of_nonneg_left hcase (mul_nonneg h1sub_nonneg h_nonneg_u)
        _ = (1 - sigma) * ‖u‖ ^ 2 := by ring
        _ = ‖u‖ ^ 2 - sigma * ‖u‖ ^ 2 := by ring
        _ ≤ ‖u‖ ^ 2 + (-‖eta‖ * ‖u‖) := by nlinarith
        _ ≤ ‖u‖ ^ 2 + ⟪eta, u⟫_ℝ := by nlinarith
    · have hlt : ‖u‖ < ‖v‖ := lt_of_not_ge hcase
      have hmax : max ‖u‖ ‖v‖ = ‖v‖ := max_eq_right (le_of_lt hlt)
      have heta_bound : ‖eta‖ ≤ sigma * ‖v‖ := by
        simpa [hmax] using heta
      have hu_eq : u = v - eta := by
        calc
          u = (u + eta) - eta := by abel
          _ = v - eta := by rw [hv]
      have h_inner_expand : ⟪v, u⟫_ℝ = ‖v‖ ^ 2 - ⟪v, eta⟫_ℝ := by
        calc
          ⟪v, u⟫_ℝ = ⟪v, v - eta⟫_ℝ := by rw [hu_eq]
          _ = ⟪v, v⟫_ℝ - ⟪v, eta⟫_ℝ := by rw [inner_sub_right]
          _ = ‖v‖ ^ 2 - ⟪v, eta⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
      have h_cauchy_high : ⟪v, eta⟫_ℝ ≤ ‖v‖ * ‖eta‖ := by
        exact (abs_le.mp (abs_real_inner_le_norm v eta)).2
      rw [h_inner_expand]
      have h_nonneg_u : 0 ≤ ‖u‖ := norm_nonneg u
      have h_nonneg_v : 0 ≤ ‖v‖ := norm_nonneg v
      calc
        (1 - sigma) * ‖u‖ * ‖v‖ ≤ (1 - sigma) * ‖v‖ * ‖v‖ := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left (le_of_lt hlt) (mul_nonneg h1sub_nonneg h_nonneg_v)
        _ = (1 - sigma) * ‖v‖ ^ 2 := by ring
        _ = ‖v‖ ^ 2 - sigma * ‖v‖ ^ 2 := by ring
        _ ≤ ‖v‖ ^ 2 - (‖v‖ * ‖eta‖) := by nlinarith
        _ ≤ ‖v‖ ^ 2 - ⟪v, eta⟫_ℝ := by nlinarith
  exact ⟨part_i, part_ii⟩

end Alvarez2004
