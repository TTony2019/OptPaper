import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.lem_1

namespace LorenzPock

private theorem div_antitone_of_nonneg (c a b : ℝ) (hc : 0 ≤ c) (ha : 0 < a)
    (hb : 0 < b) (hab : a ≤ b) : c / b ≤ c / a :=
  (div_le_div_iff₀ hb ha).mpr (mul_le_mul_of_nonneg_left hab hc)

/-- Remark 7: changing the balancing parameter changes the product of the
primal and dual step sizes in the zero-smoothness cases. -/
theorem balancing_parameter_remark (K LQ LP γ δ r r' : ℝ)
    (hγ : 0 < γ ∧ γ < 2) (hδ : 0 < δ ∧ δ < 2) (hr : 0 < r) (hr' : 0 < r')
    (hLQ : 0 ≤ LQ) (hLP : 0 ≤ LP)
    (hzero : LP = 0 ∨ LQ = 0) :
    (|K| * r + LQ / γ) * (|K| / r + LP / δ) ≥ |K| ^ 2 ∧
    (LP = 0 → r ≤ r' →
      (|K| * r' + LQ / γ) * (|K| / r' + LP / δ) ≤
        (|K| * r + LQ / γ) * (|K| / r + LP / δ)) ∧
    (LQ = 0 → r' ≤ r →
      (|K| * r' + LQ / γ) * (|K| / r' + LP / δ) ≤
        (|K| * r + LQ / γ) * (|K| / r + LP / δ)) := by
  rcases hγ with ⟨hγ_pos, hγ_lt⟩
  rcases hδ with ⟨hδ_pos, hδ_lt⟩
  have hK : 0 ≤ |K| := abs_nonneg K
  have hQr : 0 ≤ LQ / γ := div_nonneg hLQ hγ_pos.le
  have hPδ : 0 ≤ LP / δ := div_nonneg hLP hδ_pos.le
  have hproduct : (|K| * r) * (|K| / r) ≤
      (|K| * r + LQ / γ) * (|K| / r + LP / δ) :=
    mul_le_mul (le_add_of_nonneg_right hQr) (le_add_of_nonneg_right hPδ)
      (div_nonneg hK hr.le) (add_nonneg (mul_nonneg hK hr.le) hQr)
  have hbase : (|K| * r) * (|K| / r) = |K| ^ 2 := by
    field_simp [hr.ne']
  have hbase_bound : (|K| * r + LQ / γ) * (|K| / r + LP / δ) ≥ |K| ^ 2 := by
    rw [← hbase]
    exact hproduct
  refine ⟨hbase_bound, ?_, ?_⟩
  · intro hLP0 hrr
    rw [hLP0]
    have h_expand_r' :
        (|K| * r' + LQ / γ) * (|K| / r' + 0 / δ) =
          |K| ^ 2 + (|K| * (LQ / γ)) / r' := by
      field_simp [hr'.ne']
      ring
    have h_expand_r :
        (|K| * r + LQ / γ) * (|K| / r + 0 / δ) =
          |K| ^ 2 + (|K| * (LQ / γ)) / r := by
      field_simp [hr.ne']
      ring
    have hc : 0 ≤ |K| * (LQ / γ) := mul_nonneg hK hQr
    have hdiv : (|K| * (LQ / γ)) / r' ≤ (|K| * (LQ / γ)) / r :=
      div_antitone_of_nonneg _ _ _ hc hr hr' hrr
    rw [h_expand_r', h_expand_r]
    simpa [add_comm] using add_le_add_left hdiv (|K| ^ 2)
  · intro hLQ0 hrr
    rw [hLQ0]
    have h_expand_r' :
        (|K| * r' + 0 / γ) * (|K| / r' + LP / δ) =
          |K| ^ 2 + (|K| * (LP / δ)) * r' := by
      field_simp [hr'.ne']
      ring
    have h_expand_r :
        (|K| * r + 0 / γ) * (|K| / r + LP / δ) =
          |K| ^ 2 + (|K| * (LP / δ)) * r := by
      field_simp [hr.ne']
      ring
    have hc : 0 ≤ |K| * (LP / δ) := mul_nonneg hK hPδ
    have hlinear : (|K| * (LP / δ)) * r' ≤ (|K| * (LP / δ)) * r :=
      mul_le_mul_of_nonneg_left hrr hc
    rw [h_expand_r', h_expand_r]
    simpa [add_comm] using add_le_add_left hlinear (|K| ^ 2)

end LorenzPock
