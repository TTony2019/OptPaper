import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_8
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_4
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_9

namespace Alvarez2002

private theorem sqrt_b_div_a_mul_sqrt_a_div_b (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (b / a) * Real.sqrt (a / b) = 1 := by
  rw [Real.sqrt_div hb.le a, Real.sqrt_div ha.le b]
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hsb : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  field_simp

/-- Proposition 6.1, with the trajectory regularity required by the
definitions of `(DIN)` and `(g-DIN)`. -/
theorem din_equiv_gradient_system
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (α β : ℝ) (x : ℝ → H)
    (hΦ : ContDiff ℝ 2 Φ) (hx : ContDiff ℝ 2 x)
    (hαpos : 0 < α) (hβpos : 0 < β) (hαβ : 1 < α * β) :
    IsDINTrajectory H Φ α β x ↔
      ∃ z : ℝ → H,
        ContDiffOn ℝ 2 z (Set.Ici 0) ∧
        IsRescaledGDINTrajectory Φ β (α - 1 / β) (1 / β)
          (x 0) (z 0) x z ∧
        IsGradientSystemTrajectory Φ β (α - 1 / β) (1 / β)
          (x 0) (z 0) x z := by
  have ha : 0 < α - 1 / β := by
    apply sub_pos.mpr
    exact (div_lt_iff₀ hβpos).2 (by simpa using hαβ)
  have hb : 0 < 1 / β := one_div_pos.mpr hβpos
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hβne : β ≠ 0 := ne_of_gt hβpos
  constructor
  · intro hDIN
    rcases hDIN with ⟨hα, hβ, hEq⟩
    let y₀ : H :=
      -(β • deriv x 0 + (β ^ 2) • gradient Φ (x 0) +
        (β * (α - 1 / β)) • x 0)
    obtain ⟨y, hyC2, hsol⟩ :=
      (din_iff_gdin Φ α β (α - 1 / β) (1 / β) x (x 0) y₀
        hΦ hx hα hβ rfl rfl rfl (by rfl)).mp ⟨hα, hβ, hEq⟩
    let z : ℝ → H := fun t => Real.sqrt ((1 / β) / (α - 1 / β)) • y t
    have hR0 :=
      (isSolution_gDIN_iff_rescaled_gDIN Φ β (α - 1 / β) (1 / β) ha hb
        (x 0) y₀ x y).mp hsol
    have hR :
        IsRescaledGDINTrajectory Φ β (α - 1 / β) (1 / β)
          (x 0) (z 0) x z := by
      simpa [z, hsol.2.2.2]
        using hR0
    have hzC2 : ContDiffOn ℝ 2 z (Set.Ici 0) := by
      dsimp [z]
      exact hyC2.const_smul _
    have hG :=
      (rescaled_gDIN_iff_gradient_system Φ β (α - 1 / β) (1 / β)
        ha hb hΦ1 (x 0) (z 0) x z).mp hR
    exact ⟨z, hzC2, hR, hG⟩
  · rintro ⟨z, hzC2, hR, _hG⟩
    let y : ℝ → H := fun t => Real.sqrt ((α - 1 / β) / (1 / β)) • z t
    let y₀ : H := y 0
    have hcd :
        Real.sqrt ((1 / β) / (α - 1 / β)) *
            Real.sqrt ((α - 1 / β) / (1 / β)) = 1 := by
      exact sqrt_b_div_a_mul_sqrt_a_div_b (α - 1 / β) (1 / β) ha hb
    have hzy : (fun t => Real.sqrt ((1 / β) / (α - 1 / β)) • y t) = z := by
      funext t
      dsimp [y]
      rw [smul_smul, hcd, one_smul]
    have hzy0 :
        Real.sqrt ((1 / β) / (α - 1 / β)) • y₀ = z 0 := by
      dsimp [y₀]
      exact congrFun hzy 0
    have hR' :
        IsRescaledGDINTrajectory Φ β (α - 1 / β) (1 / β)
          (x 0) (Real.sqrt ((1 / β) / (α - 1 / β)) • y₀) x
          (fun t => Real.sqrt ((1 / β) / (α - 1 / β)) • y t) := by
      rw [hzy, hzy0]
      exact hR
    have hsol :=
      (isSolution_gDIN_iff_rescaled_gDIN Φ β (α - 1 / β) (1 / β) ha hb
        (x 0) y₀ x y).mpr hR'
    have hyC2 : ContDiffOn ℝ 2 y (Set.Ici 0) := by
      dsimp [y]
      exact hzC2.const_smul _
    have hy₀ : y₀ =
        -(β • deriv x 0 + (β ^ 2) • gradient Φ (x 0) +
          (β * (α - 1 / β)) • x 0) := by
      have hfirst := hsol.1 0 le_rfl
      have hscaled := congrArg (fun q : H => β • q) hfirst
      apply eq_neg_iff_add_eq_zero.mpr
      simp only [smul_add, smul_smul, smul_zero] at hscaled
      rw [show β * (1 / β) = 1 by field_simp [hβne]] at hscaled
      dsimp [y₀]
      simpa [pow_two, add_assoc, add_comm, add_left_comm, mul_comm] using hscaled
    exact
      (din_iff_gdin Φ α β (α - 1 / β) (1 / β) x (x 0) y₀
        hΦ hx hαpos hβpos rfl rfl rfl hy₀).mpr ⟨y, hyC2, hsol⟩

end Alvarez2002
