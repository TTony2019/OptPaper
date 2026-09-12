import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_6
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_5
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_3

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set

private theorem def_6_le_of_norm_le {H : Type*} [NormedAddCommGroup H] {r : ℝ}
    (hr : 0 < r) (A B : H → H)
    (hbounded : BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖A u - B u‖})
    {u : H} (hu : ‖u‖ ≤ r) :
    ‖A u - B u‖ ≤ def_6 r hr A B := by
  unfold def_6
  exact le_csSup hbounded ⟨u, hu, rfl⟩

/-- Remark 6.3: If, instead of (9), for given r,T>0, x_μ(t)∈B(0,r)
  for a.e. t∈[0,T] and all μ, then
  ‖∇ε_μ(X_μ(t))−∇ε_{μ′}(X_μ(t))‖ ≤ β D_r(∇φ_μ,∇φ_μ′).

  Deviations: the identity `∇ε_μ = β ∇φ_μ` is an explicit hypothesis
  (`hgradE`); the paper derives it from `ε_μ = βφ_μ + (μ-independent
  quadratic term)`, so only the cancellation of the quadratic term in the
  μ-difference is really used, and the hypothesis is slightly stronger than
  needed.  Boundedness of the real-`sSup` `D_r` (see `def_6`) is explicit
  (`hD_bdd`). -/
theorem rem_3 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedSpace ℝ H] [NormedAddCommGroup M]
    (_φ : M → H → ℝ) (gradE : M → H → H) (gradφ : M → H → H) (X : M → ℝ → H)
    (β r T : ℝ) (hβ : 0 < β) (hr : 0 < r) (_hT : 0 < T)
    (hgradE : ∀ (μ : M) (q : H), gradE μ q = β • gradφ μ q)
    (hD_bdd : ∀ μ μ' : M,
      BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖gradφ μ u - gradφ μ' u‖})
    (hball : ∀ μ : M, ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → ‖X μ t‖ ≤ r) :
    ∀ μ μ' : M, ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      ‖(gradE μ) (X μ t) - (gradE μ') (X μ t)‖ ≤ β * def_6 r hr (gradφ μ) (gradφ μ') := by
  intro μ μ'
  filter_upwards [hball μ] with t ht
  intro hmem
  have hD : ‖gradφ μ (X μ t) - gradφ μ' (X μ t)‖ ≤
      def_6 r hr (gradφ μ) (gradφ μ') :=
    def_6_le_of_norm_le hr (gradφ μ) (gradφ μ') (hD_bdd μ μ') (ht hmem)
  calc
    ‖gradE μ (X μ t) - gradE μ' (X μ t)‖ =
        ‖β • (gradφ μ (X μ t) - gradφ μ' (X μ t))‖ := by
          rw [hgradE μ (X μ t), hgradE μ' (X μ t), ← smul_sub]
    _ = β * ‖gradφ μ (X μ t) - gradφ μ' (X μ t)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
    _ ≤ β * def_6 r hr (gradφ μ) (gradφ μ') :=
          mul_le_mul_of_nonneg_left hD hβ.le

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
