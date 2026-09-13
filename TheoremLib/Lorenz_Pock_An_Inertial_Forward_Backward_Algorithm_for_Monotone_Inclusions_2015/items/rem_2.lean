import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_2
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_2

namespace LorenzPock

/-- Remark 4: for a linear self-adjoint positive semidefinite `B` and `M̄ = M - λB`
(positive definite), the fully implicit scheme in the `M̄` metric is equivalent — step by
step — to the proposed inertial forward--backward splitting algorithm (10) in the `M`
metric, which only requires the resolvent with respect to `A`.

The hypotheses `hB_selfadjoint`, `hB_positive_semidefinite`, `hMbar_positive_definite` are
the paper's requirements on `B` and on the choice of `λ`; the equivalence itself, as the
paper notes, only uses linearity.  The paper's closing remark — that condition (i) of
Theorem 1 may be replaced by `M - λB > 0` when `{α_k}` is nondecreasing in `[0, α]` with
`α < 1/3` — is not formalized here. -/
theorem fully_implicit_metric_substitution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : SetValuedOperator H H) (B : H →L[ℝ] H) (M : H →L[ℝ] H) (step : ℝ)
    (hB_selfadjoint : ∀ u v, inner ℝ (B u) v = inner ℝ u (B v))
    (hB_positive_semidefinite : ∀ u, 0 ≤ inner ℝ (B u) u)
    (hMbar_positive_definite : ∀ u, u ≠ 0 → 0 < inner ℝ ((M - step • B) u) u)
    (x y : ℕ → H) (α : ℕ → ℝ) :
    (∀ k, y k = x k + α k • (x k - x (k - 1))) →
    ∀ k, (∃ a ∈ A (x (k + 1)),
      (M - step • B) (y k - x (k + 1)) = step • (a + B (x (k + 1)))) ↔
      (∃ a ∈ A (x (k + 1)),
        M (y k - x (k + 1)) - step • B (y k) = step • a) := by
  intro _ k
  constructor
  · rintro ⟨a, ha, himplicit⟩
    refine ⟨a, ha, ?_⟩
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      map_sub, smul_add] at himplicit ⊢
    apply add_right_cancel (b := step • B (x (k + 1)))
    abel_nf at himplicit ⊢
    exact himplicit
  · rintro ⟨a, ha, hforward⟩
    refine ⟨a, ha, ?_⟩
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      map_sub, smul_add] at hforward ⊢
    have h := congrArg (fun z => z + step • B (x (k + 1))) hforward
    abel_nf at h ⊢
    exact h

end LorenzPock
