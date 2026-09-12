import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.algo_1

namespace Nesterov1983

/- EXTERNAL DEPENDENCY: Backtracking predecessor reference
   Source: B. N. Pshenichnyī and Yu. M. Danilin, Numerical Methods in Extremal Problems,
   Nauka, Moscow, 1975; French translation, Mir, Moscow, 1977.
   Status: proof not available — provide referenced paper MD to fill.
   To resolve: place the referenced paper in todo/ and re-run the pipeline.
-/
/-- The earlier one-dimensional search, represented by its successive halved
trial step sizes. -/
structure EarlierOneDimensionalHalvingSearch where
  trialStep : ℝ → ℕ → ℝ
  trialStep_eq : ∀ (α : ℝ) (i : ℕ),
    trialStep α i = (2 : ℝ) ^ (-(i : ℤ)) * α

/-- Method (3)-(5) starts its `k`th halving search at the preceding accepted
step (and at the initial step for `k = 0`). -/
def StartsKthSearchFromPreviousStep {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f)
    (S : EarlierOneDimensionalHalvingSearch) : Prop :=
  ∀ k : ℕ, M.step k = S.trialStep
    (if k = 0 then M.initialStep else M.step (k - 1)) (M.searchIndex k)

/-- The cited earlier one-dimensional search is a halving search.  The historical
comparison is that method (3)-(5) starts its `k`th such search at `α_{k-1}`. -/
theorem backtracking_predecessor_reference {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) :
    ∃ S : EarlierOneDimensionalHalvingSearch,
      StartsKthSearchFromPreviousStep f M S := by
  refine ⟨⟨fun α i => (2 : ℝ) ^ (-(i : ℤ)) * α, ?_⟩, ?_⟩
  · intro α i
    rfl
  · intro k
    change M.step k =
      (2 : ℝ) ^ (-(M.searchIndex k : ℤ)) *
        (if k = 0 then M.initialStep else M.step (k - 1))
    exact M.step_eq_dyadic_previous k

end Nesterov1983
