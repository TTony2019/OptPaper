import Mathlib

namespace AttouchAdlyDryFrictionDynamics2023

/-- Time scaling `y(s)=z(τ(s))`. -/
def timeScaledTrajectory {H : Type*} (z : ℝ → H) (τ : ℝ → ℝ) : ℝ → H := fun s => z (τ s)

def IsIncreasingC1TimeScale (τ dτ : ℝ → ℝ) : Prop :=
  StrictMono τ ∧ ∀ s, HasDerivAt τ (dτ s) s

/- The time scale used in Theorem 4.2 is only required to be increasing on
   the half-line on which the trajectory is defined.  Requiring global
   strict monotonicity is incorrect for the quadratic scale s ↦ s²/C. -/
def IsIncreasingC1TimeScaleOn (τ dτ : ℝ → ℝ) (s₀ : ℝ) : Prop :=
  StrictMonoOn τ (Set.Ici s₀) ∧ ∀ s ∈ Set.Ici s₀, HasDerivAt τ (dτ s) s

/-- The weighted-average trajectory satisfies `ẋ + τ̇⁻¹ • (x-y) = 0` and `x(s₀)=y(s₀)`. -/
def IsWeightedAverage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (τ dτ : ℝ → ℝ) (x y dx : ℝ → H) (s₀ : ℝ) : Prop :=
  IsIncreasingC1TimeScale τ dτ ∧ x s₀ = y s₀ ∧
    ∀ s ∈ Set.Ici s₀, HasDerivAt x (dx s) s ∧ dx s + (dτ s)⁻¹ • (x s - y s) = 0

def IsWeightedAverageOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (τ dτ : ℝ → ℝ) (x y dx : ℝ → H) (s₀ : ℝ) : Prop :=
  IsIncreasingC1TimeScaleOn τ dτ s₀ ∧ x s₀ = y s₀ ∧
    ∀ s ∈ Set.Ici s₀, HasDerivAt x (dx s) s ∧ dx s + (dτ s)⁻¹ • (x s - y s) = 0

theorem quadraticTimeScale_isIncreasingC1TimeScaleOn {s₀ α : ℝ}
    (hα : 1 < α) (hs₀ : 0 < s₀) :
    IsIncreasingC1TimeScaleOn
      (fun s : ℝ => s ^ 2 / (2 * (α - 1)))
      (fun s : ℝ => s / (α - 1)) s₀ := by
  have hden : 0 < 2 * (α - 1) := mul_pos (by norm_num) (sub_pos.mpr hα)
  have hαsub : 0 < α - 1 := sub_pos.mpr hα
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    apply (div_lt_div_iff_of_pos_right hden).mpr
    have ha0 : 0 < a := lt_of_lt_of_le hs₀ ha
    have habsq : a ^ 2 < b ^ 2 := by nlinarith
    exact habsq
  · intro s hs
    convert ((hasDerivAt_pow 2 s).div_const (2 * (α - 1))) using 1
    · field_simp [ne_of_gt hαsub]
      ring

end AttouchAdlyDryFrictionDynamics2023
