import Mathlib

/-!
# Monotonicity-Adjusting Factor δ_n

Let β_n > 0 and μ_n > 0 be monotone sequences. Define the auxiliary sequence δ_n according to
four cases depending on whether each of β_n, μ_n is nonincreasing or nondecreasing.

The definition ensures that the scaled sequences μ_n/δ_n, β_n/δ_n, and β_n μ_n/δ_n
are all nonincreasing.

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Classical

/-- The type of monotonicity behavior: either nonincreasing or nondecreasing. -/
inductive MonotonicityBehavior
  | nonincreasing
  | nondecreasing
  deriving DecidableEq

/-- Decode a monotonicity behavior into the corresponding sequence property. -/
def MonotonicityBehavior.toProp {β : ℕ → ℝ} (b : MonotonicityBehavior) : Prop :=
  match b with
  | .nonincreasing => ∀ n, β (n+1) ≤ β n
  | .nondecreasing => ∀ n, β n ≤ β (n+1)

/-- The monotonicity-adjusting factor δ_n defined by four cases based on the
monotone behavior of β_n and μ_n. -/
noncomputable def deltaSeq (β μ : ℕ → ℝ) (β_behavior μ_behavior : MonotonicityBehavior) : ℕ → ℝ :=
  match β_behavior, μ_behavior with
  | .nonincreasing, .nonincreasing => fun _ => 1
  | .nonincreasing, .nondecreasing => fun n => μ n
  | .nondecreasing, .nonincreasing => fun n => β n
  | .nondecreasing, .nondecreasing => fun n => β n * μ n

/-- The nonincrease property of the scaled sequence μ_n/δ_n.
For each of the four cases, we have μ_n/δ_n is nonincreasing. -/
lemma mu_div_delta_nonincreasing (β μ : ℕ → ℝ) (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_pos : ∀ n, β n > 0) (hμ_pos : ∀ n, μ n > 0)
    (hβ_prop : β_behavior.toProp (β := β)) (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∀ n, μ (n+1) / deltaSeq β μ β_behavior μ_behavior (n+1) ≤
         μ n / deltaSeq β μ β_behavior μ_behavior n := by
  intro n
  unfold deltaSeq
  have hβpos_n : 0 < β n := hβ_pos n
  have hβpos_n1 : 0 < β (n+1) := hβ_pos (n+1)
  have hμpos_n : 0 < μ n := hμ_pos n
  have hμpos_n1 : 0 < μ (n+1) := hμ_pos (n+1)
  match β_behavior, μ_behavior with
  | .nonincreasing, .nonincreasing =>
    -- δ = 1, so the claim reduces to μ(n+1) ≤ μ(n)
    simp [hμ_prop n]
  | .nonincreasing, .nondecreasing =>
    -- δ = μ, so both sides equal 1
    field_simp [hμpos_n.ne.symm, hμpos_n1.ne.symm]
    exact le_refl 1
  | .nondecreasing, .nonincreasing =>
    -- δ = β. μ is nonincreasing, β is nondecreasing, both positive.
    -- Multiply both sides by β(n+1)·β(n) > 0, then use calc chain.
    have hprod : μ (n+1) * β n ≤ μ n * β (n+1) := by
      calc
        μ (n+1) * β n ≤ μ n * β n := mul_le_mul_of_nonneg_right (hμ_prop n) (by positivity)
        _ ≤ μ n * β (n+1) := mul_le_mul_of_nonneg_left (hβ_prop n) (by positivity)
    field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  | .nondecreasing, .nondecreasing =>
    -- δ = β·μ. Both fractions simplify to reciprocals of β:
    -- μ(n+1)/(β(n+1)·μ(n+1)) = 1/β(n+1), μ(n)/(β(n)·μ(n)) = 1/β(n)
    -- So the claim reduces to β(n) ≤ β(n+1)
    field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm, hμpos_n.ne.symm, hμpos_n1.ne.symm]
    exact hβ_prop n

/-- The nonincrease property of the scaled sequence β_n/δ_n. -/
lemma beta_div_delta_nonincreasing (β μ : ℕ → ℝ) (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_pos : ∀ n, β n > 0) (hμ_pos : ∀ n, μ n > 0)
    (hβ_prop : β_behavior.toProp (β := β)) (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∀ n, β (n+1) / deltaSeq β μ β_behavior μ_behavior (n+1) ≤
         β n / deltaSeq β μ β_behavior μ_behavior n := by
  intro n
  unfold deltaSeq
  have hβpos_n : 0 < β n := hβ_pos n
  have hβpos_n1 : 0 < β (n+1) := hβ_pos (n+1)
  have hμpos_n : 0 < μ n := hμ_pos n
  have hμpos_n1 : 0 < μ (n+1) := hμ_pos (n+1)
  match β_behavior, μ_behavior with
  | .nonincreasing, .nonincreasing =>
    -- δ = 1, so the claim reduces to β(n+1) ≤ β(n)
    simp [hβ_prop n]
  | .nonincreasing, .nondecreasing =>
    -- δ = μ. β is nonincreasing, μ is nondecreasing, both positive.
    -- Multiply both sides by μ(n+1)·μ(n) > 0, then use calc chain.
    have hprod : β (n+1) * μ n ≤ β n * μ (n+1) := by
      calc
        β (n+1) * μ n ≤ β n * μ n := mul_le_mul_of_nonneg_right (hβ_prop n) (by positivity)
        _ ≤ β n * μ (n+1) := mul_le_mul_of_nonneg_left (hμ_prop n) (by positivity)
    field_simp [hμpos_n.ne.symm, hμpos_n1.ne.symm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  | .nondecreasing, .nonincreasing =>
    -- δ = β, so both sides equal 1
    field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm]
    exact le_refl 1
  | .nondecreasing, .nondecreasing =>
    -- δ = β·μ. Both fractions simplify to reciprocals of μ:
    -- β(n+1)/(β(n+1)·μ(n+1)) = 1/μ(n+1), β(n)/(β(n)·μ(n)) = 1/μ(n)
    -- So the claim reduces to μ(n) ≤ μ(n+1)
    field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm, hμpos_n.ne.symm, hμpos_n1.ne.symm]
    exact hμ_prop n
