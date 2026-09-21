import Foundation.SetValued.Resolvent
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.def_2

namespace AlvarezAttouch2001

open scoped Pointwise
open SetValuedOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The recurrence defining the inertial proximal point algorithm. -/
structure InertialProximalPointAlgorithm (A : SetValuedOperator H H)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ) : Prop where
  alpha_mem : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1
  lambda_pos : ∀ k : ℕ, 0 < lambda k
  update : ∀ k : ℕ, 1 ≤ k →
    x (k + 1) ∈ (lambda k • A).resolvent (x k + alpha k • (x k - x (k - 1)))

/-- Formula (1) of the paper, written as a set-valued inclusion. -/
def InertialProximalPointInclusion (A : SetValuedOperator H H)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (0 : H) ∈
      ({x (k + 1) - x k - alpha k • (x k - x (k - 1))} +
        lambda k • A (x (k + 1)))

/-- At every iteration, the resolvent update is equivalent to the inclusion in formula (1). -/
theorem inertial_proximal_step_iff_inclusion (A : SetValuedOperator H H)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ) (k : ℕ) :
    x (k + 1) ∈ (lambda k • A).resolvent
        (x k + alpha k • (x k - x (k - 1))) ↔
      (0 : H) ∈
        ({x (k + 1) - x k - alpha k • (x k - x (k - 1))} +
          lambda k • A (x (k + 1))) := by
  rw [SetValuedOperator.mem_resolvent_smul_iff]
  constructor
  · intro h
    dsimp [SetValuedOperator.identityAddScaled] at h
    rcases h with ⟨w, hw, hw_eq⟩
    rw [Set.mem_add]
    refine ⟨x (k + 1) - x k - alpha k • (x k - x (k - 1)), by simp,
      lambda k • w, ?_, ?_⟩
    · exact Set.mem_smul_set.mpr ⟨w, hw, rfl⟩
    · calc
        x (k + 1) - x k - alpha k • (x k - x (k - 1)) + lambda k • w =
            (x (k + 1) + lambda k • w) -
              (x k + alpha k • (x k - x (k - 1))) := by abel
        _ = 0 := sub_eq_zero.mpr hw_eq
  · intro h
    rw [Set.mem_add] at h
    rcases h with ⟨d, hd, lw, hlw, hzero⟩
    simp only [Set.mem_singleton_iff] at hd
    rcases Set.mem_smul_set.mp hlw with ⟨w, hw, rfl⟩
    dsimp [SetValuedOperator.identityAddScaled]
    refine ⟨w, hw, ?_⟩
    rw [hd] at hzero
    apply sub_eq_zero.mp
    calc
      (x (k + 1) + lambda k • w) -
          (x k + alpha k • (x k - x (k - 1))) =
        x (k + 1) - x k - alpha k • (x k - x (k - 1)) + lambda k • w := by abel
      _ = 0 := hzero

/-- The structured algorithm and formula (1) have the same update condition. -/
theorem inertial_proximal_point_algorithm_iff_inclusion
    (A : SetValuedOperator H H) (x : ℕ → H) (alpha lambda : ℕ → ℝ) :
    InertialProximalPointAlgorithm A x alpha lambda ↔
      (∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1) ∧
      (∀ k : ℕ, 0 < lambda k) ∧
      InertialProximalPointInclusion A x alpha lambda := by
  constructor
  · intro h
    exact ⟨h.alpha_mem, h.lambda_pos, fun k hk =>
      (inertial_proximal_step_iff_inclusion A x alpha lambda k).mp (h.update k hk)⟩
  · rintro ⟨halpha, hlambda, hupdate⟩
    exact ⟨halpha, hlambda, fun k hk =>
      (inertial_proximal_step_iff_inclusion A x alpha lambda k).mpr (hupdate k hk)⟩

/-- Given two starting points and admissible parameters, the inertial proximal iteration
produces a sequence. -/
theorem inertial_proximal_point_algorithm_exists
    [CompleteSpace H] (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    (alpha lambda : ℕ → ℝ)
    (halpha : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1)
    (hlambda : ∀ k : ℕ, 0 < lambda k) (x0 x1 : H) :
    ∃ x : ℕ → H, x 0 = x0 ∧ x 1 = x1 ∧
      InertialProximalPointAlgorithm A x alpha lambda := by
  classical
  have hstep (k : ℕ) (u : H) : ∃ z : H, z ∈ (lambda k • A).resolvent u := by
    rcases identityAddScaled_existsUnique_of_maximal_monotone A hA (hlambda k) u with
      ⟨z, hz, _⟩
    exact ⟨z, (SetValuedOperator.mem_resolvent_smul_iff A (lambda k) u z).mpr hz⟩
  let next : ℕ → H → H → H := fun k y z =>
    Classical.choose (hstep k (z + alpha k • (z - y)))
  let state : ℕ → H × H := fun n =>
    Nat.rec (x0, x1) (fun n p => (p.2, next (n + 1) p.1 p.2)) n
  let x : ℕ → H := fun n => (state n).1
  have hx0 : x 0 = x0 := by simp [x, state]
  have hx1 : x 1 = x1 := by simp [x, state]
  have hstate_succ (n : ℕ) :
      state (n + 1) = ((state n).2, next (n + 1) (state n).1 (state n).2) := by
    simp [state]
  have hx_next (n : ℕ) :
      x (n + 2) = next (n + 1) (x n) (x (n + 1)) := by
    change (state (n + 2)).1 = next (n + 1) (state n).1 (state (n + 1)).1
    rw [hstate_succ (n + 1), hstate_succ n]
  refine ⟨x, hx0, hx1, ⟨halpha, hlambda, ?_⟩⟩
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [hx_next n]
  exact Classical.choose_spec
    (hstep (n + 1) (x (n + 1) + alpha (n + 1) • (x (n + 1) - x n)))

end AlvarezAttouch2001
