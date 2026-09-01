import Mathlib
import Foundation.SetValued.Fitzpatrick

/-!
# Minty's theorem for maximal monotone operators

This file proves Minty's surjectivity criterion for maximal monotone
set-valued operators on real Hilbert spaces.
-/

open SetValuedOperator
open scoped InnerProductSpace

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem surjective_from_monotonically_related_resolvent_point
    {T : SetValuedOperator H H} (hT : IsMaximalMonotone T) {y x : H}
    (hxrel : ∀ z v, v ∈ T z → 0 ≤ inner ℝ ((y - x) - v) (x - z)) :
    ∃ u ∈ T x, y = x + u := by
  refine ⟨y - x, ?_, ?_⟩
  · exact mem_of_monotonically_related_to_graph (T := T) hT hxrel
  · abel

private theorem exists_zero_monotonically_related_point
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) :
    ∃ x : H, ∀ z v, v ∈ A z → 0 ≤ inner ℝ ((-x) - v) (x - z) := by
  rcases exists_fitzpatrick_quadratic_minorant_pair (A := A) hA with ⟨a, b, hminor⟩
  have hrel : ∀ z v, v ∈ A z → 0 ≤ inner ℝ (a - v) (b - z) :=
    monotonically_related_of_minorant (A := A) hA.1 hminor
  have haA : a ∈ A b :=
    mem_of_monotonically_related_to_graph (T := A) hA hrel
  have hb_eq : b = -a :=
    eq_neg_of_minorant_and_mem (A := A) hA.1 hminor haA
  refine ⟨b, ?_⟩
  intro z v hv
  have hneg : -b ∈ A b := by
    have hba : -b = a := by
      rw [hb_eq]
      simp
    simpa [hba] using haA
  simpa using hA.1 (-b) hneg v hv

private theorem exists_monotonically_related_resolvent_point
    {T : SetValuedOperator H H} (hT : IsMaximalMonotone T) (y : H) :
    ∃ x : H, ∀ z v, v ∈ T z → 0 ≤ inner ℝ ((y - x) - v) (x - z) := by
  let B : SetValuedOperator H H := fun z => {w : H | ∃ v, v ∈ T z ∧ w = v - y}
  have hB : IsMaximalMonotone B := translate_sub_const_maximal_monotone (T := T) hT y
  rcases exists_zero_monotonically_related_point (A := B) hB with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro z v hv
  have hmemB : v - y ∈ B z := ⟨v, hv, rfl⟩
  have hrel := hx z (v - y) hmemB
  convert hrel using 2
  abel

/-- A maximal monotone operator on a real Hilbert space has full range under `I + T`. -/
theorem minty_surjective_of_maximal_monotone
    {T : SetValuedOperator H H}
    (hT : IsMaximalMonotone T) :
    ∀ y : H, ∃ x : H, ∃ u ∈ T x, y = x + u := by
  intro y
  obtain ⟨x, hxrel⟩ :
      ∃ x : H, ∀ z v, v ∈ T z → 0 ≤ inner ℝ ((y - x) - v) (x - z) := by
    exact exists_monotonically_related_resolvent_point (T := T) hT y
  exact ⟨x, surjective_from_monotonically_related_resolvent_point (T := T) hT hxrel⟩

omit [CompleteSpace H] in
/-- The elementary half of Minty's criterion: surjectivity of `I + T` forces maximality. -/
theorem maximal_monotone_of_minty_surjective {T : SetValuedOperator H H}
    (hT_mono : IsMonotone T)
    (hsurj : ∀ y : H, ∃ x : H, ∃ u ∈ T x, y = x + u) :
    IsMaximalMonotone T := by
  refine ⟨hT_mono, ?_⟩
  intro T' hT'_mono hsubset p hp
  rcases p with ⟨x, u⟩
  rw [SetValuedOperator.mem_graph_iff] at hp ⊢
  rcases hsurj (x + u) with ⟨z, v, hv, hEq⟩
  have hvT' : v ∈ T' z := by
    exact (SetValuedOperator.mem_graph_iff T' z v).mp
      (hsubset ((SetValuedOperator.mem_graph_iff T z v).mpr hv))
  have hmono : 0 ≤ ⟪u - v, x - z⟫_ℝ := hT'_mono u hp v hvT'
  have hxz : x - z = v - u := by
    have hx : x = z + v - u := by
      calc
        x = x + u - u := by abel
        _ = z + v - u := by rw [hEq]
    rw [hx]
    abel
  have hmono_norm : 0 ≤ - ‖u - v‖ ^ 2 := by
    calc
      0 ≤ ⟪u - v, x - z⟫_ℝ := hmono
      _ = - ‖u - v‖ ^ 2 := by
        rw [hxz, show v - u = -(u - v) by abel]
        rw [inner_neg_right, real_inner_self_eq_norm_sq]
  have huv : u = v := by
    have hnorm : ‖u - v‖ = 0 := by
      nlinarith [sq_nonneg ‖u - v‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hx_eq : x = z := by
    have hEq' : x + v = z + v := by simpa [huv] using hEq
    exact add_right_cancel hEq'
  rw [hx_eq, huv]
  exact hv

/-- Minty's surjectivity criterion for maximal monotone operators:
a monotone operator `T` is maximal monotone iff `range (Id + T) = H`. -/
theorem minty_surjective_iff_maximal_monotone {T : SetValuedOperator H H}
    (hT_mono : IsMonotone T) :
    IsMaximalMonotone T ↔ ∀ y : H, ∃ x : H, ∃ u ∈ T x, y = x + u := by
  constructor
  · intro hT_max
    exact minty_surjective_of_maximal_monotone hT_max
  · intro hsurj
    exact maximal_monotone_of_minty_surjective hT_mono hsurj

/-! The order-theoretic presentation is the canonical source-facing form. -/

/-- Minty's criterion stated with Mathlib's `Maximal` predicate. -/
theorem minty_surjective_iff_maximal_isMonotone {T : SetValuedOperator H H}
    (hT_mono : IsMonotone T) :
    Maximal IsMonotone T ↔ ∀ y : H, ∃ x : H, ∃ u ∈ T x, y = x + u := by
  rw [← SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone T]
  exact minty_surjective_iff_maximal_monotone hT_mono
