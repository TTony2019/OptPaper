import Mathlib

/-!
# Kantorovich optimal transport

For probability measures `α` and `β`, a coupling is a probability measure on the
product whose two push-forwards by the coordinate projections are `α` and `β`.
This is the measure-theoretic formulation in Remark 2.13 and equation (2.14) of
Peyré--Cuturi, *Computational Optimal Transport*.
-/

namespace MeasureTheory

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}
variable [MeasurableSpace X] [MeasurableSpace Y]

/-- A probability measure `π` on `X × Y` coupling `α` and `β`.

The two equalities are the marginal constraints
`(P_X)_# π = α` and `(P_Y)_# π = β`, where `P_X` and `P_Y` are the
coordinate projections.
-/
def IsKantorovichCoupling (α : Measure X) (β : Measure Y)
    (π : Measure (X × Y)) : Prop :=
  IsProbabilityMeasure π ∧
    Measure.map Prod.fst π = α ∧ Measure.map Prod.snd π = β

/-- The set `U(α, β)` of Kantorovich couplings of `α` and `β`. -/
def KantorovichCouplings (α : Measure X) (β : Measure Y) : Set (Measure (X × Y)) :=
  {π | IsKantorovichCoupling α β π}

@[simp]
theorem mem_KantorovichCouplings_iff (α : Measure X) (β : Measure Y)
    (π : Measure (X × Y)) :
    π ∈ KantorovichCouplings α β ↔ IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = α ∧ Measure.map Prod.snd π = β :=
  Iff.rfl

/-- The product measure is a feasible coupling of two probability measures. -/
theorem prod_mem_KantorovichCouplings (α : Measure X) (β : Measure Y)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    α.prod β ∈ KantorovichCouplings α β := by
  refine ⟨inferInstance, ?_, ?_⟩ <;> simp

/-- The transport cost of a coupling for a nonnegative extended-real cost. -/
noncomputable def KantorovichCost (c : X → Y → ℝ≥0∞) (π : Measure (X × Y)) : ℝ≥0∞ :=
  ∫⁻ z, c z.1 z.2 ∂π

/-- The Kantorovich problem for probability measures `α` and `β`.

This is the infimum of the cost over all probability couplings with the prescribed
marginals.  The value is `⊤` when the feasible set is empty, as for the infimum
of an empty subset of `ℝ≥0∞`.
-/
noncomputable def KantorovichProblem (α : Measure X) (β : Measure Y)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (c : X → Y → ℝ≥0∞) : ℝ≥0∞ :=
  sInf (KantorovichCost c '' KantorovichCouplings α β)

/-! Lower-case names are convenient in developments that use the usual Lean naming style. -/

abbrev isKantorovichCoupling {X : Type u} {Y : Type v} [MeasurableSpace X]
    [MeasurableSpace Y] (α : Measure X) (β : Measure Y) (π : Measure (X × Y)) : Prop :=
  IsKantorovichCoupling α β π

abbrev kantorovichCouplings {X : Type u} {Y : Type v} [MeasurableSpace X]
    [MeasurableSpace Y] (α : Measure X) (β : Measure Y) : Set (Measure (X × Y)) :=
  KantorovichCouplings α β

noncomputable abbrev kantorovichCost {X : Type u} {Y : Type v} [MeasurableSpace X]
    [MeasurableSpace Y] (c : X → Y → ℝ≥0∞) (π : Measure (X × Y)) : ℝ≥0∞ :=
  KantorovichCost c π

noncomputable abbrev kantorovichProblem {X : Type u} {Y : Type v} [MeasurableSpace X]
    [MeasurableSpace Y] (α : Measure X) (β : Measure Y)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (c : X → Y → ℝ≥0∞) : ℝ≥0∞ :=
  KantorovichProblem α β c

end MeasureTheory
