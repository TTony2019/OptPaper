import Foundation.OptimalTransport.Kantorovich

/-!
# Finite Kantorovich transport plans

This file gives the matrix form used in equations (1) and (2) of
Xia--Ding--Liang--Zhang, *Dual-guided Hierarchical Edge Localization for
Large-scale Optimal Transport Across Dimensions*.  The row and column sum
constraints are the finite-support form of the two marginal push-forward
constraints in `KantorovichCouplings`.
-/

namespace MeasureTheory

open scoped BigOperators
open scoped ENNReal

universe u

/-! ### Finite-support data for the measure-theoretic problem -/

/-- A finite family of real weights that defines a probability measure. -/
def IsDiscreteProbabilityVector {m : ℕ} (a : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1

/-- Nonnegativity of a finite real-valued cost matrix. -/
def IsNonnegativeDiscreteCost {m n : ℕ}
    (C : Fin m → Fin n → ℝ) : Prop :=
  ∀ i j, 0 ≤ C i j

/-- The atomic probability measure associated with a finite weight vector. -/
noncomputable def DiscreteMeasure {m : ℕ} (a : Fin m → ℝ) : Measure (Fin m) :=
  Measure.sum fun i => ENNReal.ofReal (a i) • Measure.dirac i

instance isProbabilityMeasure_discreteMeasure {m : ℕ} (a : Fin m → ℝ)
    (ha : IsDiscreteProbabilityVector a) : IsProbabilityMeasure (DiscreteMeasure a) := by
  apply HasSum.isProbabilityMeasure_sum_dirac
  · exact ha.1
  · simpa [DiscreteMeasure, ha.2] using (hasSum_fintype (fun i : Fin m => a i))

/-- The atomic coupling measure represented by a nonnegative matrix. -/
noncomputable def DiscreteCouplingMeasure {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℝ) : Measure (Fin m × Fin n) :=
  Measure.sum fun ij => ENNReal.ofReal (X ij.1 ij.2) • Measure.dirac ij

/-- A nonnegative real cost matrix viewed as an `ENNReal` cost. -/
def DiscreteENNRealCost {m n : ℕ}
    (C : Fin m → Fin n → ℝ) (_hC : IsNonnegativeDiscreteCost C) :
    Fin m → Fin n → ℝ≥0∞ :=
  fun i j => ENNReal.ofReal (C i j)

theorem discreteCouplingMeasure_map_fst {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : ∀ i j, 0 ≤ X i j) :
    Measure.map Prod.fst (DiscreteCouplingMeasure X) =
      DiscreteMeasure (fun i => ∑ j, X i j) := by
  rw [Measure.ext_iff_singleton]
  intro i
  simp only [DiscreteCouplingMeasure]
  rw [Measure.map_sum (by fun_prop)]
  simp only [DiscreteMeasure, Measure.map_smul, Measure.map_dirac, Measure.sum_fintype,
    Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    MeasurableSpace.measurableSet_top, Measure.dirac_apply', Set.indicator_singleton,
    Pi.one_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ENNReal.ofReal_sum_of_nonneg (fun j _ => hX x j)]
  rw [Finset.sum_mul]

theorem discreteCouplingMeasure_map_snd {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : ∀ i j, 0 ≤ X i j) :
    Measure.map Prod.snd (DiscreteCouplingMeasure X) =
      DiscreteMeasure (fun j => ∑ i, X i j) := by
  rw [Measure.ext_iff_singleton]
  intro j
  simp only [DiscreteCouplingMeasure]
  rw [Measure.map_sum (by fun_prop)]
  simp only [DiscreteMeasure, Measure.map_smul, Measure.map_dirac, Measure.sum_fintype,
    Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    MeasurableSpace.measurableSet_top, Measure.dirac_apply', Set.indicator_singleton,
    Pi.one_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ENNReal.ofReal_sum_of_nonneg (fun i _ => hX i x)]
  rw [Finset.sum_mul]

theorem discreteENNRealCost_eq_of_nonnegative {m n : ℕ}
    (C : Fin m → Fin n → ℝ) (hC : IsNonnegativeDiscreteCost C)
    (i : Fin m) (j : Fin n) :
    DiscreteENNRealCost C hC i j = ENNReal.ofReal (C i j) :=
  rfl

/-- The finite discrete problem viewed through the general measure-theoretic definition.

The hypotheses make the two atomic measures probability measures and ensure that
`ENNReal.ofReal` preserves the prescribed real-valued cost matrix. -/
noncomputable def DiscreteKantorovichProblem {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (C : Fin m → Fin n → ℝ)
    (ha : IsDiscreteProbabilityVector a)
    (hb : IsDiscreteProbabilityVector b)
    (hC : IsNonnegativeDiscreteCost C) : ℝ≥0∞ := by
  letI : IsProbabilityMeasure (DiscreteMeasure a) :=
    isProbabilityMeasure_discreteMeasure a ha
  letI : IsProbabilityMeasure (DiscreteMeasure b) :=
    isProbabilityMeasure_discreteMeasure b hb
  exact KantorovichProblem (DiscreteMeasure a) (DiscreteMeasure b)
    (DiscreteENNRealCost C hC)

/-- A nonnegative matrix with prescribed source and target marginals. -/
def IsDiscreteKantorovichCoupling {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ X i j) ∧
    (∀ i, ∑ j, X i j = a i) ∧
    (∀ j, ∑ i, X i j = b j)

/-- The finite transport polytope `U(a, b)`. -/
def DiscreteKantorovichCouplings {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {X | IsDiscreteKantorovichCoupling a b X}

@[simp]
theorem mem_DiscreteKantorovichCouplings_iff {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ) :
    X ∈ DiscreteKantorovichCouplings a b ↔
      (∀ i j, 0 ≤ X i j) ∧
        (∀ i, ∑ j, X i j = a i) ∧
        (∀ j, ∑ i, X i j = b j) :=
  Iff.rfl

theorem discreteCouplingMeasure_mem_KantorovichCouplings {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (hb : IsDiscreteProbabilityVector b)
    (hX : IsDiscreteKantorovichCoupling a b X) :
    DiscreteCouplingMeasure X ∈
      KantorovichCouplings (DiscreteMeasure a) (DiscreteMeasure b) := by
  letI : IsProbabilityMeasure (DiscreteMeasure b) :=
    isProbabilityMeasure_discreteMeasure b hb
  have hfst := discreteCouplingMeasure_map_fst X hX.1
  have hsnd := discreteCouplingMeasure_map_snd X hX.1
  have ha_rows : (fun i => ∑ j, X i j) = a := funext hX.2.1
  have hb_cols : (fun j => ∑ i, X i j) = b := funext hX.2.2
  have hπ : IsProbabilityMeasure (DiscreteCouplingMeasure X) := by
    refine ⟨?_⟩
    calc
      DiscreteCouplingMeasure X Set.univ =
          (Measure.map Prod.snd (DiscreteCouplingMeasure X)) Set.univ := by
            rw [Measure.map_apply measurable_snd MeasurableSet.univ]
            simp
      _ = DiscreteMeasure b Set.univ := by rw [hsnd, hb_cols]
      _ = 1 := measure_univ
  exact ⟨hπ, hfst.trans (congrArg DiscreteMeasure ha_rows),
    hsnd.trans (congrArg DiscreteMeasure hb_cols)⟩

/-- The matrix objective `⟨C, X⟩ = ∑ᵢ ∑ⱼ Cᵢⱼ Xᵢⱼ`. -/
def DiscreteKantorovichCost {m n : ℕ}
    (C : Fin m → Fin n → ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, C i j * X i j

theorem kantorovichCost_discreteCouplingMeasure {m n : ℕ}
    (C : Fin m → Fin n → ℝ) (hC : IsNonnegativeDiscreteCost C)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : ∀ i j, 0 ≤ X i j) :
    KantorovichCost (DiscreteENNRealCost C hC) (DiscreteCouplingMeasure X) =
      ENNReal.ofReal (DiscreteKantorovichCost C X) := by
  simp only [KantorovichCost, DiscreteCouplingMeasure, Measure.sum_fintype,
    DiscreteENNRealCost, lintegral_finset_sum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]
  simp_rw [← ENNReal.ofReal_mul (hX _ _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
    mul_nonneg (hX x.1 x.2) (hC x.1 x.2))]
  simp [DiscreteKantorovichCost, Fintype.sum_prod_type, mul_comm]

/-- The matrix primal value in equation (1), represented as an extended real infimum.

`DiscreteKantorovichProblem` is the unified measure-theoretic version above. -/
noncomputable def DiscreteKantorovichMatrixProblem {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (C : Fin m → Fin n → ℝ)
    (hC : IsNonnegativeDiscreteCost C) : EReal := by
  let _hC := hC
  exact sInf ((fun X => (DiscreteKantorovichCost C X : EReal)) ''
    DiscreteKantorovichCouplings a b)

/-- Feasibility of the dual potentials `(f, g)` in equation (2). -/
def IsDiscreteKantorovichDualFeasible {m n : ℕ}
    (C : Fin m → Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) : Prop :=
  ∀ i j, f i + g j ≤ C i j

/-- The feasible set of dual Kantorovich potentials. -/
def DiscreteKantorovichDualFeasible {m n : ℕ}
    (C : Fin m → Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {(f, g) | IsDiscreteKantorovichDualFeasible C f g}

@[simp]
theorem mem_DiscreteKantorovichDualFeasible_iff {m n : ℕ}
    (C : Fin m → Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) :
    (f, g) ∈ DiscreteKantorovichDualFeasible C ↔
      ∀ i j, f i + g j ≤ C i j :=
  Iff.rfl

/-- The dual objective `⟨a, f⟩ + ⟨b, g⟩`. -/
def DiscreteKantorovichDualObjective {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) : ℝ :=
  (∑ i, a i * f i) + ∑ j, b j * g j

/-- The dual value in equation (2), represented as an extended real supremum. -/
noncomputable def DiscreteKantorovichDual {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (C : Fin m → Fin n → ℝ)
    (hC : IsNonnegativeDiscreteCost C) : EReal := by
  let _hC := hC
  exact sSup ((fun fg =>
      (DiscreteKantorovichDualObjective a b fg.1 fg.2 : EReal)) ''
    DiscreteKantorovichDualFeasible C)

end MeasureTheory
