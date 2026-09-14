import Mathlib
import Foundation.Metric.FixedPoint
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_1

/-!
# Excess of a set over another
Given subsets $A, B \subset H$, the excess of $A$ over $B$ is
$e(A, B) = \sup_{x \in A} d(x, B)$.
-/
open Set
variable {H : Type _} [NormedAddCommGroup H]
/-- The excess of set `A` over set `B`: `e(A, B) = sup_{x ∈ A} d(x, B)`.

This is the real-valued view of the canonical `ℝ≥0∞`-valued `excess` of
`Foundation.Metric.FixedPoint`, exactly as Mathlib defines `Metric.infDist`
from `Metric.infEDist` and `Metric.hausdorffDist` from `Metric.hausdorffEDist`. -/
noncomputable def setExcess (A B : Set H) : ℝ := (excess A B).toReal

/-- The real-valued excess is the supremum of the point-to-set distances
written in the paper. -/
theorem setExcess_eq_iSup_infDist (A B : Set H) :
    setExcess A B = ⨆ x : A, Metric.infDist (x : H) B := by
  by_cases hB : B.Nonempty
  · rw [setExcess, excess, ← iSup_subtype'' A (fun x => Metric.infEDist x B),
      ENNReal.toReal_iSup (fun x => Metric.infEDist_ne_top hB)]
    rfl
  · obtain rfl : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    rw [setExcess, excess, show (⨆ x : A, Metric.infDist (x : H) (∅ : Set H)) = 0 by simp,
      ENNReal.toReal_eq_zero_iff]
    rcases A.eq_empty_or_nonempty with hA | hA
    · simp [hA]
    · right
      simp only [Metric.infEDist_empty]
      rcases hA with ⟨a, ha⟩
      exact le_antisymm le_top (le_iSup₂ (f := fun x (_ : x ∈ A) => (⊤ : ENNReal)) a ha)
