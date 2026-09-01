import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

/-- Lemma 2.7: `B` is constant on the zero set of `∂Phi + B`. -/
theorem operator_constant_on_solution_set {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (beta : ℝ) (S : Set H)
    (hbeta : 0 < beta)
    (hcoco : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x))
    (hBmax : Maximal SetValuedOperator.IsMonotone B.toSetValuedOperator)
    (hS : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    ∀ z ∈ S, ∀ w ∈ S, B z = B w := by
  intro z hz w hw
  have hzsub : -B z ∈ ERealFunction.subdifferential Phi z := (hS z).1 hz
  have hwsub : -B w ∈ ERealFunction.subdifferential Phi w := (hS w).1 hw
  have hmono := ERealFunction.isMonotone_subdifferential
    (fun x : H => (Phi x : EReal))
    (ERealFunction.isProper_of_mem_gammaZero hPhi)
    (-B z) hzsub (-B w) hwsub
  have hsubmono : inner ℝ (B z - B w) (z - w) ≤ 0 := by
    rw [show (-B z) - (-B w) = -(B z - B w) by abel, inner_neg_left] at hmono
    linarith
  have hc := hcoco.ineq
    (⟨z, Set.mem_univ z⟩ : Set.univ)
    (⟨w, Set.mem_univ w⟩ : Set.univ)
  have hcobound : beta * ‖B z - B w‖ ^ 2 ≤
      inner ℝ (B z - B w) (z - w) := by
    simpa [real_inner_comm] using hc
  have hnonneg : 0 ≤ beta * ‖B z - B w‖ ^ 2 :=
    mul_nonneg hbeta.le (sq_nonneg _)
  have hprodzero : beta * ‖B z - B w‖ ^ 2 = 0 :=
    le_antisymm (hcobound.trans hsubmono) hnonneg
  have hnormzero : ‖B z - B w‖ = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hprodzero).resolve_left hbeta.ne')
  exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)

end AbbasDynamical2015
