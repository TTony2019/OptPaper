import Mathlib
import Foundation.Hilbert.WeakTopology
import Foundation.Convex.Gamma0

namespace AbbasDynamical2015

open Filter

/-- Remark 2.19: the Kadek--Klee property. -/
theorem kadek_klee_property {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (_hPhi : Phi ∈ ERealFunction.gammaZero H) :
    (hKadecKlee : ∀ (xSeq : ℕ → H) (x : H),
      Tendsto (fun k ↦ toWeakSpace ℝ H (xSeq k)) atTop
        (nhds (toWeakSpace ℝ H x)) →
      Tendsto (fun k ↦ (Phi (xSeq k) : EReal)) atTop
        (nhds (Phi x : EReal)) →
      Tendsto (fun k ↦ ‖xSeq k - x‖) atTop (nhds 0)) →
    ∀ (xSeq : ℕ → H) (x : H),
      Tendsto (fun k ↦ toWeakSpace ℝ H (xSeq k)) atTop
        (nhds (toWeakSpace ℝ H x)) →
      Tendsto (fun k ↦ (Phi (xSeq k) : EReal)) atTop
        (nhds (Phi x : EReal)) →
      Tendsto (fun k ↦ ‖xSeq k - x‖) atTop (nhds 0) := id

end AbbasDynamical2015
