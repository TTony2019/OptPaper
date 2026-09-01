import Mathlib
import Foundation.FixedPoint.Nonexpansive

namespace AbbasDynamical2015

/-- A beta-cocoercive operator is `1 / beta`-Lipschitz (Lemma 2.4). -/
theorem cocoercive_lipschitz {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (beta : ℝ) (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x)) :
    LipschitzWith ⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩ B := by
  have heq : Real.toNNReal (1 / beta) =
      ⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩ :=
    NNReal.eq (Real.coe_toNNReal (1 / beta) (one_div_nonneg.mpr hB.pos.le))
  rw [← heq]
  exact cocoercive_implies_lipschitz B beta hB

end AbbasDynamical2015
