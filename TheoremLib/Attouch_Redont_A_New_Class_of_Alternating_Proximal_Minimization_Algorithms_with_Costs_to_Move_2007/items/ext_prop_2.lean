import Mathlib
import Foundation.Hilbert.WeakConvergence
import Foundation.Convex.Subdifferential

open Filter
open ERealFunction

namespace AttouchRedont2007

/-- Weak--strong sequential closedness of the convex subdifferential.

This is the extended-real compatibility theorem used by the 2011 Attouch--Svaiter
development.  The function is represented as a proper `EReal`-valued function;
the proof transports it to the library's `GammaZero` representation and applies
maximal monotonicity of the subdifferential.
-/
theorem convexSubdifferential_weak_strong_closed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (phi : H → EReal)
    (hproper : (∀ x, phi x ≠ ⊥) ∧ ∃ x, phi x ≠ ⊤) (hlsc : LowerSemicontinuous phi)
    (hconvex : ∀ x y : H, ∀ a b : NNReal, a + b = 1 →
      phi ((a : ℝ) • x + (b : ℝ) • y) ≤ (a : EReal) * phi x + (b : EReal) * phi y)
    (x u : ℕ → H) (xbar ubar : H)
    (hx : Tendsto (fun n => toWeakSpace ℝ H (x n)) Filter.atTop
      (nhds (toWeakSpace ℝ H xbar)))
    (hu : Filter.Tendsto u Filter.atTop (nhds ubar))
    (hmem : ∀ n, u n ∈ subdifferential phi (x n)) :
    ubar ∈ subdifferential phi xbar := by
  have hproper' : ERealFunction.IsProper phi := by
    refine ⟨hproper.1, ?_⟩
    rcases hproper.2 with ⟨z, hz⟩
    exact ⟨z, (ERealFunction.mem_dom_iff phi z).2 (lt_top_iff_ne_top.mpr hz)⟩
  let F : H → Set.Ioi (⊥ : EReal) := ERealFunction.properIoi phi hproper'
  have hF_lsc : LowerSemicontinuous (fun z : H => (F z : EReal)) := by
    simpa [F] using hlsc
  have hF_convex : ERealFunction.ConvexOn F (effectiveDomain F) := by
    refine ⟨?_, subset_rfl, ?_⟩
    · rcases hproper.2 with ⟨z, hz⟩
      exact ⟨z, (mem_effectiveDomain_iff).2 (by
        simpa [F] using (lt_top_iff_ne_top.mpr hz))⟩
    · intro p hp q hq a ha0 ha1
      let aNN : NNReal := ⟨a, le_of_lt ha0⟩
      let bNN : NNReal := ⟨1 - a, sub_nonneg.mpr (le_of_lt ha1)⟩
      have hab : aNN + bNN = 1 := by
        apply Subtype.ext
        change a + (1 - a) = 1
        ring
      have h := hconvex p q aNN bNN hab
      simpa [aNN, bNN, F] using h
  have hF_gamma : F ∈ gammaZero H := by
    exact ⟨hF_lsc, hF_convex⟩
  have hmax : SetValuedOperator.IsMaximalMonotone (subdifferential F) :=
    subdifferential_isMaximalMonotone_of_mem_gammaZero hF_gamma
  apply maximal_monotone_graph_weak_strong_closed (subdifferential F) hmax x u xbar ubar
  · simpa [F] using hx
  · exact hu
  · intro n
    simpa [F] using hmem n

end AttouchRedont2007
