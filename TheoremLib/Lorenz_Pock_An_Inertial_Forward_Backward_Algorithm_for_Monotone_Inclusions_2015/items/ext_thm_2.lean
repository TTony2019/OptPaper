import Mathlib
import Foundation.Hilbert.WeakConvergence
import Foundation.Hilbert.WeakTopology

open Filter

namespace LorenzPock

/-- Opial's weak convergence theorem. -/
theorem opial_weak_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (x : ℕ → H) (S : Set H) (hne : S.Nonempty)
    (hdist : ∀ z ∈ S, ∃ r : ℝ, Tendsto (fun k ↦ ‖x k - z‖) Filter.atTop (nhds r))
    (hcluster : ∀ z, IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (x k))
      (toWeakSpace ℝ H z) → z ∈ S) :
    ∃ z ∈ S, Tendsto (fun k ↦ toWeakSpace ℝ H (x k)) Filter.atTop
      (nhds (toWeakSpace ℝ H z)) := by
  simpa using (opial_lemma (H := H) (C := S) hne x hdist hcluster)

end LorenzPock
