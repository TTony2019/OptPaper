import Mathlib.Tactic
import Foundation.Hilbert.WeakConvergence

/-!
# Lemma 2.4 (Opial)
-/

open Filter
open scoped Topology

recall opial_lemma
recall bounded_sequence_has_weakly_convergent_subsequence

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lemma 2.4: Opial's weak convergence criterion. -/
lemma lemma_2_4_opial
    (x : ℕ → H) (S : Set H)
    (hS : S.Nonempty)
    (hdist : ∀ xbar ∈ S, ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar‖) atTop (𝓝 l))
    (hcluster :
      ∀ xhat : H, ∀ subseq : ℕ → ℕ, StrictMono subseq →
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (x (subseq j))) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) →
        xhat ∈ S) :
    ∃ xstar ∈ S,
      Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (x k)) atTop
        (𝓝 (toWeakSpace ℝ H xstar)) := by
  have hcluster' : ∀ (z : H),
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) → z ∈ S := by
    intro z hp
    rcases hp.exists_subseq_tendsto with ⟨φ, hφ, hφz⟩
    have hsubseq :
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (x (φ j))) atTop
          (𝓝 (toWeakSpace ℝ H z)) := by
      simpa [Function.comp] using hφz
    exact hcluster z φ hφ hsubseq
  exact opial_lemma hS x hdist hcluster'

end Alvarez2004
