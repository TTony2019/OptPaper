import Mathlib
import Foundation.Hilbert.WeakConvergence

namespace AbbasDynamical2015

open Filter

/-- Opial's trajectory lemma (Lemma 2.10). -/
theorem opial_trajectory_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : Set H) (x : ℝ → H) (hS : S.Nonempty)
    (hdist : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds l))
    (hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop (nhds (toWeakSpace ℝ H z))) → z ∈ S) :
    ∃ z ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z)) := by
  have hcluster' : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n ↦ f (x (u n))) atTop (nhds (f z))) → z ∈ S := by
    rintro z ⟨u, hu, hfun⟩
    exact hcluster z ⟨u, hu, by
      rw [weakConvergence_iff_forall_tendsto_inner_right]
      intro v
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        hfun (InnerProductSpace.toDual ℝ H v)⟩
  obtain ⟨z, hz, hf⟩ := opial_lemma_continuous_weak x S hS hdist hcluster'
  exact ⟨z, hz, by
    rw [weakConvergence_iff_forall_tendsto_inner_right]
    intro u
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hf (InnerProductSpace.toDual ℝ H u)⟩

end AbbasDynamical2015
