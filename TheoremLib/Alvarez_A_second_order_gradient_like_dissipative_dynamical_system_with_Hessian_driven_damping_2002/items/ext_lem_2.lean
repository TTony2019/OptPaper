import Mathlib
import Foundation.Hilbert.WeakConvergence

namespace Alvarez2002

open Filter

private theorem opial_sampled {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (x : ℝ → H) (S : Set H) (hS : S.Nonempty)
    (hcluster : ∀ s : ℕ → ℝ, Tendsto s atTop atTop → ∀ z,
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H z)) → z ∈ S)
    (hdist : ∀ z ∈ S, ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d))
    (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) :
    ∃ q ∈ S, Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
      (nhds (toWeakSpace ℝ H q)) := by
  refine opial_lemma hS (fun n => x (s n)) ?_ ?_
  · intro z hz
    rcases hdist z hz with ⟨d, hd⟩
    exact ⟨d, hd.comp hs⟩
  · intro z hzcluster
    rcases hzcluster with ⟨φ, hφmono, hφweak⟩
    let r : ℕ → ℝ := fun n => s (φ n)
    have hr : Tendsto r atTop atTop := by
      simpa [r, Function.comp_def] using hs.comp hφmono.tendsto_atTop
    apply hcluster r hr z
    simpa [r, Function.comp_def] using hφweak

private theorem weak_limit_eq_of_time_distance_limits {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (x : ℝ → H) (S : Set H)
    (hdist : ∀ z ∈ S, ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d))
    {u v : ℕ → ℝ} (hu : Tendsto u atTop atTop) (hv : Tendsto v atTop atTop)
    {p q : H} (hpS : p ∈ S) (hqS : q ∈ S)
    (hpweak : Tendsto (fun n => toWeakSpace ℝ H (x (u n))) atTop
      (nhds (toWeakSpace ℝ H p)))
    (hqweak : Tendsto (fun n => toWeakSpace ℝ H (x (v n))) atTop
      (nhds (toWeakSpace ℝ H q))) : p = q := by
  have hdist_u : ∀ z ∈ S, ∃ d : ℝ,
      Tendsto (fun n => ‖x (u n) - z‖) atTop (nhds d) := by
    intro z hz
    rcases hdist z hz with ⟨d, hd⟩
    exact ⟨d, hd.comp hu⟩
  have hdist_v : ∀ z ∈ S, ∃ d : ℝ,
      Tendsto (fun n => ‖x (v n) - z‖) atTop (nhds d) := by
    intro z hz
    rcases hdist z hz with ⟨d, hd⟩
    exact ⟨d, hd.comp hv⟩
  rcases inner_tendsto_of_tendsto_dist_to_two_points hdist_u hpS hqS with ⟨l, hlu⟩
  rcases inner_tendsto_of_tendsto_dist_to_two_points hdist_v hpS hqS with ⟨l', hlv⟩
  have hl_eq : l = l' := by
    rcases hdist p hpS with ⟨lp, hlp⟩
    rcases hdist q hqS with ⟨lq, hlq⟩
    have hform_u : l = (lq ^ 2 - lp ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2) / 2 := by
      have htwo_eq :
          (fun n => 2 * inner ℝ (x (u n)) (p - q)) =
            fun n => ‖x (u n) - q‖ ^ 2 - ‖x (u n) - p‖ ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
        funext n
        rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
        ring_nf
      have htwo : Tendsto (fun n => 2 * inner ℝ (x (u n)) (p - q)) atTop
          (nhds (lq ^ 2 - lp ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2)) := by
        rw [htwo_eq]
        have hconst : Tendsto (fun _ : ℕ => ‖p‖ ^ 2 - ‖q‖ ^ 2) atTop
            (nhds (‖p‖ ^ 2 - ‖q‖ ^ 2)) := tendsto_const_nhds
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (((hlq.comp hu).pow 2).sub ((hlp.comp hu).pow 2)).add hconst
      have hhalf := htwo.const_mul (1 / 2 : ℝ)
      exact tendsto_nhds_unique hlu (by convert hhalf using 1 <;> ring_nf)
    have hform_v : l' = (lq ^ 2 - lp ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2) / 2 := by
      have htwo_eq :
          (fun n => 2 * inner ℝ (x (v n)) (p - q)) =
            fun n => ‖x (v n) - q‖ ^ 2 - ‖x (v n) - p‖ ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
        funext n
        rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
        ring_nf
      have htwo : Tendsto (fun n => 2 * inner ℝ (x (v n)) (p - q)) atTop
          (nhds (lq ^ 2 - lp ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2)) := by
        rw [htwo_eq]
        have hconst : Tendsto (fun _ : ℕ => ‖p‖ ^ 2 - ‖q‖ ^ 2) atTop
            (nhds (‖p‖ ^ 2 - ‖q‖ ^ 2)) := tendsto_const_nhds
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (((hlq.comp hv).pow 2).sub ((hlp.comp hv).pow 2)).add hconst
      have hhalf := htwo.const_mul (1 / 2 : ℝ)
      exact tendsto_nhds_unique hlv (by convert hhalf using 1 <;> ring_nf)
    rw [hform_u, hform_v]
  have hpinner : Tendsto (fun n => inner ℝ (x (u n)) (p - q)) atTop
      (nhds (inner ℝ p (p - q))) := by
    simpa using
      (weakSpace_continuous_inner_right (p - q)).tendsto (toWeakSpace ℝ H p) |>.comp hpweak
  have hqinner : Tendsto (fun n => inner ℝ (x (v n)) (p - q)) atTop
      (nhds (inner ℝ q (p - q))) := by
    simpa using
      (weakSpace_continuous_inner_right (p - q)).tendsto (toWeakSpace ℝ H q) |>.comp hqweak
  have hinner_eq : inner ℝ p (p - q) = inner ℝ q (p - q) := by
    calc
      inner ℝ p (p - q) = l := tendsto_nhds_unique hpinner hlu
      _ = l' := hl_eq
      _ = inner ℝ q (p - q) := (tendsto_nhds_unique hqinner hlv).symm
  have hsq : ‖p - q‖ ^ 2 = 0 := by
    calc
      ‖p - q‖ ^ 2 = inner ℝ (p - q) (p - q) := by rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ p (p - q) - inner ℝ q (p - q) := by rw [inner_sub_left]
      _ = 0 := by rw [hinner_eq, sub_self]
  have hnorm : ‖p - q‖ = 0 := sq_eq_zero_iff.mp hsq
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Opial's continuous-time weak convergence principle. -/
theorem opial_continuous_time {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (x : ℝ → H) (S : Set H) (hS : S.Nonempty)
    (hcluster : ∀ s : ℕ → ℝ, Tendsto s atTop atTop → ∀ z,
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H z)) → z ∈ S)
    (hdist : ∀ z ∈ S, ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d)) :
    ∃ z ∈ S, Tendsto (fun t => toWeakSpace ℝ H (x t)) atTop
      (nhds (toWeakSpace ℝ H z)) := by
  rcases opial_sampled x S hS hcluster hdist (fun n : ℕ => (n : ℝ))
      tendsto_natCast_atTop_atTop with ⟨p, hpS, hpweak⟩
  have hsample : ∀ s : ℕ → ℝ, Tendsto s atTop atTop →
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H p)) := by
    intro s hs
    rcases opial_sampled x S hS hcluster hdist s hs with ⟨q, hqS, hqweak⟩
    have hpq : p = q := weak_limit_eq_of_time_distance_limits x S hdist
      tendsto_natCast_atTop_atTop hs hpS hqS hpweak hqweak
    simpa [hpq] using hqweak
  refine ⟨p, hpS, Filter.tendsto_iff_seq_tendsto.2 ?_⟩
  intro s hs
  simpa [Function.comp_def] using hsample s hs

end Alvarez2002
