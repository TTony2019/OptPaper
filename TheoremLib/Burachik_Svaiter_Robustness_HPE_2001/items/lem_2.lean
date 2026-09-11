import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.cor_2
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.cor_3
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.ext_thm_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.ext_thm_2

open Filter
open scoped Topology

namespace BurachikSvaiterRobustnessHPE2001

private theorem hpe_y_subseq_tendsto_weakly_of_x_subseq {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {T : SetValuedOperator H H}
    (A : HPEIterates H T) {p : H} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hx : Tendsto (fun j ↦ toWeakSpace ℝ H (A.x (φ j))) atTop
      (nhds (toWeakSpace ℝ H p)))
    (hyx : Tendsto (fun k ↦ ‖A.y k - A.x k‖) atTop (nhds 0)) :
    Tendsto (fun j ↦ toWeakSpace ℝ H (A.y (φ j))) atTop
      (nhds (toWeakSpace ℝ H p)) := by
  have hsubStrong : Tendsto (fun j ↦ A.y (φ j) - A.x (φ j)) atTop
      (nhds (0 : H)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Function.comp] using hyx.comp hφ.tendsto_atTop
  have hsubWeak : Tendsto (fun j ↦ toWeakSpace ℝ H (A.y (φ j) - A.x (φ j))) atTop
      (nhds (0 : WeakSpace ℝ H)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (0 : H)).comp hsubStrong
  have hsum := hx.add hsubWeak
  simpa [show (fun j ↦ A.x (φ j) + (A.y (φ j) - A.x (φ j))) =
      fun j ↦ A.y (φ j) by funext j; abel] using hsum

/-- Lemma 3.3: if a zero exists, HPE converges weakly to a zero. -/
theorem hpe_weakly_converges_to_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) (A : HPEIterates H T)
    (hzero : ∃ xStar, (0 : H) ∈ T xStar) :
    ∃ xStar, (0 : H) ∈ T xStar ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (A.x k)) atTop
        (nhds (toWeakSpace ℝ H xStar)) := by
  rcases hpe_asymptotics A hzero with ⟨hxBounded, hyx0, hε0, hvNorm0, _⟩
  have hcluster_zero : ∀ p : H,
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (A.x k)) (toWeakSpace ℝ H p) →
        (0 : H) ∈ T p := by
    intro p hp
    rcases hp with ⟨φ, hφmono, hφx⟩
    have hxφ : Tendsto (fun j ↦ toWeakSpace ℝ H (A.x (φ j))) atTop
        (nhds (toWeakSpace ℝ H p)) := by
      simpa [Function.comp] using hφx
    have hyφ := hpe_y_subseq_tendsto_weakly_of_x_subseq A hφmono hxφ hyx0
    have hvφ : Tendsto (fun j ↦ A.v (φ j)) atTop (nhds (0 : H)) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [Function.comp] using hvNorm0.comp hφmono.tendsto_atTop
    have hεφ : Tendsto (fun j ↦ A.ε (φ j)) atTop (nhds 0) := by
      simpa [Function.comp] using hε0.comp hφmono.tendsto_atTop
    exact epsilon_enlargement_demiclosed hT (fun j ↦ A.y (φ j)) (fun j ↦ A.v (φ j))
      (fun j ↦ A.ε (φ j)) p 0 hyφ hvφ hεφ (fun j ↦ A.ε_nonneg (φ j))
      (fun j ↦ A.enlargement_mem (φ j))
  have hunique : ∀ p q : H,
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (A.x k)) (toWeakSpace ℝ H p) →
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (A.x k)) (toWeakSpace ℝ H q) →
          p = q := by
    intro p q hp hq
    have hp0 := hcluster_zero p hp
    have hq0 := hcluster_zero q hq
    rcases hpe_distance_converges A hp0 with ⟨Lp, _, hdistP⟩
    rcases hpe_distance_converges A hq0 with ⟨Lq, _, hdistQ⟩
    rcases hp with ⟨φ, hφmono, hφweak⟩
    rcases hq with ⟨ψ, hψmono, hψweak⟩
    have hdistPφ : Tendsto (fun j ↦ ‖A.x (φ j) - p‖) atTop (nhds Lp) := by
      simpa [Function.comp] using hdistP.comp hφmono.tendsto_atTop
    have hdistQφ : Tendsto (fun j ↦ ‖A.x (φ j) - q‖) atTop (nhds Lq) := by
      simpa [Function.comp] using hdistQ.comp hφmono.tendsto_atTop
    have hdistPψ : Tendsto (fun j ↦ ‖A.x (ψ j) - p‖) atTop (nhds Lp) := by
      simpa [Function.comp] using hdistP.comp hψmono.tendsto_atTop
    have hdistQψ : Tendsto (fun j ↦ ‖A.x (ψ j) - q‖) atTop (nhds Lq) := by
      simpa [Function.comp] using hdistQ.comp hψmono.tendsto_atTop
    have hφweak' : Tendsto (fun j ↦ toWeakSpace ℝ H (A.x (φ j))) atTop
        (nhds (toWeakSpace ℝ H p)) := by simpa [Function.comp] using hφweak
    have hψweak' : Tendsto (fun j ↦ toWeakSpace ℝ H (A.x (ψ j))) atTop
        (nhds (toWeakSpace ℝ H q)) := by simpa [Function.comp] using hψweak
    by_contra hpq
    have hqp : q ≠ p := Ne.symm hpq
    have hLq_gt_Lp := opial_lemma_paper (fun j ↦ A.x (φ j)) p q hφweak' hqp
    rw [hdistQφ.liminf_eq, hdistPφ.liminf_eq] at hLq_gt_Lp
    have hLp_gt_Lq := opial_lemma_paper (fun j ↦ A.x (ψ j)) q p hψweak' hpq
    rw [hdistPψ.liminf_eq, hdistQψ.liminf_eq] at hLp_gt_Lq
    linarith
  rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint A.x).2
      ⟨hxBounded, hunique⟩ with ⟨xStar, hxStarWeak⟩
  have hxStarCluster :
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (A.x k)) (toWeakSpace ℝ H xStar) :=
    ⟨id, strictMono_id, by simpa [Function.comp] using hxStarWeak⟩
  exact ⟨xStar, hcluster_zero xStar hxStarCluster, hxStarWeak⟩

end BurachikSvaiterRobustnessHPE2001
