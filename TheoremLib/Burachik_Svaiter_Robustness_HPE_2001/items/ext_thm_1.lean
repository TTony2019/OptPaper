import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_1
import Foundation.Hilbert.WeakConvergence
import Foundation.SetValued.MaximalMonotone

open scoped InnerProductSpace Topology
open Filter

namespace BurachikSvaiterRobustnessHPE2001

/-- Demiclosedness of the epsilon-enlargement. -/
theorem epsilon_enlargement_demiclosed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) (y v : ℕ → H) (ε : ℕ → ℝ) (yLimit vLimit : H)
    (hy : Tendsto (fun j ↦ toWeakSpace ℝ H (y j)) Filter.atTop
      (nhds (toWeakSpace ℝ H yLimit)))
    (hv : Tendsto v Filter.atTop (nhds vLimit))
    (hε : Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ j, 0 ≤ ε j)
    (hm : ∀ j, v j ∈ epsilonEnlargement T (ε j) (hε_nonneg j) (y j)) :
    vLimit ∈ T yLimit := by
  apply mem_of_monotonically_related_to_graph hT
  intro z w hw
  have h_eps_le : ∀ j, -ε j ≤ inner ℝ (y j - z) (v j - w) := by
    intro j
    have hj := hm j
    have h_eq : inner ℝ (w - v j) (z - y j) = inner ℝ (y j - z) (v j - w) := by
      simp [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    simpa [epsilonEnlargement, h_eq] using hj z w hw
  have hy_bdd : Bornology.IsBounded (Set.range y) :=
    bounded_range_of_tendsto_weakly hy
  rcases isBounded_iff_forall_norm_le.mp hy_bdd with ⟨M, hM⟩
  have hM_sub : ∀ j, ‖y j - yLimit‖ ≤ M + ‖yLimit‖ := by
    intro j
    calc
      ‖y j - yLimit‖ ≤ ‖y j‖ + ‖yLimit‖ := norm_sub_le _ _
      _ ≤ M + ‖yLimit‖ := by
        gcongr
        exact hM (y j) (Set.mem_range_self j)
  have hv_norm_tendsto : Tendsto (fun j => ‖v j - vLimit‖) atTop (nhds 0) := by
    have hv_sub : Tendsto (fun j => v j - vLimit) atTop (nhds 0) := by
      simpa using hv.sub_const vLimit
    simpa using (tendsto_zero_iff_norm_tendsto_zero.mp hv_sub)
  have hlim1 : Tendsto (fun j => inner ℝ (y j - yLimit) (v j - vLimit)) atTop
      (nhds (0 : ℝ)) := by
    have hbound : ∀ j, ‖inner ℝ (y j - yLimit) (v j - vLimit)‖ ≤
        (M + ‖yLimit‖) * ‖v j - vLimit‖ := by
      intro j
      calc
        ‖inner ℝ (y j - yLimit) (v j - vLimit)‖ =
            |inner ℝ (y j - yLimit) (v j - vLimit)| := by rw [Real.norm_eq_abs]
        _ ≤ ‖y j - yLimit‖ * ‖v j - vLimit‖ := abs_real_inner_le_norm _ _
        _ ≤ (M + ‖yLimit‖) * ‖v j - vLimit‖ := by
          gcongr
          exact hM_sub j
    have hprod : Tendsto (fun j => (M + ‖yLimit‖) * ‖v j - vLimit‖) atTop
        (nhds (0 : ℝ)) := by
      simpa using hv_norm_tendsto.const_mul (M + ‖yLimit‖)
    exact squeeze_zero_norm hbound hprod
  have hlim2 : Tendsto (fun j => inner ℝ (yLimit - z) (v j - vLimit)) atTop
      (nhds (0 : ℝ)) := by
    have hsub : Tendsto (fun j => v j - vLimit) atTop (nhds 0) := by
      simpa using hv.sub_const vLimit
    simpa using Filter.Tendsto.inner (tendsto_const_nhds (x := yLimit - z)) hsub
  have hlim3 : Tendsto (fun j => inner ℝ (y j - z) (vLimit - w)) atTop
      (nhds (inner ℝ (yLimit - z) (vLimit - w))) := by
    have hcoord : Tendsto (fun j => inner ℝ (y j) (vLimit - w)) atTop
        (nhds (inner ℝ yLimit (vLimit - w))) := by
      simpa using (weakSpace_continuous_inner_right (vLimit - w)).tendsto
        (toWeakSpace ℝ H yLimit) |>.comp hy
    simpa [inner_sub_left] using hcoord.sub_const (inner ℝ z (vLimit - w))
  have hdecomp : ∀ j, inner ℝ (y j - z) (v j - w) =
      inner ℝ (y j - yLimit) (v j - vLimit) +
        inner ℝ (yLimit - z) (v j - vLimit) +
          inner ℝ (y j - z) (vLimit - w) := by
    intro j
    calc
      inner ℝ (y j - z) (v j - w) =
          inner ℝ (y j - z) ((v j - vLimit) + (vLimit - w)) := by
            simp [sub_add_sub_cancel]
      _ = inner ℝ (y j - z) (v j - vLimit) + inner ℝ (y j - z) (vLimit - w) := by
            rw [inner_add_right]
      _ = inner ℝ ((y j - yLimit) + (yLimit - z)) (v j - vLimit) +
          inner ℝ (y j - z) (vLimit - w) := by simp [sub_add_sub_cancel]
      _ = (inner ℝ (y j - yLimit) (v j - vLimit) +
          inner ℝ (yLimit - z) (v j - vLimit)) +
          inner ℝ (y j - z) (vLimit - w) := by rw [inner_add_left]
      _ = inner ℝ (y j - yLimit) (v j - vLimit) +
          inner ℝ (yLimit - z) (v j - vLimit) +
          inner ℝ (y j - z) (vLimit - w) := by ring
  have hlim : Tendsto (fun j => inner ℝ (y j - z) (v j - w)) atTop
      (nhds (inner ℝ (yLimit - z) (vLimit - w))) := by
    have hsum := hlim1.add (hlim2.add hlim3)
    simpa [hdecomp, add_assoc] using hsum
  have hneg_eps : Tendsto (fun j => -ε j) atTop (nhds (0 : ℝ)) := by
    simpa using hε.neg
  have hineq : 0 ≤ inner ℝ (yLimit - z) (vLimit - w) := by
    apply le_of_tendsto_of_tendsto hneg_eps hlim
    exact Filter.Eventually.of_forall h_eps_le
  simpa [real_inner_comm] using hineq

end BurachikSvaiterRobustnessHPE2001
