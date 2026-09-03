import Foundation.Hilbert.WeakConvergence
import Foundation.SetValued.Monotone
import Foundation.SetValued.MaximalMonotone
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.def_1

namespace AlvarezAttouch2001

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Weak-strong closedness of the graph of a maximal monotone operator. -/
theorem weak_strong_closedness_maximal_monotone_graph
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    {x u : H} {xs us : ℕ → H}
    (hxs : Tendsto (fun n => toWeakSpace ℝ H (xs n)) atTop
      (𝓝 (toWeakSpace ℝ H x)))
    (hus : Tendsto us atTop (𝓝 u))
    (hmem : ∀ n : ℕ, us n ∈ A (xs n)) :
    u ∈ A x := by
  classical
  apply mem_of_monotonically_related_to_graph hA
  intro y v hv
  have hmono_n : ∀ n : ℕ, 0 ≤ inner ℝ (us n - v) (xs n - y) := by
    intro n
    exact hA.1 (us n) (hmem n) v hv
  have hxs_bdd : Bornology.IsBounded (Set.range xs) :=
    bounded_range_of_tendsto_weakly hxs
  rcases (isBounded_iff_forall_norm_le (s := Set.range xs)).mp hxs_bdd with ⟨C, hC⟩
  let M : ℝ := max C 0
  have hxs_norm_le' (n : ℕ) : ‖xs n‖ ≤ M :=
    le_trans (hC (xs n) ⟨n, rfl⟩) (le_max_left _ _)
  have hxs_inner : ∀ z : H, Tendsto (fun n : ℕ ↦ inner ℝ (xs n) z) atTop
      (𝓝 (inner ℝ x z)) :=
    ((weakConvergence_iff_forall_tendsto_inner_right (𝓗 := H) xs x).mp hxs)
  have hus_norm_sub_zero : Tendsto (fun n : ℕ ↦ ‖us n - u‖) atTop (𝓝 0) := by
    simpa [sub_self] using (hus.sub (tendsto_const_nhds (x := u))).norm
  have h_cross_inner_tendsto :
      Tendsto (fun n : ℕ ↦ inner ℝ (us n - u) (xs n)) atTop (𝓝 0) := by
    have h_bound (n : ℕ) :
        |inner ℝ (us n - u) (xs n)| ≤ ‖us n - u‖ * M := by
      calc
        |inner ℝ (us n - u) (xs n)| ≤ ‖us n - u‖ * ‖xs n‖ := by
          simpa [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (us n - u) (xs n)
        _ ≤ ‖us n - u‖ * M :=
          mul_le_mul_of_nonneg_left (hxs_norm_le' n) (norm_nonneg _)
    have h_prod_zero : Tendsto (fun n : ℕ ↦ ‖us n - u‖ * M) atTop (𝓝 0) := by
      simpa [zero_mul] using Filter.Tendsto.mul hus_norm_sub_zero tendsto_const_nhds
    have h_abs_tendsto : Tendsto (fun n : ℕ ↦ |inner ℝ (us n - u) (xs n)|)
        atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ abs_nonneg _) h_bound h_prod_zero
    have h_neg_tendsto : Tendsto (fun n : ℕ ↦ -|inner ℝ (us n - u) (xs n)|)
        atTop (𝓝 0) := by
      simpa using h_abs_tendsto.neg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le h_neg_tendsto h_abs_tendsto
    · intro n
      exact neg_abs_le _
    · intro n
      exact le_abs_self _
  have husxs_tendsto : Tendsto (fun n : ℕ ↦ inner ℝ (us n) (xs n)) atTop
      (𝓝 (inner ℝ u x)) := by
    have h_weak_part : Tendsto (fun n : ℕ ↦ inner ℝ u (xs n)) atTop
        (𝓝 (inner ℝ u x)) := by
      simpa [real_inner_comm] using hxs_inner u
    have h_sum : Tendsto
        (fun n : ℕ ↦ inner ℝ (us n - u) (xs n) + inner ℝ u (xs n)) atTop
        (𝓝 (0 + inner ℝ u x)) :=
      Filter.Tendsto.add h_cross_inner_tendsto h_weak_part
    simpa [← inner_add_left, sub_add_cancel] using h_sum
  have husy_tendsto : Tendsto (fun n : ℕ ↦ inner ℝ (us n) y) atTop
      (𝓝 (inner ℝ u y)) :=
    hus.inner tendsto_const_nhds
  have hvxs_tendsto : Tendsto (fun n : ℕ ↦ inner ℝ v (xs n)) atTop
      (𝓝 (inner ℝ v x)) := by
    simpa [real_inner_comm] using hxs_inner v
  have h_const : Tendsto (fun _ : ℕ ↦ inner ℝ v y) atTop (𝓝 (inner ℝ v y)) :=
    tendsto_const_nhds
  have h_total : Tendsto (fun n : ℕ ↦ inner ℝ (us n - v) (xs n - y)) atTop
      (𝓝 (inner ℝ (u - v) (x - y))) := by
    have h := ((husxs_tendsto.sub husy_tendsto).sub hvxs_tendsto).add h_const
    convert h using 1
    · ext n
      simp [inner_sub_left, inner_sub_right]
      ring
    · simp [inner_sub_left, inner_sub_right]
      ring
  exact ge_of_tendsto h_total (Filter.Eventually.of_forall hmono_n)

end AlvarezAttouch2001
