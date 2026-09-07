import Mathlib.Tactic
import Foundation.SetValued.Monotone
import Foundation.Hilbert.WeakConvergence

/-!
# Weak-strong closedness of maximal monotone graphs

Source: H. Brezis, *Operateurs maximaux monotones et semi-groupes de
contractions dans les espaces de Hilbert*, Mathematics Studies 5,
North-Holland, Amsterdam, 1973.
-/

open SetValuedOperator
open Filter
open scoped InnerProductSpace Topology

recall SetValuedOperator.graph
recall SetValuedOperator.IsMaximalMonotone

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A point monotonically related to the graph of a maximal monotone operator belongs to
the graph. This local copy avoids importing a non-built helper module for this item. -/
theorem alvarez2004_mem_of_monotonically_related_to_graph
    {T : SetValuedOperator H H} (hT : SetValuedOperator.IsMaximalMonotone T) {x u : H}
    (hrel : ∀ y v, v ∈ T y → 0 ≤ inner ℝ (u - v) (x - y)) :
    u ∈ T x := by
  let T' : SetValuedOperator H H := fun z => T z ∪ {w | z = x ∧ w = u}
  have hsubset : T.graph ⊆ T'.graph := by
    intro p hp
    exact Or.inl hp
  have hmono' : SetValuedOperator.IsMonotone T' := by
    intro a b p hp q hq
    rcases hp with hp_old | hp_new
    · rcases hq with hq_old | hq_new
      · exact hT.1 p hp_old q hq_old
      · rcases hq_new with ⟨rfl, rfl⟩
        have h := hrel a p hp_old
        have hinner : inner ℝ (p - q) (a - b) = inner ℝ (q - p) (b - a) := by
          calc
            inner ℝ (p - q) (a - b) = inner ℝ (-(q - p)) (-(b - a)) := by
              congr <;> abel
            _ = inner ℝ (q - p) (b - a) := by
              rw [inner_neg_neg]
        simpa [hinner] using h
    · rcases hp_new with ⟨rfl, rfl⟩
      rcases hq with hq_old | hq_new
      · exact hrel b q hq_old
      · rcases hq_new with ⟨rfl, rfl⟩
        simp
  have hadd : (x, u) ∈ T'.graph := by
    exact Or.inr ⟨rfl, rfl⟩
  exact hT.2 T' hmono' hsubset hadd

/-- The graph of a maximal monotone operator is closed for weak convergence in
the first component and strong convergence in the second component. -/
theorem weak_strong_closedness_maximal_monotone_graph
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    {x v : H} {xs vs : ℕ → H}
    (hxs : Tendsto (fun i : ℕ ↦ toWeakSpace ℝ H (xs i)) atTop
      (𝓝 (toWeakSpace ℝ H x)))
    (hvs : Tendsto vs atTop (𝓝 v))
    (hmem : ∀ i : ℕ, vs i ∈ A (xs i)) :
    v ∈ A x := by
  classical
  apply alvarez2004_mem_of_monotonically_related_to_graph hA
  intro y w hw
  have hmono_i : ∀ i : ℕ, 0 ≤ inner ℝ (vs i - w) (xs i - y) := by
    intro i
    exact hA.1 (vs i) (hmem i) w hw
  have hxs_bdd : Bornology.IsBounded (Set.range xs) :=
    bounded_range_of_tendsto_weakly hxs
  rcases (isBounded_iff_forall_norm_le (s := Set.range xs)).mp hxs_bdd with ⟨C, hC⟩
  have hxs_norm_le (i : ℕ) : ‖xs i‖ ≤ C := hC (xs i) ⟨i, rfl⟩
  let M : ℝ := max C 0
  have hxs_norm_le' (i : ℕ) : ‖xs i‖ ≤ M :=
    le_trans (hxs_norm_le i) (le_max_left _ _)
  have hxs_inner : ∀ u : H, Tendsto (fun i : ℕ ↦ inner ℝ (xs i) u) atTop
      (𝓝 (inner ℝ x u)) :=
    ((weakConvergence_iff_forall_tendsto_inner_right (𝓗 := H) xs x).mp hxs)
  have hvs_norm_sub_zero : Tendsto (fun i : ℕ ↦ ‖vs i - v‖) atTop (𝓝 0) := by
    simpa [sub_self] using (hvs.sub (tendsto_const_nhds (x := v))).norm
  have h_cross_inner_tendsto :
      Tendsto (fun i : ℕ ↦ inner ℝ (vs i - v) (xs i)) atTop (𝓝 0) := by
    have h_bound (i : ℕ) :
        |inner ℝ (vs i - v) (xs i)| ≤ ‖vs i - v‖ * M := by
      calc
        |inner ℝ (vs i - v) (xs i)| ≤ ‖vs i - v‖ * ‖xs i‖ := by
          simpa [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (vs i - v) (xs i)
        _ ≤ ‖vs i - v‖ * M :=
          mul_le_mul_of_nonneg_left (hxs_norm_le' i) (norm_nonneg _)
    have h_prod_zero : Tendsto (fun i : ℕ ↦ ‖vs i - v‖ * M) atTop (𝓝 0) := by
      simpa [zero_mul] using Filter.Tendsto.mul hvs_norm_sub_zero tendsto_const_nhds
    have h_abs_tendsto : Tendsto (fun i : ℕ ↦ |inner ℝ (vs i - v) (xs i)|)
        atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ abs_nonneg _) h_bound h_prod_zero
    have h_neg_tendsto : Tendsto (fun i : ℕ ↦ -|inner ℝ (vs i - v) (xs i)|)
        atTop (𝓝 0) := by
      simpa using h_abs_tendsto.neg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le h_neg_tendsto h_abs_tendsto
    · intro i
      exact neg_abs_le _
    · intro i
      exact le_abs_self _
  have hvsxs_tendsto : Tendsto (fun i : ℕ ↦ inner ℝ (vs i) (xs i)) atTop
      (𝓝 (inner ℝ v x)) := by
    have h_weak_part : Tendsto (fun i : ℕ ↦ inner ℝ v (xs i)) atTop
        (𝓝 (inner ℝ v x)) := by
      simpa [real_inner_comm] using hxs_inner v
    have h_sum : Tendsto
        (fun i : ℕ ↦ inner ℝ (vs i - v) (xs i) + inner ℝ v (xs i)) atTop
        (𝓝 (0 + inner ℝ v x)) :=
      Filter.Tendsto.add h_cross_inner_tendsto h_weak_part
    simpa [← inner_add_left, sub_add_cancel] using h_sum
  have hvsy_tendsto : Tendsto (fun i : ℕ ↦ inner ℝ (vs i) y) atTop
      (𝓝 (inner ℝ v y)) :=
    hvs.inner tendsto_const_nhds
  have hwxs_tendsto : Tendsto (fun i : ℕ ↦ inner ℝ w (xs i)) atTop
      (𝓝 (inner ℝ w x)) := by
    simpa [real_inner_comm] using hxs_inner w
  have h_const : Tendsto (fun _ : ℕ ↦ inner ℝ w y) atTop (𝓝 (inner ℝ w y)) :=
    tendsto_const_nhds
  have h_total : Tendsto (fun i : ℕ ↦ inner ℝ (vs i - w) (xs i - y)) atTop
      (𝓝 (inner ℝ (v - w) (x - y))) := by
    have h := ((hvsxs_tendsto.sub hvsy_tendsto).sub hwxs_tendsto).add h_const
    convert h using 1
    · ext i
      simp [inner_sub_left, inner_sub_right]
      ring
    · simp [inner_sub_left, inner_sub_right]
      ring
  exact ge_of_tendsto h_total (Filter.Eventually.of_forall hmono_i)

end Alvarez2004
