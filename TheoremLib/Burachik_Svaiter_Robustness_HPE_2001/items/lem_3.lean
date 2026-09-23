import Foundation.SetValued.Enlargement
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.algo_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_2
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_3
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_4
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.lem_2
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.ext_def_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.ext_thm_3
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.ext_thm_4
import Foundation.SetValued.Minty

open scoped Pointwise Set

namespace BurachikSvaiterRobustnessHPE2001

private theorem nonneg_summable_uniform_bound {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : Summable f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k, f k ≤ B := by
  refine ⟨∑' i, f i, tsum_nonneg hf, ?_⟩
  intro k
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hs.hasSum.tendsto_sum_nat
  filter_upwards [Filter.eventually_atTop.2
    ⟨k + 1, fun n hn => lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩]
    with n hn
  have hk : k ∈ Finset.range n := Finset.mem_range.mpr hn
  simpa using Finset.single_le_sum (fun i _ => hf i) hk

private theorem related_operator_dom_subset_ball {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (T : SetValuedOperator H H) (M : ℝ) :
    (relatedOperator T M).dom ⊆ relatedBall (H := H) M := by
  intro x hx
  rcases SetValuedOperator.mem_dom_iff _ _ |>.mp hx with ⟨w, hw⟩
  change w ∈ T x + N[relatedBall (H := H) M] x at hw
  rw [Set.mem_add] at hw
  rcases hw with ⟨u, hu, η, hη, _⟩
  exact (Set.mem_normalCone_iff_forall.mp hη).1

private theorem squared_reverse_triangle_bound {H : Type*} [NormedAddCommGroup H]
    {a b : H} : (‖b‖ - ‖a‖) ^ 2 ≤ ‖a + b‖ ^ 2 := by
  have habs : |‖b‖ - ‖a‖| ≤ ‖b + a‖ := by
    simpa [add_comm] using (abs_norm_sub_norm_le b (-a))
  have hs : |‖b‖ - ‖a‖| ^ 2 ≤ ‖b + a‖ ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 habs
  simpa [sq_abs, add_comm] using hs

private theorem quadratic_nonneg_root_bound {p C D t : ℝ} (hp : 0 < p)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (hquad : p * t ^ 2 - 2 * C * t ≤ D) :
    t ≤ (C + Real.sqrt (C ^ 2 + p * D)) / p := by
  have hrad : 0 ≤ C ^ 2 + p * D := by positivity
  have hsqrt : (Real.sqrt (C ^ 2 + p * D)) ^ 2 = C ^ 2 + p * D :=
    Real.sq_sqrt hrad
  have hsqrt0 : 0 ≤ Real.sqrt (C ^ 2 + p * D) := Real.sqrt_nonneg _
  by_contra h
  have hlt : C + Real.sqrt (C ^ 2 + p * D) < p * t :=
    by simpa [mul_comm] using (div_lt_iff₀ hp).mp (lt_of_not_ge h)
  have hpos : 0 < p * t - C := by linarith
  have hsq : (Real.sqrt (C ^ 2 + p * D)) ^ 2 < (p * t - C) ^ 2 := by
    nlinarith
  nlinarith

private theorem normalCone_zero_of_interior {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {S : Set H} {x η : H}
    (hx : x ∈ interior S) (hη : η ∈ N[S] x) : η = 0 := by
  by_contra hne
  have hnhds : S ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  rcases (Metric.mem_nhds_iff.mp hnhds) with ⟨ε, hε, hεsub⟩
  let c : ℝ := ε / (2 * ‖η‖)
  let y : H := x + c • η
  have hyS : y ∈ S := by
    apply hεsub
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [y, c]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hc : 0 ≤ ε / (2 * ‖η‖) := by positivity
    rw [abs_of_nonneg hc]
    have hηpos : 0 < ‖η‖ := norm_pos_iff.mpr hne
    field_simp [ne_of_gt hηpos]
    linarith
  have hle : inner ℝ (y - x) η ≤ 0 := (Set.mem_normalCone_iff_forall.mp hη).2 y hyS
  have hpos : 0 < inner ℝ η (y - x) := by
    dsimp [y, c]
    rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
    have hηpos : 0 < ‖η‖ := norm_pos_iff.mpr hne
    positivity
  rw [real_inner_comm] at hle
  linarith

/-- Lemma 3.4: in the absence of zeros, the HPE sequence is unbounded. -/
theorem hpe_unbounded_of_no_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) (A : HPEIterates H T) (hzero : T.zeros = ∅) :
    ¬ Bornology.IsBounded (Set.range A.x) := by
  intro hxb
  rcases isBounded_iff_forall_norm_le.mp hxb with ⟨Bx, hBx⟩
  have hx : ∀ k, ‖A.x k‖ ≤ Bx := by
    intro k
    exact hBx _ (Set.mem_range_self k)
  have hBx0 : 0 ≤ Bx := le_trans (norm_nonneg (A.x 0)) (hx 0)
  rcases nonneg_summable_uniform_bound A.α_nonneg A.summable_alpha with
    ⟨Bα, hBα0, hα⟩
  rcases nonneg_summable_uniform_bound A.δ_nonneg A.summable_delta with
    ⟨Bδ, hBδ0, hδ⟩
  have hcv : ∀ k, ‖A.c k • A.v k‖ ≤ Bx + Bx + Bα := by
    intro k
    let e : H := A.x (k + 1) - (A.x k - A.c k • A.v k)
    have he : ‖e‖ ≤ A.α k := by
      simpa [e] using A.update_error k
    have hrepr : A.c k • A.v k = A.x k - A.x (k + 1) + e := by
      dsimp [e]
      abel
    calc
      ‖A.c k • A.v k‖ = ‖A.x k - A.x (k + 1) + e‖ := by rw [hrepr]
      _ ≤ ‖A.x k - A.x (k + 1)‖ + ‖e‖ := norm_add_le _ _
      _ ≤ (‖A.x k‖ + ‖A.x (k + 1)‖) + A.α k := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ Bx + Bx + Bα := by
        exact add_le_add (add_le_add (hx k) (hx (k + 1))) (hα k)
  have hcv0 : 0 ≤ Bx + Bx + Bα := by positivity
  rcases A.sigma_bound with ⟨σbar, hσbar0, hσbar1, hσ⟩
  let C : ℝ := Bx + Bx + Bα
  have hC : 0 ≤ C := by simpa [C] using hcv0
  have hquadratic : ∀ k, (1 - σbar ^ 2) * ‖A.y k - A.x k‖ ^ 2 -
      2 * C * ‖A.y k - A.x k‖ ≤ Bδ := by
    intro k
    let q : H := A.c k • A.v k
    let b : H := A.y k - A.x k
    have hrev : (‖b‖ - ‖q‖) ^ 2 ≤ ‖q + b‖ ^ 2 :=
      squared_reverse_triangle_bound (a := q) (b := b)
    have heq : q + b = A.c k • A.v k + A.y k - A.x k := by
      dsimp [q, b]
      abel
    have hres := A.residual_bound k
    have hce : 0 ≤ 2 * A.c k * A.ε k := by
      have := A.c_pos k
      have := A.ε_nonneg k
      positivity
    have hnorm : ‖q + b‖ ^ 2 ≤ A.δ k + (A.σ k) ^ 2 * ‖b‖ ^ 2 := by
      rw [heq]
      linarith
    have hs0 : 0 ≤ A.σ k := A.σ_nonneg k
    have hsle : A.σ k ≤ σbar := (hσ k).2
    have hssq : (A.σ k) ^ 2 ≤ σbar ^ 2 := by nlinarith
    have htb : 0 ≤ ‖b‖ ^ 2 := sq_nonneg _
    have hmult : (A.σ k) ^ 2 * ‖b‖ ^ 2 ≤ σbar ^ 2 * ‖b‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hssq htb
    have hqbound : ‖q‖ ≤ C := by simpa [q, C] using hcv k
    have hqmul : 2 * ‖q‖ * ‖b‖ ≤ 2 * C * ‖b‖ := by
      gcongr
    have hδbound : A.δ k ≤ Bδ := hδ k
    change (1 - σbar ^ 2) * ‖b‖ ^ 2 - 2 * C * ‖b‖ ≤ Bδ
    nlinarith [hrev, hnorm, hmult, hqmul, sq_nonneg ‖q‖]
  have hp : 0 < 1 - σbar ^ 2 := by nlinarith [sq_nonneg σbar]
  let R : ℝ := (C + Real.sqrt (C ^ 2 + (1 - σbar ^ 2) * Bδ)) /
    (1 - σbar ^ 2)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have htbound : ∀ k, ‖A.y k - A.x k‖ ≤ R := by
    intro k
    apply quadratic_nonneg_root_bound hp hC hBδ0 (norm_nonneg _)
    simpa [R] using hquadratic k
  let By : ℝ := R + Bx
  have hBy0 : 0 ≤ By := by dsimp [By]; positivity
  have hy : ∀ k, ‖A.y k‖ ≤ By := by
    intro k
    calc
      ‖A.y k‖ = ‖(A.y k - A.x k) + A.x k‖ := by congr 1 <;> abel
      _ ≤ ‖A.y k - A.x k‖ + ‖A.x k‖ := norm_add_le _ _
      _ ≤ R + Bx := add_le_add (htbound k) (hx k)
      _ = By := rfl
  rcases minty_surjective_of_maximal_monotone hT (0 : H) with
    ⟨z0, u0, hu0, _⟩
  have hz0 : z0 ∈ T.dom := SetValuedOperator.mem_dom_iff T z0 |>.2 ⟨u0, hu0⟩
  let M : ℝ := max ‖z0‖ (max Bx By) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hz0M : ‖z0‖ < M := by
    dsimp [M]
    linarith [le_max_left ‖z0‖ (max Bx By)]
  have hxM : ∀ k, ‖A.x k‖ < M := by
    intro k
    exact lt_of_le_of_lt (le_trans (hx k) (le_trans (le_max_left _ _) (le_max_right _ _)))
      (lt_add_one _)
  have hyM : ∀ k, ‖A.y k‖ < M := by
    intro k
    exact lt_of_le_of_lt (le_trans (hy k) (le_trans (le_max_right _ _) (le_max_right _ _)))
      (lt_add_one _)
  have hBxM : Bx < M := by
    dsimp [M]
    linarith [le_max_left Bx By, le_max_right ‖z0‖ (max Bx By)]
  have hz0int : z0 ∈ interior (relatedBall (H := H) M) := by
    apply Metric.ball_subset_interior_closedBall
    change dist z0 0 < 2 * M
    rw [dist_zero_right]
    linarith
  have hxint : ∀ k, A.x k ∈ interior (relatedBall (H := H) M) := by
    intro k
    apply Metric.ball_subset_interior_closedBall
    change dist (A.x k) 0 < 2 * M
    rw [dist_zero_right]
    linarith [hxM k]
  have hyint : ∀ k, A.y k ∈ interior (relatedBall (H := H) M) := by
    intro k
    apply Metric.ball_subset_interior_closedBall
    change dist (A.y k) 0 < 2 * M
    rw [dist_zero_right]
    linarith [hyM k]
  have hSnonempty : (relatedBall (H := H) M).Nonempty := by
    refine ⟨0, ?_⟩
    simp [relatedBall]
    linarith
  have hSclosed : IsClosed (relatedBall (H := H) M) := by
    simpa [relatedBall] using (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) (2 * M)))
  have hSconvex : Convex ℝ (relatedBall (H := H) M) := by
    simpa [relatedBall] using (convex_closedBall (0 : H) (2 * M))
  let U : SetValuedOperator H H := relatedOperator T M
  have hU : U.IsMaximalMonotone := by
    dsimp [U, relatedOperator]
    apply rockafellar_sum_maximal hT (relatedBall (H := H) M) hSnonempty hSclosed hSconvex
    exact ⟨z0, hz0, hz0int⟩
  have hUdom : Bornology.IsBounded U.dom := by
    apply Bornology.IsBounded.subset (Metric.isBounded_closedBall :
      Bornology.IsBounded (Metric.closedBall (0 : H) (2 * M)))
    intro x hxU
    have hxball : x ∈ relatedBall (H := H) M := by
      simpa [U] using related_operator_dom_subset_ball T M hxU
    simpa [relatedBall] using hxball
  rcases (maximal_monotone_surjective_of_bounded_domain hU hUdom).2 with ⟨xzero, hxzero⟩
  have hUzero : ∃ x : H, (0 : H) ∈ U x := ⟨xzero, hxzero⟩
  have hUmem : ∀ k, A.v k ∈ enlargement U (A.ε k) (A.y k) := by
    intro k
    change ∀ z w, w ∈ U z → -A.ε k ≤ inner ℝ (w - A.v k) (z - A.y k)
    intro z w hw
    change w ∈ T z + N[relatedBall (H := H) M] z at hw
    rw [Set.mem_add] at hw
    rcases hw with ⟨u, hu, η, hη, rfl⟩
    have hTmem := A.enlargement_mem k z u hu
    change -A.ε k ≤ inner ℝ (u - A.v k) (z - A.y k) at hTmem
    have hηineq : 0 ≤ inner ℝ η (z - A.y k) := by
      have hle : inner ℝ (A.y k - z) η ≤ 0 :=
        (Set.mem_normalCone_iff_forall.mp hη).2 (A.y k) (interior_subset (hyint k))
      have hle' : inner ℝ η (A.y k - z) ≤ 0 := by simpa [real_inner_comm] using hle
      have hcomm : inner ℝ η (A.y k - z) = -inner ℝ η (z - A.y k) := by
        rw [show A.y k - z = -(z - A.y k) by abel, inner_neg_right]
      linarith
    calc
      -A.ε k = -A.ε k + 0 := by ring
      _ ≤ inner ℝ (u - A.v k) (z - A.y k) + inner ℝ η (z - A.y k) :=
        add_le_add hTmem hηineq
      _ = inner ℝ (u + η - A.v k) (z - A.y k) := by
        rw [show u + η - A.v k = (u - A.v k) + η by abel, inner_add_left]
  let AU : HPEIterates H U := { A with enlargement_mem := hUmem }
  rcases hpe_weakly_converges_to_zero hU AU hUzero with ⟨xbar, hxbarU, hxweak⟩
  have hxbarB : ‖xbar‖ ≤ Bx := by
    have hmem : ∀ k, A.x k ∈ Metric.closedBall (0 : H) Bx := by
      intro k
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx k
    have hlim : xbar ∈ Metric.closedBall (0 : H) Bx := by
      apply mem_of_tendsto_weakly_of_isClosed_convex (C := Metric.closedBall (0 : H) Bx)
        Metric.isClosed_closedBall (convex_closedBall (0 : H) Bx) hmem
      simpa [AU] using hxweak
    simpa [Metric.mem_closedBall, dist_zero_right] using hlim
  have hxbarint : xbar ∈ interior (relatedBall (H := H) M) := by
    apply Metric.ball_subset_interior_closedBall
    change dist xbar 0 < 2 * M
    rw [dist_zero_right]
    linarith [hxbarB, hBxM]
  change (0 : H) ∈ U xbar at hxbarU
  change (0 : H) ∈ T xbar + N[relatedBall (H := H) M] xbar at hxbarU
  rw [Set.mem_add] at hxbarU
  rcases hxbarU with ⟨u, hu, η, hη, hsum⟩
  have hηzero : η = 0 := normalCone_zero_of_interior hxbarint hη
  have huzero : u = 0 := by simpa [hηzero] using hsum
  have hcontr : xbar ∈ T.zeros := by simpa [SetValuedOperator.mem_zeros_iff, huzero] using hu
  simpa [hzero] using hcontr

end BurachikSvaiterRobustnessHPE2001
