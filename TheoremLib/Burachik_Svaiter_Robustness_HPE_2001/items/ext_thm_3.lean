import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_3
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.ext_def_1
import Foundation.SetValued.Minty
import Foundation.Projection.BestApproximation
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_thm_1

namespace BurachikSvaiterRobustnessHPE2001

open SetValuedOperator
open scoped InnerProductSpace Pointwise

private theorem normalityOperator_dom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (C : Set H) : (normalityOperator C).dom = C := by
  ext x
  constructor
  · rintro hx
    rcases (mem_dom_iff _ _).mp hx with ⟨u, hu⟩
    by_cases hxc : x ∈ C
    · exact hxc
    · simp [normalityOperator, hxc] at hu
  · intro hxc
    apply (mem_dom_iff _ _).mpr
    refine ⟨0, ?_⟩
    simp [normalityOperator, hxc]

private theorem normalityOperator_monotone {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (C : Set H) : IsMonotone (normalityOperator C) := by
  intro x y u hu v hv
  by_cases hx : x ∈ C
  · by_cases hy : y ∈ C
    · simp [normalityOperator, hx, hy] at hu hv
      have hu_xy : 0 ≤ inner ℝ u (x - y) := hu y hy
      have hv_yx : 0 ≤ inner ℝ v (y - x) := hv x hx
      have hv_xy : 0 ≤ inner ℝ (-v) (x - y) := by
        calc
          0 ≤ inner ℝ v (y - x) := hv_yx
          _ = inner ℝ (-v) (x - y) := by
            rw [show x - y = -(y - x) by abel, inner_neg_left, inner_neg_right]
            ring
      calc
        0 ≤ inner ℝ u (x - y) + inner ℝ (-v) (x - y) := add_nonneg hu_xy hv_xy
        _ = inner ℝ (u - v) (x - y) := by
          rw [show u - v = u + -v by abel, inner_add_left]
    · simp [normalityOperator, hy] at hv
  · simp [normalityOperator, hx] at hu

private theorem normalityOperator_minty_surjective {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C) (hCconvex : Convex ℝ C) :
    ∀ r : H, ∃ p : H, ∃ u ∈ normalityOperator C p, r = p + u := by
  intro r
  let hCheb : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex hCnonempty hCclosed hCconvex
  let p : H := projectionPoint C hCheb r
  have hpC : p ∈ C := projectionPoint_mem C hCheb r
  refine ⟨p, r - p, ?_, by abel⟩
  simp only [normalityOperator, hpC, ↓reduceIte, Set.mem_setOf_eq]
  intro z hz
  have hproj : inner ℝ (z - p) (r - p) ≤ 0 := by
    exact ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hCheb hCconvex).mp rfl).2 z hz
  calc
    0 ≤ -inner ℝ (z - p) (r - p) := neg_nonneg.mpr hproj
    _ = inner ℝ (r - p) (p - z) := by
      rw [real_inner_comm, show p - z = -(z - p) by abel, inner_neg_right]

private theorem normalityOperator_maximal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C) (hCconvex : Convex ℝ C) :
    IsMaximalMonotone (normalityOperator C) := by
  exact (minty_surjective_iff_maximal_monotone (normalityOperator_monotone C)).2
    (normalityOperator_minty_surjective C hCnonempty hCclosed hCconvex)

theorem rockafellar_sum_maximal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {T : SetValuedOperator H H} (hT : T.IsMaximalMonotone) (C : Set H)
    (hCnonempty : C.Nonempty) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (hint : (T.dom ∩ interior C).Nonempty) :
    (setValuedSum T (normalityOperator C)).IsMaximalMonotone := by
  have hnormal_max : IsMaximalMonotone (normalityOperator C) :=
    normalityOperator_maximal C hCnonempty hCclosed hCconvex
  rcases hint with ⟨x, hxT, hxC⟩
  have hqual : (interior (normalityOperator C).dom ∩ T.dom).Nonempty := by
    refine ⟨x, ?_, hxT⟩
    rw [normalityOperator_dom]
    exact hxC
  have hsum : IsMaximalMonotone (normalityOperator C + T) :=
    sum_maximal_monotone (normalityOperator C) T hnormal_max hT hqual
  have hcomm : normalityOperator C + T = T + normalityOperator C := by
    ext x w
    change w ∈ normalityOperator C x + T x ↔ w ∈ T x + normalityOperator C x
    rw [Set.mem_add]
    constructor
    · rintro ⟨n, hn, t, ht, rfl⟩
      exact ⟨t, ht, n, hn, by exact add_comm t n⟩
    · rintro ⟨t, ht, n, hn, rfl⟩
      exact ⟨n, hn, t, ht, by exact add_comm n t⟩
  have hsetValuedSum : setValuedSum T (normalityOperator C) = T + normalityOperator C := by
    ext x w
    change (∃ t ∈ T x, ∃ n ∈ normalityOperator C x, w = t + n) ↔
      w ∈ T x + normalityOperator C x
    rw [Set.mem_add]
    constructor
    · rintro ⟨t, ht, n, hn, hEq⟩
      exact ⟨t, ht, n, hn, hEq.symm⟩
    · rintro ⟨t, ht, n, hn, hEq⟩
      exact ⟨t, ht, n, hn, hEq.symm⟩
  rw [hcomm, ← hsetValuedSum] at hsum
  exact hsum

end BurachikSvaiterRobustnessHPE2001
