import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_3
import Foundation.SetValued.Minty
import Foundation.SetValued.MaximalMonotoneSum
import Foundation.Projection.BestApproximation

namespace BurachikSvaiterRobustnessHPE2001

open SetValuedOperator
open scoped InnerProductSpace Pointwise Set

private theorem normalCone_dom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (C : Set H) : (SetValuedOperator.dom (N[C])) = C := by
  ext x
  constructor
  · rintro hx
    rcases (mem_dom_iff _ _).mp hx with ⟨u, hu⟩
    exact (Set.mem_normalCone_iff_forall.mp hu).1
  · intro hxc
    apply (mem_dom_iff _ _).mpr
    refine ⟨0, ?_⟩
    rw [Set.mem_normalCone_iff_forall]
    exact ⟨hxc, fun y _ => by simp⟩

private theorem normalCone_monotone {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (C : Set H) : IsMonotone (N[C]) := by
  intro x y u hu v hv
  have hxu : x ∈ C := (Set.mem_normalCone_iff_forall.mp hu).1
  have hyv : y ∈ C := (Set.mem_normalCone_iff_forall.mp hv).1
  have hu_le : inner ℝ (y - x) u ≤ 0 := (Set.mem_normalCone_iff_forall.mp hu).2 y hyv
  have hv_le : inner ℝ (x - y) v ≤ 0 := (Set.mem_normalCone_iff_forall.mp hv).2 x hxu
  have hu_xy : 0 ≤ inner ℝ u (x - y) := by
    have h1 : inner ℝ u (y - x) ≤ 0 := by simpa [real_inner_comm] using hu_le
    have h2 : inner ℝ u (y - x) = -inner ℝ u (x - y) := by
      rw [show y - x = -(x - y) by abel, inner_neg_right]
    linarith
  have hv_xy : 0 ≤ inner ℝ (-v) (x - y) := by
    have h1 : inner ℝ v (x - y) ≤ 0 := by simpa [real_inner_comm] using hv_le
    have h2 : inner ℝ (-v) (x - y) = -inner ℝ v (x - y) := by rw [inner_neg_left]
    linarith
  calc
    0 ≤ inner ℝ u (x - y) + inner ℝ (-v) (x - y) := add_nonneg hu_xy hv_xy
    _ = inner ℝ (u - v) (x - y) := by
      rw [show u - v = u + -v by abel, inner_add_left]

private theorem normalCone_minty_surjective {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C) (hCconvex : Convex ℝ C) :
    ∀ r : H, ∃ p : H, ∃ u ∈ N[C] p, r = p + u := by
  intro r
  let hCheb : IsChebyshev C :=
    isChebyshev_of_nonempty_isClosed_convex hCnonempty hCclosed hCconvex
  let p : H := projectionPoint C hCheb r
  have hpC : p ∈ C := projectionPoint_mem C hCheb r
  refine ⟨p, r - p, ?_, by abel⟩
  rw [Set.mem_normalCone_iff_forall]
  exact ⟨hpC, fun z hz =>
    ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hCheb hCconvex).mp rfl).2 z hz⟩

private theorem normalCone_maximal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C) (hCconvex : Convex ℝ C) :
    IsMaximalMonotone (N[C]) := by
  exact (minty_surjective_iff_maximal_monotone (normalCone_monotone C)).2
    (normalCone_minty_surjective C hCnonempty hCclosed hCconvex)

/-! ### The sum theorem for maximal monotone operators

Lemma 3.4 of the paper invokes the following classical theorem, cited there as
`Ref. 29, Theorem 1` (R. T. Rockafellar, *On the maximality of sums of nonlinear
monotone operators*, Trans. Amer. Math. Soc. **149** (1970), 75--88).  It is the
same statement as H. Brézis, *Opérateurs maximaux monotones et semi-groupes de
contractions dans les espaces de Hilbert* (1973), Corollaire 2.7, and
Bauschke--Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert
Spaces*, Theorem 25.1.

The interior qualification point is the second regularity alternative of
Bauschke--Combettes Corollary 25.5, with the roles of `A` and `B` exchanged, so the
statement is proved here from the migrated
`SetValuedOperator.Maximal.add_of_sumRegularity`.  That corollary is itself proved
modulo the documented `sorry` for Bauschke--Combettes Theorem 25.3 in
`Foundation/SetValued/MaximalMonotoneSum.lean`; only `rockafellar_sum_maximal` below
depends on this statement. -/
theorem sum_maximal_monotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A B : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    (hB : B.IsMaximalMonotone) (hqual : (interior A.dom ∩ B.dom).Nonempty) :
    IsMaximalMonotone (A + B) := by
  -- Swap the two operators so that the qualification point matches the second alternative of
  -- Corollary 25.5, then transport the maximality conclusion back along commutativity of `+`.
  have hA' : Maximal SetValuedOperator.IsMonotone A :=
    (isMaximalMonotone_iff_maximal_isMonotone A).1 hA
  have hB' : Maximal SetValuedOperator.IsMonotone B :=
    (isMaximalMonotone_iff_maximal_isMonotone B).1 hB
  have hqual' : (B.dom ∩ interior A.dom).Nonempty := by
    rcases hqual with ⟨x, hxA, hxB⟩
    exact ⟨x, hxB, hxA⟩
  have hmax : Maximal SetValuedOperator.IsMonotone (B + A) :=
    Maximal.add_of_sumRegularity (A := B) (B := A) hB' hA' (Or.inr (Or.inl hqual'))
  exact (isMaximalMonotone_iff_maximal_isMonotone (A + B)).2 (by simpa [add_comm] using hmax)

/-- Rockafellar's sum theorem specialized to the sum of a maximal monotone
operator with the normal-cone operator of a nonempty closed convex set: the
qualification point `z0 ∈ dom T ∩ interior C` supplied by Lemma 3.4 makes the
sum maximal monotone. -/
theorem rockafellar_sum_maximal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {T : SetValuedOperator H H} (hT : T.IsMaximalMonotone) (C : Set H)
    (hCnonempty : C.Nonempty) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (hint : (T.dom ∩ interior C).Nonempty) :
    (T + N[C]).IsMaximalMonotone := by
  have hnormal_max : IsMaximalMonotone (N[C]) :=
    normalCone_maximal C hCnonempty hCclosed hCconvex
  rcases hint with ⟨x, hxT, hxC⟩
  have hqual : (interior (SetValuedOperator.dom (N[C])) ∩ T.dom).Nonempty := by
    refine ⟨x, ?_, hxT⟩
    rw [normalCone_dom]
    exact hxC
  have hsum : IsMaximalMonotone (N[C] + T) :=
    sum_maximal_monotone (N[C]) T hnormal_max hT hqual
  have hcomm : N[C] + T = T + N[C] := by
    ext x w
    change w ∈ N[C] x + T x ↔ w ∈ T x + N[C] x
    rw [Set.mem_add]
    constructor
    · rintro ⟨n, hn, t, ht, rfl⟩
      exact ⟨t, ht, n, hn, by exact add_comm t n⟩
    · rintro ⟨t, ht, n, hn, rfl⟩
      exact ⟨n, hn, t, ht, by exact add_comm n t⟩
  rwa [hcomm] at hsum

end BurachikSvaiterRobustnessHPE2001
