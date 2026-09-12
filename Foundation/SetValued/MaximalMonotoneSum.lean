import Mathlib
import Foundation.SetValued.MaximalMonotone
import Foundation.Convex.NormalCone
import Foundation.Convex.RelativeInterior
import Foundation.Convex.Subdifferential

/-!
# Maximality of sums of maximally monotone operators

Bauschke–Combettes Chapter 25 maximality criterion for the sum of two maximally
monotone operators whose domains satisfy a cone/closed-span regularity condition,
promoted from Bauschke-lean-project (`Chap25/Theorem_25_3`,
`Chap25/Corollary_25_5`).

The reusable owner conclusion is `Maximal IsMonotone (A + B)`.  The deep input is
Theorem 25.3, whose proof needs the Chapter 25 Fitzpatrick-duality machinery
(fiberwise infimal convolution of Fitzpatrick functions and the product-space
normal cone of the graph of a linear map) that is not yet part of `Foundation`, so
it is recorded below as `Maximal.add_adjointImage_of_cone_dom_sub_eq_closure_span`
with a documented `sorry`.  Corollary 25.5 is then proved from it, routing the
five textbook regularity alternatives through the same cone condition.
-/

open Set SetValuedOperator
open scoped Pointwise InnerProductSpace

universe u v

namespace SetValuedOperator

section AdjointImageConeCondition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Theorem 25.3: let `A : H → 2^H` and `B : K → 2^K` be maximally monotone on real Hilbert
spaces, let `L : H →L[ℝ] K`, and suppose that
`cone (dom B - L '' dom A) = closure (span (dom B - L '' dom A))`; then `A + L^* B L`,
realized as `A + L.adjointImage B`, is maximally monotone.

The Chapter 25 Fitzpatrick-duality proof of this statement (Bauschke-lean-project
`Chap25/Theorem_25_3`, via Theorem 25.2 and Proposition 25.41) has not been migrated to
`Foundation` yet, so the statement is recorded here and left as a `sorry`.  Only
`Maximal.add_of_sumRegularity` below depends on it. -/
theorem Maximal.add_adjointImage_of_cone_dom_sub_eq_closure_span
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hcone :
      Set.cone (B.dom - L '' A.dom) =
        ((Submodule.span ℝ (B.dom - L '' A.dom)).topologicalClosure : Set K)) :
    Maximal IsMonotone (A + L.adjointImage B) := by
  sorry

end AdjointImageConeCondition

section SumRegularity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 25.5: a common point of `A` and `interior B` translates an interior
neighborhood of the origin into `A - B`. -/
private theorem zeroMemInterior_sub_of_mem_left_mem_interior_right {A B : Set H} {y : H}
    (hyA : y ∈ A) (hyB : y ∈ interior B) :
    (0 : H) ∈ interior (A - B) := by
  -- Translate a small ball around `y` inside `B` back to a ball around `0` inside `A - B`.
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hyB) with ⟨ε, hε, hball⟩
  have hsubset : Metric.ball (0 : H) ε ⊆ A - B := by
    intro z hz
    refine Set.mem_sub.mpr ⟨y, hyA, y - z, hball ?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, norm_neg] using hz
    · abel
  refine mem_interior_iff_mem_nhds.mpr ?_
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) hε) hsubset

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: once `cone S = univ`, its closed span is also the whole space. -/
private theorem cone_eq_closedSpan_of_cone_eq_univ {S : Set H}
    (hcone_univ : Set.cone S = (Set.univ : Set H)) :
    Set.cone S = ((Submodule.span ℝ S).topologicalClosure : Set H) := by
  have hsubset :
      Set.cone S ⊆ ((Submodule.span ℝ S).topologicalClosure : Set H) :=
    Set.cone_subset_topologicalClosure_span (C := S)
  have hclosure_univ :
      ((Submodule.span ℝ S).topologicalClosure : Set H) = (Set.univ : Set H) := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx_cone : x ∈ Set.cone S := by simp [hcone_univ]
    exact hsubset hx_cone
  simpa [hclosure_univ] using hcone_univ

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: every vector admits a positive scalar multiple in any ball around
the origin. -/
private theorem exists_pos_smul_mem_ball {x : H} {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t • x ∈ Metric.ball (0 : H) ε := by
  by_cases hx : x = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    subst hx
    simpa [Metric.mem_ball, dist_eq_norm] using hε
  · let t : ℝ := ε / (2 * ‖x‖)
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have hnorm : ‖t • x‖ < ε := by
      have ht_mul : t * ‖x‖ = ε / 2 := by
        dsimp [t]
        field_simp [hxnorm.ne']
      calc
        ‖t • x‖ = |t| * ‖x‖ := norm_smul t x
        _ = t * ‖x‖ := by rw [abs_of_nonneg ht.le]
        _ = ε / 2 := ht_mul
        _ < ε := by linarith
    refine ⟨t, ht, ?_⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: an interior neighborhood of `0` yields the cone/closed-span
identity. -/
private theorem cone_eq_closedSpan_of_zero_mem_interior {S : Set H}
    (h0 : (0 : H) ∈ interior S) :
    Set.cone S = ((Submodule.span ℝ S).topologicalClosure : Set H) := by
  have hcone_univ : Set.cone S = (Set.univ : Set H) := by
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0) with ⟨ε, hε, hball⟩
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases exists_pos_smul_mem_ball (x := x) hε with ⟨t, ht, htx_mem_ball⟩
      have htx : t • x ∈ S := hball htx_mem_ball
      have hx_eq : x = t⁻¹ • (t • x) := by
        calc
          x = (1 : ℝ) • x := by simp
          _ = (t⁻¹ * t) • x := by rw [inv_mul_cancel₀ ht.ne']
          _ = t⁻¹ • (t • x) := by rw [smul_smul]
      exact hx_eq ▸
        ConvexCone.smul_mem (ConvexCone.hull ℝ S) (inv_pos.mpr ht) (ConvexCone.subset_hull htx)
  exact cone_eq_closedSpan_of_cone_eq_univ hcone_univ

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: a strong-relative-interior witness at `0` is exactly the
cone/closed-span identity. -/
private theorem cone_eq_closedSpan_of_zero_mem_sri {S : Set H}
    (h0 : (0 : H) ∈ Set.strongRelativeInterior S) :
    Set.cone S = ((Submodule.span ℝ S).topologicalClosure : Set H) := by
  rcases Set.mem_strongRelativeInterior_iff.mp h0 with ⟨hzero, hcone_raw⟩
  simpa [Set.sub_singleton_zero_eq_self (C := S), hzero] using hcone_raw

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: short initial ray segments in every direction force the
cone/closed-span identity. -/
private theorem cone_eq_closedSpan_of_segmentRegularity {S : Set H}
    (hseg : ∀ x : H, ∃ ε : ℝ, 0 < ε ∧ segment ℝ (0 : H) (ε • x) ⊆ S) :
    Set.cone S = ((Submodule.span ℝ S).topologicalClosure : Set H) := by
  have hcone_univ : Set.cone S = (Set.univ : Set H) := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hseg x with ⟨ε, hε, hεseg⟩
      have hscaled_mem : ε • x ∈ S := hεseg (right_mem_segment ℝ (0 : H) (ε • x))
      have hx_eq : x = ε⁻¹ • (ε • x) := by
        calc
          x = (1 : ℝ) • x := by simp
          _ = (ε⁻¹ * ε) • x := by rw [inv_mul_cancel₀ hε.ne']
          _ = ε⁻¹ • (ε • x) := by rw [smul_smul]
      exact hx_eq ▸
        ConvexCone.smul_mem (ConvexCone.hull ℝ S) (inv_pos.mpr hε)
          (ConvexCone.subset_hull hscaled_mem)
  exact cone_eq_closedSpan_of_cone_eq_univ hcone_univ

/-- Helper for Corollary 25.5: the identity map leaves the adjoint-image operator unchanged. -/
private theorem id_adjointImage_eq (A : SetValuedOperator H H) :
    (ContinuousLinearMap.id ℝ H).adjointImage A = A := by
  ext x u
  simp [ContinuousLinearMap.adjointImage]

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: the identity map does not change a set under image. -/
private theorem id_image_eq (S : Set H) :
    (ContinuousLinearMap.id ℝ H) '' S = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [CompleteSpace H] in
/-- Helper for Corollary 25.5: the five source regularity alternatives all imply the
cone/closed-span hypothesis on `dom A - dom B`. -/
private theorem cone_dom_sub_eq_closureSpan_of_sumRegularity
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hreg :
      B.dom = (Set.univ : Set H) ∨
        (A.dom ∩ interior B.dom).Nonempty ∨
        (0 : H) ∈ interior (A.dom - B.dom) ∨
        (∀ x : H, ∃ ε : ℝ, 0 < ε ∧ segment ℝ (0 : H) (ε • x) ⊆ A.dom - B.dom) ∨
        (0 : H) ∈ Set.strongRelativeInterior (A.dom - B.dom)) :
    Set.cone (A.dom - B.dom) =
      ((Submodule.span ℝ (A.dom - B.dom)).topologicalClosure : Set H) := by
  rcases hreg with hBuniv | hreg
  · have hdiff_univ : A.dom - B.dom = (Set.univ : Set H) := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        rcases dom_nonempty_of_maximal A hA with ⟨a, ha⟩
        have ha_sub_x_B : a - x ∈ B.dom := by
          simp [hBuniv]
        have hxa : a - (a - x) = x := by
          abel
        exact Set.mem_sub.mpr ⟨a, ha, a - x, ha_sub_x_B, hxa⟩
    have h0Interior : (0 : H) ∈ interior (A.dom - B.dom) := by
      simp [hdiff_univ]
    exact cone_eq_closedSpan_of_zero_mem_interior h0Interior
  rcases hreg with hinter | hreg
  · rcases hinter with ⟨x, hxA, hxInteriorB⟩
    have h0Interior : (0 : H) ∈ interior (A.dom - B.dom) :=
      zeroMemInterior_sub_of_mem_left_mem_interior_right hxA hxInteriorB
    exact cone_eq_closedSpan_of_zero_mem_interior h0Interior
  rcases hreg with h0Interior | hreg
  · exact cone_eq_closedSpan_of_zero_mem_interior h0Interior
  rcases hreg with hseg | hsri
  · exact cone_eq_closedSpan_of_segmentRegularity hseg
  · exact cone_eq_closedSpan_of_zero_mem_sri hsri

/-- Corollary 25.5: let `A` and `B` be maximally monotone operators from `H → 2^H`. If one of
the five source regularity alternatives holds, namely `dom B = H`, or
`(dom A ∩ interior (dom B)).Nonempty`, or `0 ∈ interior (dom A - dom B)`, or `∀ x, ∃ ε > 0,
segment ℝ (0 : H) (ε • x) ⊆ dom A - dom B`, or `0 ∈ sri (dom A - dom B)`, then `A + B` is
maximally monotone. -/
theorem Maximal.add_of_sumRegularity
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hreg :
      B.dom = (Set.univ : Set H) ∨
        (A.dom ∩ interior B.dom).Nonempty ∨
        (0 : H) ∈ interior (A.dom - B.dom) ∨
        (∀ x : H, ∃ ε : ℝ, 0 < ε ∧ segment ℝ (0 : H) (ε • x) ⊆ A.dom - B.dom) ∨
        (0 : H) ∈ Set.strongRelativeInterior (A.dom - B.dom)) :
    Maximal IsMonotone (A + B) := by
  have hcone :
      Set.cone (A.dom - B.dom) =
        ((Submodule.span ℝ (A.dom - B.dom)).topologicalClosure : Set H) :=
    cone_dom_sub_eq_closureSpan_of_sumRegularity hA hreg
  have hconeId :
      Set.cone (A.dom - (ContinuousLinearMap.id ℝ H) '' B.dom) =
        ((Submodule.span ℝ (A.dom - (ContinuousLinearMap.id ℝ H) '' B.dom)).topologicalClosure :
          Set H) := by
    rw [id_image_eq]
    exact hcone
  -- Apply Theorem 25.3 with the operator roles swapped, so its cone hypothesis is exactly the
  -- one produced by the source alternatives; the identity adjoint-image then collapses to `A + B`.
  have hmaxId :
      Maximal IsMonotone (B + (ContinuousLinearMap.id ℝ H).adjointImage A) :=
    Maximal.add_adjointImage_of_cone_dom_sub_eq_closure_span
      (A := B) (B := A) hB hA (ContinuousLinearMap.id ℝ H) hconeId
  have hmax : Maximal IsMonotone (B + A) := by
    simpa [id_adjointImage_eq] using hmaxId
  simpa [add_comm] using hmax

/-- Brézis Corollary 2.7 (equivalently Rockafellar's sum theorem, Bauschke–Combettes Theorem
25.1): if `A` and `B` are maximally monotone and the interior of `dom A` meets `dom B`, then
`A + B` is maximally monotone.  This is the second regularity alternative of Corollary 25.5 with
the roles of `A` and `B` exchanged. -/
theorem Maximal.add_of_interior_dom_inter_dom_nonempty
    {A B : SetValuedOperator H H} (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hqual : (interior A.dom ∩ B.dom).Nonempty) :
    Maximal IsMonotone (A + B) := by
  have hqual' : (B.dom ∩ interior A.dom).Nonempty := by
    rcases hqual with ⟨x, hxA, hxB⟩
    exact ⟨x, hxB, hxA⟩
  have hmax : Maximal IsMonotone (B + A) :=
    Maximal.add_of_sumRegularity (A := B) (B := A) hB hA (Or.inr (Or.inl hqual'))
  simpa [add_comm] using hmax

end SumRegularity

end SetValuedOperator
