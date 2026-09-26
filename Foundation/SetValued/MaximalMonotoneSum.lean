import Mathlib
import Foundation.SetValued.MaximalMonotone
import Foundation.SetValued.Resolvent
import Foundation.SetValued.ProductNormalCone
import Foundation.SetValued.Fitzpatrick
import Foundation.Convex.NormalCone
import Foundation.Convex.RelativeInterior
import Foundation.Convex.RelativeInteriorGraph
import Foundation.Convex.Subdifferential
import Foundation.Convex.FiberwiseDuality
import Foundation.Convex.FenchelRockafellar

/-!
# Maximality of sums of maximally monotone operators

Bauschke–Combettes Chapter 25 maximality criterion for the sum of two maximally
monotone operators whose domains satisfy a cone/closed-span regularity condition,
promoted from Bauschke-lean-project (`Chap25/Theorem_25_3`,
`Chap25/Corollary_25_5`).

The reusable owner conclusion is `Maximal IsMonotone (A + B)`.  The proof of
Theorem 25.3 uses the Chapter 25 Fitzpatrick-duality machinery (fiberwise
infimal convolution of Fitzpatrick functions and the product-space normal cone
of the graph of a linear map), and Corollary 25.5 routes the five textbook
regularity alternatives through the same cone condition.
-/

open Set SetValuedOperator
open scoped Pointwise InnerProductSpace

universe u v

namespace SetValuedOperator

section AdjointImageConeCondition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

omit [CompleteSpace H] [CompleteSpace K] in
/-- The first, purely algebraic part of the sum theorem: pointwise sums preserve monotonicity. -/
theorem IsMonotone.pointwiseSum
    {A : SetValuedOperator H H} {B : SetValuedOperator H H}
    (hA : IsMonotone A) (hB : IsMonotone B) :
    IsMonotone (A + B) := by
  exact SetValuedOperator.IsMonotone.add hA hB

omit [CompleteSpace H] in
/-- Every first-coordinate Fitzpatrick-domain point can be approximated by points of the
operator domain.  The proof uses the resolvent of a small positive multiple of the operator. -/
private theorem fst_image_dom_fitzpatrick_subset_closure_dom
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : SetValuedOperator E E) (hT : Maximal IsMonotone T) :
    Prod.fst '' ERealFunction.dom (fitzpatrickProd T) ⊆ closure T.dom := by
  let hTm : IsMaximalMonotone T :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone T).2 hT
  intro x hx
  rcases hx with ⟨⟨x, u⟩, hxu, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hF_lt_top : fitzpatrick T x u < (⊤ : EReal) :=
    (ERealFunction.mem_dom_iff (fitzpatrickProd T) (x, u)).mp hxu
  have hF_ne_top : fitzpatrick T x u ≠ (⊤ : EReal) := ne_of_lt hF_lt_top
  have hF_ne_bot : fitzpatrick T x u ≠ (⊥ : EReal) := fitzpatrick_ne_bot hTm x u
  have hF_coe : fitzpatrick T x u = ((fitzpatrick T x u).toReal : EReal) :=
    (EReal.coe_toReal hF_ne_top hF_ne_bot).symm
  let d : ℝ := (fitzpatrick T x u).toReal - inner ℝ x u
  have hd : 0 ≤ d := by
    have hinner := inner_le_fitzpatrick_of_maximal hTm x u
    rw [hF_coe] at hinner
    have hinner' : inner ℝ x u ≤ (fitzpatrick T x u).toReal :=
      EReal.coe_le_coe_iff.mp hinner
    dsimp [d]
    linarith
  let μ : ℝ := ε ^ 2 / (d + 1)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact div_pos (sq_pos_of_pos hε) (by linarith)
  let y : E := resolventMap T hTm μ hμ (x + μ • u)
  let a : E := μ⁻¹ • ((x + μ • u) - y)
  have ha : a ∈ T y := by
    simpa [a, y] using resolventMap_residual_mem T hTm μ hμ (x + μ • u)
  have hμa : μ • a = (x + μ • u) - y := by
    dsimp [a]
    rw [smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
  have hxy : x - y = μ • (a - u) := by
    rw [smul_sub, hμa]
    abel
  have hterm :
      ((inner ℝ x a + inner ℝ y u - inner ℝ y a : ℝ) : EReal) ≤
        fitzpatrick T x u := by
    exact le_sSup ⟨y, a, ha, rfl⟩
  rw [hF_coe] at hterm
  have hterm' : inner ℝ x a + inner ℝ y u - inner ℝ y a ≤
      (fitzpatrick T x u).toReal := EReal.coe_le_coe_iff.mp hterm
  have hexpr :
      inner ℝ x a + inner ℝ y u - inner ℝ y a - inner ℝ x u =
        μ * ‖a - u‖ ^ 2 := by
    calc
      inner ℝ x a + inner ℝ y u - inner ℝ y a - inner ℝ x u =
          inner ℝ (x - y) (a - u) := by
            rw [inner_sub_left, inner_sub_right, inner_sub_right]
            ring
      _ = inner ℝ (μ • (a - u)) (a - u) := by rw [hxy]
      _ = μ * ‖a - u‖ ^ 2 := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hμnorm : μ * ‖a - u‖ ^ 2 ≤ d := by
    rw [← hexpr]
    dsimp [d]
    linarith
  have hyx : y - x = μ • (u - a) := by
    calc
      y - x = -(x - y) := by abel
      _ = -(μ • (a - u)) := by rw [hxy]
      _ = μ • (-(a - u)) := by rw [smul_neg]
      _ = μ • (u - a) := by congr 1 <;> abel
  have hnorm_sq : ‖y - x‖ ^ 2 = μ ^ 2 * ‖a - u‖ ^ 2 := by
    rw [hyx, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
    rw [mul_pow]
    congr 1
    rw [norm_sub_rev]
  have hnorm_bound : ‖y - x‖ ^ 2 ≤ μ * d := by
    rw [hnorm_sq]
    have hmul := mul_le_mul_of_nonneg_left hμnorm hμ.le
    nlinarith
  have hμd : μ * d < ε ^ 2 := by
    dsimp [μ]
    have hden : 0 < d + 1 := by linarith
    have hden_ne : d + 1 ≠ 0 := ne_of_gt hden
    field_simp [hden_ne]
    nlinarith
  have hnorm_lt : ‖y - x‖ < ε := by
    have hnonneg : 0 ≤ ‖y - x‖ := norm_nonneg _
    nlinarith
  exact ⟨y, (SetValuedOperator.mem_dom_iff T y).2 ⟨a, ha⟩, by
    simpa [dist_eq_norm, norm_sub_rev] using hnorm_lt⟩

private theorem fitzpatrick_product_term_eq_add
    {x₁ u₁ z₁ v₁ : H} {x₂ u₂ z₂ v₂ : K} :
    inner ℝ (x₁, x₂) (v₁, v₂) + inner ℝ (z₁, z₂) (u₁, u₂) -
        inner ℝ (z₁, z₂) (v₁, v₂) =
      (inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁) +
        (inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂) := by
  rw [ERealFunction.prod_inner_l2_apply, ERealFunction.prod_inner_l2_apply,
    ERealFunction.prod_inner_l2_apply]
  ring

private theorem fst_image_dom_fitzpatrick_product_eq
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Prod.fst '' ERealFunction.dom (fitzpatrickProd (SetValuedOperator.product A B)) =
      (Prod.fst '' ERealFunction.dom (fitzpatrickProd A)) ×ˢ
        (Prod.fst '' ERealFunction.dom (fitzpatrickProd B)) := by
  apply Set.Subset.antisymm
  · intro q hq
    rcases hq with ⟨p, hP, hpq⟩
    rcases p with ⟨p₁, p₂⟩
    rcases p₁ with ⟨x₁, x₂⟩
    rcases p₂ with ⟨u₁, u₂⟩
    subst q
    have hP_top : fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) <
        (⊤ : EReal) :=
      (ERealFunction.mem_dom_iff (fitzpatrickProd (SetValuedOperator.product A B))
        ((x₁, x₂), (u₁, u₂))).mp hP
    have hBm : IsMaximalMonotone B :=
      (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone B).2 hB
    rcases maximalMonotone_graph_nonempty hBm with ⟨⟨z₂, v₂⟩, hv₂⟩
    have hA_top : fitzpatrick A x₁ u₁ < (⊤ : EReal) := by
      have hA_le : fitzpatrick A x₁ u₁ ≤
          fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) -
            ((inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂ : ℝ) : EReal) := by
        rw [fitzpatrick_eq_iSup_graph A x₁ u₁]
        refine iSup_le fun r ↦ ?_
        rcases r with ⟨⟨z₁, v₁⟩, hv₁⟩
        have hprod : (v₁, v₂) ∈
            SetValuedOperator.product A B (z₁, z₂) :=
          (mem_product A B (z₁, z₂) (v₁, v₂)).2 ⟨hv₁, hv₂⟩
        have hterm :
            (((inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁ : ℝ) : EReal) +
              ((inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂ : ℝ) : EReal)) ≤
              fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) := by
          change _ ≤ fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂)
          rw [← EReal.coe_add]
          exact le_sSup ⟨(z₁, z₂), (v₁, v₂), hprod, by
            rw [fitzpatrick_product_term_eq_add]⟩
        have hterm' :
            (((inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁ : ℝ) : EReal) +
              ((inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂ : ℝ) : EReal)) ≤
              fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) := hterm
        exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
          (Or.inl (EReal.coe_ne_top _))).2 (by
            calc
              _ = (((inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁) +
                (inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂) : ℝ) : EReal) := by
                  rw [EReal.coe_add]
              _ ≤ _ := hterm)
      have hA_ne_top : fitzpatrick A x₁ u₁ ≠ (⊤ : EReal) := by
        intro htop
        have htop_le := hA_le
        rw [htop] at htop_le
        have hsub_lt :
            fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) -
                ((inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂ : ℝ) : EReal) <
              (⊤ : EReal) := by
          apply (EReal.sub_lt_iff (a := (⊤ : EReal))
            (b := ((inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂ : ℝ) : EReal))
            (c := fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂))
            (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).2
          simpa [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] using hP_top
        exact (not_lt_of_ge htop_le) hsub_lt
      exact lt_of_le_of_ne le_top hA_ne_top
    have hB_top : fitzpatrick B x₂ u₂ < (⊤ : EReal) := by
      have hAm : IsMaximalMonotone A :=
        (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).2 hA
      rcases maximalMonotone_graph_nonempty hAm with ⟨⟨z₁, v₁⟩, hv₁⟩
      have hB_le : fitzpatrick B x₂ u₂ ≤
          fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) -
            ((inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁ : ℝ) : EReal) := by
        rw [fitzpatrick_eq_iSup_graph B x₂ u₂]
        refine iSup_le fun r ↦ ?_
        rcases r with ⟨⟨z₂, v₂⟩, hv₂⟩
        have hprod : (v₁, v₂) ∈
            SetValuedOperator.product A B (z₁, z₂) :=
          (mem_product A B (z₁, z₂) (v₁, v₂)).2 ⟨hv₁, hv₂⟩
        have hterm :
            (((inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁ : ℝ) : EReal) +
              ((inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂ : ℝ) : EReal)) ≤
              fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) := by
          rw [← EReal.coe_add]
          exact le_sSup ⟨(z₁, z₂), (v₁, v₂), hprod, by
            rw [fitzpatrick_product_term_eq_add]⟩
        exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
          (Or.inl (EReal.coe_ne_top _))).2 (by
            simpa [EReal.coe_add, add_comm] using hterm)
      have hB_ne_top : fitzpatrick B x₂ u₂ ≠ (⊤ : EReal) := by
        intro htop
        have htop_le := hB_le
        rw [htop] at htop_le
        have hsub_lt :
            fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) -
                ((inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁ : ℝ) : EReal) <
              (⊤ : EReal) := by
          apply (EReal.sub_lt_iff (a := (⊤ : EReal))
            (b := ((inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁ : ℝ) : EReal))
            (c := fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂))
            (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).2
          simpa [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] using hP_top
        exact (not_lt_of_ge htop_le) hsub_lt
      exact lt_of_le_of_ne le_top hB_ne_top
    refine ⟨⟨⟨x₁, u₁⟩, hA_top, rfl⟩, ⟨⟨x₂, u₂⟩, hB_top, rfl⟩⟩
  · intro q hq
    rcases q with ⟨q₁, q₂⟩
    rcases hq with ⟨⟨pA, hA, hpA⟩, ⟨pB, hB, hpB⟩⟩
    rcases pA with ⟨x₁, u₁⟩
    rcases pB with ⟨x₂, u₂⟩
    simp only [Prod.fst] at hpA hpB
    subst q₁
    subst q₂
    refine ⟨⟨(x₁, x₂), (u₁, u₂)⟩, ?_, rfl⟩
    rw [ERealFunction.mem_dom_iff]
    have hP_le : fitzpatrick (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂) ≤
        fitzpatrick A x₁ u₁ + fitzpatrick B x₂ u₂ := by
      rw [fitzpatrick_eq_iSup_graph (SetValuedOperator.product A B) (x₁, x₂) (u₁, u₂)]
      refine iSup_le fun r ↦ ?_
      rcases r with ⟨⟨⟨z₁, z₂⟩, ⟨v₁, v₂⟩⟩, hprod⟩
      rcases (mem_product A B (z₁, z₂) (v₁, v₂)).mp hprod with ⟨hv₁, hv₂⟩
      have hAterm :
          ((inner ℝ x₁ v₁ + inner ℝ z₁ u₁ - inner ℝ z₁ v₁ : ℝ) : EReal) ≤
            fitzpatrick A x₁ u₁ := by
        rw [fitzpatrick_eq_iSup_graph A x₁ u₁]
        exact le_iSup_of_le ⟨(z₁, v₁), hv₁⟩ le_rfl
      have hBterm :
          ((inner ℝ x₂ v₂ + inner ℝ z₂ u₂ - inner ℝ z₂ v₂ : ℝ) : EReal) ≤
            fitzpatrick B x₂ u₂ := by
        rw [fitzpatrick_eq_iSup_graph B x₂ u₂]
        exact le_iSup_of_le ⟨(z₂, v₂), hv₂⟩ le_rfl
      rw [fitzpatrick_product_term_eq_add, EReal.coe_add]
      exact add_le_add hAterm hBterm
    exact lt_of_le_of_lt hP_le (EReal.add_lt_top (ne_of_lt hA) (ne_of_lt hB))

private theorem fst_image_sub_eq_sub_fst_image
    {E : Type*} [AddGroup E] {S T : Set (E × E)} :
    Prod.fst '' (S - T) = (Prod.fst '' S) - (Prod.fst '' T) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases Set.mem_sub.mp hp with ⟨s, hs, t, ht, hst⟩
    refine Set.mem_sub.mpr ⟨s.1, ⟨s, hs, rfl⟩, t.1, ⟨t, ht, rfl⟩, ?_⟩
    simpa using congrArg Prod.fst hst
  · intro hx
    rcases Set.mem_sub.mp hx with ⟨s, hs, t, ht, hst⟩
    rcases hs with ⟨p, hp, rfl⟩
    rcases ht with ⟨q, hq, rfl⟩
    refine ⟨p - q, Set.mem_sub.mpr ⟨p, hp, q, hq, rfl⟩, ?_⟩
    simpa [hst]

private theorem normalCone_dom_eq_of_nonempty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} (hC : C.Nonempty) :
    SetValuedOperator.dom (Set.normalCone C) = C := by
  ext x
  constructor
  · intro hx
    rcases (SetValuedOperator.mem_dom_iff (Set.normalCone C) x).mp hx with ⟨u, hu⟩
    exact (Set.mem_normalCone_iff_forall.mp hu).1
  · intro hx
    apply (SetValuedOperator.mem_dom_iff (Set.normalCone C) x).2
    refine ⟨0, (Set.mem_normalCone_iff_forall).2 ⟨hx, ?_⟩⟩
    intro y hy
    simp

private theorem fst_image_dom_fitzpatrick_eq_of_closed_convex_normalCone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {C : Set E} (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hN : Maximal IsMonotone (Set.normalCone C)) :
    Prod.fst '' ERealFunction.dom (fitzpatrickProd (Set.normalCone C)) = C := by
  apply Set.Subset.antisymm
  · intro x hx
    have hsub := fst_image_dom_fitzpatrick_subset_closure_dom
      (Set.normalCone C) hN hx
    rw [normalCone_dom_eq_of_nonempty hCne] at hsub
    exact hCclosed.closure_subset hsub
  · intro x hx
    refine ⟨(x, 0), ?_, rfl⟩
    rw [ERealFunction.mem_dom_iff]
    change fitzpatrick (Set.normalCone C) x 0 < (⊤ : EReal)
    have hzero : (0 : E) ∈ Set.normalCone C x :=
      (Set.mem_normalCone_iff_forall).2 ⟨hx, fun y hy => by simp⟩
    rw [fitzpatrick_graph_eq_inner hN.1 hzero]
    exact EReal.coe_lt_top _

private theorem cone_eq_closedSpan_of_zero_mem_sri_aux
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} (h0 : (0 : E) ∈ Set.strongRelativeInterior S) :
    Set.cone S = ((Submodule.span ℝ S).topologicalClosure : Set E) := by
  rcases Set.mem_strongRelativeInterior_iff.mp h0 with ⟨hzero, hcone⟩
  simpa [Set.sub_singleton_zero_eq_self (C := S), hzero] using hcone

/-! ## The pairing-contact bridge used in the final maximality step

The contact operator is kept local to this file.  Its proof below follows the textbook
quadratic-kernel argument, with the product-space norm supplied by the local `l2` instances.
-/

namespace ERealFunction

noncomputable def pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) : EReal := ((inner ℝ p.1 p.2 : ℝ) : EReal)

@[simp] theorem pairing_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x u : E) : pairing (x, u) = ((inner ℝ x u : ℝ) : EReal) := rfl

end ERealFunction

noncomputable def pairingEqualityOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : E × E → EReal) : SetValuedOperator E E :=
  fun x ↦ {u | F (x, u) = ERealFunction.pairing (x, u)}

@[simp] theorem mem_pairingEqualityOperator_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : E × E → EReal) (x u : E) :
    u ∈ pairingEqualityOperator F x ↔ F (x, u) = ERealFunction.pairing (x, u) := Iff.rfl

noncomputable def bivariateQuadraticKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : E) (p : E × E) : ℝ :=
  -inner ℝ p.1 p.2 + ‖p.1 + p.2 - (z + w)‖ ^ 2 / 2

private theorem bivariateQuadraticKernel_add_pairing_eq_half_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w x u : E) :
    bivariateQuadraticKernel z w (x, u) + inner ℝ x u =
      (1 / 2 : ℝ) * ‖(x - z) + (u - w)‖ ^ 2 := by
  dsimp [bivariateQuadraticKernel]
  rw [show x + u - (z + w) = (x - z) + (u - w) by abel]
  ring

private theorem bivariateQuadraticKernel_add_pairing_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w x u : E) :
    0 ≤ bivariateQuadraticKernel z w (x, u) + inner ℝ x u := by
  rw [bivariateQuadraticKernel_add_pairing_eq_half_norm_sq]
  positivity

private theorem bivariateQuadraticKernel_zero_pairing_and_cross_nonneg_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w y v : E)
    (hzero : bivariateQuadraticKernel z w (y, v) + inner ℝ y v = 0)
    (hcross : 0 ≤ inner ℝ (z - y) (w - v)) :
    (y, v) = (z, w) := by
  have hnorm : ‖(y - z) + (v - w)‖ ^ 2 = 0 := by
    rw [bivariateQuadraticKernel_add_pairing_eq_half_norm_sq] at hzero
    nlinarith
  have hsum : (y - z) + (v - w) = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hvw : v - w = -(y - z) := by
    apply eq_neg_of_add_eq_zero_right
    simpa [add_comm] using hsum
  have hcross_eq : inner ℝ (z - y) (w - v) = -‖y - z‖ ^ 2 := by
    calc
      inner ℝ (z - y) (w - v) = inner ℝ (-(y - z)) (y - z) := by
        rw [show z - y = -(y - z) by abel, show w - v = - (v - w) by abel, hvw]
        simp
      _ = -inner ℝ (y - z) (y - z) := by rw [inner_neg_left]
      _ = -‖y - z‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  have hcross' : 0 ≤ -‖y - z‖ ^ 2 := by
    rw [← hcross_eq]
    exact hcross
  have hyz : y = z := by
    have : ‖y - z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖y - z‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp this))
  have hvw : v = w := by
    rw [hyz] at hsum
    have : v - w = 0 := by simpa using hsum
    exact sub_eq_zero.mp this
  exact Prod.ext hyz hvw

private theorem bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w x u : E) :
    bivariateQuadraticKernel z w (x, u) =
      (1 / 2 : ℝ) * ‖x‖ ^ 2 + (1 / 2 : ℝ) * ‖u‖ ^ 2
        - inner ℝ x (z + w) - inner ℝ u (z + w) +
          (1 / 2 : ℝ) * ‖z + w‖ ^ 2 := by
  have hsum :
      ‖x + u - (z + w)‖ ^ 2 =
        ‖x + u‖ ^ 2 - 2 * inner ℝ (x + u) (z + w) + ‖z + w‖ ^ 2 := by
    simpa [sub_eq_add_neg, two_mul, real_inner_comm, add_assoc, add_left_comm, add_comm]
      using norm_sub_sq_real (x + u) (z + w)
  have hadd :
      ‖x + u‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x u + ‖u‖ ^ 2 := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using norm_add_sq_real x u
  dsimp [bivariateQuadraticKernel]
  rw [hsum, hadd, inner_add_left]
  ring

private theorem convex_epigraph_infimalPostcomposition_local
    {Q R : Type*} [NormedAddCommGroup Q] [NormedAddCommGroup R]
    [Module ℝ Q] [Module ℝ R]
    (f : Q → Set.Ioi (⊥ : EReal)) (L : Q →ᵃ[ℝ] R)
    (hf : Convex ℝ (ERealFunction.epigraph f.asEReal)) :
    Convex ℝ (ERealFunction.epigraph (ERealFunction.infimalPostcomposition L f)) := by
  have hfJ := (ERealFunction.convex_epigraph_iff_jensen_on_dom f.asEReal).1 hf
  refine (ERealFunction.convex_epigraph_iff_jensen_on_dom
    (ERealFunction.infimalPostcomposition L f)).2 ?_
  intro y₁ y₂ hy₁ hy₂ a ha0 ha1
  have ha_pos : 0 < a := ha0
  have hb_pos : 0 < 1 - a := sub_pos.mpr ha1
  have haE : (0 : EReal) < (a : EReal) := by exact_mod_cast ha_pos
  have hbE : (0 : EReal) < ((1 - a : ℝ) : EReal) := by exact_mod_cast hb_pos
  have hterm₁ : (a : EReal) *
      ERealFunction.infimalPostcomposition L f y₁ ≠ (⊤ : EReal) := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (by exact_mod_cast ha0.le),
      Or.inl (EReal.coe_ne_top _), Or.inr (ERealFunction.mem_dom_iff_ne_top.mp hy₁)⟩
  have hterm₂ : ((1 - a : ℝ) : EReal) *
      ERealFunction.infimalPostcomposition L f y₂ ≠ (⊤ : EReal) := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (by exact_mod_cast (sub_nonneg.mpr ha1.le)),
      Or.inl (EReal.coe_ne_top _), Or.inr (ERealFunction.mem_dom_iff_ne_top.mp hy₂)⟩
  refine EReal.le_add_of_forall_gt (Or.inr hterm₂) (Or.inl hterm₁) ?_
  intro a' ha' b' hb'
  have hξ₁ : ERealFunction.infimalPostcomposition L f y₁ < a' / (a : EReal) :=
    (EReal.lt_div_iff haE (EReal.coe_ne_top _)).2 (by simpa [mul_comm] using ha')
  have hξ₂ : ERealFunction.infimalPostcomposition L f y₂ < b' / ((1 - a : ℝ) : EReal) :=
    (EReal.lt_div_iff hbE (EReal.coe_ne_top _)).2 (by simpa [mul_comm] using hb')
  obtain ⟨ξ₁, hξ₁l, hξ₁u⟩ := EReal.exists_between_coe_real hξ₁
  obtain ⟨ξ₂, hξ₂l, hξ₂u⟩ := EReal.exists_between_coe_real hξ₂
  have hfiber (y : R) (ξ : EReal)
      (hξ : ERealFunction.infimalPostcomposition L f y < ξ) :
      ∃ x : Q, L x = y ∧ (f x : EReal) < ξ := by
    change sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' {y})) < ξ at hξ
    obtain ⟨s, hs, hslt⟩ := (sInf_lt_iff).1 hξ
    rcases hs with ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hx, hslt⟩
  obtain ⟨x₁, hx₁L, hx₁⟩ := hfiber y₁ ξ₁ hξ₁l
  obtain ⟨x₂, hx₂L, hx₂⟩ := hfiber y₂ ξ₂ hξ₂l
  have hx₁dom : x₁ ∈ ERealFunction.dom f.asEReal := by
    rw [ERealFunction.mem_dom_iff]
    exact lt_trans hx₁ (EReal.coe_lt_top _)
  have hx₂dom : x₂ ∈ ERealFunction.dom f.asEReal := by
    rw [ERealFunction.mem_dom_iff]
    exact lt_trans hx₂ (EReal.coe_lt_top _)
  have hmap : L (a • x₁ + (1 - a) • x₂) = a • y₁ + (1 - a) • y₂ := by
    calc
      L (a • x₁ + (1 - a) • x₂) = a • L x₁ + (1 - a) • L x₂ := by
        simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
          L.apply_lineMap x₂ x₁ a
      _ = a • y₁ + (1 - a) • y₂ := by rw [hx₁L, hx₂L]
  have heval : ERealFunction.infimalPostcomposition L f
      (a • y₁ + (1 - a) • y₂) ≤ (f (a • x₁ + (1 - a) • x₂) : EReal) := by
    change sInf ((fun x ↦ (f x : EReal)) ''
      (L ⁻¹' {a • y₁ + (1 - a) • y₂})) ≤ _
    exact sInf_le ⟨a • x₁ + (1 - a) • x₂, by simpa [hmap], rfl⟩
  have hconv := hfJ hx₁dom hx₂dom ha0 ha1
  have hweight₁ : (a : EReal) * (f x₁ : EReal) < (a : EReal) * (ξ₁ : EReal) := by
    have htop : (f x₁ : EReal) ≠ ⊤ := ne_of_lt (lt_trans hx₁ (EReal.coe_lt_top _))
    have hbot : (f x₁ : EReal) ≠ ⊥ := ne_of_gt (f x₁).property
    rw [← EReal.coe_toReal htop hbot]
    have hreal : (f x₁ : EReal).toReal < ξ₁ := by
      apply EReal.coe_lt_coe_iff.mp
      simpa [EReal.coe_toReal htop hbot] using hx₁
    have hmul := mul_lt_mul_of_pos_left hreal ha_pos
    simpa [EReal.coe_mul] using (show ((a * (f x₁ : EReal).toReal : ℝ) : EReal) <
      ((a * ξ₁ : ℝ) : EReal) by exact_mod_cast hmul)
  have hweight₂ : ((1 - a : ℝ) : EReal) * (f x₂ : EReal) <
      ((1 - a : ℝ) : EReal) * (ξ₂ : EReal) := by
    have htop : (f x₂ : EReal) ≠ ⊤ := ne_of_lt (lt_trans hx₂ (EReal.coe_lt_top _))
    have hbot : (f x₂ : EReal) ≠ ⊥ := ne_of_gt (f x₂).property
    rw [← EReal.coe_toReal htop hbot]
    have hreal : (f x₂ : EReal).toReal < ξ₂ := by
      apply EReal.coe_lt_coe_iff.mp
      simpa [EReal.coe_toReal htop hbot] using hx₂
    have hmul := mul_lt_mul_of_pos_left hreal hb_pos
    simpa [EReal.coe_mul] using (show (((1 - a) * (f x₂ : EReal).toReal : ℝ) : EReal) <
      (((1 - a) * ξ₂ : ℝ) : EReal) by exact_mod_cast hmul)
  have hbud₁ : (a : EReal) * (ξ₁ : EReal) < a' :=
    by simpa [mul_comm] using (EReal.lt_div_iff haE (EReal.coe_ne_top _)).1 hξ₁u
  have hbud₂ : ((1 - a : ℝ) : EReal) * (ξ₂ : EReal) < b' :=
    by simpa [mul_comm] using (EReal.lt_div_iff hbE (EReal.coe_ne_top _)).1 hξ₂u
  exact (lt_of_le_of_lt (le_trans heval hconv)
    (lt_trans (EReal.add_lt_add hweight₁ hweight₂)
      (EReal.add_lt_add hbud₁ hbud₂))).le

private theorem bivariateQuadraticKernel_continuous_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : E) : Continuous (bivariateQuadraticKernel z w) := by
  have hrepr : bivariateQuadraticKernel z w = fun p : E × E ↦
      (1 / 2 : ℝ) * ‖p.1‖ ^ 2 + (1 / 2 : ℝ) * ‖p.2‖ ^ 2
        - inner ℝ p.1 (z + w) - inner ℝ p.2 (z + w) +
          (1 / 2 : ℝ) * ‖z + w‖ ^ 2 := by
    funext p
    exact bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm z w p.1 p.2
  rw [hrepr]
  have h1 : Continuous (fun p : E × E ↦ (1 / 2 : ℝ) * ‖p.1‖ ^ 2) :=
    continuous_const.mul (continuous_fst.norm.pow 2)
  have h2 : Continuous (fun p : E × E ↦ (1 / 2 : ℝ) * ‖p.2‖ ^ 2) :=
    continuous_const.mul (continuous_snd.norm.pow 2)
  have h3 : Continuous (fun p : E × E ↦ inner ℝ p.1 (z + w)) :=
    continuous_fst.inner continuous_const
  have h4 : Continuous (fun p : E × E ↦ inner ℝ p.2 (z + w)) :=
    continuous_snd.inner continuous_const
  exact (((h1.add h2).sub h3).sub h4).add continuous_const

private theorem bivariateQuadraticKernel_convexOn_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : E) :
    ConvexOn ℝ (Set.univ : Set (E × E)) (bivariateQuadraticKernel z w) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, u⟩
  rcases q with ⟨y, v⟩
  have hx := norm_sq_combo_le x y a b ha hb hab
  have hu := norm_sq_combo_le u v a b ha hb hab
  rw [bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm,
    bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm]
  change _ ≤ a * _ + b * _
  rw [bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  rw [inner_add_left, inner_add_left, inner_smul_left, inner_smul_left,
    inner_smul_left, inner_smul_left]
  simp [starRingEnd_apply]
  nlinarith

private theorem bivariateQuadraticKernel_mem_gammaZero_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (z w : E) :
    (bivariateQuadraticKernel z w).toEReal ∈
      ERealFunction.gammaZero (E × E) := by
  rw [ERealFunction.mem_gammaZero_iff]
  constructor
  · simpa [Function.toEReal_apply] using (continuous_coe_real_ereal.comp
      (bivariateQuadraticKernel_continuous_local z w)).lowerSemicontinuous
  · refine ⟨?_, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · simp [Function.effectiveDomain_toEReal]
    · intro p hp q hq a ha hb
      simp [Function.effectiveDomain_toEReal] at hp hq
      have hconv := bivariateQuadraticKernel_convexOn_local z w
      have hreal : bivariateQuadraticKernel z w
          (a • p + (1 - a) • q) ≤
          a * bivariateQuadraticKernel z w p +
            (1 - a) * bivariateQuadraticKernel z w q := by
        exact hconv.2 hp hq (by exact_mod_cast ha.le)
          (by exact_mod_cast (sub_nonneg.mpr hb.le)) (by ring)
      simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using
        (show (((bivariateQuadraticKernel z w
          (a • p + (1 - a) • q) : ℝ) : EReal)) ≤
          (((a * bivariateQuadraticKernel z w p +
            (1 - a) * bivariateQuadraticKernel z w q : ℝ) : EReal)) by
      exact_mod_cast hreal)

private theorem iSup_iSup_add_eq_add_iSup_local
    {ι κ : Sort*} (a : ι → EReal) (b : κ → EReal) :
    (⨆ i, ⨆ j, a i + b j) = (⨆ i, a i) + (⨆ j, b j) := by
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    refine iSup_le fun j ↦ ?_
    exact add_le_add (le_iSup a i) (le_iSup b j)
  · refine EReal.add_le_of_forall_lt ?_
    intro a' ha b' hb
    rcases lt_iSup_iff.mp ha with ⟨i, hi⟩
    rcases lt_iSup_iff.mp hb with ⟨j, hj⟩
    exact (EReal.add_lt_add hi hj).le.trans <| le_iSup_of_le i <| le_iSup_of_le j le_rfl

private theorem iSup_add_real_const_local {ι : Sort*} (a : ι → EReal) (c : ℝ) :
    (⨆ i, a i + (c : EReal)) = (⨆ i, a i) + (c : EReal) := by
  calc
    (⨆ i, a i + (c : EReal)) = ⨆ i, ⨆ _ : Unit, a i + (c : EReal) := by
      refine iSup_congr fun i ↦ ?_
      simp
    _ = (⨆ i, a i) + (⨆ _ : Unit, (c : EReal)) :=
      iSup_iSup_add_eq_add_iSup_local a (fun _ : Unit ↦ (c : EReal))
    _ = (⨆ i, a i) + (c : EReal) := by simp

private theorem prodL2_norm_sq_eq_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) : ‖p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  have hnorm : ‖p‖ = ‖WithLp.toLp 2 p‖ := by
    simpa [ERealFunction.prod_normedAddCommGroup_l2, ERealFunction.prod_seminormedAddCommGroup_l2]
      using (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := E) (β := E) p)
  have hnorm_sq : ‖p‖ ^ 2 = ‖WithLp.toLp 2 p‖ ^ 2 := by
    simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
  exact hnorm_sq.trans <| by simpa [sq] using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 p))

private theorem bivariateQuadraticKernel_conjugate_apply_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (z w x u : E) :
    ERealFunction.conjugate (fun p : E × E =>
      (((bivariateQuadraticKernel z w p : ℝ) : EReal))) (u, x) =
      (((bivariateQuadraticKernel z w (-x, -u) : ℝ) : EReal)) := by
  rw [ERealFunction.conjugate_apply]
  have hterm (p : E × E) :
      (((inner ℝ p (u, x) : ℝ) : EReal) -
        (((bivariateQuadraticKernel z w p : ℝ) : EReal))) =
      (((inner ℝ p (u + (z+w), x + (z+w)) : ℝ) : EReal) -
        (((1 / 2 : ℝ) * ‖p‖ ^ 2 : ℝ) : EReal)) -
        (((1/2:ℝ)*‖z+w‖^2 : ℝ) : EReal) := by
    rw [bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm]
    have hreal : inner ℝ p (u,x) -
        (1 / 2 * ‖p‖ ^ 2 - inner ℝ p.1 (z+w) - inner ℝ p.2 (z+w) +
          (1/2:ℝ)*‖z+w‖^2) =
        (inner ℝ p (u + (z+w), x + (z+w)) - 1 / 2 * ‖p‖ ^ 2) -
          (1/2:ℝ)*‖z+w‖^2 := by
      simp [ERealFunction.prod_inner_l2_apply, inner_add_right]
      ring
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]
    rw [prodL2_norm_sq_eq_local]
    rw [prodL2_norm_sq_eq_local] at hreal
    have hreal' : inner ℝ p (u,x) -
        ((1 / 2 : ℝ) * ‖p.1‖ ^ 2 + (1 / 2 : ℝ) * ‖p.2‖ ^ 2 -
          inner ℝ p.1 (z+w) - inner ℝ p.2 (z+w) +
          (1/2:ℝ)*‖z+w‖^2) =
        (inner ℝ p (u + (z+w), x + (z+w)) -
          (1 / 2 : ℝ) * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)) -
          (1/2:ℝ)*‖z+w‖^2 := by
      calc
        _ = inner ℝ p (u,x) -
            (1 / 2 * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) -
              inner ℝ p.1 (z+w) - inner ℝ p.2 (z+w) +
              (1/2:ℝ)*‖z+w‖^2) := by ring
        _ = _ := hreal
    exact_mod_cast hreal'
  simp_rw [hterm]
  let A : (E × E) → EReal := fun p ↦
    (((inner ℝ p (u + (z+w), x+(z+w)) : ℝ) : EReal) -
      (((1 / 2 : ℝ) * ‖p‖ ^ 2 : ℝ) : EReal))
  change (⨆ p, A p - (((1/2:ℝ)*‖z+w‖^2 : ℝ) : EReal)) = _
  have hconst (c : ℝ) : (⨆ p : E × E, A p - (c : EReal)) =
      (⨆ p : E × E, A p) - (c : EReal) := by
    simpa [sub_eq_add_neg] using iSup_add_real_const_local A (-c)
  rw [hconst]
  have hbase : ERealFunction.conjugate
      (fun p : E × E ↦ (((1 / 2 : ℝ) * ‖p‖ ^ 2 : ℝ) : EReal))
      (u + (z+w), x+(z+w)) = (⨆ p : E × E, A p) := by
    rfl
  rw [← hbase]
  have hbase' := congrFun (ERealFunction.conjugate_halfSquaredNorm (H := E × E))
    (u + (z+w), x+(z+w))
  have hbase'' : ERealFunction.conjugate
      (fun p : E × E ↦ (((1 / 2 : ℝ) * ‖p‖ ^ 2 : ℝ) : EReal))
      (u + (z+w), x+(z+w)) =
      (((1 / 2 : ℝ) * ‖(u+(z+w), x+(z+w))‖ ^ 2 : ℝ) : EReal) := by
    simpa [Function.asEReal_apply, ERealFunction.halfSquaredNorm_apply] using hbase'
  rw [hbase'', prodL2_norm_sq_eq_local]
  rw [bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm]
  simp only [Prod.fst, Prod.snd, inner_neg_left, inner_neg_right, norm_neg, neg_neg,
    sub_neg_eq_add]
  change (((1 / 2 : ℝ) * (‖u + (z+w)‖^2 + ‖x + (z+w)‖^2) : ℝ) : EReal) -
      (((1/2:ℝ)*‖z+w‖^2 : ℝ) : EReal) =
    (((1/2:ℝ) * ‖x‖^2 + (1/2:ℝ) * ‖u‖^2 + inner ℝ x (z+w) + inner ℝ u (z+w) +
      (1/2:ℝ)*‖z+w‖^2 : ℝ) : EReal)
  have hU : (1 / 2 : ℝ) * (‖u + (z+w)‖^2 + ‖x + (z+w)‖^2) =
      (1 / 2 : ℝ) * (‖u‖^2 + 2*inner ℝ u (z+w) + ‖z+w‖^2 +
        (‖x‖^2 + 2*inner ℝ x (z+w) + ‖z+w‖^2)) := by
    rw [norm_add_sq_real u (z+w), norm_add_sq_real x (z+w)]
  rw [hU]
  rw [← EReal.coe_sub]
  have hreal :
      (1 / 2 : ℝ) * (‖u‖^2 + 2*inner ℝ u (z+w) + ‖z+w‖^2 +
        (‖x‖^2 + 2*inner ℝ x (z+w) + ‖z+w‖^2)) -
        (1/2:ℝ)*‖z+w‖^2 =
      (1/2:ℝ) * ‖x‖^2 + (1/2:ℝ) * ‖u‖^2 + inner ℝ x (z+w) +
        inner ℝ u (z+w) + (1/2:ℝ)*‖z+w‖^2 := by
    ring
  exact_mod_cast hreal

private theorem bivariateQuadraticKernel_effectiveDomain_univ_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : E) :
    ERealFunction.effectiveDomain (bivariateQuadraticKernel z w).toEReal =
      (Set.univ : Set (E × E)) := by
  simp [Function.effectiveDomain_toEReal]

private theorem zero_mem_sri_sub_effectiveDomain_of_dom_univ_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : E × E → Set.Ioi (⊥ : EReal)} (hf : f ∈ ERealFunction.gammaZero (E × E))
    (hdom : ERealFunction.effectiveDomain g = (Set.univ : Set (E × E))) :
    ((0 : E), (0 : E)) ∈ sri (ERealFunction.effectiveDomain f - ERealFunction.effectiveDomain g) := by
  rw [hdom]
  obtain ⟨p, hp⟩ : (ERealFunction.effectiveDomain f).Nonempty := hf.2.nonempty
  have hsub :
      ERealFunction.effectiveDomain f - (Set.univ : Set (E × E)) = (Set.univ : Set (E × E)) := by
    ext q
    constructor
    · intro hq
      simp
    · intro hq
      exact Set.mem_sub.mpr ⟨p, hp, p - q, by simp, by abel⟩
  rw [hsub, Set.mem_strongRelativeInterior_iff]
  refine ⟨by simp, ?_⟩
  ext q
  constructor
  · intro hq
    have hspan :
        Submodule.span ℝ (Set.range (fun x : E × E ↦ x - ((0 : E), (0 : E)))) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro q
      refine Submodule.subset_span ?_
      exact ⟨q, by simp⟩
    simp [hspan]
  · intro hq
    rw [Set.cone_def]
    exact ConvexCone.subset_hull (by simp)

private theorem bivariateQuadraticKernel_conjugate_eq_comp_negSwap_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (z w : E) (L : E × E →L[ℝ] E × E)
    (hL : ∀ p : E × E, L p = (-p.2, -p.1)) :
    ERealFunction.conjugate (fun p : E × E ↦
      (((bivariateQuadraticKernel z w p : ℝ) : EReal))) =
      (fun p : E × E ↦ (((bivariateQuadraticKernel z w p : ℝ) : EReal))) ∘ L := by
  ext p
  rcases p with ⟨u, x⟩
  rw [Function.comp_apply, hL]
  exact bivariateQuadraticKernel_conjugate_apply_local z w x u

private theorem properIoi_biconjugate_conjugate_apply_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E × E → EReal} (hbiconj_proper : ERealFunction.IsProper (ERealFunction.conjugate (ERealFunction.conjugate F)))
    (p : E × E) :
    ERealFunction.conjugate
      ((ERealFunction.properIoi (ERealFunction.conjugate (ERealFunction.conjugate F))
        hbiconj_proper).asEReal) p =
      ERealFunction.conjugate F p := by
  change ERealFunction.conjugate (ERealFunction.conjugate (ERealFunction.conjugate F)) p =
    ERealFunction.conjugate F p
  simpa using congrFun (ERealFunction.triple_conjugate_eq_conjugate (f := F)) p

private theorem conjugateSwap_contact_midpoint_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E × E → EReal}
    (hdual : ∀ x u : E,
      ERealFunction.pairing (x, u) ≤ ERealFunction.conjugate F (u, x))
    {x u y v : E}
    (hx : ERealFunction.conjugate F (u, x) = ERealFunction.pairing (x, u))
    (hy : ERealFunction.conjugate F (v, y) = ERealFunction.pairing (y, v)) :
    0 ≤ inner ℝ (x - y) (u - v) := by
  let a : ℝ := 1 / 2
  have ha0 : 0 ≤ a := by norm_num [a]
  have ha1 : a ≤ 1 := by norm_num [a]
  have hconv : ERealFunction.IsConvex (ERealFunction.conjugate F) :=
    (ERealFunction.mem_gamma_iff (ERealFunction.conjugate F)).mp
      (ERealFunction.conjugate_mem_gamma (f := F)) |>.1
  have hmid_conv := hconv (x := (u, x)) (y := (v, y)) (a := a) ha0 ha1
  have hmid_lower :
      ERealFunction.pairing (a • x + (1 - a) • y, a • u + (1 - a) • v) ≤
        ERealFunction.conjugate F (a • u + (1 - a) • v, a • x + (1 - a) • y) := by
    simpa [a] using hdual (a • x + (1 - a) • y) (a • u + (1 - a) • v)
  have hineq :
      ERealFunction.pairing (a • x + (1 - a) • y, a • u + (1 - a) • v) ≤
        (a : EReal) * ERealFunction.pairing (x, u) +
          (1 - a : EReal) * ERealFunction.pairing (y, v) := by
    calc
      _ ≤ ERealFunction.conjugate F (a • u + (1 - a) • v, a • x + (1 - a) • y) := hmid_lower
      _ ≤ (a : EReal) * ERealFunction.conjugate F (u, x) +
          (1 - a : EReal) * ERealFunction.conjugate F (v, y) := hmid_conv
      _ = _ := by rw [hx, hy]
  have hineq' :
      (((inner ℝ (a • x + (1 - a) • y) (a • u + (1 - a) • v) : ℝ) : EReal)) ≤
        (((a * inner ℝ x u + (1 - a) * inner ℝ y v : ℝ) : EReal)) := by
    simpa [ERealFunction.pairing_apply, a, EReal.coe_add, EReal.coe_mul] using hineq
  have hreal :
      inner ℝ (a • x + (1 - a) • y) (a • u + (1 - a) • v) ≤
        a * inner ℝ x u + (1 - a) * inner ℝ y v :=
    EReal.coe_le_coe_iff.mp hineq'
  have hcross :
      inner ℝ x v + inner ℝ y u ≤ inner ℝ x u + inner ℝ y v := by
    have hreal_half := hreal
    simp [a, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] at hreal_half
    nlinarith
  calc
    0 ≤ inner ℝ x u - inner ℝ x v - inner ℝ y u + inner ℝ y v := by linarith
    _ = inner ℝ (x - y) (u - v) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      ring

private theorem biconjugate_eq_liminfAt_of_isConvex_of_dom_conjugate_nonempty_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E × E → EReal} (hF_conv : ERealFunction.IsConvex F)
    (hFstar_proper : ERealFunction.IsProper (ERealFunction.conjugate F))
    (p : E × E) :
    ERealFunction.conjugate (ERealFunction.conjugate F) p =
      ERealFunction.liminfAt F p := by
  let hconv_epi : Convex ℝ (ERealFunction.epigraph F) := by
    exact (ERealFunction.convex_epigraph_iff_jensen_on_dom F).2 (by
      intro x y hx hy a ha ha1
      exact hF_conv ha.le ha1.le)
  let g : (E × E) → EReal := ERealFunction.lowerSemicontinuousConvexEnvelope F
  have henv_lsc : LowerSemicontinuous g := by
    simpa [g] using ERealFunction.lowerSemicontinuous_lowerSemicontinuousConvexEnvelope F
  have henv_epi_conv : Convex ℝ (ERealFunction.epigraph g) := by
    simpa [g] using ERealFunction.convex_epigraph_lowerSemicontinuousConvexEnvelope F
  have henv_le : g ≤ F := by
    simpa [g] using ERealFunction.lowerSemicontinuousConvexEnvelope_le F
  let u₀ : E × E := Classical.choose hFstar_proper.2
  have hu₀ : ERealFunction.conjugate F u₀ < (⊤ : EReal) :=
    Classical.choose_spec hFstar_proper.2
  have hu₀_bot : ERealFunction.conjugate F u₀ ≠ (⊥ : EReal) := hFstar_proper.1 u₀
  have hdomF : (ERealFunction.dom F).Nonempty := by
    by_contra hne
    have htop : F = (fun _ => (⊤ : EReal)) := by
      funext x
      exact top_unique (not_lt.mp (fun hx => hne ⟨x, hx⟩))
    have hconj_bot : ERealFunction.conjugate F u₀ = (⊥ : EReal) := by
      rw [htop, ERealFunction.conjugate_apply]
      simp
    exact hu₀_bot hconj_bot
  have hminor₀ : ∀ x : E × E,
      (((inner ℝ x u₀ : ℝ) - (ERealFunction.conjugate F u₀).toReal : ℝ) : EReal) ≤ F x := by
    intro x
    apply (ERealFunction.affine_defect_le_real_iff F x u₀
      (ERealFunction.conjugate F u₀).toReal).1
    have hsup : ((inner ℝ x u₀ : ℝ) : EReal) - F x ≤ ERealFunction.conjugate F u₀ := by
      rw [ERealFunction.conjugate_apply]
      exact le_iSup (fun q : E × E ↦ ((inner ℝ q u₀ : ℝ) : EReal) - F q) x
    rw [← EReal.coe_toReal (ne_of_lt hu₀) hu₀_bot] at hsup
    simpa [EReal.coe_sub] using hsup
  have affine_le_env : ∀ (u : E × E) (η : ℝ),
      (∀ x : E × E, (((inner ℝ x u : ℝ) + η : ℝ) : EReal) ≤ F x) →
      (fun x : E × E ↦ (((inner ℝ x u : ℝ) + η : ℝ) : EReal)) ≤ g := by
    intro u η hminor
    have hconv : ERealFunction.IsConvex
        (fun x : E × E ↦ (((inner ℝ x u : ℝ) + η : ℝ) : EReal)) := by
      intro x y a ha0 ha1
      change (((inner ℝ (a • x + (1 - a) • y) (u) : ℝ) + η : ℝ) : EReal) ≤ _
      have hreal : inner ℝ (a • x + (1 - a) • y) u + η =
          a * (inner ℝ x u + η) + (1 - a) * (inner ℝ y u + η) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      rw [hreal]
      exact le_of_eq (by
        norm_num [EReal.coe_add, EReal.coe_mul, EReal.coe_sub]
        )
    have hlsc : LowerSemicontinuous
        (fun x : E × E ↦ (((inner ℝ x u : ℝ) + η : ℝ) : EReal)) := by
      have hreal : Continuous (fun x : E × E ↦ inner ℝ x u + η) := by
        simpa [ERealFunction.prod_inner_l2_apply] using
          ((continuous_fst.inner (continuous_const : Continuous (fun _ : E × E ↦ u.1))).add
            (continuous_snd.inner (continuous_const : Continuous (fun _ : E × E ↦ u.2)))).add
              (continuous_const : Continuous (fun _ : E × E ↦ η))
      exact (continuous_coe_real_ereal.comp hreal).lowerSemicontinuous
    have hepi : Convex ℝ (ERealFunction.epigraph
        (fun x : E × E ↦ (((inner ℝ x u : ℝ) + η : ℝ) : EReal))) := by
      exact (ERealFunction.convex_epigraph_iff_jensen_on_dom _).2 (by
        intro x y hx hy a ha ha1
        exact hconv ha.le ha1.le)
    exact ERealFunction.le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
      hlsc hepi hminor
  have hminor_env : (fun x : E × E ↦
      (((inner ℝ x u₀ : ℝ) - (ERealFunction.conjugate F u₀).toReal : ℝ) : EReal)) ≤ g := by
    simpa [sub_eq_add_neg] using affine_le_env u₀ (-(ERealFunction.conjugate F u₀).toReal) hminor₀
  have hg_proper : ERealFunction.IsProper g := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have hle := hminor_env x
      rw [hx] at hle
      exact (not_le_of_gt (EReal.bot_lt_coe _)) hle
    · rcases hdomF with ⟨x, hx⟩
      exact ⟨x, lt_of_le_of_lt (henv_le x) ((ERealFunction.mem_dom_iff F x).mp hx)⟩
  have hg_gamma : g ∈ ERealFunction.gamma (E × E) := by
    rw [ERealFunction.mem_gamma_iff]
    exact ⟨ERealFunction.isConvex_of_convex_epigraph hg_proper henv_epi_conv, henv_lsc⟩
  have hg_pkg : ERealFunction.properIoi g hg_proper ∈ ERealFunction.gammaZero (E × E) :=
    ERealFunction.properIoi_mem_gammaZero_of_mem_gamma hg_proper hg_gamma
  have hg_biconj : ERealFunction.conjugate (ERealFunction.conjugate g) = g := by
    simpa [Function.asEReal] using ERealFunction.biconjugate_eq_of_mem_gammaZero hg_pkg
  have hconj_eq : ERealFunction.conjugate g = ERealFunction.conjugate F := by
    apply funext
    intro u
    apply le_antisymm
    · by_cases htop : ERealFunction.conjugate F u = ⊤
      · rw [htop]
        exact le_top
      · rw [ERealFunction.conjugate_apply]
        refine iSup_le fun x ↦ ?_
        have hnebot : ERealFunction.conjugate F u ≠ ⊥ := hFstar_proper.1 u
        have hminor_real_all : ∀ y : E × E, (((inner ℝ y u : ℝ) -
            (ERealFunction.conjugate F u).toReal : ℝ) : EReal) ≤ F y := by
          intro y
          have hsup : ((inner ℝ y u : ℝ) : EReal) - F y ≤ ERealFunction.conjugate F u := by
            rw [ERealFunction.conjugate_apply]
            exact le_iSup (fun q : E × E ↦ ((inner ℝ q u : ℝ) : EReal) - F q) y
          rw [← EReal.coe_toReal htop hnebot] at hsup
          exact (ERealFunction.affine_defect_le_real_iff F y u
            (ERealFunction.conjugate F u).toReal).1 (by simpa [EReal.coe_sub] using hsup)
        have hminor_real : (((inner ℝ x u : ℝ) -
            (ERealFunction.conjugate F u).toReal : ℝ) : EReal) ≤ F x := hminor_real_all x
        have hminor_g : (((inner ℝ x u : ℝ) : EReal) -
            ((ERealFunction.conjugate F u).toReal : EReal)) ≤ g x := by
          have htmp := affine_le_env u (-(ERealFunction.conjugate F u).toReal) hminor_real_all
          simpa [sub_eq_add_neg] using htmp x
        have hEq : (((inner ℝ x u : ℝ) : EReal) -
            ((ERealFunction.conjugate F u).toReal : EReal)) =
            (((inner ℝ x u : ℝ) : EReal) - ERealFunction.conjugate F u) := by
          rw [EReal.coe_toReal htop hnebot]
        rw [hEq] at hminor_g
        calc
          ((inner ℝ x u : ℝ) : EReal) - g x ≤
              ((inner ℝ x u : ℝ) : EReal) -
                (((inner ℝ x u : ℝ) : EReal) - ERealFunction.conjugate F u) :=
            EReal.sub_le_sub le_rfl hminor_g
          _ = ERealFunction.conjugate F u := by
            rw [← EReal.coe_toReal htop hnebot, ← EReal.coe_sub]
            rw [← EReal.coe_sub]
            norm_num
    · change (⨆ x : E × E, ((inner ℝ x u : ℝ) : EReal) - F x) ≤
        (⨆ x : E × E, ((inner ℝ x u : ℝ) : EReal) - g x)
      refine iSup_le fun x ↦ ?_
      exact (EReal.sub_le_sub le_rfl (henv_le x)).trans
        (le_iSup (fun y : E × E ↦ ((inner ℝ y u : ℝ) : EReal) - g y) x)
  have hbiconj_eq : ERealFunction.conjugate (ERealFunction.conjugate F) = g := by
    calc
      ERealFunction.conjugate (ERealFunction.conjugate F) =
          ERealFunction.conjugate (ERealFunction.conjugate g) := by rw [hconj_eq]
      _ = g := hg_biconj
  have henv_eq : g = ERealFunction.lowerSemicontinuousEnvelope F := by
    apply le_antisymm
    · exact (ERealFunction.lowerSemicontinuousHull_isGreatest F).2
        ⟨henv_lsc, henv_le⟩
    · have hclosed : Convex ℝ (ERealFunction.epigraph (ERealFunction.lowerSemicontinuousEnvelope F)) := by
        rw [ERealFunction.epi_lowerSemicontinuousHull_eq_closure_epi]
        exact hconv_epi.closure
      exact ERealFunction.le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
        ((ERealFunction.lowerSemicontinuousHull_isGreatest F).1.1) hclosed
        ((ERealFunction.lowerSemicontinuousHull_isGreatest F).1.2)
  calc
    ERealFunction.conjugate (ERealFunction.conjugate F) p = g p := congrFun hbiconj_eq p
    _ = ERealFunction.lowerSemicontinuousEnvelope F p := congrFun henv_eq p
    _ = ERealFunction.liminfAt F p := ERealFunction.lowerSemicontinuousHull_eq_liminfAt F p

private theorem pairing_le_biconjugate_of_convex_of_properConjugate_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E × E → EReal}
    (hF_conv : ERealFunction.IsConvex F)
    (hFstar_proper : ERealFunction.IsProper (ERealFunction.conjugate F))
    (hF_ge : ∀ p : E × E,
      ERealFunction.pairing p ≤ F p) :
    ∀ p : E × E, ERealFunction.pairing p ≤ ERealFunction.conjugate (ERealFunction.conjugate F) p := by
  intro p
  have hpair_lsc : LowerSemicontinuousAt ERealFunction.pairing p := by
    exact (continuous_coe_real_ereal.comp (continuous_fst.inner continuous_snd)).continuousAt
      |>.lowerSemicontinuousAt
  have hliminf_pair : ERealFunction.pairing p ≤ ERealFunction.liminfAt ERealFunction.pairing p :=
    hpair_lsc.le_liminf
  have hliminf_mono :
      ERealFunction.liminfAt ERealFunction.pairing p ≤ ERealFunction.liminfAt F p := by
    simpa [ERealFunction.liminfAt] using
      (Filter.liminf_le_liminf (Filter.Eventually.of_forall hF_ge) :
        Filter.liminf ERealFunction.pairing (nhds p) ≤ Filter.liminf F (nhds p))
  calc
    ERealFunction.pairing p ≤ ERealFunction.liminfAt ERealFunction.pairing p := hliminf_pair
    _ ≤ ERealFunction.liminfAt F p := hliminf_mono
    _ = ERealFunction.conjugate (ERealFunction.conjugate F) p := by
      symm
      exact biconjugate_eq_liminfAt_of_isConvex_of_dom_conjugate_nonempty_local
        hF_conv hFstar_proper p

private theorem dual_witness_exists_kernel_bound_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E × E → EReal}
    (hF_conv : ERealFunction.IsConvex F)
    (hFstar_proper : ERealFunction.IsProper (ERealFunction.conjugate F))
    (hF_ge : ∀ x u : E, ERealFunction.pairing (x, u) ≤ F (x, u))
    (z w : E) :
    ∃ y v : E,
      ERealFunction.conjugate F (v, y) +
        ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) ≤ 0 := by
  have hbiconj_proper : ERealFunction.IsProper (ERealFunction.conjugate (ERealFunction.conjugate F)) :=
    ERealFunction.conjugate_is_proper_of_mem_gamma hFstar_proper
      (ERealFunction.conjugate_mem_gamma (f := F))
  let f : (E × E) → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi (ERealFunction.conjugate (ERealFunction.conjugate F)) hbiconj_proper
  let g : (E × E) → Set.Ioi (⊥ : EReal) :=
    (bivariateQuadraticKernel z w).toEReal
  have hf_gamma : f ∈ ERealFunction.gammaZero (E × E) := by
    exact ERealFunction.properIoi_mem_gammaZero_of_mem_gamma hbiconj_proper
      (ERealFunction.conjugate_mem_gamma (f := ERealFunction.conjugate F))
  have hg_gamma : g ∈ ERealFunction.gammaZero (E × E) := by
    simpa [g] using bivariateQuadraticKernel_mem_gammaZero_local z w
  have hsri : ((0 : E), (0 : E)) ∈ sri
      (ERealFunction.effectiveDomain f - ERealFunction.effectiveDomain g) := by
    exact zero_mem_sri_sub_effectiveDomain_of_dom_univ_local hf_gamma
      (by simpa [g] using bivariateQuadraticKernel_effectiveDomain_univ_local z w)
  have hcone : Set.cone (ERealFunction.effectiveDomain f - ERealFunction.effectiveDomain g) =
      ((Submodule.span ℝ (ERealFunction.effectiveDomain f - ERealFunction.effectiveDomain g)).topologicalClosure :
        Set (E × E)) :=
    cone_eq_closedSpan_of_zero_mem_sri_aux hsri
  have hbiconj_ge : ∀ p : E × E,
      ERealFunction.pairing p ≤ ERealFunction.conjugate (ERealFunction.conjugate F) p := by
    apply pairing_le_biconjugate_of_convex_of_properConjugate_local hF_conv hFstar_proper
    intro p
    rcases p with ⟨x, u⟩
    exact hF_ge x u
  have hfg_nonneg : ∀ p : E × E, (0 : EReal) ≤ ERealFunction.primalObjective f g p := by
    intro p
    rcases p with ⟨x, u⟩
    have hkernel_nonneg_real : (0 : EReal) ≤
        (((bivariateQuadraticKernel z w (x, u) + inner ℝ x u : ℝ) : EReal)) := by
      exact_mod_cast bivariateQuadraticKernel_add_pairing_nonneg z w x u
    have hkernel_nonneg : (0 : EReal) ≤
        ERealFunction.pairing (x, u) +
          ((bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) := by
      simpa [ERealFunction.pairing_apply, EReal.coe_add, add_comm] using hkernel_nonneg_real
    have hshift : ERealFunction.pairing (x, u) +
        ((bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) ≤
        ERealFunction.conjugate (ERealFunction.conjugate F) (x, u) +
          ((bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) := by
      simpa [add_comm] using add_le_add_right (hbiconj_ge (x, u))
        (((bivariateQuadraticKernel z w (x, u) : ℝ) : EReal))
    calc
      (0 : EReal) ≤ ERealFunction.pairing (x, u) +
          ((bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) := hkernel_nonneg
      _ ≤ ERealFunction.conjugate (ERealFunction.conjugate F) (x, u) +
          ((bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) := hshift
      _ = ERealFunction.primalObjective f g (x, u) := by
        simp [f, g, ERealFunction.primalObjective_apply]
  let L : (E × E) →L[ℝ] E × E :=
    (-ContinuousLinearMap.snd ℝ E E).prod (-ContinuousLinearMap.fst ℝ E E)
  have hL : ∀ p : E × E, L p = (-p.2, -p.1) := by
    intro p
    rfl
  have hg_conj : ERealFunction.conjugate g.asEReal = g.asEReal ∘ L := by
    simpa [g] using bivariateQuadraticKernel_conjugate_eq_comp_negSwap_local z w L hL
  have hzero : ERealFunction.conjugate (f + g).asEReal (0 : E × E) ≤ 0 := by
    rw [ERealFunction.conjugate_apply]
    refine iSup_le fun p ↦ ?_
    have hp := hfg_nonneg p
    change ((inner ℝ p (0 : E × E) : ℝ) : EReal) -
      ((f p : EReal) + (g p : EReal)) ≤ 0
    simpa [ERealFunction.primalObjective_apply] using hp
  obtain ⟨r, hr⟩ := ERealFunction.attouchBrezis_split_attainment f g hf_gamma hg_gamma hcone
    (0 : E × E)
  let q : E × E := -r
  have hdual : ERealFunction.conjugate f.asEReal (-q) +
      ERealFunction.conjugate g.asEReal q ≤ 0 := by
    calc
      ERealFunction.conjugate f.asEReal (-q) + ERealFunction.conjugate g.asEReal q =
          ERealFunction.conjugate (f + g).asEReal (0 : E × E) := by
            rw [hr]
            simp [q]
      _ ≤ 0 := hzero
  have hfconj : ∀ p : E × E,
      ERealFunction.conjugate f.asEReal p = ERealFunction.conjugate F p := by
    intro p
    simpa [f] using properIoi_biconjugate_conjugate_apply_local hbiconj_proper p
  have hgcomp := congrFun hg_conj q
  have hdual' : ERealFunction.conjugate F (-q) +
      ((bivariateQuadraticKernel z w (L q) : ℝ) : EReal) ≤ 0 := by
    calc
      ERealFunction.conjugate F (-q) +
          ((bivariateQuadraticKernel z w (L q) : ℝ) : EReal) =
          ERealFunction.conjugate f.asEReal (-q) + ERealFunction.conjugate g.asEReal q := by
            rw [hfconj (-q), hgcomp]
            rfl
      _ ≤ 0 := hdual
  refine ⟨-q.2, -q.1, ?_⟩
  change ERealFunction.conjugate F (-q) +
    ((bivariateQuadraticKernel z w (L q) : ℝ) : EReal) ≤ 0
  exact hdual'

private theorem ereal_eq_neg_iff_add_eq_zero_local
    {a b : EReal} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥)
    (hb_top : b ≠ ⊤) (hb_bot : b ≠ ⊥) :
    a = -b ↔ a + b = 0 := by
  constructor
  · intro hab
    have hab_real : a.toReal = -b.toReal := by
      apply_fun EReal.toReal at hab
      simpa [EReal.toReal_neg_eq] using hab
    have hsum_real : a.toReal + b.toReal = 0 := by
      linarith
    calc
      a + b = ((a.toReal : ℝ) : EReal) + ((b.toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot]
      _ = ((a.toReal + b.toReal : ℝ) : EReal) := by rw [EReal.coe_add]
      _ = 0 := congrArg (fun t : ℝ ↦ (t : EReal)) hsum_real
  · intro hsum
    have hsum_real : a.toReal + b.toReal = 0 := by
      apply EReal.coe_eq_coe_iff.mp
      calc
        ((a.toReal + b.toReal : ℝ) : EReal) =
            ((a.toReal : ℝ) : EReal) + ((b.toReal : ℝ) : EReal) := by rw [EReal.coe_add]
        _ = a + b := by rw [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot]
        _ = 0 := hsum
    have hab_real : a.toReal = -b.toReal := by linarith
    calc
      a = ((a.toReal : ℝ) : EReal) := (EReal.coe_toReal ha_top ha_bot).symm
      _ = ((-b.toReal : ℝ) : EReal) := congrArg (fun t : ℝ ↦ (t : EReal)) hab_real
      _ = -b := by rw [EReal.coe_neg, EReal.coe_toReal hb_top hb_bot]

private theorem dual_witness_contact_of_pairing_le_and_kernel_nonneg_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E × E → EReal} {z w y v : E}
    (hFstar_proper : ERealFunction.IsProper (ERealFunction.conjugate F))
    (hpair_le : ERealFunction.pairing (y, v) ≤ ERealFunction.conjugate F (v, y))
    (hkernel_nonneg : 0 ≤ bivariateQuadraticKernel z w (y, v) + inner ℝ y v)
    (hdual : ERealFunction.conjugate F (v, y) +
      ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) ≤ 0) :
    ERealFunction.conjugate F (v, y) = ERealFunction.pairing (y, v) ∧
      bivariateQuadraticKernel z w (y, v) + inner ℝ y v = 0 := by
  have hpair_kernel_nonneg : (0 : EReal) ≤ ERealFunction.pairing (y, v) +
      ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) := by
    have hreal : (0 : EReal) ≤
        (((bivariateQuadraticKernel z w (y, v) + inner ℝ y v : ℝ) : EReal)) := by
      exact_mod_cast hkernel_nonneg
    simpa [ERealFunction.pairing_apply, EReal.coe_add, add_comm] using hreal
  have hpair_kernel_le : ERealFunction.pairing (y, v) +
      ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) ≤ 0 := by
    have hshift : ERealFunction.pairing (y, v) +
        ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) ≤
        ERealFunction.conjugate F (v, y) +
          ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) := by
      simpa [add_comm] using add_le_add_right hpair_le
        (((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal))
    exact le_trans hshift hdual
  have hpair_kernel_zero : ERealFunction.pairing (y, v) +
      ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) = 0 :=
    le_antisymm hpair_kernel_le hpair_kernel_nonneg
  have hkernel_zero : bivariateQuadraticKernel z w (y, v) + inner ℝ y v = 0 := by
    apply EReal.coe_eq_coe_iff.mp
    simpa [ERealFunction.pairing_apply, EReal.coe_add, add_comm] using hpair_kernel_zero
  have hdual_nonneg : (0 : EReal) ≤ ERealFunction.conjugate F (v, y) +
      ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) := by
    have hshift : ERealFunction.pairing (y, v) +
        ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) ≤
        ERealFunction.conjugate F (v, y) +
          ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) := by
      simpa [add_comm] using add_le_add_right hpair_le
        (((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal))
    exact le_trans hpair_kernel_nonneg hshift
  have hdual_zero : ERealFunction.conjugate F (v, y) +
      ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) = 0 :=
    le_antisymm hdual hdual_nonneg
  have hFstar_ne_bot : ERealFunction.conjugate F (v, y) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hpair_le
    exact not_le_of_gt (by simpa [ERealFunction.pairing_apply] using
      (EReal.bot_lt_coe (inner ℝ y v))) hpair_le
  have hFstar_ne_top : ERealFunction.conjugate F (v, y) ≠ ⊤ := by
    intro htop
    have hsum_top : ERealFunction.conjugate F (v, y) +
        ((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) = ⊤ := by
      rw [htop]
      exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    exact EReal.zero_ne_top (hdual_zero.symm.trans hsum_top)
  have hFstar_eq_neg : ERealFunction.conjugate F (v, y) =
      -((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) :=
    (ereal_eq_neg_iff_add_eq_zero_local hFstar_ne_top hFstar_ne_bot
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).2 hdual_zero
  have hpair_eq_neg : ERealFunction.pairing (y, v) =
      -((bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) :=
    (ereal_eq_neg_iff_add_eq_zero_local
      (by simpa [ERealFunction.pairing_apply] using EReal.coe_ne_top (inner ℝ y v))
      (by simpa [ERealFunction.pairing_apply] using EReal.coe_ne_bot (inner ℝ y v))
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).2 (by
        simpa [ERealFunction.pairing_apply, EReal.coe_add, add_comm] using hpair_kernel_zero)
  constructor
  · exact hFstar_eq_neg.trans hpair_eq_neg.symm
  · exact hkernel_zero

set_option maxHeartbeats 1000000 in
private theorem pairingEqualityOperator_conjugateSwap_isMaximallyMonotone_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E × E → EReal}
    (hFstarT_ge : ∀ x u : E,
      ERealFunction.pairing (x, u) ≤ ERealFunction.conjugate F (u, x))
    (hF_conv : ERealFunction.IsConvex F)
    (hFstar_proper : ERealFunction.IsProper (ERealFunction.conjugate F))
    (hF_ge : ∀ x u : E, ERealFunction.pairing (x, u) ≤ F (x, u)) :
    Maximal IsMonotone
      (pairingEqualityOperator (fun p : E × E ↦ ERealFunction.conjugate F (p.2, p.1))) := by
  let T : SetValuedOperator E E :=
    pairingEqualityOperator (fun p : E × E ↦ ERealFunction.conjugate F (p.2, p.1))
  have hmonoT : IsMonotone T := by
    intro x y u hu v hv
    have hu' : ERealFunction.conjugate F (u, x) = ERealFunction.pairing (x, u) := hu
    have hv' : ERealFunction.conjugate F (v, y) = ERealFunction.pairing (y, v) := hv
    have hcross := conjugateSwap_contact_midpoint_nonneg hFstarT_ge hu' hv'
    simpa [real_inner_comm] using hcross
  rw [maximal_iff]
  constructor
  · exact hmonoT
  · intro B hB hTB
    apply le_antisymm hTB
    intro z w hwB
    have hdualLower := hFstarT_ge
    obtain ⟨y, v, hdual⟩ := dual_witness_exists_kernel_bound_local
      hF_conv hFstar_proper hF_ge z w
    have hpair_le : ERealFunction.pairing (y, v) ≤ ERealFunction.conjugate F (v, y) :=
      hdualLower y v
    obtain ⟨hcontact, hkernel_zero⟩ :=
      dual_witness_contact_of_pairing_le_and_kernel_nonneg_local hFstar_proper hpair_le
        (bivariateQuadraticKernel_add_pairing_nonneg z w y v) hdual
    have hvT : v ∈ T y := by
      change ERealFunction.conjugate F (v, y) = ERealFunction.pairing (y, v)
      exact hcontact
    have hvB : v ∈ B y := hTB y hvT
    have hcross : 0 ≤ inner ℝ (z - y) (w - v) := by
      simpa [real_inner_comm] using hB w hwB v hvB
    have hyv_eq : (y, v) = (z, w) :=
      bivariateQuadraticKernel_zero_pairing_and_cross_nonneg_iff z w y v hkernel_zero hcross
    cases hyv_eq
    exact hvT


/-- Theorem 25.3: let `A : H → 2^H` and `B : K → 2^K` be maximally monotone on real Hilbert
spaces, let `L : H →L[ℝ] K`, and suppose that
`cone (dom B - L '' dom A) = closure (span (dom B - L '' dom A))`; then `A + L^* B L`,
realized as `A + L.adjointImage B`, is maximally monotone.

The Chapter 25 Fitzpatrick-duality proof of this statement (Bauschke-lean-project
`Chap25/Theorem_25_3`, via Theorem 25.2 and Proposition 25.41) is carried out
directly in `Foundation` above.  `Maximal.add_of_sumRegularity` below uses this
completed result. -/
theorem Maximal.add_adjointImage_of_cone_dom_sub_eq_closure_span
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hcone :
      Set.cone (B.dom - L '' A.dom) =
        ((Submodule.span ℝ (B.dom - L '' A.dom)).topologicalClosure : Set K)) :
    Maximal IsMonotone (A + L.adjointImage B) := by
  let P : SetValuedOperator (H × K) (H × K) :=
    SetValuedOperator.product A B
  let Γ : Set (H × K) := (L.toLinearMap.graph : Set (H × K))
  let G : SetValuedOperator (H × K) (H × K) := Set.normalCone Γ
  have hAm : IsMaximalMonotone A :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).2 hA
  have hBm : IsMaximalMonotone B :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone B).2 hB
  have hPmax : Maximal IsMonotone P := by
    simpa [P] using (Maximal.product hA hB)
  have hP : IsMaximalMonotone P :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone P).2 hPmax
  have hΓne : Γ.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [Γ, LinearMap.mem_graph_iff]
  have hΓclosed : IsClosed Γ := by
    simpa [Γ, LinearMap.mem_graph_iff, eq_comm] using
      isClosed_eq continuous_snd (L.continuous.comp continuous_fst)
  have hΓconv : Convex ℝ Γ := by
    simpa [Γ] using L.toLinearMap.graph.convex
  have hGmax : Maximal IsMonotone G := by
    dsimp [G, Γ]
    exact (maximalityData_product_normalConeGraph hA hB L).2
  have hG : IsMaximalMonotone G :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone G).2 hGmax
  let C : Set H := Prod.fst '' ERealFunction.dom (fitzpatrickProd A)
  let D : Set K := Prod.fst '' ERealFunction.dom (fitzpatrickProd B)
  have hCne : C.Nonempty := by
    rcases maximalMonotone_graph_nonempty hAm with ⟨⟨x, u⟩, hu⟩
    refine ⟨x, ⟨(x, u), ?_, rfl⟩⟩
    rw [ERealFunction.mem_dom_iff]
    change fitzpatrick A x u < (⊤ : EReal)
    rw [fitzpatrick_graph_eq_inner hAm.1 hu]
    exact EReal.coe_lt_top _
  have hDne : D.Nonempty := by
    rcases maximalMonotone_graph_nonempty hBm with ⟨⟨x, u⟩, hu⟩
    refine ⟨x, ⟨(x, u), ?_, rfl⟩⟩
    rw [ERealFunction.mem_dom_iff]
    change fitzpatrick B x u < (⊤ : EReal)
    rw [fitzpatrick_graph_eq_inner hBm.1 hu]
    exact EReal.coe_lt_top _
  have hCconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨p, hp, rfl⟩
    rcases hy with ⟨q, hq, rfl⟩
    refine ⟨a • p + b • q, ?_, ?_⟩
    · rw [ERealFunction.mem_dom_iff] at hp hq ⊢
      have hpbot : fitzpatrickProd A p ≠ (⊥ : EReal) :=
        fitzpatrick_ne_bot hAm p.1 p.2
      have hqbot : fitzpatrickProd A q ≠ (⊥ : EReal) :=
        fitzpatrick_ne_bot hAm q.1 q.2
      have hpcoe : fitzpatrickProd A p = ((fitzpatrickProd A p).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt hp) hpbot).symm
      have hqcoe : fitzpatrickProd A q = ((fitzpatrickProd A q).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt hq) hqbot).symm
      have hconv := fitzpatrickProd_convex (A := A) p q a b ha hb hab
      have hright :
          (a : EReal) * fitzpatrickProd A p + (b : EReal) * fitzpatrickProd A q <
            (⊤ : EReal) := by
        rw [hpcoe, hqcoe, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
        exact EReal.coe_lt_top _
      exact lt_of_le_of_lt hconv hright
    · simp
  have hDconv : Convex ℝ D := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨p, hp, rfl⟩
    rcases hy with ⟨q, hq, rfl⟩
    refine ⟨a • p + b • q, ?_, ?_⟩
    · rw [ERealFunction.mem_dom_iff] at hp hq ⊢
      have hpbot : fitzpatrickProd B p ≠ (⊥ : EReal) :=
        fitzpatrick_ne_bot hBm p.1 p.2
      have hqbot : fitzpatrickProd B q ≠ (⊥ : EReal) :=
        fitzpatrick_ne_bot hBm q.1 q.2
      have hpcoe : fitzpatrickProd B p = ((fitzpatrickProd B p).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt hp) hpbot).symm
      have hqcoe : fitzpatrickProd B q = ((fitzpatrickProd B q).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt hq) hqbot).symm
      have hconv := fitzpatrickProd_convex (A := B) p q a b ha hb hab
      have hright :
          (a : EReal) * fitzpatrickProd B p + (b : EReal) * fitzpatrickProd B q <
            (⊤ : EReal) := by
        rw [hpcoe, hqcoe, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
        exact EReal.coe_lt_top _
      exact lt_of_le_of_lt hconv hright
    · simp
  have hAdomC : A.dom ⊆ C := by
    intro x hx
    rcases (SetValuedOperator.mem_dom_iff A x).mp hx with ⟨u, hu⟩
    refine ⟨(x, u), ?_, rfl⟩
    rw [ERealFunction.mem_dom_iff]
    change fitzpatrick A x u < (⊤ : EReal)
    rw [fitzpatrick_graph_eq_inner hAm.1 hu]
    exact EReal.coe_lt_top _
  have hBdomD : B.dom ⊆ D := by
    intro x hx
    rcases (SetValuedOperator.mem_dom_iff B x).mp hx with ⟨u, hu⟩
    refine ⟨(x, u), ?_, rfl⟩
    rw [ERealFunction.mem_dom_iff]
    change fitzpatrick B x u < (⊤ : EReal)
    rw [fitzpatrick_graph_eq_inner hBm.1 hu]
    exact EReal.coe_lt_top _
  have hCclosure : C ⊆ closure (convexHull ℝ A.dom) := by
    intro x hx
    exact (closure_mono (subset_convexHull ℝ A.dom))
      (fst_image_dom_fitzpatrick_subset_closure_dom A hA hx)
  have hDclosure : D ⊆ closure (convexHull ℝ B.dom) := by
    intro x hx
    exact (closure_mono (subset_convexHull ℝ B.dom))
      (fst_image_dom_fitzpatrick_subset_closure_dom B hB hx)
  have hsriGraph :
      (0 : H × K) ∈ Set.strongRelativeInterior
        (C ×ˢ D - Γ) := by
    simpa [Γ] using
      (Set.zero_mem_strongRelativeInterior_prod_sub_graph_of_subset_closure_convexHull
        (C := C) (D := D) (A := A.dom) (B := B.dom) (L := L)
        hCne hDne hCconv hDconv hAdomC hCclosure hBdomD hDclosure hcone)
  have hPproj :
      Prod.fst '' ERealFunction.dom (fitzpatrickProd P) = C ×ˢ D := by
    simpa [P, C] using fst_image_dom_fitzpatrick_product_eq hA hB
  have hGproj :
      Prod.fst '' ERealFunction.dom (fitzpatrickProd G) = Γ := by
    apply Set.Subset.antisymm
    · intro x hx
      have hsub := fst_image_dom_fitzpatrick_subset_closure_dom G hGmax hx
      have hdom : G.dom = Γ := by
        ext y
        rw [normalCone_dom_eq_of_nonempty hΓne]
      rw [hdom] at hsub
      exact hΓclosed.closure_subset hsub
    · intro x hx
      refine ⟨(x, 0), ?_, rfl⟩
      rw [ERealFunction.mem_dom_iff]
      change fitzpatrick G x 0 < (⊤ : EReal)
      have hzero : (0 : H × K) ∈ G x := by
        exact (Set.mem_normalCone_iff_forall).2 ⟨hx, fun y hy => by simp⟩
      rw [fitzpatrick_graph_eq_inner hG.1 hzero]
      exact EReal.coe_lt_top _
  have hsriProjected :
      (0 : H × K) ∈ Set.strongRelativeInterior
        (Prod.fst '' (ERealFunction.dom (fitzpatrickProd P) -
          ERealFunction.dom (fitzpatrickProd G))) := by
    rw [fst_image_sub_eq_sub_fst_image, hPproj, hGproj]
    exact hsriGraph
  have hsriLifted :=
    fitzpatrick_lifted_sri_of_projected_sri (H := H × K) hP hG hsriProjected
  let φ : (H × K) × (H × K) → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi (fitzpatrickProd P) (fitzpatrickProd_proper hP)
  let ψ : (H × K) × (H × K) → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi (fitzpatrickProd G) (fitzpatrickProd_proper hG)
  have hφ : φ ∈ ERealFunction.gammaZero ((H × K) × (H × K)) := by
    exact fitzpatrickProd_properIoi_mem_gammaZero hP
  have hψ : ψ ∈ ERealFunction.gammaZero ((H × K) × (H × K)) := by
    exact fitzpatrickProd_properIoi_mem_gammaZero hG
  have hconeLifted :
      Set.cone
          (ERealFunction.effectiveDomain (φ ∘ ERealFunction.firstLastPullbackMap) -
            ERealFunction.effectiveDomain
              (ψ ∘ ERealFunction.firstDifferencePullbackMap)) =
        ((Submodule.span ℝ
          (ERealFunction.effectiveDomain (φ ∘ ERealFunction.firstLastPullbackMap) -
            ERealFunction.effectiveDomain
              (ψ ∘ ERealFunction.firstDifferencePullbackMap))).topologicalClosure :
          Set (((H × K) × (H × K)) × (H × K))) := by
    exact cone_eq_closedSpan_of_zero_mem_sri_aux hsriLifted
  have hAttain : ∀ q : ((H × K) × (H × K)) × (H × K), ∃ r :
      ((H × K) × (H × K)) × (H × K),
      ERealFunction.conjugate
          ((φ ∘ ERealFunction.firstLastPullbackMap) +
            (ψ ∘ ERealFunction.firstDifferencePullbackMap)).asEReal q =
        ERealFunction.conjugate (φ ∘ ERealFunction.firstLastPullbackMap).asEReal r +
      ERealFunction.conjugate (ψ ∘ ERealFunction.firstDifferencePullbackMap).asEReal
            (q - r) := by
    intro q
    exact ERealFunction.attouchBrezis_split_attainment
      (φ ∘ ERealFunction.firstLastPullbackMap (H := H × K) (K := H × K))
      (ψ ∘ ERealFunction.firstDifferencePullbackMap (H := H × K) (K := H × K))
      (ERealFunction.firstLastPullback_mem_gammaZero (H := H × K) (K := H × K) φ hφ)
      (ERealFunction.firstDifferencePullback_mem_gammaZero (H := H × K) (K := H × K) ψ hψ)
      hconeLifted q
  have hAttain' := hAttain
  dsimp [φ, ψ] at hAttain'
  set_option maxHeartbeats 1000000 in
  have hcontact :=
    fitzpatrickFiberwise_conjugate_swap_eq_inner_iff_mem_add_of_split_attainment
      (H := H × K) hP hG hAttain'
  let Fsum : (H × K) × (H × K) → EReal :=
    fitzpatrickFiberwiseInfimalConvolution P G
  let Φ : ((H × K) × (H × K)) × (H × K) → Set.Ioi (⊥ : EReal) :=
    φ ∘ ERealFunction.firstLastPullbackMap
  let Ψ : ((H × K) × (H × K)) × (H × K) → Set.Ioi (⊥ : EReal) :=
    ψ ∘ ERealFunction.firstDifferencePullbackMap
  let S : (((H × K) × (H × K)) × (H × K)) → Set.Ioi (⊥ : EReal) := Φ + Ψ
  have hΦ : Φ ∈ ERealFunction.gammaZero
      ((((H × K) × (H × K)) × (H × K))) := by
    exact ERealFunction.firstLastPullback_mem_gammaZero φ hφ
  have hΨ : Ψ ∈ ERealFunction.gammaZero
      ((((H × K) × (H × K)) × (H × K))) := by
    exact ERealFunction.firstDifferencePullback_mem_gammaZero ψ hψ
  have hS_gamma : S ∈ ERealFunction.gammaZero
      ((((H × K) × (H × K)) × (H × K))) := by
    exact ERealFunction.pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
      Φ Ψ hΦ hΨ (by simpa [Φ, Ψ] using hsriLifted)
  have hzeroProjected : (0 : H × K) ∈
      Prod.fst '' (ERealFunction.dom (fitzpatrickProd P) -
        ERealFunction.dom (fitzpatrickProd G)) := by
    exact (Set.mem_strongRelativeInterior_iff.mp hsriProjected).1
  have hfinite : ∃ x uA uB : H × K,
      fitzpatrick P x uA < (⊤ : EReal) ∧ fitzpatrick G x uB < (⊤ : EReal) := by
    exact exists_common_finite_fitzpatrick_slice_of_zero_mem_projected_dom_difference
      hzeroProjected
  have hFsum_proper : ERealFunction.IsProper Fsum := by
    simpa [Fsum] using fitzpatrickFiberwiseInfimalConvolution_isProper_of_common_finite hP hG hfinite
  have hS_epi : Convex ℝ (ERealFunction.epigraph S.asEReal) :=
    ERealFunction.convex_epigraph_asEReal_of_mem_gammaZero hS_gamma
  let Lfst : (((H × K) × (H × K)) × (H × K)) →ᵃ[ℝ] ((H × K) × (H × K)) :=
    (ContinuousLinearMap.fst ℝ ((H × K) × (H × K)) (H × K)).toAffineMap
  have hFrepr : Fsum = ERealFunction.infimalPostcomposition Prod.fst S.asEReal := by
    simpa [Fsum, S, Φ, Ψ, φ, ψ, fitzpatrickFiberwiseInfimalConvolution,
      fitzpatrickProd, ERealFunction.properIoi_apply, ERealFunction.asEReal_properIoi] using
      (ERealFunction.secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted
        φ ψ)
  have hFepi : Convex ℝ (ERealFunction.epigraph Fsum) := by
    rw [hFrepr]
    simpa [Lfst] using convex_epigraph_infimalPostcomposition_local S Lfst hS_epi
  have hFsum_conv : ERealFunction.IsConvex Fsum :=
    ERealFunction.isConvex_of_convex_epigraph hFsum_proper hFepi
  have hFsum_ge : ∀ x u : H × K,
      ERealFunction.pairing (x, u) ≤ Fsum (x, u) := by
    intro x u
    simpa [Fsum] using pairing_le_fitzpatrickFiberwiseInfimalConvolution hP hG x u
  have hFconj_repr : ERealFunction.conjugate Fsum =
      (fun q : (H × K) × (H × K) ↦
        ((fun v : H × K ↦ ERealFunction.conjugate (fitzpatrickProd P) (v, q.2)) □
          (fun v : H × K ↦ ERealFunction.conjugate (fitzpatrickProd G) (v, q.2))) q.1) := by
    simpa [Fsum] using
      (fitzpatrickFiberwise_conjugate_swap_eq_firstVariableInfimalConvolution_of_split_attainment
        (H := H × K) hP hG hsriProjected hAttain')
  have hFsum_star_lower : ∀ x u : H × K,
      ERealFunction.pairing (x, u) ≤ ERealFunction.conjugate Fsum (u, x) := by
    intro x u
    rw [hFconj_repr]
    change ERealFunction.pairing (x, u) ≤
      ⨅ v : H × K,
        ERealFunction.conjugate (fitzpatrickProd P) (v, x) +
          ERealFunction.conjugate (fitzpatrickProd G) (u - v, x)
    refine le_iInf fun v ↦ ?_
    have hPbound : ERealFunction.pairing (x, v) ≤
        ERealFunction.conjugate (fitzpatrickProd P) (v, x) :=
      (inner_le_fitzpatrick_of_maximal hP x v).trans
        (fitzpatrick_le_conjugate_swap hP.1 x v)
    have hGbound : ERealFunction.pairing (x, u - v) ≤
        ERealFunction.conjugate (fitzpatrickProd G) (u - v, x) :=
      (inner_le_fitzpatrick_of_maximal hG x (u - v)).trans
        (fitzpatrick_le_conjugate_swap hG.1 x (u - v))
    have hpair : ERealFunction.pairing (x, u) =
        ERealFunction.pairing (x, v) + ERealFunction.pairing (x, u - v) := by
      rw [ERealFunction.pairing_apply, ERealFunction.pairing_apply,
        ERealFunction.pairing_apply, ← EReal.coe_add]
      congr 1
      rw [inner_sub_right]
      ring
    rw [hpair]
    exact add_le_add hPbound hGbound
  have hFsum_star_proper : ERealFunction.IsProper (ERealFunction.conjugate Fsum) := by
    let g : ((H × K) × (H × K)) → EReal :=
      ERealFunction.lowerSemicontinuousEnvelope Fsum
    have henv_lsc : LowerSemicontinuous g := by
      simpa [g] using ERealFunction.lowerSemicontinuousHull_isGreatest Fsum |>.1.1
    have hconv_epi : Convex ℝ (ERealFunction.epigraph Fsum) := by
      exact (ERealFunction.convex_epigraph_iff_jensen_on_dom Fsum).2 (by
        intro p q hp hq a ha ha1
        exact hFsum_conv ha.le ha1.le)
    have henv_epi_conv : Convex ℝ (ERealFunction.epigraph g) := by
      rw [show ERealFunction.epigraph g =
          closure (ERealFunction.epigraph Fsum) by
            simpa [g] using ERealFunction.epi_lowerSemicontinuousHull_eq_closure_epi Fsum]
      exact hconv_epi.closure
    have henv_le : g ≤ Fsum := by
      simpa [g] using ERealFunction.lowerSemicontinuousHull_isGreatest Fsum |>.1.2
    have hpair_le_env : ∀ p : (H × K) × (H × K),
        ERealFunction.pairing p ≤ g p := by
      intro p
      have hliminf_pair : ERealFunction.pairing p ≤
          ERealFunction.liminfAt ERealFunction.pairing p := by
        have hp_lsc : LowerSemicontinuousAt ERealFunction.pairing p := by
          exact (continuous_coe_real_ereal.comp
            (continuous_fst.inner continuous_snd)).continuousAt.lowerSemicontinuousAt
        exact hp_lsc.le_liminf
      have hliminf_mono : ERealFunction.liminfAt ERealFunction.pairing p ≤
          ERealFunction.liminfAt Fsum p := by
        simpa [ERealFunction.liminfAt] using
          (Filter.liminf_le_liminf
            (Filter.Eventually.of_forall (fun q ↦ hFsum_ge q.1 q.2)) :
            Filter.liminf ERealFunction.pairing (nhds p) ≤
              Filter.liminf Fsum (nhds p))
      calc
        ERealFunction.pairing p ≤ ERealFunction.liminfAt ERealFunction.pairing p := hliminf_pair
        _ ≤ ERealFunction.liminfAt Fsum p := hliminf_mono
        _ = g p := by
          simpa [g] using (ERealFunction.lowerSemicontinuousHull_eq_liminfAt Fsum p).symm
    have hgenv_proper : ERealFunction.IsProper g := by
      constructor
      · intro p hp
        have hle := hpair_le_env p
        rw [hp] at hle
        exact (not_le_of_gt (EReal.bot_lt_coe (⟪p.1, p.2⟫_ℝ))) hle
      · rcases hFsum_proper.2 with ⟨p, hp⟩
        refine ⟨p, ?_⟩
        exact lt_of_le_of_lt (henv_le p) ((ERealFunction.mem_dom_iff Fsum p).mp hp)
    have hgenv_gamma : g ∈ ERealFunction.gamma ((H × K) × (H × K)) := by
      rw [ERealFunction.mem_gamma_iff]
      exact ⟨ERealFunction.isConvex_of_convex_epigraph hgenv_proper henv_epi_conv, henv_lsc⟩
    have hgenv_star_proper :
        ERealFunction.IsProper (ERealFunction.conjugate g) :=
      ERealFunction.conjugate_is_proper_of_mem_gamma hgenv_proper hgenv_gamma
    have hconj_eq : ERealFunction.conjugate g = ERealFunction.conjugate Fsum := by
      funext u
      apply le_antisymm
      · by_cases htop : ERealFunction.conjugate Fsum u = (⊤ : EReal)
        · rw [htop]
          exact le_top
        · have hnebot : ERealFunction.conjugate Fsum u ≠ (⊥ : EReal) :=
            ERealFunction.conjugate_ne_bot_of_isProper hFsum_proper u
          have hminor : ∀ p : (H × K) × (H × K),
              (((inner ℝ p u : ℝ) -
                (ERealFunction.conjugate Fsum u).toReal : ℝ) : EReal) ≤ Fsum p := by
            intro p
            apply (ERealFunction.affine_defect_le_real_iff Fsum p u
              (ERealFunction.conjugate Fsum u).toReal).1
            have hsup : ((inner ℝ p u : ℝ) : EReal) - Fsum p ≤
                ERealFunction.conjugate Fsum u := by
              rw [ERealFunction.conjugate_apply]
              exact le_iSup
                (fun q : (H × K) × (H × K) ↦
                  ((inner ℝ q u : ℝ) : EReal) - Fsum q) p
            rw [← EReal.coe_toReal (ne_of_lt (lt_top_iff_ne_top.mpr htop)) hnebot] at hsup
            simpa [EReal.coe_sub] using hsup
          have ha_lsc : LowerSemicontinuous
              (fun p : (H × K) × (H × K) ↦
                (((inner ℝ p u : ℝ) -
                  (ERealFunction.conjugate Fsum u).toReal : ℝ) : EReal)) := by
            have hreal : Continuous (fun p : (H × K) × (H × K) ↦
                inner ℝ p u - (ERealFunction.conjugate Fsum u).toReal) := by
              simpa [ERealFunction.prod_inner_l2_apply] using
                ((continuous_fst.inner (continuous_const :
                    Continuous (fun _ : (H × K) × (H × K) ↦ u.1))).add
                  (continuous_snd.inner (continuous_const :
                    Continuous (fun _ : (H × K) × (H × K) ↦ u.2)))).sub
                  (continuous_const : Continuous (fun _ : (H × K) × (H × K) ↦
                    (ERealFunction.conjugate Fsum u).toReal))
            exact (continuous_coe_real_ereal.comp hreal).lowerSemicontinuous
          have hminor_env : ∀ p : (H × K) × (H × K),
              (((inner ℝ p u : ℝ) -
                (ERealFunction.conjugate Fsum u).toReal : ℝ) : EReal) ≤ g p := by
            intro p
            exact (ERealFunction.lowerSemicontinuousHull_isGreatest Fsum).2
              ⟨ha_lsc, hminor⟩ p
          rw [ERealFunction.conjugate_apply]
          refine iSup_le fun p ↦ ?_
          have hp := hminor_env p
          have hterm :
              (((inner ℝ p u : ℝ) : EReal) - g p) ≤
                ERealFunction.conjugate Fsum u := by
            calc
              (((inner ℝ p u : ℝ) : EReal) - g p) ≤
                  (((inner ℝ p u : ℝ) : EReal) -
                    (((inner ℝ p u : ℝ) -
                      (ERealFunction.conjugate Fsum u).toReal : ℝ) : EReal)) :=
                EReal.sub_le_sub le_rfl hp
              _ = ERealFunction.conjugate Fsum u := by
                rw [← EReal.coe_toReal (ne_of_lt (lt_top_iff_ne_top.mpr htop)) hnebot,
                  ← EReal.coe_sub]
                norm_num
          exact hterm
      ·
        rw [ERealFunction.conjugate_apply, ERealFunction.conjugate_apply]
        refine iSup_le fun q ↦ ?_
        exact (EReal.sub_le_sub le_rfl (henv_le q)).trans
          (le_iSup (fun r : (H × K) × (H × K) ↦
            ((inner ℝ r u : ℝ) : EReal) - g r) q)
    constructor
    · intro p
      exact ERealFunction.conjugate_ne_bot_of_isProper hFsum_proper p
    · rcases hgenv_star_proper.2 with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      rw [← hconj_eq]
      exact hp
  have hmax_contact := pairingEqualityOperator_conjugateSwap_isMaximallyMonotone_local
    (F := Fsum) hFsum_star_lower hFsum_conv hFsum_star_proper
      (by simpa [Fsum] using hFsum_ge)
  have hsum_eq : P + G =
      pairingEqualityOperator (fun p : (H × K) × (H × K) ↦
        ERealFunction.conjugate Fsum (p.2, p.1)) := by
    funext x
    ext u
    rw [mem_pairingEqualityOperator_iff]
    simpa [Fsum] using (hcontact x u).symm
  have hProd : Maximal IsMonotone (P + G) := by
    simpa [hsum_eq] using hmax_contact
  exact Maximal.add_adjointImage_of_maximal_product_normalConeGraph hA hB L hProd

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Projection form of Theorem 25.3 with the lifted maximality supplied explicitly.

This is the complete operator-theoretic remainder after the Fitzpatrick/sri argument has
established maximality of the product operator plus the graph normal cone. -/
theorem Maximal.add_adjointImage_of_lifted_maximal
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hProd : Maximal IsMonotone
      (SetValuedOperator.product A B +
        N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))])) :
    Maximal IsMonotone (A + L.adjointImage B) := by
  exact Maximal.add_adjointImage_of_maximal_product_normalConeGraph hA hB L hProd

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
theorem cone_eq_closedSpan_of_zero_mem_sri {S : Set H}
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
