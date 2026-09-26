import Foundation.Convex.FiberwiseDuality
import Foundation.Convex.Subdifferential
import Foundation.SetValued.MaximalMonotone

/-!
# Product operators and graph normal cones

Maximality of the two operators used in the product-space lift of the maximal
monotone sum theorem.
-/

open Set ERealFunction
open scoped InnerProductSpace Pointwise

universe u v

namespace SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- The componentwise product of set-valued operators. -/
def product (A : SetValuedOperator H H) (B : SetValuedOperator K K) :
    SetValuedOperator (H × K) (H × K) :=
  fun p => A p.1 ×ˢ B p.2

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] in
@[simp] theorem mem_product (A : SetValuedOperator H H) (B : SetValuedOperator K K)
    (p w : H × K) :
    w ∈ product A B p ↔ w.1 ∈ A p.1 ∧ w.2 ∈ B p.2 :=
  Iff.rfl

omit [CompleteSpace H] [CompleteSpace K] in
private theorem graph_mem_iff
    (L : H →L[ℝ] K) {x : H} {y : K} :
    (x, y) ∈ ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)) ↔
      y = L x := by
  simp [LinearMap.mem_graph_iff]

/-- The normal cone of a linear graph is its orthogonal complement at every graph point. -/
theorem normalCone_graph_eq_orthogonal
    (L : H →L[ℝ] K) {p : H × K}
    (hp : p ∈ ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))) :
    N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))] p =
      (((L.toLinearMap.graph : Submodule ℝ (H × K))ᗮ : Submodule ℝ (H × K)) : Set (H × K)) := by
  ext n
  rw [Set.mem_normalCone_iff_forall]
  constructor
  · rintro ⟨_, hn⟩
    apply (Submodule.mem_orthogonal' _ n).2
    intro d hd
    have hplus : p + d ∈
        ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)) := by
      exact (L.toLinearMap.graph : Submodule ℝ (H × K)).add_mem hp hd
    have hminus : p - d ∈
        ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)) := by
      exact (L.toLinearMap.graph : Submodule ℝ (H × K)).sub_mem hp hd
    have hplus' := hn (p + d) hplus
    have hminus' := hn (p - d) hminus
    have hpos : inner ℝ d n ≤ 0 := by
      simpa [sub_eq_add_neg, inner_add_left, inner_sub_left] using hplus'
    have hneg : -inner ℝ d n ≤ 0 := by
      simpa [sub_eq_add_neg, inner_add_left, inner_sub_left] using hminus'
    have hz : inner ℝ d n = 0 := le_antisymm hpos (by linarith)
    simpa [real_inner_comm] using hz
  · intro hn
    refine ⟨hp, ?_⟩
    intro y hy
    have hyd : y - p ∈
        ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)) := by
      exact (L.toLinearMap.graph : Submodule ℝ (H × K)).sub_mem hy hp
    have hz := (Submodule.mem_orthogonal' _ n).1 hn (y - p) hyd
    have hz' : inner ℝ (y - p) n = 0 := by
      simpa [real_inner_comm] using hz
    exact hz'.le

/-- The canonical orthogonal vector to the graph of `L` is `(L† v, -v)`. -/
theorem pair_adjoint_neg_mem_orthogonal_graph
    (L : H →L[ℝ] K) (v : K) :
    (L.adjoint v, -v) ∈
      (((L.toLinearMap.graph : Submodule ℝ (H × K))ᗮ : Submodule ℝ (H × K)) : Set (H × K)) := by
  apply (Submodule.mem_orthogonal' _ (L.adjoint v, -v)).2
  intro p hp
  have hpL : p.2 = L p.1 := (graph_mem_iff L).mp hp
  rw [ERealFunction.prod_inner_l2_apply]
  rw [hpL, ContinuousLinearMap.adjoint_inner_left]
  simp

private theorem orthogonal_graph_first_eq_adjoint_neg_second
    (L : H →L[ℝ] K) {n : H × K}
    (hn : n ∈
      (((L.toLinearMap.graph : Submodule ℝ (H × K))ᗮ : Submodule ℝ (H × K)) : Set (H × K))) :
    n.1 = L.adjoint (-n.2) := by
  apply ext_inner_right ℝ
  intro z
  have hz := (Submodule.mem_orthogonal' _ n).1 hn
    (z, L z) (by simp [LinearMap.mem_graph_iff])
  rw [ERealFunction.prod_inner_l2_apply] at hz
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hz' : inner ℝ z n.1 + inner ℝ n.2 (L z) = 0 := by
    simpa [real_inner_comm] using hz
  have hz'' : inner ℝ n.1 z + inner ℝ n.2 (L z) = 0 := by
    simpa [real_inner_comm] using hz'
  rw [inner_neg_left]
  linarith [hz'']

/-- Membership in the lifted product-space sum is equivalent to membership in the adjoint-image
composite on a point of the graph of `L`. -/
theorem mem_product_add_normalConeGraph_iff
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (L : H →L[ℝ] K) {x u : H} {v : K} :
    (u, v) ∈
        (SetValuedOperator.product A B +
          N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))]) (x, L x) ↔
      u + L.adjoint v ∈ (A + L.adjointImage B) x := by
  have hxGraph : (x, L x) ∈
      ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)) := by
    simp [LinearMap.mem_graph_iff]
  constructor
  · intro huv
    change (u, v) ∈
      SetValuedOperator.product A B (x, L x) +
        N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))] (x, L x) at huv
    rcases Set.mem_add.mp huv with ⟨a, ha, n, hn, hsum⟩
    rcases a with ⟨a₁, a₂⟩
    rcases n with ⟨n₁, n₂⟩
    have ha' : a₁ ∈ A x ∧ a₂ ∈ B (L x) :=
      (mem_product A B (x, L x) (a₁, a₂)).mp ha
    have hnOrth : (n₁, n₂) ∈
        (((L.toLinearMap.graph : Submodule ℝ (H × K))ᗮ : Submodule ℝ (H × K)) : Set (H × K)) := by
      rw [← normalCone_graph_eq_orthogonal L hxGraph]
      exact hn
    have hn₁ : n₁ = L.adjoint (-n₂) :=
      orthogonal_graph_first_eq_adjoint_neg_second L hnOrth
    have huEq : u = a₁ + n₁ := by simpa using (congrArg Prod.fst hsum).symm
    have hvEq : v = a₂ + n₂ := by simpa using (congrArg Prod.snd hsum).symm
    change u + L.adjoint v ∈ A x + L.adjoint '' B (L x)
    refine Set.mem_add.mpr ⟨a₁, ha'.1, L.adjoint a₂, ⟨a₂, ha'.2, rfl⟩, ?_⟩
    rw [huEq, hvEq, hn₁]
    simp [add_assoc, add_left_comm, add_comm]
  · intro hu
    change u + L.adjoint v ∈ A x + L.adjoint '' B (L x) at hu
    rcases Set.mem_add.mp hu with ⟨a, ha, w, hw, hsum⟩
    rcases hw with ⟨b, hb, rfl⟩
    let n : H × K := (L.adjoint (b - v), -(b - v))
    have hnOrth : n ∈
        (((L.toLinearMap.graph : Submodule ℝ (H × K))ᗮ : Submodule ℝ (H × K)) : Set (H × K)) := by
      dsimp [n]
      exact pair_adjoint_neg_mem_orthogonal_graph L (b - v)
    have hn : n ∈
        N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))] (x, L x) := by
      rw [normalCone_graph_eq_orthogonal L hxGraph]
      exact hnOrth
    refine Set.mem_add.mpr ⟨(a, b), (mem_product A B (x, L x) (a, b)).2 ⟨ha, hb⟩, n, hn, ?_⟩
    dsimp [n]
    ext
    · have huEq : u = a + L.adjoint b - L.adjoint v := by
        calc
          u = (u + L.adjoint v) - L.adjoint v := by abel
          _ = (a + L.adjoint b) - L.adjoint v := by rw [hsum]
      rw [huEq]
      simp [sub_eq_add_neg, add_assoc]
    · simp [sub_eq_add_neg]

/-- The adjoint-image composite of a monotone operator is monotone after pointwise addition. -/
theorem IsMonotone.add_adjointImage
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : IsMonotone A) (L : H →L[ℝ] K) (hB : IsMonotone B) :
    IsMonotone (A + L.adjointImage B) := by
  intro x y u hu v hv
  change u ∈ A x + L.adjoint '' B (L x) at hu
  change v ∈ A y + L.adjoint '' B (L y) at hv
  rcases Set.mem_add.mp hu with ⟨a, ha, u', hu', rfl⟩
  rcases hu' with ⟨b, hb, rfl⟩
  rcases Set.mem_add.mp hv with ⟨c, hc, v', hv', rfl⟩
  rcases hv' with ⟨d, hd, rfl⟩
  have hA' : 0 ≤ inner ℝ (a - c) (x - y) := hA a ha c hc
  have hB' : 0 ≤ inner ℝ (b - d) (L x - L y) := hB b hb d hd
  rw [show (a + L.adjoint b) - (c + L.adjoint d) =
      (a - c) + L.adjoint (b - d) by rw [map_sub]; abel, inner_add_left]
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact add_nonneg hA' (by simpa [map_sub] using hB')

/-- The componentwise product of maximally monotone operators is maximally monotone. -/
theorem Maximal.product {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Maximal IsMonotone (SetValuedOperator.product A B) := by
  have hmono : IsMonotone (SetValuedOperator.product A B) := by
    intro p q w hw z hz
    rcases p with ⟨x, y⟩
    rcases q with ⟨x', y'⟩
    rcases w with ⟨a, b⟩
    rcases z with ⟨a', b'⟩
    rcases (mem_product A B (x, y) (a, b)).mp hw with ⟨ha, hb⟩
    rcases (mem_product A B (x', y') (a', b')).mp hz with ⟨ha', hb'⟩
    rw [ERealFunction.prod_inner_l2_apply]
    exact add_nonneg (hA.1 a ha a' ha') (hB.1 b hb b' hb')
  apply (minty_surjective_iff_maximal_isMonotone hmono).2
  rintro ⟨s, t⟩
  obtain ⟨x, a, ha, hs⟩ :=
    (minty_surjective_iff_maximal_isMonotone hA.1).1 hA s
  obtain ⟨y, b, hb, ht⟩ :=
    (minty_surjective_iff_maximal_isMonotone hB.1).1 hB t
  refine ⟨(x, y), (a, b), (mem_product A B (x, y) (a, b)).2 ⟨ha, hb⟩, ?_⟩
  ext <;> assumption

end SetValuedOperator

namespace Set

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The indicator of a nonempty closed convex set belongs to `Γ₀`. -/
private theorem indicator_mem_gammaZero_of_nonempty_closed_convex
    {C : Set H} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  have hlsc : LowerSemicontinuous (fun x => ((ι[C]) x : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hclosed
  have hdom : effectiveDomain (ι[C]) = C := by
    ext x
    by_cases hx : x ∈ C <;> simp [effectiveDomain, ERealFunction.indicator, hx]
  refine ⟨hlsc, ?_⟩
  refine ⟨by simpa [hdom] using hne, fun _ hx => hx, ?_⟩
  intro x hx y hy a ha0 ha1
  have hxC : x ∈ C := by simpa [hdom] using hx
  have hyC : y ∈ C := by simpa [hdom] using hy
  have hxyC : a • x + (1 - a) • y ∈ C :=
    hconv hxC hyC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hxC, hyC, hxyC]

/-- The normal cone of a nonempty closed convex set is maximally monotone. -/
theorem normalCone_maximal_isMonotone
    {C : Set H} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C) :
    Maximal SetValuedOperator.IsMonotone (N[C]) := by
  have hgamma : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_closed_convex hne hclosed hconv
  simpa [subdifferential_setIndicator_eq_normalCone C hne] using
    subdifferential_isMaximallyMonotone_of_mem_gammaZero hgamma

end Set

namespace SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-! The two maximality inputs for the product-space lift. -/
theorem maximalityData_product_normalConeGraph
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K) :
    Maximal IsMonotone (SetValuedOperator.product A B) ∧
      Maximal IsMonotone
        (N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))] :
          SetValuedOperator (H × K) (H × K)) := by
  refine ⟨Maximal.product hA hB, ?_⟩
  have hne :
      ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [LinearMap.mem_graph_iff]
  have hclosed :
      IsClosed ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)) := by
    simpa [LinearMap.mem_graph_iff, eq_comm] using
      isClosed_eq continuous_snd (L.continuous.comp continuous_fst)
  have hconv :
      Convex ℝ ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)) := by
    simpa using L.toLinearMap.graph.convex
  exact Set.normalCone_maximal_isMonotone hne hclosed hconv

/-- Maximality of the product operator plus the graph normal cone descends to the
adjoint-image sum. -/
theorem Maximal.add_adjointImage_of_maximal_product_normalConeGraph
    {A : SetValuedOperator H H} {B : SetValuedOperator K K}
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (L : H →L[ℝ] K)
    (hProd : Maximal IsMonotone
      (SetValuedOperator.product A B +
        N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))])) :
    Maximal IsMonotone (A + L.adjointImage B) := by
  have hmono : IsMonotone (A + L.adjointImage B) :=
    IsMonotone.add_adjointImage hA.1 L hB.1
  apply (isMaximalMonotone_iff_maximal_isMonotone _).1
  refine ⟨hmono, ?_⟩
  intro T hTmono hsub p hp
  rcases p with ⟨z, w⟩
  have hrel : ∀ y v, v ∈ (A + L.adjointImage B) y →
      0 ≤ inner ℝ (w - v) (z - y) := by
    intro y v hv
    have hvT : (y, v) ∈ T.graph := hsub hv
    exact hTmono w hp v hvT
  have hrelProd : ∀ y v, v ∈
      (SetValuedOperator.product A B +
        N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))]) y →
      0 ≤ inner ℝ (((w, (0 : K)) : H × K) - v) ((z, L z) - y) := by
    intro y v hv
    have hyGraph : y ∈
        ((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K)) := by
      by_contra hyGraph
      change v ∈ SetValuedOperator.product A B y +
        N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))] y at hv
      rw [Set.normalCone_of_not_mem hyGraph] at hv
      rcases Set.mem_add.mp hv with ⟨a, ha, n, hn, -⟩
      simp at hn
    have hyL : y.2 = L y.1 := (graph_mem_iff L).mp hyGraph
    rcases y with ⟨x, y'⟩
    rcases v with ⟨u, t⟩
    change y' = L x at hyL
    subst y'
    have hu : u + L.adjoint t ∈ (A + L.adjointImage B) x :=
      (mem_product_add_normalConeGraph_iff (A := A) (B := B) L).1 hv
    have hsource := hrel x (u + L.adjoint t) hu
    have hinner :
        inner ℝ (((w, (0 : K)) : H × K) - (u, t))
            ((z, L z) - (x, L x)) =
          inner ℝ (w - (u + L.adjoint t)) (z - x) := by
      rw [ERealFunction.prod_inner_l2_apply]
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero,
        zero_sub, map_sub, inner_neg_left]
      rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_left]
      rw [sub_eq_add_neg, inner_add_left, inner_neg_left]
      rw [inner_sub_left]
      rw [inner_add_left]
      ring
    rwa [hinner]
  have hmem : ((w, (0 : K)) : H × K) ∈
      (SetValuedOperator.product A B +
        N[((L.toLinearMap.graph : Submodule ℝ (H × K)) : Set (H × K))]) (z, L z) :=
    (Maximal.mem_iff hProd (z, L z) (w, 0)).2 (by
      intro y v hv
      exact hrelProd y v hv)
  have hw : w + L.adjoint (0 : K) ∈ (A + L.adjointImage B) z :=
    (mem_product_add_normalConeGraph_iff (A := A) (B := B) L).1 hmem
  simpa using hw

end SetValuedOperator
