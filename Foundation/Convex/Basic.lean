import Mathlib
import Foundation.SetValued.Basic
import Foundation.Analysis.ExtendedRealFunctions

/-!
# Convex Basic

Basic convex, affine, segment, hull, closure, and interior facts.
-/

open AffineMap
open Set
open scoped Pointwise
open AffineSubspace
open scoped BigOperators
open scoped BigOperators Pointwise
open scoped InnerProductSpace
open Set AffineMap

/-! Source item: Chap01/Text_1_0_1 -/

universe u

section Additive

variable {X : Type u} [AddCommGroup X]

/-- Pointwise addition of two subsets of an additive commutative group is the set of all
pairwise sums. -/
theorem pointwise_add_eq_setOf_add (C D : Set X) :
    C + D = {x | ∃ c ∈ C, ∃ d ∈ D, c + d = x} := by
  ext x
  simp [Set.mem_add]

/-- Pointwise subtraction of two subsets of an additive commutative group is the set of all
pairwise differences. -/
theorem pointwise_sub_eq_setOf_sub (C D : Set X) :
    C - D = {x | ∃ c ∈ C, ∃ d ∈ D, c - d = x} := by
  ext x
  simp [Set.mem_sub]

end Additive

section Module

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Scalar multiplication of a singleton subset by a set of scalars is the set of all scalar
multiples of the chosen vector. -/
theorem set_smul_singleton_eq_setOf_smul (Λ : Set ℝ) (z : X) :
    Λ • ({z} : Set X) = {x | ∃ r ∈ Λ, r • z = x} := by
  ext x
  simp

end Module

/-! Source item: Chap01/Text_1_0_2 -/

section

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.2 (1): A subset of a real vector space is a cone when it equals its set of positive
real multiples. -/
def IsCone (C : Set X) : Prop :=
  C = (Ioi (0 : ℝ) : Set ℝ) • C

/-- A cone is exactly a set equal to its positive scalar multiples. -/
theorem isCone_iff {C : Set X} :
    IsCone C ↔ C = (Ioi (0 : ℝ) : Set ℝ) • C :=
  Iff.rfl

/-- Text 1.0.2 (2): A subset of a real vector space is a ray when it is the set of nonnegative
real multiples of some nonzero vector. -/
def IsRay (C : Set X) : Prop :=
  ∃ u : X, u ≠ 0 ∧ C = (Ici (0 : ℝ) : Set ℝ) • ({u} : Set X)

/-- A ray is exactly a set of the form `ℝ_+ • {u}` for some nonzero vector `u`. -/
theorem isRay_iff {C : Set X} :
    IsRay C ↔ ∃ u : X, u ≠ 0 ∧ C = (Ici (0 : ℝ) : Set ℝ) • ({u} : Set X) :=
  Iff.rfl

/-- Text 1.0.2 (3): A subset of a real vector space is a line when it is the set of all real
scalar multiples of some nonzero vector. -/
def IsLine (C : Set X) : Prop :=
  ∃ u : X, u ≠ 0 ∧ C = (↑(ℝ ∙ u) : Set X)

/-- A line is exactly the underlying set of a one-dimensional submodule `ℝ ∙ u`
for some nonzero vector `u`. -/
theorem isLine_iff {C : Set X} :
    IsLine C ↔ ∃ u : X, u ≠ 0 ∧ C = (↑(ℝ ∙ u) : Set X) :=
  Iff.rfl

/-- Textbook formulation of `IsLine`: a line is exactly a set of the form `ℝ • {u}` for some
nonzero vector `u`. -/
theorem isLine_iff_eq_univ_smul_singleton {C : Set X} :
    IsLine C ↔ ∃ u : X, u ≠ 0 ∧ C = (univ : Set ℝ) • ({u} : Set X) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    ext x
    simp [Submodule.mem_span_singleton]
  · rintro ⟨u, hu, hC⟩
    refine ⟨u, hu, hC.trans ?_⟩
    ext x
    simp [Submodule.mem_span_singleton]

end

/-! Source item: Chap01/Text_1_0_4 -/

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.4 (1): the span of `C` is the intersection of all linear subspaces of `X`
containing `C`. -/
-- Proof sketch: use the Galois insertion between `Submodule.span ℝ` and coercion from submodules
-- to sets to identify the generated submodule with the infimum of all containing submodules.
theorem span_eq_sInf_submodule (C : Set X) :
    Submodule.span ℝ C = sInf {S : Submodule ℝ X | C ⊆ S} := by
  refine le_antisymm ?_ ?_
  · exact le_sInf fun S hS ↦ Submodule.span_le.2 hS
  · exact sInf_le Submodule.subset_span

/-- Text 1.0.4 (2): the affine hull of `C` is the intersection of all affine subspaces of `X`
containing `C`. -/
-- Proof sketch: apply the existing `AffineSubspace.affineSpan_eq_sInf` characterization of
-- `affineSpan ℝ C` as the infimum of all affine subspaces containing `C`.
theorem affine_hull_eq_sInf_affineSubspace (C : Set X) :
    affineSpan ℝ C = sInf {S : AffineSubspace ℝ X | C ⊆ S} := by
  simpa using AffineSubspace.affineSpan_eq_sInf ℝ X C

/-! Source item: Chap01/Text_1_0_5 -/


variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.5: if `C` is a nonempty affine subspace of a real vector space, then the textbook
difference set `C - C` is the carrier of the canonical direction subspace `C.direction`, and `C`
is the translate of this direction through any point of `C`. -/
-- Proof sketch: use `coe_direction_eq_vsub_set` to identify the textbook difference set with
-- `C.direction`, then characterize the translate through `x ∈ C` pointwise using
-- `vsub_mem_direction` and `vadd_mem_of_mem_direction`.
theorem text_1_0_5 (C : AffineSubspace ℝ X) (hC : (C : Set X).Nonempty) :
    (C.direction : Set X) = (C : Set X) -ᵥ (C : Set X) ∧
    ∀ ⦃x : X⦄, x ∈ C → (C : Set X) = (fun v ↦ v +ᵥ x) '' (C.direction : Set X) := by
  refine ⟨?_, ?_⟩
  · -- The textbook difference set `C - C` is exactly the canonical direction set of `C`.
    simpa using coe_direction_eq_vsub_set hC
  · -- Any point of `C` together with the direction determines `C` again.
    intro x hx
    ext y
    constructor
    · intro hy
      refine ⟨y -ᵥ x, vsub_mem_direction hy hx, ?_⟩
      simp
    · rintro ⟨v, hv, rfl⟩
      exact vadd_mem_of_mem_direction hv hx

/-! Source item: Chap01/Text_1_0_6 -/

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.6 (1): The half-open line segment `[x,y[` is the image of the interval
`Set.Ico (0 : ℝ) 1` under the affine line map from `x` to `y`. -/
def closedOpenSegment (x y : X) : Set X :=
  AffineMap.lineMap x y '' Set.Ico (0 : ℝ) 1

/-- Membership in `closedOpenSegment x y` means lying on the affine line from `x` to `y`
with parameter in `[0,1)`. -/
theorem mem_closedOpenSegment_iff {x y z : X} :
    z ∈ closedOpenSegment x y ↔
      ∃ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 ∧ AffineMap.lineMap x y t = z := by
  simp [closedOpenSegment]

/-- Text 1.0.6 (2): The half-open line segment `]x,y]` is the image of the interval
`Set.Ioc (0 : ℝ) 1` under the affine line map from `x` to `y`. -/
def openClosedSegment (x y : X) : Set X :=
  AffineMap.lineMap x y '' Set.Ioc (0 : ℝ) 1

/-- Membership in `openClosedSegment x y` means lying on the affine line from `x` to `y`
with parameter in `(0,1]`. -/
theorem mem_openClosedSegment_iff {x y z : X} :
    z ∈ openClosedSegment x y ↔
      ∃ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 ∧ AffineMap.lineMap x y t = z := by
  simp [openClosedSegment]

/-! Source item: Chap01/Text_1_0_7 -/


variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.7: the half-open segment `]x,y]` coincides with the half-open segment `[y,x[`. -/
-- Proof sketch: rewrite both sides as images of `AffineMap.lineMap` on `Ioc 0 1` and `Ico 0 1`,
-- then use the change of variables `s = 1 - t` together with `AffineMap.lineMap_apply_one_sub`.
theorem text_1_0_7 (x y : X) :
    openClosedSegment x y = closedOpenSegment y x := by
  ext z
  constructor
  · intro hz
    rcases mem_openClosedSegment_iff.mp hz with ⟨t, ht, htz⟩
    -- Reverse the parameter by sending `t` to `1 - t`.
    refine mem_closedOpenSegment_iff.mpr ?_
    refine ⟨1 - t, ?_, ?_⟩
    · simpa using (Set.sub_mem_Ico_zero_iff_right : 1 - t ∈ Set.Ico (0 : ℝ) 1 ↔
        t ∈ Set.Ioc (0 : ℝ) 1).2 ht
    -- Reversing the endpoints of the line map matches the textbook identity.
    exact (AffineMap.lineMap_apply_one_sub y x t).trans htz
  · intro hz
    rcases mem_closedOpenSegment_iff.mp hz with ⟨s, hs, hsz⟩
    -- Apply the inverse parameter change `s ↦ 1 - s`.
    refine mem_openClosedSegment_iff.mpr ?_
    refine ⟨1 - s, ?_, ?_⟩
    · simpa using (Set.sub_mem_Ioc_zero_iff_right : 1 - s ∈ Set.Ioc (0 : ℝ) 1 ↔
        s ∈ Set.Ico (0 : ℝ) 1).2 hs
    -- The same line-map symmetry gives the converse inclusion.
    exact (AffineMap.lineMap_apply_one_sub x y s).trans hsz

/-! Source item: Chap01/Text_1_0_15 -/
universe v

variable {X : Type u} {Y : Type v}

/-- Text 1.0.15: the image `T(C)` of a subset `C ⊆ X` under a single-valued map `T : X → Y`
is the canonical set-theoretic construction `Set.image T C`. -/
-- Proof sketch: this is definitional, since the notation `T '' C` expands to `Set.image T C`.
theorem image_eq_set_image (T : X → Y) (C : Set X) :
    T '' C = Set.image T C := rfl

/-- The preimage `T⁻¹(D)` of a subset `D ⊆ Y` under a map `T : X → Y` is the set
`Set.preimage T D`. -/
-- Proof sketch: this is definitional, since the notation `T ⁻¹' D` expands to
-- `Set.preimage T D`.
theorem preimage_eq_set_preimage (T : X → Y) (D : Set Y) :
    T ⁻¹' D = Set.preimage T D := rfl

/-! Source item: Chap01/Text_1_0_18 -/

/-- Text 1.0.18: an operator between real vector spaces is positively homogeneous when it
commutes with scalar multiplication by every positive real scalar. -/
def PositivelyHomogeneous {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (T : X → Y) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a → ∀ x : X, T (a • x) = a • T x

namespace PositivelyHomogeneous

variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {T : X → Y}

/-- A positively homogeneous operator maps a positive scalar multiple to the corresponding
scalar multiple of the image. -/
theorem map_smul_of_pos (hT : PositivelyHomogeneous T) {a : ℝ} (ha : 0 < a) (x : X) :
    T (a • x) = a • T x :=
  hT ha x

end PositivelyHomogeneous

/-! Source item: Chap01/Text_1_0_19 -/

/-- Text 1.0.19: affine mappings between real vector spaces are the canonical affine maps
`X →ᵃ[ℝ] Y`. -/
theorem affineMap_notation_eq (X : Type u) (Y : Type v) [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] :
    (X →ᵃ[ℝ] Y) = AffineMap ℝ X Y :=
  rfl

variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

namespace AffineMap

/-- An affine map between real vector spaces preserves binary affine combinations. -/
theorem map_affine_combination (T : X →ᵃ[ℝ] Y) (x y : X) (a : ℝ) :
    T (a • x + (1 - a) • y) = a • T x + (1 - a) • T y := by
  simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
    T.apply_lineMap y x a

end AffineMap

/-! Source item: Chap01/Text_1_0_20 -/

variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

private lemma centered_map_smul_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x : X) (μ : ℝ) :
    T (μ • x) - T 0 = μ • (T x - T 0) := by
  have hAffine : T (μ • x) = μ • T x + (1 - μ) • T 0 := by
    simpa using hT x 0 (1 - μ)
  have hShift : (1 - μ) • T 0 = -(μ • T 0) + T 0 := by
    rw [sub_eq_add_neg, add_smul, one_smul, neg_smul]
    abel
  rw [sub_eq_iff_eq_add]
  calc
    T (μ • x) = μ • T x + (1 - μ) • T 0 := hAffine
    _ = μ • T x + (-(μ • T 0) + T 0) := by rw [hShift]
    _ = μ • (T x - T 0) + T 0 := by
      rw [smul_sub, sub_eq_add_neg]
      abel

private lemma centered_map_half_sum_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x y : X) :
    T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0 =
      (1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0)) := by
  have hMidpoint :
      T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) = (1 / 2 : ℝ) • T x + (1 / 2 : ℝ) • T y := by
    have h := hT x y (1 / 2 : ℝ)
    norm_num at h
    exact h
  have hHalf : ((1 / 2 : ℝ) • T 0) + (1 / 2 : ℝ) • T 0 = T 0 := by
    rw [← add_smul]
    norm_num
  calc
    T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0
        = ((1 / 2 : ℝ) • T x + (1 / 2 : ℝ) • T y) -
            (((1 / 2 : ℝ) • T 0) + (1 / 2 : ℝ) • T 0) := by
              rw [hMidpoint, hHalf]
    _ = (1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0)) := by
      rw [smul_add, smul_sub, smul_sub]
      abel

private lemma centered_map_add_of_affine_combination (T : X → Y)
    (hT : ∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y)
    (x y : X) :
    T (x + y) - T 0 = (T x - T 0) + (T y - T 0) := by
  have hScale :=
    centered_map_smul_of_affine_combination T hT
      (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) (2 : ℝ)
  have hx : (2 : ℝ) • ((1 / 2 : ℝ) • x) = x := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • x) = ((2 : ℝ) * (1 / 2 : ℝ)) • x := by
        simp
      _ = x := by norm_num
  have hy : (2 : ℝ) • ((1 / 2 : ℝ) • y) = y := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • y) = ((2 : ℝ) * (1 / 2 : ℝ)) • y := by
        simp
      _ = y := by norm_num
  have hArg : (2 : ℝ) • (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) = x + y := by
    rw [smul_add, hx, hy]
  have hCentered :
      (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) =
        (T x - T 0) + (T y - T 0) := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) =
          ((2 : ℝ) * (1 / 2 : ℝ)) • ((T x - T 0) + (T y - T 0)) := by
            simp
      _ = (T x - T 0) + (T y - T 0) := by norm_num
  calc
    T (x + y) - T 0
        = T ((2 : ℝ) • (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y)) - T 0 := by rw [hArg]
    _ = (2 : ℝ) • (T (((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • y) - T 0) := hScale
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • ((T x - T 0) + (T y - T 0))) := by
          rw [centered_map_half_sum_of_affine_combination T hT x y]
    _ = (T x - T 0) + (T y - T 0) := hCentered

/-- Companion bridge for Text 1.0.20: the textbook affine-combination formula for a map `T`
is equivalent to the existence of a bundled affine map with underlying function `T`. -/
theorem affine_combination_iff_exists_affineMap (T : X → Y) :
    (∀ x y : X, ∀ t : ℝ, T ((1 - t) • x + t • y) = (1 - t) • T x + t • T y) ↔
      ∃ A : X →ᵃ[ℝ] Y, (A : X → Y) = T := by
  constructor
  · intro hT
    let L : X →ₗ[ℝ] Y := IsLinearMap.mk' (fun x : X ↦ T x - T 0)
      { map_add := fun x y ↦ centered_map_add_of_affine_combination T hT x y
        map_smul := fun t x ↦ centered_map_smul_of_affine_combination T hT x t }
    refine ⟨AffineMap.mk' T L 0 ?_, rfl⟩
    intro x
    simp [L, sub_eq_add_neg, add_assoc]
  · rintro ⟨A, rfl⟩ x y t
    simpa [AffineMap.lineMap_apply_module] using A.apply_lineMap x y t

/-- Text 1.0.20: a map between real vector spaces is affine, in the canonical sense of arising
from an element of `X →ᵃ[ℝ] Y`, exactly when its translate through the origin,
`x ↦ T x - T 0`, is linear. -/
theorem affine_iff_isLinearMap_sub_apply_zero (T : X → Y) :
    (∃ A : X →ᵃ[ℝ] Y, (A : X → Y) = T) ↔
      IsLinearMap ℝ (fun x : X ↦ T x - T 0) := by
  constructor
  · rintro ⟨A, rfl⟩
    have hCentered : (fun x : X ↦ A x - A 0) = A.linear := by
      funext x
      simpa using (congrArg (fun f : X → Y ↦ f x) A.decomp').symm
    rw [hCentered]
    exact A.linear.isLinear
  · intro hL
    let L : X →ₗ[ℝ] Y := IsLinearMap.mk' (fun x : X ↦ T x - T 0) hL
    refine ⟨AffineMap.mk' T L 0 ?_, rfl⟩
    intro x
    simp [L, sub_eq_add_neg, add_assoc]

/-! Source item: Chap03/Definition_3_1 -/


variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

-- Proof sketch: specialize `convex_iff_pointwise_add_subset` to coefficients `a` and `1 - a`,
-- then use `0 < a` and `a < 1` to obtain the required nonnegativity hypotheses; conversely,
-- recover the textbook one-parameter form from the standard two-parameter characterization.
/-- The textbook pointwise characterization of convexity says that `C` is closed under
combinations `a • x + (1 - a) • y` with `0 < a < 1`, expressed setwise as
`a • C + (1 - a) • C ⊆ C`. -/
theorem convex_iff_smul_add_smul_subset_of_lt_one (C : Set E) :
    Convex ℝ C ↔ ∀ a : ℝ, 0 < a → a < 1 → a • C + (1 - a) • C ⊆ C := by
  constructor
  · intro hC a ha hlt
    exact hC.set_combo_subset ha.le (sub_nonneg.mpr hlt.le) (by ring)
  · intro hC
    refine convex_iff_forall_pos.2 ?_
    intro x hx y hy a b ha hb hab
    have hsubset : a • C + (1 - a) • C ⊆ C := hC a ha (by linarith)
    have hmem : a • x + (1 - a) • y ∈ a • C + (1 - a) • C :=
      Set.add_mem_add ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have hb' : b = 1 - a := by linarith
    exact hsubset (by simpa [hb'] using hmem)

/-! Source item: Chap03/Definition_3_3 -/

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- The closed convex hull of `C` is the intersection of all closed convex subsets of the ambient
Hilbert space that contain `C`. -/
theorem closedConvexHull_eq_iInter_closed_convex_supersets (C : Set 𝓗) :
    closedConvexHull ℝ C = ⋂ (D : Set 𝓗) (_ : C ⊆ D) (_ : Convex ℝ D) (_ : IsClosed D), D := by
  simp [closedConvexHull, Set.iInter_subtype, Set.iInter_and]

/-! Source item: Chap03/Proposition_3_4 -/


variable {𝓗 : Type u} [AddCommGroup 𝓗] [Module ℝ 𝓗]

/-- Textbook membership form of Proposition 3.4: a point lies in `convexHull ℝ C` exactly when it
is a finite center of mass of points of `C` with nonnegative weights summing to `1`. -/
theorem mem_convexHull_iff_exists_finset_centerMass (C : Set 𝓗) (x : 𝓗) :
    x ∈ convexHull ℝ C ↔
      ∃ ι : Type, ∃ t : Finset ι, ∃ w : ι → ℝ, ∃ z : ι → 𝓗,
        (∀ i ∈ t, 0 ≤ w i) ∧
          ∑ i ∈ t, w i = 1 ∧
          (∀ i ∈ t, z i ∈ C) ∧
          t.centerMass w z = x := by
  rw [_root_.convexHull_eq]
  simp only [Set.mem_setOf_eq]

/-! Source item: Chap03/Proposition_3_5 -/

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F]

/-- Proposition 3.5: the image of a convex set under an affine map is convex, and the preimage of
a convex set under an affine map is convex. -/
theorem affine_image_and_preimage_convex (T : E →ᵃ[ℝ] F) (C : Set E) (D : Set F)
    (hC : Convex ℝ C) (hD : Convex ℝ D) :
    Convex ℝ (T '' C) ∧ Convex ℝ (T ⁻¹' D) := by
  exact ⟨hC.affine_image T, hD.affine_preimage T⟩

/-! Source item: Chap03/Proposition_3_6 -/

variable {ι : Type u} {E : Type v} [AddCommGroup E] [Module ℝ E]

/-- Proposition 3.6 (2): a finite weighted Minkowski sum of convex subsets of a real vector space
is convex. -/
theorem convex_weighted_minkowski_sum_finset
    (s : Finset ι) (α : ι → ℝ) (C : ι → Set E) (hC : ∀ i ∈ s, Convex ℝ (C i)) :
    Convex ℝ (∑ i ∈ s, α i • C i) := by
  exact convex_sum (fun i ↦ α i • C i) fun i hi ↦ (hC i hi).smul (α i)

/-! Source item: Chap03/Proposition_3_7 -/

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

-- Proof sketch: if `C` contained distinct points `x` and `y`, convexity would place their midpoint
-- in `C`; applying `norm_combo_lt_of_ne` to the coefficients `1 / 2` and `1 / 2` would then force
-- the midpoint to have norm strictly less than the common radius `(β : ℝ)`, contradicting the
-- constant-norm hypothesis. Use `hC_nonempty` together with `Set.Subsingleton.eq_singleton_of_mem`
-- to turn the resulting subsingleton conclusion into an equality `C = {z}`.
/- The midpoint norm computation is local proof scaffolding for Proposition 3.7. -/
private lemma midpoint_norm_eq_radius_of_mem
    (C : Set 𝓗) (β : NNReal) (hC_convex : Convex ℝ C)
    (hC_norm : ∀ x ∈ C, ‖x‖ = (β : ℝ)) {x y : 𝓗}
    (hx : x ∈ C) (hy : y ∈ C) : ‖midpoint ℝ x y‖ = (β : ℝ) := by
  -- Convexity keeps the midpoint inside `C`, so the constant-norm hypothesis applies there.
  exact hC_norm _ (hC_convex.midpoint_mem hx hy)

/- Distinct points of a common sphere have midpoint of strictly smaller norm. -/
private lemma midpoint_norm_lt_radius_of_ne_mem
    (C : Set 𝓗) (β : NNReal) (hC_norm : ∀ x ∈ C, ‖x‖ = (β : ℝ)) {x y : 𝓗}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) : ‖midpoint ℝ x y‖ < (β : ℝ) := by
  have h_norm_eq : ‖x‖ = ‖y‖ := by
    -- Both endpoints lie on the same sphere of radius `(β : ℝ)`.
    rw [hC_norm x hx, hC_norm y hy]
  have h_midpoint_lt : ‖(1 / 2 : ℝ) • (x + y)‖ < ‖x‖ :=
      (norm_midpoint_lt_iff h_norm_eq).2 hxy
  -- Rewrite the midpoint and the endpoint norm into the radius `(β : ℝ)`.
  simpa [midpoint_eq_smul_add, hC_norm x hx] using h_midpoint_lt

/-- A convex subset of a real Hilbert space on which the norm is constantly `(β : ℝ)` is
subsingleton. -/
theorem subsingleton_of_convex_of_forall_norm_eq
    (C : Set 𝓗) (β : NNReal) (hC_convex : Convex ℝ C)
    (hC_norm : ∀ x ∈ C, ‖x‖ = (β : ℝ)) : C.Subsingleton := by
  intro x hx y hy
  -- Distinct points would give a midpoint with two incompatible norm estimates.
  by_contra hxy
  have h_midpoint_eq :
      ‖midpoint ℝ x y‖ = (β : ℝ) :=
    midpoint_norm_eq_radius_of_mem C β hC_convex hC_norm hx hy
  have h_midpoint_lt :
      ‖midpoint ℝ x y‖ < (β : ℝ) :=
    midpoint_norm_lt_radius_of_ne_mem C β hC_norm hx hy hxy
  exact (lt_irrefl (β : ℝ)) (h_midpoint_eq ▸ h_midpoint_lt)

/-- Proposition 3.7: a nonempty convex subset of a real Hilbert space on which every point has the
same norm `(β : ℝ)` is a singleton. -/
theorem exists_eq_singleton_of_nonempty_convex_of_forall_norm_eq
    (C : Set 𝓗) (β : NNReal) (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C)
    (hC_norm : ∀ x ∈ C, ‖x‖ = (β : ℝ)) : ∃ z : 𝓗, C = {z} := by
  rcases hC_nonempty with ⟨z, hz⟩
  -- Once `C` is known to be subsingleton, any point of `C` determines the whole set.
  refine ⟨z, ?_⟩
  exact (subsingleton_of_convex_of_forall_norm_eq C β hC_convex hC_norm).eq_singleton_of_mem hz

/-! Source item: Chap03/Proposition_3_39 -/

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Proposition 3.39: the convex join of two compact sets is compact because it is the
continuous image of the compact parameter space of endpoints together with a scalar in `[0,1]`. -/
private lemma isCompact_convexJoin {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  -- Parameterize each point of the join by its two endpoints and one interpolation scalar.
  have hjoin :
      convexJoin ℝ s t =
        (fun p : (E × E) × ℝ ↦ (1 - p.2) • p.1.1 + p.2 • p.1.2) ''
          ((s ×ˢ t) ×ˢ Set.Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · intro hz
      rcases mem_convexJoin.mp hz with ⟨x, hx, y, hy, hzSeg⟩
      rw [segment_eq_image_lineMap] at hzSeg
      rcases hzSeg with ⟨a, ha, rfl⟩
      refine ⟨((x, y), a), ⟨⟨hx, hy⟩, ha⟩, ?_⟩
      simp [AffineMap.lineMap_apply_module]
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨⟨x, y⟩, a⟩
      rcases hp with ⟨⟨hx, hy⟩, ha⟩
      rcases ha with ⟨ha0, ha1⟩
      refine mem_convexJoin.mpr ⟨x, hx, y, hy, ?_⟩
      refine ⟨1 - a, a, sub_nonneg.mpr ha1, ha0, by ring, rfl⟩
  -- Compactness follows from compactness of the parameter space and continuity of the join map.
  rw [hjoin]
  have hcont : Continuous fun p : (E × E) × ℝ ↦ (1 - p.2) • p.1.1 + p.2 • p.1.2 := by
    fun_prop
  exact ((hs.prod ht).prod isCompact_Icc).image hcont

/-- Helper for Proposition 3.39: a finite family of compact convex sets has compact convex hull. -/
private lemma isCompact_convexHull_iUnion_finset {ι : Type*} {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (s : Finset ι) (C : ι → Set E)
    (hconv : ∀ i, Convex ℝ (C i)) (hcompact : ∀ i, IsCompact (C i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ s, C i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi ih =>
      have hUnion : (⋃ j ∈ insert i s, C j) = C i ∪ ⋃ j ∈ s, C j := by
        ext x
        simp
      rw [hUnion]
      by_cases hi_nonempty : (C i).Nonempty
      · by_cases hs_nonempty : (⋃ j ∈ s, C j).Nonempty
        · rw [convexHull_union hi_nonempty hs_nonempty, hconv i |>.convexHull_eq]
          exact isCompact_convexJoin (hcompact i) ih
        · have hs_empty : (⋃ j ∈ s, C j) = ∅ := Set.not_nonempty_iff_eq_empty.mp hs_nonempty
          simp [hs_empty, hconv i |>.convexHull_eq, hcompact i]
      · have hi_empty : C i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi_nonempty
        simp [hi_empty, ih]

-- Proof sketch: write `convexHull ℝ (⋃ i, C i)` as the image of the compact product
-- `(∏ i, C i) × stdSimplex ℝ (Fin m)` under the continuous barycentric map
-- `(x, η) ↦ ∑ i, η i • x i`, using convexity of each `C i` to regroup any finite convex
-- combination into one point from each `C i`.
/-- Proposition 3.39 (1): the convex hull of a finite family of compact convex subsets of a real
topological vector space, hence in particular of a real Hilbert space, is compact. -/
theorem isCompact_convexHull_iUnion_fin
    {ι : Type*} [Finite ι] {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (C : ι → Set E)
    (hconv : ∀ i, Convex ℝ (C i))
    (hcompact : ∀ i, IsCompact (C i)) :
    IsCompact (convexHull ℝ (⋃ i, C i) : Set E) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  simpa using isCompact_convexHull_iUnion_finset (Finset.univ : Finset ι) C hconv hcompact

private lemma isCompact_convexHull_iUnion_fin_weakSpace
    {ι : Type*} [Finite ι] (C : ι → Set (WeakSpace ℝ 𝓗))
    (hconv : ∀ i, Convex ℝ (C i)) (hcompact : ∀ i, IsCompact (C i)) :
    IsCompact (convexHull ℝ (⋃ i, C i) : Set (WeakSpace ℝ 𝓗)) := by
  let hModule : Module ℝ (WeakSpace ℝ 𝓗) := by
    haveI : AddCommGroup (WeakSpace ℝ 𝓗) := WeakSpace.instAddCommGroup
    infer_instance
  exact
    @isCompact_convexHull_iUnion_fin ι inferInstance (WeakSpace ℝ 𝓗)
      WeakSpace.instAddCommGroup hModule inferInstance WeakSpace.instIsTopologicalAddGroup
      WeakSpace.instContinuousSMul C hconv hcompact

-- Proof sketch: transport the family to `WeakSpace ℝ 𝓗`, where each image
-- `(toWeakSpace ℝ 𝓗) '' C i` is compact and convex. Then apply the first clause in the weak
-- topology and use that
-- `toWeakSpace ℝ 𝓗` commutes with convex hulls because it is linear.
/-- Proposition 3.39 (2): the convex hull of a finite family of weakly compact convex subsets of a
real Hilbert space is weakly compact, expressed as compactness in `WeakSpace ℝ 𝓗`. -/
theorem weaklyCompact_convexHull_iUnion_fin
    {ι : Type*} [Finite ι] (C : ι → Set 𝓗) (hconv : ∀ i, Convex ℝ (C i))
    (hweaklyCompact : ∀ i, IsCompact ((toWeakSpace ℝ 𝓗) '' C i)) :
    IsCompact ((toWeakSpace ℝ 𝓗) '' convexHull ℝ (⋃ i, C i)) := by
  classical
  -- Transport convexity to the weak space via the canonical linear map.
  have hconvWeak : ∀ i, Convex ℝ ((toWeakSpace ℝ 𝓗) '' C i) := by
    intro i
    exact (hconv i).linear_image (toWeakSpace ℝ 𝓗).toLinearMap
  -- The canonical map to `WeakSpace` commutes with convex hull and finite unions.
  have himage :
      (toWeakSpace ℝ 𝓗) '' convexHull ℝ (⋃ i, C i) =
        convexHull ℝ (⋃ i, (toWeakSpace ℝ 𝓗) '' C i) := by
    simpa [Set.image_iUnion] using
      (LinearMap.image_convexHull (toWeakSpace ℝ 𝓗).toLinearMap (⋃ i, C i))
  rw [himage]
  -- Apply the same compact-convex-hull theorem inside the weak topology.
  simpa using
    (isCompact_convexHull_iUnion_fin_weakSpace
      (fun i ↦ (toWeakSpace ℝ 𝓗) '' C i) hconvWeak hweaklyCompact :
        IsCompact
          (convexHull ℝ (⋃ i, (toWeakSpace ℝ 𝓗) '' C i) : Set (WeakSpace ℝ 𝓗)))

/-! Source item: Chap03/Proposition_3_44 -/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Proposition 3.44, pointwise form: if `C` is convex, `x ∈ interior C`, `y ∈ closure C`, and
`t ∈ [0,1)`, then the point `lineMap x y t` lies in `interior C`. -/
theorem lineMap_mem_interior_of_mem_Ico_of_mem_interior_of_mem_closure {C : Set E}
    (hC : Convex ℝ C) {x y : E} (hx : x ∈ interior C) (hy : y ∈ closure C)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    lineMap x y t ∈ interior C := by
  rcases ht with ⟨ht0, ht1⟩
  simpa [lineMap_apply_module] using
    hC.combo_interior_closure_mem_interior hx hy
      (sub_pos.mpr ht1) ht0 (sub_add_cancel 1 t)

/-- Proposition 3.44: if `C` is convex, `x ∈ interior C`, and `y ∈ closure C`, then the half-open
segment `[x,y[` is contained in `interior C`. -/
theorem closedOpenSegment_subset_interior_of_mem_interior_of_mem_closure {C : Set E}
    (hC : Convex ℝ C) {x y : E} (hx : x ∈ interior C) (hy : y ∈ closure C) :
    closedOpenSegment x y ⊆ interior C := by
  intro z hz
  rcases mem_closedOpenSegment_iff.mp hz with ⟨t, ht, rfl⟩
  exact lineMap_mem_interior_of_mem_Ico_of_mem_interior_of_mem_closure hC hx hy ht

/-! Source item: Chap03/Proposition_3_45 -/

variable {E : Type u}

section ContinuousConstSMul

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]

/-- Proposition 3.45 (1): the closure of a convex subset of a real topological vector space is
convex. -/
theorem convex_closure_of_convex {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (closure C) := by
  simpa using hC.closure

/-- Proposition 3.45 (2): the interior of a convex subset of a real topological vector space is
convex. -/
theorem convex_interior_of_convex {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (interior C) := by
  simpa using hC.interior

end ContinuousConstSMul

section ContinuousSMul

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Proposition 3.45 (3): if a convex set has nonempty interior, then taking the closure does not
change its interior. -/
theorem interior_closure_eq_interior_of_convex_nonempty_interior {C : Set E}
    (hC : Convex ℝ C) (hCint : (interior C).Nonempty) :
    interior (closure C) = interior C := by
  simpa using hC.interior_closure_eq_interior_of_nonempty_interior hCint

/-- Proposition 3.45 (4): if a convex set has nonempty interior, then the closure of its interior
is the closure of the set. -/
theorem closure_interior_eq_closure_of_convex_nonempty_interior {C : Set E}
    (hC : Convex ℝ C) (hCint : (interior C).Nonempty) :
    closure (interior C) = closure C := by
  simpa using hC.closure_interior_eq_closure_of_nonempty_interior hCint

end ContinuousSMul

/-! Source item: Chap03/Proposition_3_46 -/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: `convexHull ℝ (closure C)` lies in the closed convex hull of `closure C`, and the
-- closed convex hull is unchanged by taking closure. The standard closed-convex-hull identity then
-- identifies the target with `closure (convexHull ℝ C)`.
/-- Proposition 3.46 (1): the convex hull of the closure of a subset of a real normed space is
contained in the closure of its convex hull. -/
theorem convexHull_closure_subset_closure_convexHull (C : Set E) :
    convexHull ℝ (closure C) ⊆ closure (convexHull ℝ C) := by
  -- Route through the canonical closed convex hull identity.
  calc
    convexHull ℝ (closure C) ⊆ closedConvexHull ℝ (closure C) :=
      convexHull_subset_closedConvexHull
    _ = closedConvexHull ℝ C := closedConvexHull_closure_eq_closedConvexHull
    _ = closure (convexHull ℝ C) := by
      simpa using (closedConvexHull_eq_closure_convexHull : closedConvexHull ℝ C = _)

-- Proof sketch: this is the standard identification of the closed convex hull with the closure of
-- the convex hull, specialized to subsets of a real normed space.
/-- Proposition 3.46 (2): the closure of the convex hull of a subset of a real normed space is its
closed convex hull. -/
theorem closure_convexHull_eq_closedConvexHull (C : Set E) :
    closure (convexHull ℝ C) = closedConvexHull ℝ C := by
  -- This is exactly the standard closed-convex-hull identity in mathlib.
  simpa [eq_comm] using
    (closedConvexHull_eq_closure_convexHull : closedConvexHull ℝ C = closure (convexHull ℝ C))

/-! Source item: Chap03/Proposition_3_48 -/

section Topological

variable {E : Type u} [TopologicalSpace E]

/-- Closedness gives the easy inclusion
`closure (C ∩ interior D) ⊆ C ∩ closure D`. -/
private lemma closure_inter_interior_subset_inter_closure
    {C D : Set E} (hC_closed : IsClosed C) :
    closure (C ∩ interior D) ⊆ C ∩ closure D := by
  -- First place `C ∩ interior D` inside the closed target set.
  refine closure_minimal ?_ (hC_closed.inter isClosed_closure)
  intro z hz
  exact ⟨hz.1, interior_subset_closure hz.2⟩

end Topological

section TopologicalVector

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Once a point of `C ∩ interior D` is fixed, every point of
`C ∩ closure D` belongs to `closure (C ∩ interior D)`. -/
private lemma mem_closure_inter_interior_of_mem_inter_closure
    {C D : Set E} (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    {x y : E} (hx : x ∈ C ∩ interior D) (hy : y ∈ C ∩ closure D) :
    y ∈ closure (C ∩ interior D) := by
  -- The geometric core is that the open segment from `x` to `y` stays in `C ∩ interior D`.
  have hsubset : openSegment ℝ x y ⊆ C ∩ interior D := by
    intro z hz
    refine ⟨?_, ?_⟩
    · exact hC_conv.openSegment_subset hx.1 hy.1 hz
    · exact hD_conv.openSegment_interior_closure_subset_interior hx.2 hy.2 hz
  -- The endpoint `y` lies in the segment, hence in the closure of the open segment.
  have hy_mem : y ∈ closure (openSegment ℝ x y) :=
    segment_subset_closure_openSegment (right_mem_segment ℝ x y)
  -- Monotonicity of closure transfers this to the desired closure.
  exact closure_mono hsubset hy_mem

-- Proof sketch: The inclusion `closure (C ∩ interior D) ⊆ C ∩ closure D` follows from
-- `interior D ⊆ closure D` and closedness of `C`. For the reverse inclusion, fix
-- `x ∈ C ∩ interior D` and `y ∈ C ∩ closure D`; convexity puts the points
-- `α • x + (1 - α) • y` in `C ∩ interior D` for `0 < α ≤ 1`, and these converge to `y`.
/-- Proposition 3.48: if `C` and `D` are convex subsets of a real topological vector space, `C`
is closed, and `C ∩ interior D` is nonempty, then the closure of `C ∩ interior D` is
`C ∩ closure D`. -/
theorem closure_inter_interior_eq_inter_closure_of_nonempty
    {C D : Set E}
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hC_closed : IsClosed C) (h_nonempty : (C ∩ interior D).Nonempty) :
    closure (C ∩ interior D) = C ∩ closure D := by
  refine subset_antisymm ?_ ?_
  · -- The forward inclusion is the closed-set argument from the textbook proof.
    exact closure_inter_interior_subset_inter_closure hC_closed
  · rcases h_nonempty with ⟨x, hx⟩
    -- Fix one point of `C ∩ interior D`; every `y ∈ C ∩ closure D` is reached as a segment endpoint.
    intro y hy
    exact mem_closure_inter_interior_of_mem_inter_closure hC_conv hD_conv hx hy

end TopologicalVector


