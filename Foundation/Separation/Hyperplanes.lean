import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Projection.BestApproximation
import Foundation.Convex.WeakClosed
import Foundation.Hilbert.WeakConvergence

/-!
# Separation Hyperplanes

Support functionals, separating hyperplanes, strong separation, and separation counterexamples.
-/

open scoped InnerProductSpace
open ERealFunction
open scoped InnerProductSpace Pointwise
open Filter
open scoped Pointwise InnerProductSpace

/-! Source item: Chap03/Definition_3_49 -/
universe u


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- The `EReal`-valued supremum of the functional `x ↦ ⟪x, u⟫` on `C`. -/
noncomputable abbrev innerSupremumOn (C : Set 𝓗) (u : 𝓗) : EReal :=
  sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)

-- Proof sketch: unfold `innerSupremumOn`.
/-- The inner-product supremum on `C` is the supremum of the image of `C` under
`x ↦ ⟪x, u⟫`. -/
theorem innerSupremumOn_eq_sSup_image (C : Set 𝓗) (u : 𝓗) :
    innerSupremumOn C u = sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) := rfl

/-- The inner-product supremum over a singleton is its unique value. -/
@[simp] theorem innerSupremumOn_singleton (x u : 𝓗) :
    innerSupremumOn ({x} : Set 𝓗) u = (⟪x, u⟫_ℝ : EReal) := by
  rw [innerSupremumOn_eq_sSup_image]
  simp

/-- The `EReal`-valued infimum of the functional `x ↦ ⟪x, u⟫` on `D`. -/
noncomputable abbrev innerInfimumOn (D : Set 𝓗) (u : 𝓗) : EReal :=
  sInf ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' D)

-- Proof sketch: unfold `innerInfimumOn`.
/-- The inner-product infimum on `D` is the infimum of the image of `D` under
`x ↦ ⟪x, u⟫`. -/
theorem innerInfimumOn_eq_sInf_image (D : Set 𝓗) (u : 𝓗) :
    innerInfimumOn D u = sInf ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' D) := rfl

/-- The inner-product infimum over a singleton is its unique value. -/
@[simp] theorem innerInfimumOn_singleton (x u : 𝓗) :
    innerInfimumOn ({x} : Set 𝓗) u = (⟪x, u⟫_ℝ : EReal) := by
  rw [innerInfimumOn_eq_sInf_image]
  simp

/-- The support-function inequality is equivalent to the corresponding pointwise
inner-product inequalities. -/
theorem innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le (C D : Set 𝓗) (u : 𝓗) :
    innerSupremumOn C u ≤ innerInfimumOn D u ↔
      ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
  constructor
  · intro hsep x hx y hy
    have hx_le : (⟪x, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
      rw [innerSupremumOn_eq_sSup_image]
      exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩
    have hy_ge : innerInfimumOn D u ≤ (⟪y, u⟫_ℝ : EReal) := by
      rw [innerInfimumOn_eq_sInf_image]
      exact (isGLB_sInf _).1 ⟨y, hy, rfl⟩
    exact_mod_cast le_trans (le_trans hx_le hsep) hy_ge
  · intro hxy
    rw [innerSupremumOn_eq_sSup_image, innerInfimumOn_eq_sInf_image]
    refine (isLUB_sSup _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine (isGLB_sInf _).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact show ((⟪x, u⟫_ℝ : EReal) ≤ (⟪y, u⟫_ℝ : EReal)) by
      exact_mod_cast hxy x hx y hy

/-- Definition 3.49: subsets `C` and `D` of a real Hilbert space are separated when some nonzero
vector `u` satisfies `sup_{c ∈ C} ⟪c, u⟫ ≤ inf_{d ∈ D} ⟪d, u⟫`; strong separation and
point-from-set separation are obtained by replacing `≤` with `<` and by taking `C = {x}`. -/
def AreSeparated (C D : Set 𝓗) : Prop :=
  ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u ≤ innerInfimumOn D u

-- Proof sketch: unfold `AreSeparated`.
/-- Two sets are separated exactly when there is a nonzero normal vector whose inner-product
supremum on the first set does not exceed the inner-product infimum on the second. -/
@[simp] theorem areSeparated_iff_exists_nonzero (C D : Set 𝓗) :
    AreSeparated C D ↔
      ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u ≤ innerInfimumOn D u := Iff.rfl

/-- Two sets are separated exactly when there is a nonzero normal vector whose inner products on
the first set are pointwise bounded above by those on the second set. -/
theorem areSeparated_iff_exists_nonzero_forall_inner_le (C D : Set 𝓗) :
    AreSeparated C D ↔
      ∃ u : 𝓗, u ≠ 0 ∧ ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
  rw [areSeparated_iff_exists_nonzero]
  constructor
  · rintro ⟨u, hu, hsep⟩
    exact ⟨u, hu, (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le C D u).mp hsep⟩
  · rintro ⟨u, hu, hxy⟩
    exact ⟨u, hu, (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le C D u).mpr hxy⟩

/-- A nonzero vector whose inner products on `C` are pointwise bounded above by those on `D`
separates `C` and `D`. -/
theorem areSeparated_of_forall_inner_le {C D : Set 𝓗} {u : 𝓗} (hu : u ≠ 0)
    (hxy : ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ) :
    AreSeparated C D :=
  (areSeparated_iff_exists_nonzero_forall_inner_le C D).2 ⟨u, hu, hxy⟩

/-- A separating support-function inequality yields the corresponding pointwise
inner-product inequalities. -/
theorem forall_inner_le_of_innerSupremumOn_le_innerInfimumOn {C D : Set 𝓗} {u : 𝓗}
    (hsep : innerSupremumOn C u ≤ innerInfimumOn D u) :
    ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ :=
  (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le C D u).1 hsep

/-- Two sets are strongly separated when some nonzero vector yields a strict gap between the
corresponding inner-product supremum and infimum. -/
def AreStronglySeparated (C D : Set 𝓗) : Prop :=
  ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u < innerInfimumOn D u

-- Proof sketch: unfold `AreStronglySeparated`.
/-- Two sets are strongly separated exactly when there is a nonzero normal vector whose
inner-product supremum on the first set is strictly smaller than the inner-product infimum on the
second. -/
theorem areStronglySeparated_iff_exists_nonzero (C D : Set 𝓗) :
    AreStronglySeparated C D ↔
      ∃ u : 𝓗, u ≠ 0 ∧ innerSupremumOn C u < innerInfimumOn D u := Iff.rfl

/-- A point is separated from `D` when some nonzero normal vector bounds its evaluation by the
inner-product infimum on `D`. -/
def IsSeparatedFrom (x : 𝓗) (D : Set 𝓗) : Prop :=
  ∃ u : 𝓗, u ≠ 0 ∧ (⟪x, u⟫_ℝ : EReal) ≤ innerInfimumOn D u

/-- A point is separated from `D` exactly when its singleton is separated from `D`. -/
@[simp] theorem isSeparatedFrom_iff_singleton (x : 𝓗) (D : Set 𝓗) :
    IsSeparatedFrom x D ↔ AreSeparated ({x} : Set 𝓗) D := by
  rw [IsSeparatedFrom, areSeparated_iff_exists_nonzero]
  simp

/-- A point is strongly separated from `D` when some nonzero normal vector yields a strict gap
between its value at `x` and the inner-product infimum on `D`. -/
def IsStronglySeparatedFrom (x : 𝓗) (D : Set 𝓗) : Prop :=
  ∃ u : 𝓗, u ≠ 0 ∧ (⟪x, u⟫_ℝ : EReal) < innerInfimumOn D u

/-- A point is strongly separated from `D` exactly when its singleton is strongly separated from
`D`. -/
theorem isStronglySeparatedFrom_iff_singleton (x : 𝓗) (D : Set 𝓗) :
    IsStronglySeparatedFrom x D ↔ AreStronglySeparated ({x} : Set 𝓗) D := by
  rw [IsStronglySeparatedFrom, areStronglySeparated_iff_exists_nonzero]
  simp

/-! Source item: Chap03/Example_3_47 -/
noncomputable section


/-- The function `x ↦ 1 / (1 + |x|)` used in Example 3.47. -/
def inv_one_add_abs (x : ℝ) : ℝ :=
  1 / (1 + |x|)

/-- The set `C = {(x, r) ∈ ℝ² | 1 / (1 + |x|) ≤ r}` from Example 3.47, written as the canonical
epigraph of `x ↦ 1 / (1 + |x|)`. -/
abbrev epigraph_inv_one_add_abs : Set (ℝ × ℝ) :=
  epigraph fun x : ℝ ↦ (inv_one_add_abs x : EReal)

/-- Membership in the epigraph means that the second coordinate dominates `1 / (1 + |x|)`. -/
@[simp]
theorem mem_epigraph_inv_one_add_abs_iff (p : ℝ × ℝ) :
    p ∈ epigraph_inv_one_add_abs ↔ 1 / (1 + |p.1|) ≤ p.2 := by
  simpa [epigraph_inv_one_add_abs, inv_one_add_abs] using
    (mem_epigraph_iff (fun x : ℝ ↦ (inv_one_add_abs x : EReal)) p.1 p.2)

-- Proof sketch: the function `x ↦ 1 / (1 + |x|)` is continuous on `ℝ`, and the epigraph of a
-- continuous real-valued function over a closed domain is closed.
/-- The set `C = {(x, r) ∈ ℝ² | 1 / (1 + |x|) ≤ r}` from Example 3.47 is closed. -/
theorem isClosed_epigraph_inv_one_add_abs :
    IsClosed epigraph_inv_one_add_abs := by
  -- View the epigraph as a closed superlevel set of two continuous coordinate maps.
  have hcont :
      Continuous fun p : ℝ × ℝ ↦ 1 / (1 + |p.1|) := by
    simpa [one_div] using
      (continuous_const.add continuous_fst.abs).inv₀ (by
        intro p
        have hpos : 0 < 1 + |p.1| := by positivity
        exact ne_of_gt hpos)
  have hclosed : IsClosed {p : ℝ × ℝ | 1 / (1 + |p.1|) ≤ p.2} :=
    isClosed_le hcont continuous_snd
  convert hclosed using 1
  ext p
  exact mem_epigraph_inv_one_add_abs_iff p

/-- Helper for Example 3.47: every point of the epigraph has strictly positive second coordinate. -/
private lemma snd_pos_of_mem_epigraph_inv_one_add_abs (p : ℝ × ℝ)
    (hp : p ∈ epigraph_inv_one_add_abs) :
    0 < p.2 := by
  rw [mem_epigraph_inv_one_add_abs_iff] at hp
  have hden_pos : 0 < 1 + |p.1| := by positivity
  have hinv_pos : 0 < 1 / (1 + |p.1|) := by
    exact one_div_pos.mpr hden_pos
  -- The epigraph inequality bounds `p.2` below by a strictly positive quantity.
  linarith

/-- Helper for Example 3.47: every point of the open upper half-plane belongs to the convex hull of
the epigraph. -/
private lemma openUpperHalfPlane_subset_convexHull_epigraph_inv_one_add_abs (p : ℝ × ℝ)
    (hp : p ∈ Set.univ ×ˢ Set.Ioi (0 : ℝ)) :
    p ∈ convexHull ℝ epigraph_inv_one_add_abs := by
  rcases p with ⟨x, r⟩
  rcases Set.mem_prod.mp hp with ⟨_, hr_mem⟩
  rw [Set.mem_Ioi] at hr_mem
  let M : ℝ := max (|x| + 1) (1 / r)
  let t : ℝ := (M - x) / (2 * M)
  have hr : 0 < r := hr_mem
  have hMr : 1 / r ≤ M := by
    exact le_max_right (|x| + 1) (1 / r)
  have hM_pos : 0 < M := by
    have hr_inv_pos : 0 < 1 / r := one_div_pos.mpr hr
    exact lt_of_lt_of_le hr_inv_pos hMr
  have hx_abs_lt_M : |x| < M := by
    have hleft : |x| + 1 ≤ M := le_max_left (|x| + 1) (1 / r)
    linarith
  have hx_left : -M < x := by
    exact (abs_lt.mp hx_abs_lt_M).1
  have hx_right : x < M := by
    exact (abs_lt.mp hx_abs_lt_M).2
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
    have htwoM_pos : 0 < 2 * M := by positivity
    have hnum_nonneg : 0 ≤ M - x := by linarith
    have hnum_le : M - x ≤ 2 * M := by linarith
    refine ⟨?_, ?_⟩
    · exact div_nonneg hnum_nonneg (le_of_lt htwoM_pos)
    · exact (div_le_iff₀ htwoM_pos).2 (by simpa using hnum_le)
  have hsmall : 1 / (1 + M) < r := by
    have hden_pos : 0 < 1 + M := by linarith
    refine (one_div_lt hden_pos hr).2 ?_
    linarith
  have hM_abs : |M| = M := abs_of_nonneg (le_of_lt hM_pos)
  have hM_mem : (M, r) ∈ epigraph_inv_one_add_abs := by
    rw [mem_epigraph_inv_one_add_abs_iff]
    -- The right endpoint sits above the graph because `M` was chosen far enough out.
    exact le_of_lt (by
      simpa [hM_abs] using hsmall)
  have hnegM_mem : (-M, r) ∈ epigraph_inv_one_add_abs := by
    rw [mem_epigraph_inv_one_add_abs_iff]
    -- Symmetry of `|x|` gives the same estimate at `-M`.
    exact le_of_lt (by
      simpa [abs_neg, hM_abs] using hsmall)
  have hline :
      AffineMap.lineMap (M, r) (-M, r) t = (x, r) := by
    -- The chosen parameter places `(x, r)` on the segment joining `(M, r)` and `(-M, r)`.
    ext <;> simp [AffineMap.lineMap_apply_module, t]
    · field_simp [hM_pos.ne']
      ring
    · ring
  have hsegment :
      AffineMap.lineMap (M, r) (-M, r) t ∈ convexHull ℝ epigraph_inv_one_add_abs := by
    -- Convexity of the hull keeps the whole segment between the two epigraph points.
    exact
      (convex_convexHull ℝ epigraph_inv_one_add_abs).lineMap_mem
        (subset_convexHull ℝ epigraph_inv_one_add_abs hM_mem)
        (subset_convexHull ℝ epigraph_inv_one_add_abs hnegM_mem)
        ht_mem
  simpa [hline] using hsegment

-- Proof sketch: every point of the epigraph has strictly positive second coordinate, so the convex
-- hull lies in the open upper half-plane. Conversely, for `(x, r)` with `r > 0`, combine two
-- far-out epigraph points above `±M` to obtain a convex-hull point with second coordinate below
-- `r`, then use the upward-closed nature of the epigraph in the second coordinate.
/-- The convex hull of the closure of the epigraph is the open upper half-plane. -/
theorem convexHull_closure_epigraph_inv_one_add_abs_eq_openUpperHalfPlane :
    convexHull ℝ (closure epigraph_inv_one_add_abs) = Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
  -- Route correction: identify the convex hull by two inclusions, using closedness first and
  -- then the explicit symmetric segment construction.
  apply le_antisymm
  · rw [isClosed_epigraph_inv_one_add_abs.closure_eq]
    refine convexHull_min ?_ ?_
    · intro p hp
      rw [Set.mem_prod, Set.mem_Ioi]
      exact ⟨by simp, snd_pos_of_mem_epigraph_inv_one_add_abs p hp⟩
    · exact convex_univ.prod (convex_Ioi (0 : ℝ))
  · intro p hp
    rw [isClosed_epigraph_inv_one_add_abs.closure_eq]
    exact openUpperHalfPlane_subset_convexHull_epigraph_inv_one_add_abs p hp

-- Proof sketch: identify the convex hull using the previous theorem and take closures; the closure
-- of the open upper half-plane is the closed upper half-plane.
/-- The closure of the convex hull of the epigraph is the closed upper half-plane. -/
theorem closure_convexHull_epigraph_inv_one_add_abs_eq_closedUpperHalfPlane :
    closure (convexHull ℝ epigraph_inv_one_add_abs) = Set.univ ×ˢ Set.Ici (0 : ℝ) := by
  -- Rewrite the convex hull using the previous theorem and then close the open upper half-plane.
  calc
    closure (convexHull ℝ epigraph_inv_one_add_abs)
        = closure (convexHull ℝ (closure epigraph_inv_one_add_abs)) := by
            rw [isClosed_epigraph_inv_one_add_abs.closure_eq]
    _ = closure (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
          rw [convexHull_closure_epigraph_inv_one_add_abs_eq_openUpperHalfPlane]
    _ = Set.univ ×ˢ Set.Ici (0 : ℝ) := by
          rw [closure_prod_eq, closure_univ, closure_Ioi]

-- Proof sketch: combine the explicit descriptions of the two sets above and note that
-- `Set.univ ×ˢ Set.Ioi (0 : ℝ)` and `Set.univ ×ˢ Set.Ici (0 : ℝ)` are different.
/-- Example 3.47: for the closed set
`C = {(x, r) ∈ ℝ² | 1 / (1 + |x|) ≤ r}`, one has
`convexHull ℝ (closure C) ≠ closure (convexHull ℝ C)`. -/
theorem convexHull_closure_ne_closure_convexHull_of_epigraph_inv_one_add_abs :
    convexHull ℝ (closure epigraph_inv_one_add_abs) ≠
      closure (convexHull ℝ epigraph_inv_one_add_abs) := by
  intro hEq
  have horigin_mem :
      ((0 : ℝ), (0 : ℝ)) ∈ closure (convexHull ℝ epigraph_inv_one_add_abs) := by
    -- The origin lies in the closed upper half-plane description of the closure.
    rw [closure_convexHull_epigraph_inv_one_add_abs_eq_closedUpperHalfPlane]
    simp
  have horigin_mem_left :
      ((0 : ℝ), (0 : ℝ)) ∈ convexHull ℝ (closure epigraph_inv_one_add_abs) := by
    simpa [hEq] using horigin_mem
  have horigin_not_mem :
      ((0 : ℝ), (0 : ℝ)) ∉ convexHull ℝ (closure epigraph_inv_one_add_abs) := by
    -- The origin is excluded from the open upper half-plane description of the convex hull.
    rw [convexHull_closure_epigraph_inv_one_add_abs_eq_openUpperHalfPlane]
    simp
  exact horigin_not_mem horigin_mem_left

end

/-! Source item: Chap03/Theorem_3_50 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : Set 𝓗}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

/-- Helper for Theorem 3.50: the projection variational inequality rewrites to a support bound at
the projection point. -/
private lemma projectionPoint_support_upper_bound {x y : 𝓗} (hy : y ∈ C) :
    ⟪y, x - P x⟫_ℝ ≤ ⟪P x, x - P x⟫_ℝ := by
  -- Read off the projection inequality at `P x`.
  have hprojection :
      P x ∈ C ∧ ∀ z ∈ C, ⟪z - P x, x - P x⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mp rfl
  have hy_nonpos : ⟪y - P x, x - P x⟫_ℝ ≤ 0 := hprojection.2 y hy
  have hrewrite :
      ⟪y - P x, x - P x⟫_ℝ = ⟪y, x - P x⟫_ℝ - ⟪P x, x - P x⟫_ℝ := by
    rw [inner_sub_left]
  rw [hrewrite] at hy_nonpos
  linarith

omit [CompleteSpace 𝓗] in
/-- Helper for Theorem 3.50: a pointwise upper bound on `⟪y, u⟫` over `C` bounds
`innerSupremumOn C u`. -/
private lemma innerSupremumOn_le_of_forall_inner_le {u : 𝓗} {a : ℝ}
    (hbound : ∀ y ∈ C, ⟪y, u⟫_ℝ ≤ a) :
    innerSupremumOn C u ≤ (a : EReal) := by
  -- Rewrite the support functional as the supremum of the image and show `a` is an upper bound.
  rw [innerSupremumOn_eq_sSup_image]
  refine (isLUB_sSup _).2 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact show ((⟪y, u⟫_ℝ : EReal) ≤ (a : EReal)) by
    exact_mod_cast hbound y hy

/-- Helper for Theorem 3.50: if `x ∉ C`, then the residual from `x` to its projection on `C` is
nonzero. -/
private lemma projectionPoint_residual_ne_zero {x : 𝓗} (hx : x ∉ C) :
    x - P x ≠ 0 := by
  -- Otherwise `x` would coincide with its projection, which lies in `C`.
  intro hu_zero
  have hPx_mem : P x ∈ C := by
    exact
      projectionPoint_mem C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  have hx_eq : x = P x := sub_eq_zero.mp hu_zero
  exact hx (hx_eq.symm ▸ hPx_mem)

/-- Helper for Theorem 3.50: the projection residual creates a strict gap between evaluation at
the projection point and evaluation at `x`. -/
private lemma projectionPoint_support_strict_gap {x : 𝓗} (hx : x ∉ C) :
    ⟪P x, x - P x⟫_ℝ < ⟪x, x - P x⟫_ℝ := by
  -- The point `x` decomposes as its projection plus the residual, and the extra term is `‖u‖^2`.
  have hu_ne : x - P x ≠ 0 :=
    projectionPoint_residual_ne_zero hC_nonempty hC_closed hC_convex hx
  have hnorm_sq_pos : 0 < ‖x - P x‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hu_ne) 2
  have hlt :
      ⟪P x, x - P x⟫_ℝ < ⟪P x, x - P x⟫_ℝ + ‖x - P x‖ ^ 2 := by
    linarith
  calc
    ⟪P x, x - P x⟫_ℝ < ⟪P x, x - P x⟫_ℝ + ‖x - P x‖ ^ 2 := hlt
    _ = ⟪x, x - P x⟫_ℝ := by
        calc
          ⟪P x, x - P x⟫_ℝ + ‖x - P x‖ ^ 2
              = ⟪P x, x - P x⟫_ℝ + ⟪x - P x, x - P x⟫_ℝ := by
                  rw [real_inner_self_eq_norm_sq]
          _ = ⟪P x + (x - P x), x - P x⟫_ℝ := by
                rw [inner_add_left]
          _ = ⟪x, x - P x⟫_ℝ := by
                congr 1
                abel_nf

-- Proof sketch: let `p := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty
-- hC_closed hC_convex) x` and set `u := x - p`. Since `x ∉ C`, one has `u ≠ 0`. The variational
-- characterization of projections gives `⟪y - p, x - p⟫_ℝ ≤ 0` for every `y ∈ C`, which rewrites
-- to `⟪y, u⟫_ℝ ≤ ⟪p, u⟫_ℝ < ⟪x, u⟫_ℝ`; this yields strict separation of `C` and `{x}`.
/-- Theorem 3.50: a point outside a nonempty closed convex set is strongly separated from that set
in the orientation used by `AreStronglySeparated C ({x} : Set 𝓗)`. -/
theorem areStronglySeparated_singleton_of_nonempty_isClosed_convex_of_not_mem {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : 𝓗}
    (hx : x ∉ C) :
    AreStronglySeparated C ({x} : Set 𝓗) := by
  -- Use the projection residual as the separating normal vector.
  let p :=
    projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  let u := x - p
  have hu_ne : u ≠ 0 := by
    simpa [u, p] using
      projectionPoint_residual_ne_zero hC_nonempty hC_closed hC_convex hx
  refine ⟨u, hu_ne, ?_⟩
  have hsup_le :
      innerSupremumOn C u ≤ (⟪p, u⟫_ℝ : EReal) := by
    -- The variational inequality bounds every support value by the value at the projection point.
    refine innerSupremumOn_le_of_forall_inner_le fun y hy ↦ ?_
    simpa [u, p] using
      projectionPoint_support_upper_bound hC_nonempty hC_closed hC_convex hy
  have hgap : ⟪p, u⟫_ℝ < ⟪x, u⟫_ℝ := by
    -- The residual contributes the strictly positive term `‖x - P x‖^2`.
    simpa [u, p] using
      projectionPoint_support_strict_gap hC_nonempty hC_closed hC_convex hx
  rw [innerInfimumOn_singleton x u]
  exact lt_of_le_of_lt hsup_le (by exact_mod_cast hgap)

-- Proof sketch: let `p := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty
-- hC_closed hC_convex) x` and `u := x - p`. Since `x ∉ C`, one has `u ≠ 0`. For every `y ∈ C`,
-- the projection inequality `⟪y - p, x - p⟫_ℝ ≤ 0` implies
-- `⟪y - x, u⟫_ℝ = ⟪y - p, u⟫_ℝ - ‖u‖ ^ 2 ≤ -‖u‖ ^ 2 < 0`; equivalently
-- `innerSupremumOn C u < ⟪x, u⟫_ℝ`.
/-- Theorem 3.50: if `C` is a nonempty closed convex subset of a real Hilbert space and `x ∉ C`,
then there is a nonzero vector `u` with `sup_{y ∈ C} ⟪y, u⟫_ℝ < ⟪x, u⟫_ℝ`, equivalently
`sup_{y ∈ C} ⟪y - x, u⟫_ℝ < 0`. -/
theorem exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
    {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : 𝓗} (hx : x ∉ C) :
    ∃ u : 𝓗,
      u ≠ 0 ∧ innerSupremumOn C u < (⟪x, u⟫_ℝ : EReal) := by
  rcases areStronglySeparated_singleton_of_nonempty_isClosed_convex_of_not_mem
      hC_nonempty hC_closed hC_convex hx with ⟨u, hu, hsep⟩
  exact ⟨u, hu, by simpa using hsep⟩

end

/-! Source item: Chap03/Corollary_3_51 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Corollary 3.51: disjointness of `C` and `D` forces `0` to lie outside the
Minkowski difference `C - D`. -/
private lemma zero_not_mem_sub_of_disjoint {C D : Set 𝓗} (hCD : Disjoint C D) :
    (0 : 𝓗) ∉ C - D := by
  intro h0
  rcases Set.mem_sub.mp h0 with ⟨c, hc, d, hd, hcd⟩
  have hEq : c = d := sub_eq_zero.mp hcd
  exact hCD.le_bot ⟨hc, hEq ▸ hd⟩

omit [CompleteSpace 𝓗] in
/-- Helper for Corollary 3.51: a strict negative upper bound on `⟪z, u⟫` over `C - D` yields a
uniform positive margin between the support values on `C` and `D`. -/
private lemma pointwise_margin_of_sub_upper_bound {C D : Set 𝓗} {u : 𝓗} {ε : ℝ}
    (hbound : ∀ z ∈ C - D, ⟪z, u⟫_ℝ < -ε) :
    ∀ c ∈ C, ∀ d ∈ D, (⟪c, u⟫_ℝ : EReal) + ε ≤ (⟪d, u⟫_ℝ : EReal) := by
  intro c hc d hd
  have hmem : c - d ∈ C - D := Set.mem_sub.mpr ⟨c, hc, d, hd, rfl⟩
  have hlt : ⟪c - d, u⟫_ℝ < -ε := hbound (c - d) hmem
  have hle : ⟪c, u⟫_ℝ + ε ≤ ⟪d, u⟫_ℝ := by
    rw [inner_sub_left] at hlt
    linarith
  have hcast : (((⟪c, u⟫_ℝ + ε : ℝ) : EReal) ≤ (⟪d, u⟫_ℝ : EReal)) := by
    exact_mod_cast hle
  simpa [EReal.coe_add] using hcast

omit [CompleteSpace 𝓗] in
/-- Helper for Corollary 3.51: a uniform positive inner-product margin forces strong separation in
the support-function formulation from Definition 3.49. -/
private lemma areStronglySeparated_of_uniform_inner_margin {C D : Set 𝓗} {u : 𝓗} {ε : ℝ}
    (hC : C.Nonempty) (hD : D.Nonempty) (hε : 0 < ε)
    (hmargin : ∀ c ∈ C, ∀ d ∈ D, (⟪c, u⟫_ℝ : EReal) + ε ≤ (⟪d, u⟫_ℝ : EReal)) :
    AreStronglySeparated C D := by
  have hu_ne : u ≠ 0 := by
    intro hu0
    obtain ⟨c, hc⟩ := hC
    obtain ⟨d, hd⟩ := hD
    have h : ((0 : ℝ) : EReal) + ε ≤ (0 : EReal) := by
      simpa [hu0] using hmargin c hc d hd
    have hε' : ((0 : ℝ) : EReal) < ε := by
      exact_mod_cast hε
    exact (not_le_of_gt hε') (by simpa using h)
  refine ⟨u, hu_ne, ?_⟩
  let S : Set EReal := (fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C
  let T : Set EReal := (fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' D
  have hε_ne_top : ((ε : ℝ) : EReal) ≠ ⊤ := by simp
  have hε_ne_bot : ((ε : ℝ) : EReal) ≠ ⊥ := by simp
  have hnegε_ne_top : ((-ε : ℝ) : EReal) ≠ ⊤ := by simp
  have hsup_bound : sSup S ≤ sInf T - ε := by
    refine (isLUB_sSup S).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    refine (EReal.le_sub_iff_add_le (Or.inl hε_ne_bot) (Or.inl hε_ne_top)).2 ?_
    refine (isGLB_sInf T).2 ?_
    rintro _ ⟨d, hd, rfl⟩
    exact hmargin c hc d hd
  have hsup_margin : sSup S + ε ≤ sInf T := EReal.add_le_of_le_sub hsup_bound
  obtain ⟨c0, hc0⟩ := hC
  obtain ⟨d0, hd0⟩ := hD
  have hsSup_upper : sSup S ≤ (⟪d0, u⟫_ℝ : EReal) - ε := by
    refine (isLUB_sSup S).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact (EReal.le_sub_iff_add_le (Or.inl hε_ne_bot) (Or.inl hε_ne_top)).2 (hmargin c hc d0 hd0)
  have hinner_d0_ne_top : (⟪d0, u⟫_ℝ : EReal) ≠ ⊤ := by simp
  have hsSup_upper_ne_top : ((⟪d0, u⟫_ℝ : EReal) - ε) ≠ ⊤ := by
    have hfinite : (⟪d0, u⟫_ℝ : EReal) + (-ε : EReal) ≠ ⊤ :=
      EReal.add_ne_top hinner_d0_ne_top hnegε_ne_top
    simpa [sub_eq_add_neg] using hfinite
  have hsSup_ne_top : sSup S ≠ ⊤ :=
    ne_top_of_le_ne_top hsSup_upper_ne_top hsSup_upper
  have hsSup_ne_bot : sSup S ≠ ⊥ := by
    have : (⟪c0, u⟫_ℝ : EReal) ≤ sSup S := le_sSup ⟨c0, hc0, rfl⟩
    exact ne_bot_of_le_ne_bot (by simp) this
  have hsInf_lower : (⟪c0, u⟫_ℝ : EReal) + ε ≤ sInf T := by
    refine (isGLB_sInf T).2 ?_
    rintro _ ⟨d, hd, rfl⟩
    exact hmargin c0 hc0 d hd
  have hsInf_ne_top : sInf T ≠ ⊤ :=
    ne_top_of_le_ne_top hinner_d0_ne_top (sInf_le ⟨d0, hd0, rfl⟩)
  have hinner_c0_margin_ne_bot : (⟪c0, u⟫_ℝ : EReal) + ε ≠ ⊥ :=
    EReal.add_ne_bot_iff.2 ⟨by simp, hε_ne_bot⟩
  have hsInf_ne_bot : sInf T ≠ ⊥ :=
    ne_bot_of_le_ne_bot hinner_c0_margin_ne_bot hsInf_lower
  have hsSup_plus_ne_bot : sSup S + ε ≠ ⊥ :=
    EReal.add_ne_bot_iff.2 ⟨hsSup_ne_bot, hε_ne_bot⟩
  have h' : (sSup S + ε).toReal ≤ (sInf T).toReal :=
    EReal.toReal_le_toReal hsup_margin hsSup_plus_ne_bot hsInf_ne_top
  have hadd : (sSup S + ε).toReal = (sSup S).toReal + ε :=
    EReal.toReal_add hsSup_ne_top hsSup_ne_bot hε_ne_top hε_ne_bot
  have hreal : (sSup S).toReal + ε ≤ (sInf T).toReal := by
    simpa [hadd] using h'
  have hlt_real : (sSup S).toReal < (sInf T).toReal :=
    lt_of_lt_of_le (lt_add_of_pos_right _ hε) hreal
  rw [innerSupremumOn_eq_sSup_image, innerInfimumOn_eq_sInf_image]
  change sSup S < sInf T
  rw [← EReal.coe_toReal hsSup_ne_top hsSup_ne_bot, ← EReal.coe_toReal hsInf_ne_top hsInf_ne_bot]
  exact_mod_cast hlt_real

-- Proof sketch: the set `C - D` is a closed convex subset that does not contain `0`, since
-- `Disjoint C D` rules out writing `0 = c - d` with `c ∈ C` and `d ∈ D`. Apply the closed-point
-- strong separation theorem to `0` and `C - D`, then rewrite the resulting strict inequality on
-- `c - d` as a strict gap between the support functionals of `C` and `D`.
/-- Corollary 3.51: if nonempty subsets `C` and `D` of a real Hilbert space are disjoint and their
Minkowski difference `C - D` is closed and convex, then `C` and `D` are strongly separated. -/
theorem areStronglySeparated_of_disjoint_of_isClosed_of_convex_sub {C D : Set 𝓗}
    (hC : C.Nonempty) (hD : D.Nonempty) (hCD : Disjoint C D) (hclosed : IsClosed (C - D))
    (hconvex : Convex ℝ (C - D)) : AreStronglySeparated C D := by
  have h0not : (0 : 𝓗) ∉ C - D := zero_not_mem_sub_of_disjoint hCD
  obtain ⟨f, β, hsub, hβ0⟩ := geometric_hahn_banach_closed_point hconvex hclosed h0not
  let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm f
  let ε : ℝ := -β
  have hβ : β < 0 := by
    simpa using hβ0
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hbound : ∀ z ∈ C - D, ⟪z, u⟫_ℝ < -ε := by
    intro z hz
    have hz' : f z < β := hsub z hz
    have hz'' : ⟪u, z⟫_ℝ < -ε := by
      simpa [u, ε] using hz'
    simpa [real_inner_comm] using hz''
  exact areStronglySeparated_of_uniform_inner_margin hC hD hε
    (pointwise_margin_of_sub_upper_bound hbound)

/-! Source item: Chap03/Corollary_3_52 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Corollary 3.52: two nonempty closed convex disjoint subsets of a real Hilbert space are
strongly separated whenever the second set is bounded. -/
-- Proof sketch: `C - D` is closed because it is the Minkowski sum `C + (-D)` of a closed convex
-- set with a bounded closed convex set, and it is convex because both `C` and `D` are convex.
-- Apply Corollary 3.51 to the closed convex difference set.
theorem areStronglySeparated_of_nonempty_isClosed_convex_disjoint_bounded
    {C D : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hCD : Disjoint C D) (hD_bounded : Bornology.IsBounded D) :
    AreStronglySeparated C D := by
  refine
    areStronglySeparated_of_disjoint_of_isClosed_of_convex_sub
      hC_nonempty hD_nonempty hCD ?_ ?_
  · simpa [sub_eq_add_neg] using
      isClosed_minkowski_sum_of_isBounded hC_closed hC_convex
        hD_closed.neg hD_convex.neg hD_bounded.neg
  · simpa using hC_convex.sub hD_convex

/-! Source item: Chap03/Theorem_3_53 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

omit [FiniteDimensional ℝ 𝓗] in
/-- Helper for Theorem 3.53: any nonzero vector with pointwise strict separation can be normalized
to unit norm while preserving those strict inequalities. -/
private lemma unit_separator_of_pointwise_strict {C D : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (hpoint : ∃ u : 𝓗, ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ < ⟪y, u⟫_ℝ) :
    ∃ v : 𝓗, ‖v‖ = 1 ∧ ∀ x ∈ C, ∀ y ∈ D, ⟪x, v⟫_ℝ < ⟪y, v⟫_ℝ := by
  -- Extract a pointwise strict separator and show it is nonzero by evaluating it on one pair of points.
  rcases hpoint with ⟨u, hu_point⟩
  obtain ⟨x0, hx0⟩ := hC_nonempty
  obtain ⟨y0, hy0⟩ := hD_nonempty
  have hu_ne : u ≠ 0 := by
    intro hu0
    have : (0 : ℝ) < 0 := by
      simpa [hu0] using hu_point x0 hx0 y0 hy0
    exact lt_irrefl _ this
  -- Rescale the normal vector to norm one; positivity of the scale preserves the strict inequalities.
  let v : 𝓗 := ‖u‖⁻¹ • u
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hv_norm : ‖v‖ = 1 := by
    simp [v, norm_smul, hnorm_pos.ne']
  refine ⟨v, hv_norm, ?_⟩
  intro x hx y hy
  have hu_lt : ⟪x, u⟫_ℝ < ⟪y, u⟫_ℝ := hu_point x hx y hy
  simp only [v, inner_smul_right]
  nlinarith [hu_lt, inv_pos.mpr hnorm_pos]

omit [FiniteDimensional ℝ 𝓗] in
/-- Helper for Theorem 3.53: eventual strict separation inequalities along a convergent subsequence
pass to a weak inequality at the limit. -/
private lemma inner_le_of_eventually_lt_along_subseq {v : ℕ → 𝓗} {φ : ℕ → ℕ} {u x y : 𝓗}
    (hvu : Tendsto (fun n ↦ v (φ n)) atTop (nhds u))
    (hevent : ∀ᶠ n in atTop, ⟪x, v (φ n)⟫_ℝ < ⟪y, v (φ n)⟫_ℝ) :
    ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
  -- Apply continuity of the inner product to both coordinate functionals.
  have hx_tendsto : Tendsto (fun n ↦ ⟪x, v (φ n)⟫_ℝ) atTop (nhds ⟪x, u⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto u).comp hvu
  have hy_tendsto : Tendsto (fun n ↦ ⟪y, v (φ n)⟫_ℝ) atTop (nhds ⟪y, u⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto u).comp hvu
  -- The order is closed, so eventual strict inequalities yield a weak inequality at the limit.
  exact le_of_tendsto_of_tendsto hx_tendsto hy_tendsto (hevent.mono fun n hn ↦ hn.le)

-- Proof sketch: intersect `D` with larger and larger closed balls to obtain nonempty compact convex
-- truncations, separate `C` from each truncation by the compact/closed separation theorem, and then
-- extract a convergent subsequence of unit normal vectors using finite dimensionality.
/-- Theorem 3.53: in a finite-dimensional real Hilbert space, two nonempty closed convex sets with
empty intersection are separated in the sense of `AreSeparated`. -/
theorem finiteDimensional_closed_convex_areSeparated_of_disjoint
    {C D : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hCD : Disjoint C D) :
    AreSeparated C D := by
  classical
  obtain ⟨y0, hy0D⟩ := hD_nonempty
  let Dn : ℕ → Set 𝓗 := fun n ↦ D ∩ Metric.closedBall y0 (n : ℝ)
  -- Exhaust `D` by bounded closed convex truncations centered at a fixed point of `D`.
  have hDn_nonempty : ∀ n, (Dn n).Nonempty := by
    intro n
    refine ⟨y0, hy0D, ?_⟩
    simp [Metric.mem_closedBall]
  have hDn_closed : ∀ n, IsClosed (Dn n) := by
    intro n
    exact hD_closed.inter
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall y0 (n : ℝ)))
  have hDn_convex : ∀ n, Convex ℝ (Dn n) := by
    intro n
    exact hD_convex.inter (convex_closedBall y0 (n : ℝ))
  have hDn_compact : ∀ n, IsCompact (Dn n) := by
    intro n
    exact (isCompact_closedBall y0 (n : ℝ)).of_isClosed_subset (hDn_closed n) fun z hz ↦ hz.2
  have hDn_disjoint : ∀ n, Disjoint C (Dn n) := by
    intro n
    exact hCD.inter_right (Metric.closedBall y0 (n : ℝ))
  -- Apply mathlib's compact/closed Hahn-Banach separation theorem to each truncation, then convert
  -- the separating functional to an inner-product vector using Riesz representation.
  have hstrict : ∀ n, ∃ u : 𝓗, ∀ x ∈ C, ∀ y ∈ Dn n, ⟪x, u⟫_ℝ < ⟪y, u⟫_ℝ := by
    intro n
    obtain ⟨f, a, b, hCside, hab, hDside⟩ :=
      geometric_hahn_banach_closed_compact hC_convex hC_closed (hDn_convex n) (hDn_compact n)
        (hDn_disjoint n)
    let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm f
    refine ⟨u, ?_⟩
    intro x hx y hy
    have hxy : f x < f y := lt_trans (hCside x hx) (lt_trans hab (hDside y hy))
    have hx_eval : f x = ⟪u, x⟫_ℝ := by
      simp [u]
    have hy_eval : f y = ⟪u, y⟫_ℝ := by
      simp [u]
    have hu_lt : ⟪u, x⟫_ℝ < ⟪u, y⟫_ℝ := by
      simpa [hx_eval, hy_eval] using hxy
    change ⟪x, u⟫_ℝ < ⟪y, u⟫_ℝ
    rw [real_inner_comm u x, real_inner_comm u y]
    exact hu_lt
  choose v hv_norm hv_lt using fun n ↦
    unit_separator_of_pointwise_strict hC_nonempty (hDn_nonempty n) (hstrict n)
  have hv_mem : ∀ n, v n ∈ Metric.closedBall (0 : 𝓗) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [hv_norm n]
  -- Extract a convergent subsequence of unit normals from the bounded sequence.
  obtain ⟨u, -, φ, hφmono, hφtendsto⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hv_mem
  have hu_norm : ‖u‖ = 1 := by
    have hnorm_tendsto : Tendsto (fun n ↦ ‖v (φ n)‖) atTop (nhds ‖u‖) := hφtendsto.norm
    have hconst : Tendsto (fun n ↦ ‖v (φ n)‖) atTop (nhds 1) := by
      refine tendsto_const_nhds.congr' ?_
      exact Filter.Eventually.of_forall fun n ↦ by simp [hv_norm (φ n)]
    exact tendsto_nhds_unique hnorm_tendsto hconst
  have hu_ne : u ≠ 0 := by
    intro hu0
    simp [hu0] at hu_norm
  -- For fixed `x ∈ C` and `y ∈ D`, the truncations eventually contain `y`, so the strict
  -- subsequence inequalities pass to the limit.
  have hlimit : ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
    intro x hx y hy
    have hy_event : ∀ᶠ n in atTop, y ∈ Dn (φ n) := by
      let N : ℕ := ⌈dist y0 y⌉₊
      filter_upwards [eventually_ge_atTop N] with n hn
      change y ∈ D ∩ Metric.closedBall y0 (φ n : ℝ)
      refine ⟨hy, ?_⟩
      rw [Metric.mem_closedBall, dist_comm]
      calc
        dist y0 y ≤ N := Nat.le_ceil _
        _ ≤ n := by exact_mod_cast hn
        _ ≤ φ n := by exact_mod_cast (hφmono.id_le n)
    have hstrict_event : ∀ᶠ n in atTop, ⟪x, v (φ n)⟫_ℝ < ⟪y, v (φ n)⟫_ℝ := by
      exact hy_event.mono fun n hyn ↦ hv_lt (φ n) x hx y hyn
    exact inner_le_of_eventually_lt_along_subseq hφtendsto hstrict_event
  -- Convert the pointwise inequalities for the limit vector into the definition of separation.
  exact areSeparated_of_forall_inner_le hu_ne hlimit

/-! Source item: Chap03/Proposition_3_54 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

noncomputable section

/- Helper for Proposition 3.54: an infinite-dimensional Hilbert space contains closed linear
subspaces with nonclosed sum. -/
private lemma exists_closed_subspaces_with_nonclosed_sup
    (hinfdim : ¬ FiniteDimensional ℝ 𝓗) :
    ∃ C D : Submodule ℝ 𝓗,
      IsClosed (C : Set 𝓗) ∧ IsClosed (D : Set 𝓗) ∧
      Disjoint C D ∧ ¬ IsClosed (((C ⊔ D : Submodule ℝ 𝓗) : Set 𝓗)) := by
  -- Isolate the infinite-dimensional input by instantiating Example 3.41 with a concrete angle
  -- sequence whose squared sines are summable.
  obtain ⟨e, he⟩ := exists_orthonormal_sequence_of_not_finiteDimensional hinfdim
  let θ : ℕ → ℝ := fun n ↦ ((1 : ℝ) / 2) ^ (n + 1)
  have hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
    intro n
    constructor
    · dsimp [θ]
      positivity
    · have hθ_le_one : θ n ≤ 1 := by
        dsimp [θ]
        exact pow_le_one₀ (by norm_num) (by norm_num : ((1 : ℝ) / 2) ≤ 1)
      linarith [Real.pi_gt_three, hθ_le_one]
  have hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2) := by
    have hθ_summable : Summable θ := by
      have hgeom :
          Summable (fun n : ℕ ↦ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n)) :=
        Summable.mul_left _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      convert hgeom using 1
      ext n
      simp [θ, pow_succ, mul_comm]
    refine Summable.of_nonneg_of_le (fun n ↦ sq_nonneg _) ?_ hθ_summable
    intro n
    have hθ_nonneg : 0 ≤ θ n := (hθ n).1.le
    have hθ_le_one : θ n ≤ 1 := by
      dsimp [θ]
      exact pow_le_one₀ (by norm_num) (by norm_num : ((1 : ℝ) / 2) ≤ 1)
    calc
      Real.sin (θ n) ^ 2 ≤ θ n ^ 2 := Real.sin_sq_le_sq
      _ ≤ θ n := by nlinarith
  refine ⟨even_indexed_closed_span e, rotated_even_odd_closed_span e θ, ?_, ?_, ?_, ?_⟩
  · exact isClosed_even_indexed_closed_span e
  · exact isClosed_rotated_even_odd_closed_span e θ
  · exact disjoint_even_indexed_closed_span_rotated_even_odd_closed_span e θ he hθ
  · exact not_isClosed_sup_even_indexed_closed_span_rotated_even_odd_closed_span
      e θ he hθ hθ_square_summable

/- Helper for Proposition 3.54: membership in `C ⊔ Sᗮ` is equivalent to the projection onto the
closed sum `S = closure (C ⊔ D)` lying in `C`. -/
private lemma mem_left_counterexample_iff_starProjection_mem_base
    (C D : Submodule ℝ 𝓗) (x : 𝓗) :
    let S : Submodule ℝ 𝓗 := (C ⊔ D).topologicalClosure
    x ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) ↔ S.starProjection x ∈ C := by
  -- The decomposition `x = proj_S x + (x - proj_S x)` separates the `S` and `Sᗮ` directions.
  dsimp
  have hC_le : C ≤ (C ⊔ D).topologicalClosure :=
    le_trans le_sup_left (Submodule.le_topologicalClosure _)
  constructor
  · intro hx
    rw [Submodule.mem_sup] at hx
    rcases hx with ⟨c, hc, w, hw, rfl⟩
    have hproj : ((C ⊔ D).topologicalClosure).starProjection (c + w) = c := by
      exact ((C ⊔ D).topologicalClosure).eq_starProjection_of_mem_orthogonal (hC_le hc)
        (by simpa [Submodule.orthogonal_closure] using hw)
    simpa [hproj] using hc
  · intro hx
    rw [Submodule.mem_sup]
    refine ⟨((C ⊔ D).topologicalClosure).starProjection x, hx,
      x - ((C ⊔ D).topologicalClosure).starProjection x,
      ((C ⊔ D).topologicalClosure).sub_starProjection_mem_orthogonal x, by abel_nf⟩

/- Helper for Proposition 3.54: if a linear functional is bounded above on the whole line
`ℝ • a`, then it vanishes on that direction. -/
private lemma inner_eq_zero_of_line_upper_bound {a c : ℝ}
    (hbound : ∀ t : ℝ, t * a ≤ c) : a = 0 := by
  -- A nonzero slope would let us choose a scalar that violates the uniform upper bound.
  by_contra ha
  have hne : a ≠ 0 := ha
  have hsign : 0 < a ∨ a < 0 := lt_or_gt_of_ne hne.symm
  rcases hsign with hpos | hneg
  · have h := hbound (c / a + 1)
    have hcalc : (c / a + 1) * a = c + a := by
      field_simp [hne]
    rw [hcalc] at h
    linarith
  · have h := hbound (c / a - 1)
    have hcalc : (c / a - 1) * a = c - a := by
      field_simp [hne]
    rw [hcalc] at h
    linarith

-- Proof sketch: choose closed linear subspaces `C` and `D` with nonclosed sum `C + D`, then pick
-- `z ∈ closure (C + D) \ (C + D)` and define `U := C + (C + D)ᗮ` and `V := z + D`. These affine
-- subspaces are closed and disjoint, while `U - V` is dense in `𝓗`, forcing every separating
-- normal vector to vanish.
/-- Proposition 3.54: an infinite-dimensional real Hilbert space contains disjoint closed affine
subspaces that are not separated. -/
theorem exists_disjoint_closed_affineSubspaces_not_separated
    (hinfdim : ¬ FiniteDimensional ℝ 𝓗) :
    ∃ U V : AffineSubspace ℝ 𝓗,
      IsClosed (U : Set 𝓗) ∧ IsClosed (V : Set 𝓗) ∧
      Disjoint (U : Set 𝓗) (V : Set 𝓗) ∧ ¬ AreSeparated (U : Set 𝓗) (V : Set 𝓗) := by
  -- Route correction: work from a nonclosed linear sum, then separate the closure direction `S`
  -- from its orthogonal complement instead of chasing a direct density computation for `U - V`.
  obtain ⟨C, D, hC_closed, hD_closed, hCD_disjoint, hCD_nonclosed⟩ :=
    exists_closed_subspaces_with_nonclosed_sup hinfdim
  let S : Submodule ℝ 𝓗 := (C ⊔ D).topologicalClosure
  have hS_closed : IsClosed (S : Set 𝓗) := by
    simp [S]
  have hC_le_S : C ≤ S := le_trans le_sup_left (Submodule.le_topologicalClosure _)
  have hD_le_S : D ≤ S := le_trans le_sup_right (Submodule.le_topologicalClosure _)
  obtain ⟨z, hzS, hz_not_mem⟩ : ∃ z : 𝓗, z ∈ S ∧ z ∉ C ⊔ D := by
    -- If every point of the closure belonged to `C ⊔ D`, that sum would already be closed.
    by_contra hz_fail
    have hS_le : S ≤ C ⊔ D := by
      intro x hx
      by_contra hx_not
      exact hz_fail ⟨x, hx, hx_not⟩
    have hS_eq : S = C ⊔ D := le_antisymm hS_le (Submodule.le_topologicalClosure _)
    exact hCD_nonclosed (by simpa [S, hS_eq] using Submodule.isClosed_topologicalClosure (C ⊔ D))
  let U : AffineSubspace ℝ 𝓗 := (C ⊔ Sᗮ).toAffineSubspace
  let V : AffineSubspace ℝ 𝓗 := z +ᵥ D.toAffineSubspace
  refine ⟨U, V, ?_, ?_, ?_, ?_⟩
  · -- The left affine subspace is the preimage of the closed set `C` under the continuous
    -- projection onto `S`.
    have hclosed_subspace : IsClosed ((C ⊔ Sᗮ : Submodule ℝ 𝓗) : Set 𝓗) := by
      convert hC_closed.preimage S.starProjection.continuous using 1
      ext x
      simpa [Set.mem_preimage, S] using
        (mem_left_counterexample_iff_starProjection_mem_base C D x)
    simpa [U] using hclosed_subspace
  · -- The right affine subspace is a translate of the closed linear subspace `D`.
    simpa [V, AffineSubspace.coe_pointwise_vadd] using
      (by simpa [vadd_eq_add] using hD_closed.left_addCoset z :
        IsClosed (z +ᵥ (D : Set 𝓗)))
  · -- Any common point would place `z` back in `C ⊔ D`, contradicting the choice of `z`.
    rw [Set.disjoint_left]
    intro x hxU hxV
    have hxU' : x ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) := by
      change x ∈ ((C ⊔ Sᗮ : Submodule ℝ 𝓗).toAffineSubspace : AffineSubspace ℝ 𝓗) at hxU
      simpa using hxU
    rcases
      (show ∃ d ∈ D, z + d = x from by
        simpa [V, AffineSubspace.coe_pointwise_vadd, Set.mem_vadd_set, vadd_eq_add] using hxV) with
      ⟨d, hd, rfl⟩
    have hxS : z + d ∈ S := S.add_mem hzS (hD_le_S hd)
    have hxC : z + d ∈ C := by
      have hprojC : S.starProjection (z + d) ∈ C :=
        (mem_left_counterexample_iff_starProjection_mem_base C D (z + d)).1 hxU'
      simpa [Submodule.starProjection_eq_self_iff.mpr hxS] using hprojC
    have hz_mem : z ∈ C ⊔ D := by
      rw [Submodule.mem_sup]
      refine ⟨z + d, hxC, -d, D.neg_mem hd, by abel_nf⟩
    exact hz_not_mem hz_mem
  · intro hsep
    rcases (areSeparated_iff_exists_nonzero (U : Set 𝓗) (V : Set 𝓗)).mp hsep with ⟨u, hu_ne, hu_sep⟩
    have hu_sep_left :
        innerSupremumOn (((C ⊔ Sᗮ : Submodule ℝ 𝓗) : Set 𝓗)) u ≤ innerInfimumOn (V : Set 𝓗) u := by
      simpa [U] using hu_sep
    have hzV : z ∈ (V : Set 𝓗) := by
      change z ∈ z +ᵥ (D : Set 𝓗)
      exact ⟨0, D.zero_mem, by simp [vadd_eq_add]⟩
    have hzero_on_orthogonal : ∀ w ∈ Sᗮ, ⟪w, u⟫_ℝ = 0 := by
      -- Bounding the separator on the full line through an orthogonal direction forces that
      -- direction to be annihilated.
      intro w hw
      apply inner_eq_zero_of_line_upper_bound
      intro t
      have hw_mem : w ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) := Submodule.mem_sup_right hw
      have ht_mem : t • w ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) := (C ⊔ Sᗮ).smul_mem t hw_mem
      have ht_le : (⟪t • w, u⟫_ℝ : EReal) ≤ (⟪z, u⟫_ℝ : EReal) := by
        have hx_le : (⟪t • w, u⟫_ℝ : EReal) ≤
            innerSupremumOn (((C ⊔ Sᗮ : Submodule ℝ 𝓗) : Set 𝓗)) u := by
          rw [innerSupremumOn_eq_sSup_image]
          exact (isLUB_sSup _).1 ⟨t • w, ht_mem, rfl⟩
        have hy_ge : innerInfimumOn (V : Set 𝓗) u ≤ (⟪z, u⟫_ℝ : EReal) := by
          rw [innerInfimumOn_eq_sInf_image]
          exact (isGLB_sInf _).1 ⟨z, hzV, rfl⟩
        exact le_trans (le_trans hx_le hu_sep_left) hy_ge
      have ht_le_real : ⟪t • w, u⟫_ℝ ≤ ⟪z, u⟫_ℝ := by
        exact_mod_cast ht_le
      simpa [inner_smul_left] using ht_le_real
    have hsubset_nonpos :
        ((C ⊔ D : Submodule ℝ 𝓗) : Set 𝓗) ⊆ {s : 𝓗 | ⟪s - z, u⟫_ℝ ≤ 0} := by
      -- Evaluating the separator on `c ∈ C ⊆ U` and `z - d ∈ V` yields the key inequality on
      -- every point `c + d` of the algebraic sum.
      intro s hs
      change s ∈ (C ⊔ D : Submodule ℝ 𝓗) at hs
      rw [Submodule.mem_sup] at hs
      rcases hs with ⟨c, hc, d, hd, rfl⟩
      have hzdV : z - d ∈ (V : Set 𝓗) := by
        simpa [V, AffineSubspace.coe_pointwise_vadd, Set.mem_vadd_set, vadd_eq_add] using
          (show ∃ w ∈ D, z + w = z - d from ⟨-d, D.neg_mem hd, by abel_nf⟩)
      have hc_mem : c ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) := Submodule.mem_sup_left hc
      have hcd_le : ⟪c, u⟫_ℝ ≤ ⟪z - d, u⟫_ℝ := by
        have hx_le : (⟪c, u⟫_ℝ : EReal) ≤
            innerSupremumOn (((C ⊔ Sᗮ : Submodule ℝ 𝓗) : Set 𝓗)) u := by
          rw [innerSupremumOn_eq_sSup_image]
          exact (isLUB_sSup _).1 ⟨c, hc_mem, rfl⟩
        have hy_ge : innerInfimumOn (V : Set 𝓗) u ≤ (⟪z - d, u⟫_ℝ : EReal) := by
          rw [innerInfimumOn_eq_sInf_image]
          exact (isGLB_sInf _).1 ⟨z - d, hzdV, rfl⟩
        exact_mod_cast le_trans (le_trans hx_le hu_sep_left) hy_ge
      have hcalc : ⟪c + d - z, u⟫_ℝ = ⟪c, u⟫_ℝ - ⟪z - d, u⟫_ℝ := by
        calc
          ⟪c + d - z, u⟫_ℝ = ⟪c - (z - d), u⟫_ℝ := by
            congr 1
            abel_nf
          _ = ⟪c, u⟫_ℝ - ⟪z - d, u⟫_ℝ := by
            rw [inner_sub_left]
      change ⟪c + d - z, u⟫_ℝ ≤ 0
      rw [hcalc]
      exact sub_nonpos.mpr hcd_le
    have hclosed_nonpos : IsClosed {s : 𝓗 | ⟪s - z, u⟫_ℝ ≤ 0} := by
      exact isClosed_le ((continuous_id.sub continuous_const).inner continuous_const) continuous_const
    have hnonpos_on_S : ∀ s ∈ S, ⟪s - z, u⟫_ℝ ≤ 0 := by
      -- Closedness propagates the inequality from the dense algebraic sum to the whole closure `S`.
      intro s hs
      have hclosure_subset :
          closure (((C ⊔ D : Submodule ℝ 𝓗) : Set 𝓗)) ⊆ {s : 𝓗 | ⟪s - z, u⟫_ℝ ≤ 0} :=
        closure_minimal hsubset_nonpos hclosed_nonpos
      exact hclosure_subset (by simpa [S] using hs)
    have hzero_on_S_shift : ∀ s ∈ S, ⟪s - z, u⟫_ℝ = 0 := by
      -- Apply the same nonpositivity estimate to the reflected point `2z - s ∈ S` to obtain the
      -- opposite inequality and hence equality.
      intro s hs
      have hs_nonpos : ⟪s - z, u⟫_ℝ ≤ 0 := hnonpos_on_S s hs
      have hsym_mem : (2 : ℝ) • z - s ∈ S := S.sub_mem (S.smul_mem 2 hzS) hs
      have hsym_nonpos : ⟪((2 : ℝ) • z - s) - z, u⟫_ℝ ≤ 0 := hnonpos_on_S ((2 : ℝ) • z - s) hsym_mem
      have hcalc : ⟪((2 : ℝ) • z - s) - z, u⟫_ℝ = -⟪s - z, u⟫_ℝ := by
        calc
          ⟪((2 : ℝ) • z - s) - z, u⟫_ℝ = ⟪z - s, u⟫_ℝ := by
            congr 1
            simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = -⟪s - z, u⟫_ℝ := by
            rw [show z - s = -(s - z) by abel_nf, inner_neg_left]
      have hs_nonneg : 0 ≤ ⟪s - z, u⟫_ℝ := by
        rw [hcalc] at hsym_nonpos
        linarith
      linarith
    have hz_inner_zero : ⟪z, u⟫_ℝ = 0 := by
      have h0 := hzero_on_S_shift 0 S.zero_mem
      simpa using h0
    have hu_mem_orth : u ∈ Sᗮ := by
      -- Vanishing on all of `S` means the separator lies in `Sᗮ`.
      rw [Submodule.mem_orthogonal']
      intro s hs
      have hs_zero : ⟪s - z, u⟫_ℝ = 0 := hzero_on_S_shift s hs
      have hs_right : ⟪s, u⟫_ℝ = 0 := by
        rw [inner_sub_left] at hs_zero
        linarith
      simpa [real_inner_comm] using hs_right
    have hu_mem_orthorth : u ∈ Sᗮᗮ := by
      -- The orthogonal directions are also annihilated, so `u` lies in the double orthogonal.
      rw [Submodule.mem_orthogonal']
      intro w hw
      have hw_zero : ⟪w, u⟫_ℝ = 0 := hzero_on_orthogonal w hw
      simpa [real_inner_comm] using hw_zero
    have hu_mem_S : u ∈ S := by
      simpa [Submodule.orthogonal_orthogonal_eq_closure, hS_closed.submodule_topologicalClosure_eq]
        using hu_mem_orthorth
    have hu_mem_bot : u ∈ (⊥ : Submodule ℝ 𝓗) := by
      have : u ∈ S ⊓ Sᗮ := ⟨hu_mem_S, hu_mem_orth⟩
      simpa [S.inf_orthogonal_eq_bot] using this
    exact hu_ne (by simpa using hu_mem_bot)

end
