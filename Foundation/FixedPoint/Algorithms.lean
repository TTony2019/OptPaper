import Mathlib
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Foundation.Hilbert.WeakTopology
import Foundation.Convex.WeakClosed
import Foundation.FixedPoint.Nonexpansive
import Foundation.Projection.BestApproximation

/-!
# FixedPoint Algorithms

Demiclosedness principles, regularized nonexpansive maps, Douglas-Rachford operators, and fixed-point behavior of composed or averaged maps.
-/

open Filter
open scoped InnerProductSpace Topology
open Function Set
open scoped InnerProductSpace
open EuclideanGeometry
open Function
open scoped BigOperators

/-! Source item: Chap04/Definition_4_26 -/
universe u


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 4.26: `T : D → H` is demiclosed at `u` if every sequence in `D` that converges
weakly to some `x ∈ D` and whose image under `T` converges strongly to `u` satisfies `T x = u`. -/
def DemiclosedAt (D : Set H) (T : D → H) (u : H) : Prop :=
  ∀ ⦃xₙ : ℕ → D⦄ ⦃x : D⦄,
    Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n : H)) atTop (nhds (toWeakSpace ℝ H (x : H))) →
      Tendsto (fun n ↦ T (xₙ n)) atTop (nhds u) →
      T x = u

/-- A map on a subset of a real Hilbert space is demiclosed if it is demiclosed at every codomain
point. -/
def Demiclosed (D : Set H) (T : D → H) : Prop :=
  ∀ u, DemiclosedAt D T u

/-- Demiclosedness is exactly demiclosedness at each codomain point. -/
theorem demiclosed_iff {D : Set H} {T : D → H} :
    Demiclosed D T ↔ ∀ u, DemiclosedAt D T u := Iff.rfl

/-! Source item: Chap04/Theorem_4_27 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private lemma bounded_range_of_tendsto_toWeakSpace {x : ℕ → H} {y : H}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H y))) :
    Bornology.IsBounded (Set.range x) := by
  let T : ℕ → H →L[ℝ] ℝ := fun n ↦ InnerProductSpace.toDual ℝ H (x n)
  have hB_inj : Function.Injective ((topDualPairing ℝ H).flip) := by
    intro z w hzw
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hne
    exact hf (DFunLike.congr_fun hzw f)
  have hpointwise : ∀ u : H, ∃ C : ℝ, ∀ n : ℕ, ‖T n u‖ ≤ C := by
    intro u
    have hu_tendsto : Tendsto (fun n ↦ inner ℝ u (x n)) atTop (𝓝 (inner ℝ u y)) := by
      have hEval :=
        (WeakBilin.tendsto_iff_forall_eval_tendsto ((topDualPairing ℝ H).flip) hB_inj).1 hy
          (InnerProductSpace.toDual ℝ H u)
      simpa [LinearMap.flip_apply, topDualPairing_apply, toWeakSpace] using hEval
    have hu_bounded : Bornology.IsBounded (Set.range fun n ↦ inner ℝ u (x n)) :=
      Metric.isBounded_range_of_tendsto _ hu_tendsto
    rcases isBounded_iff_forall_norm_le.mp hu_bounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    have hCn : ‖inner ℝ u (x n)‖ ≤ C := hC _ (Set.mem_range_self n)
    simpa [T, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hCn
  obtain ⟨C, hC⟩ := banach_steinhaus hpointwise
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro z ⟨n, rfl⟩
  have hTn : ‖T n‖ ≤ C := hC n
  change ‖InnerProductSpace.toDual ℝ H (x n)‖ ≤ C at hTn
  rw [(InnerProductSpace.toDual ℝ H).norm_map] at hTn
  exact hTn

private lemma tendsto_inner_sub_right_zero {x : ℕ → H} {y v : H}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto (fun n ↦ ⟪x n - y, v⟫_ℝ) atTop (𝓝 0) := by
  have hEval :=
    ((WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
      (InnerProductSpace.toDual ℝ H v)).tendsto (toWeakSpace ℝ H y)).comp hy
  have hEval' : Tendsto (fun n ↦ ⟪v, x n⟫_ℝ) atTop (𝓝 (⟪v, y⟫_ℝ)) := by
    simpa only [toWeakSpace, LinearEquiv.refl_apply, LinearMap.flip_apply,
      topDualPairing_apply, InnerProductSpace.toDual_apply_apply] using hEval
  have hsub :
      Tendsto (fun n ↦ ⟪v, x n⟫_ℝ - ⟪v, y⟫_ℝ) atTop (𝓝 (⟪v, y⟫_ℝ - ⟪v, y⟫_ℝ)) := by
    exact hEval'.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ⟪v, y⟫_ℝ) atTop (𝓝 ⟪v, y⟫_ℝ))
  simpa [inner_sub_right, real_inner_comm] using hsub

omit [CompleteSpace H] in
private lemma residual_difference_norm_sq_le_two_inner
    {D : Set H} {T : D → H} (hT : LipschitzWith 1 T) {xSeq : ℕ → D} {x : D} :
    ∀ n,
      ‖(((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))‖ ^ 2 ≤
        2 * ⟪(xSeq n : H) - x, (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))⟫_ℝ := by
  intro n
  have hnonexp : ‖T (xSeq n) - T x‖ ≤ ‖(xSeq n : H) - x‖ := by
    simpa [dist_eq_norm, Subtype.dist_eq] using hT.dist_le_mul (xSeq n) x
  have hsq : ‖T (xSeq n) - T x‖ ^ 2 ≤ ‖(xSeq n : H) - x‖ ^ 2 := by
    nlinarith [hnonexp, norm_nonneg (T (xSeq n) - T x), norm_nonneg ((xSeq n : H) - x)]
  have hrewrite :
      T (xSeq n) - T x = ((xSeq n : H) - x) - (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x)) := by
    abel
  have hsq' :
      ‖((xSeq n : H) - x) - (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))‖ ^ 2 ≤
        ‖(xSeq n : H) - x‖ ^ 2 := by
    simpa [hrewrite] using hsq
  have hexp :=
    norm_sub_sq_real ((xSeq n : H) - x) (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))
  nlinarith [hsq', hexp]

private lemma residual_difference_inner_tendsto_zero
    {D : Set H} {T : D → H} {xSeq : ℕ → D} {x : D} {u : H}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n : H)) atTop
      (𝓝 (toWeakSpace ℝ H (x : H))))
    (hu : Tendsto (fun n ↦ (xSeq n : H) - T (xSeq n)) atTop (𝓝 u)) :
    Tendsto
      (fun n ↦ ⟪(xSeq n : H) - x, (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))⟫_ℝ)
      atTop (𝓝 0) := by
  have hbounded : Bornology.IsBounded (Set.range fun n ↦ (xSeq n : H)) :=
    bounded_range_of_tendsto_toWeakSpace hx
  rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0 + ‖(x : H)‖
  have hC : ∀ n, ‖(xSeq n : H) - x‖ ≤ C := by
    intro n
    calc
      ‖(xSeq n : H) - x‖ ≤ ‖(xSeq n : H)‖ + ‖(x : H)‖ := norm_sub_le _ _
      _ ≤ max C₀ 0 + ‖(x : H)‖ := by
        exact add_le_add (le_trans (hC₀ _ (Set.mem_range_self n)) (le_max_left _ _)) le_rfl
      _ = C := rfl
  have hfixed : Tendsto (fun n ↦ ⟪(xSeq n : H) - x, u - ((x : H) - T x)⟫_ℝ) atTop (𝓝 0) := by
    simpa only [sub_eq_add_neg] using tendsto_inner_sub_right_zero hx
  have hdiff : Tendsto (fun n ↦ (((xSeq n : H) - T (xSeq n)) - u)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n ↦ (((xSeq n : H) - T (xSeq n)) - u)) atTop (𝓝 (u - u)) := by
      exact hu.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ u) atTop (𝓝 u))
    simpa using hsub
  have hnorm_diff : Tendsto (fun n ↦ ‖((xSeq n : H) - T (xSeq n)) - u‖) atTop (𝓝 0) := by
    simpa using hdiff.norm
  have hmul : Tendsto (fun n ↦ C * ‖((xSeq n : H) - T (xSeq n)) - u‖) atTop (𝓝 0) := by
    simpa using hnorm_diff.const_mul C
  have hsecond_abs :
      Tendsto (fun n ↦ |⟪(xSeq n : H) - x, ((xSeq n : H) - T (xSeq n)) - u⟫_ℝ|) atTop
        (𝓝 0) := by
    refine squeeze_zero' (f := fun n ↦ |⟪(xSeq n : H) - x, ((xSeq n : H) - T (xSeq n)) - u⟫_ℝ|)
      (g := fun n ↦ C * ‖((xSeq n : H) - T (xSeq n)) - u‖)
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards with n
      exact le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    · simpa using hmul
  have hsecond :
      Tendsto (fun n ↦ ⟪(xSeq n : H) - x, ((xSeq n : H) - T (xSeq n)) - u⟫_ℝ) atTop
        (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp] using hsecond_abs
  have hsplit :
      (fun n ↦ ⟪(xSeq n : H) - x, (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x))⟫_ℝ) =
        fun n ↦
          ⟪(xSeq n : H) - x, u - ((x : H) - T x)⟫_ℝ +
            ⟪(xSeq n : H) - x, ((xSeq n : H) - T (xSeq n)) - u⟫_ℝ := by
    funext n
    rw [show (((xSeq n : H) - T (xSeq n)) - ((x : H) - T x)) =
        (u - ((x : H) - T x)) + (((xSeq n : H) - T (xSeq n)) - u) by abel,
      inner_add_right]
  rw [hsplit]
  simpa using hfixed.add hsecond

/-- Canonical residual form of Browder demiclosedness: on the subtype domain `D`, a nonexpansive
map has demiclosed residual map. -/
theorem demiclosed_residual_of_nonexpansive
    {D : Set H} {T : D → H} (hT : LipschitzWith 1 T) :
    Demiclosed D (fun x ↦ (x : H) - T x) := by
  intro u xₙ x hweak hu
  have hsq_left :
      Tendsto (fun n ↦ ‖(((xₙ n : H) - T (xₙ n)) - ((x : H) - T x))‖ ^ 2) atTop
        (𝓝 (‖u - ((x : H) - T x)‖ ^ 2)) := by
    have hdiff : Tendsto (fun n ↦ (((xₙ n : H) - T (xₙ n)) - ((x : H) - T x))) atTop
        (𝓝 (u - ((x : H) - T x))) := by
      exact hu.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (x : H) - T x) atTop (𝓝 ((x : H) - T x)))
    simpa using hdiff.norm.pow 2
  have hinner_zero :
      Tendsto
        (fun n ↦ ⟪(xₙ n : H) - x, (((xₙ n : H) - T (xₙ n)) - ((x : H) - T x))⟫_ℝ)
        atTop (𝓝 0) :=
    residual_difference_inner_tendsto_zero hweak hu
  have hsq_right :
      Tendsto
        (fun n ↦ 2 * ⟪(xₙ n : H) - x, (((xₙ n : H) - T (xₙ n)) - ((x : H) - T x))⟫_ℝ)
        atTop (𝓝 0) := by
    simpa using hinner_zero.const_mul 2
  have hnonpos : ‖u - ((x : H) - T x)‖ ^ 2 ≤ 0 := by
    exact le_of_tendsto_of_tendsto hsq_left hsq_right <|
      Eventually.of_forall (residual_difference_norm_sq_le_two_inner hT)
  have hsq_zero : ‖u - ((x : H) - T x)‖ ^ 2 = 0 := by
    exact le_antisymm hnonpos (sq_nonneg ‖u - ((x : H) - T x)‖)
  have hnorm_zero : ‖u - ((x : H) - T x)‖ = 0 := eq_zero_of_pow_eq_zero hsq_zero
  have hzero : u - ((x : H) - T x) = 0 := norm_eq_zero.mp hnorm_zero
  exact (sub_eq_zero.mp hzero).symm

/-- Theorem 4.27: Browder's demiclosedness principle says that if `D` is weakly sequentially
closed in a real Hilbert space and `T` is nonexpansive on `D`, then weak convergence of a sequence
in `D` together with norm convergence of the residuals `xₙ - T xₙ` forces the limit residual to be
`x - T x`. -/
-- Proof sketch: use weak sequential closedness to show that the weak limit `x` belongs to `D`.
-- Then expand `‖x - T x - u‖²` around the sequence terms, estimate the `‖T (xSeq n) - T x‖²`
-- term by nonexpansiveness, and pass to the limit using norm convergence of the residuals and weak
-- convergence of `xSeq` to make the inner-product error terms vanish.
theorem browder_demiclosedness_principle
    {D : Set H} (hD : IsSeqClosed ((toWeakSpace ℝ H) '' D))
    {T : H → H} (hT : LipschitzOnWith 1 T D) {xSeq : ℕ → H} (hxSeq : ∀ n, xSeq n ∈ D)
    {x u : H}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hu : Tendsto (fun n ↦ xSeq n - T (xSeq n)) atTop (𝓝 u)) :
    x - T x = u := by
  have hxD : x ∈ D := by
    have hxWeakMem : ∀ n, toWeakSpace ℝ H (xSeq n) ∈ ((toWeakSpace ℝ H) '' D) := by
      intro n
      exact ⟨xSeq n, hxSeq n, rfl⟩
    rcases hD hxWeakMem hx with ⟨y, hyD, hyEq⟩
    have hyx : y = x := (toWeakSpace ℝ H).injective hyEq
    simpa [hyx] using hyD
  let T' : D → H := fun z ↦ T z
  have hT' : LipschitzWith 1 T' := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro y z
    simpa [T', Subtype.dist_eq] using hT.dist_le_mul y y.property z z.property
  let xSeq' : ℕ → D := fun n ↦ ⟨xSeq n, hxSeq n⟩
  let xD : D := ⟨x, hxD⟩
  have hx' :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq' n : H)) atTop (𝓝 (toWeakSpace ℝ H (xD : H))) := by
    simpa [xSeq', xD] using hx
  have hu' : Tendsto (fun n ↦ (xSeq' n : H) - T' (xSeq' n)) atTop (𝓝 u) := by
    simpa [xSeq', T'] using hu
  simpa [T', xD] using (demiclosed_residual_of_nonexpansive hT') u hx' hu'

/-! Source item: Chap04/Corollary_4_28 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: closed convex subsets of a real Hilbert space are weakly sequentially closed by
-- Theorem 3.34. Apply the demiclosedness principle from Theorem 4.27 to the residual map
-- `x ↦ x - T x` at `0`; the residual convergence hypothesis then forces `T x = x`.
/-- Corollary 4.28: if `D` is a closed convex subset of a real Hilbert space, `T : D → H` is
nonexpansive, `xₙ` converges weakly to `x` in `D`, and the residuals `xₙ - T xₙ` converge strongly
to `0`, then `x` is a fixed point of `T`. -/
theorem map_eq_of_tendsto_weakly_of_residual_tendsto_zero_of_nonexpansive
    {D : Set H} (_hD_closed : IsClosed D) (_hD_convex : Convex ℝ D)
    {T : D → H} (hT : LipschitzWith 1 T) {xₙ : ℕ → D} {x : D}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n : H)) atTop
      (𝓝 (toWeakSpace ℝ H (x : H))))
    (hres : Tendsto (fun n ↦ (xₙ n : H) - T (xₙ n)) atTop (𝓝 (0 : H))) :
    T x = (x : H) := by
  have hx_residual : (x : H) - T x = (0 : H) :=
    demiclosed_residual_of_nonexpansive hT 0 hweak hres
  exact (sub_eq_zero.mp hx_residual).symm

/-! Source item: Chap04/Theorem_4_29 -/


section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Theorem 4.29: convexity keeps each affine regularization
`x ↦ α • x₀ + (1 - α) • T x` inside the set `D`. -/
private theorem regularized_map_mapsTo {D : Set H} (hD_convex : Convex ℝ D) {T : H → H}
    (hTD : MapsTo T D D) {x0 : H} (hx0 : x0 ∈ D) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    MapsTo (fun x ↦ α • x0 + (1 - α) • T x) D D := by
  intro x hx
  -- Rewrite the affine combination as a line-map point of the segment `[T x, x₀]`.
  have hline : (AffineMap.lineMap (T x) x0) α ∈ D :=
    hD_convex.lineMap_mem (hTD hx) hx0 hα
  simpa [AffineMap.lineMap_apply, sub_eq_add_neg, smul_sub, add_smul, one_smul, add_comm,
    add_left_comm, add_assoc] using hline

/-- Helper for Theorem 4.29: a forward-invariant regularized affine combination defines a self-map
of the subtype `D`. -/
private noncomputable def regularized_selfMap {D : Set H} {T : H → H} {x0 : H} {α : ℝ}
    (hMap : MapsTo (fun x ↦ α • x0 + (1 - α) • T x) D D) : D → D :=
  fun x ↦ ⟨α • x0 + (1 - α) • T x, hMap x.2⟩

/-- Helper for Theorem 4.29: on the subtype `D`, the regularized map is a strict contraction with
constant `1 - α`. -/
private theorem regularized_map_contractingWith {D : Set H} (hD_convex : Convex ℝ D) {T : H → H}
    (hTD : MapsTo T D D) (hT : LipschitzOnWith 1 T D) {x0 : H} (hx0 : x0 ∈ D) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1) :
    ContractingWith (Real.toNNReal (1 - α))
      (regularized_selfMap
        (regularized_map_mapsTo hD_convex hTD hx0 ⟨le_of_lt hα_pos, hα_le⟩)) := by
  let hMap :
      MapsTo (fun x ↦ α • x0 + (1 - α) • T x) D D :=
    regularized_map_mapsTo hD_convex hTD hx0 ⟨le_of_lt hα_pos, hα_le⟩
  let K : NNReal := Real.toNNReal (1 - α)
  change ContractingWith K (regularized_selfMap hMap)
  refine ⟨?_, ?_⟩
  · -- The contraction constant is strictly less than `1` because `α` is positive.
    exact (Real.toNNReal_lt_one).2 (sub_lt_self (1 : ℝ) hα_pos)
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hxy : ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
      simpa [dist_eq_norm] using hT.dist_le_mul x x.2 y y.2
    -- The common `α • x₀` term cancels, leaving only the scaled nonexpansive difference.
    calc
      dist (regularized_selfMap hMap x) (regularized_selfMap hMap y) =
          ‖(1 - α) • (T x - T y)‖ := by
            simp [regularized_selfMap, Subtype.dist_eq, dist_eq_norm, sub_eq_add_neg, add_comm,
              add_left_comm, add_assoc]
      _ = (1 - α) * ‖T x - T y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hα_le)]
      _ ≤ (1 - α) * ‖(x : H) - y‖ := by
        exact mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hα_le)
      _ = (1 - α) * dist x y := by
        rw [Subtype.dist_eq, dist_eq_norm]
      _ = K * dist x y := by
        rw [show (K : ℝ) = 1 - α by
          simp [K, Real.toNNReal_of_nonneg (sub_nonneg.mpr hα_le)]]

/-- Helper for Theorem 4.29: a fixed point of the regularized map has residual
`x - T x = α • (x₀ - T x)`. -/
private theorem regularized_fixed_point_residual_eq {T : H → H} {x x0 : H} {α : ℝ}
    (hx : x = α • x0 + (1 - α) • T x) :
    x - T x = α • (x0 - T x) := by
  -- Expand the fixed-point identity and collect the `T x` terms.
  have hx' : x - T x = (α • x0 + (1 - α) • T x) - T x := by
    simpa using congrArg (fun z ↦ z - T x) hx
  calc
    x - T x = (α • x0 + (1 - α) • T x) - T x := hx'
    _ = α • (x0 - T x) := by
      module

/-- Helper for Theorem 4.29: if regularized fixed points satisfy a uniform bound
`‖x₀ - T xₙ‖ ≤ R` and `αₙ → 0`, then the residuals `xₙ - T xₙ` converge strongly to `0`. -/
private theorem residual_tendsto_zero_of_regularized_fixed_points {D : Set H} {T : H → H}
    {x0 : H} {α : ℕ → ℝ} {xSeq : ℕ → D} {R : ℝ}
    (hbound : ∀ n, ‖x0 - T (xSeq n)‖ ≤ R)
    (hfixed : ∀ n, (xSeq n : H) = α n • x0 + (1 - α n) • T (xSeq n))
    (hα_nonneg : ∀ n, 0 ≤ α n) (hα_tendsto : Tendsto α atTop (nhds 0)) :
    Tendsto (fun n ↦ (xSeq n : H) - T (xSeq n)) atTop (nhds 0) := by
  have hnorm_le : ∀ n, ‖(xSeq n : H) - T (xSeq n)‖ ≤ α n * R := by
    intro n
    rw [regularized_fixed_point_residual_eq (hfixed n), norm_smul,
      Real.norm_of_nonneg (hα_nonneg n)]
    exact mul_le_mul_of_nonneg_left (hbound n) (hα_nonneg n)
  have hαR : Tendsto (fun n ↦ α n * R) atTop (nhds (0 * R)) := by
    exact hα_tendsto.mul tendsto_const_nhds
  -- Squeeze the residual norms between `0` and the scalar sequence `αₙ R`.
  exact squeeze_zero_norm hnorm_le (by simpa using hαR)

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use boundedness and closed convexity of `D` in the Hilbert space to obtain weak
-- sequential compactness, regularize `T` by the contractions `x ↦ α • x₀ + (1 - α) • T x`, apply
-- the Banach fixed-point theorem to each regularization, extract a weakly convergent subsequence,
-- and conclude with the demiclosedness principle for `id - T`.
/-- Theorem 4.29: Browder--Göhde--Kirk guarantees that a nonexpansive self-map of a nonempty
bounded closed convex subset of a real Hilbert space has a fixed point in that subset. -/
theorem browder_gohde_kirk_fixed_point
    {D : Set H} (hD_nonempty : D.Nonempty) (hD_bounded : Bornology.IsBounded D)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) {T : H → H}
    (hTD : MapsTo T D D) (hT : LipschitzOnWith 1 T D) :
    (D ∩ fixedPoints T).Nonempty := by
  classical
  obtain ⟨x0, hx0⟩ := hD_nonempty
  let α : ℕ → ℝ := fun n ↦ (1 : ℝ) / ((n : ℝ) + 1)
  letI : Nonempty D := ⟨⟨x0, hx0⟩⟩
  letI : CompleteSpace D := hD_closed.completeSpace_coe
  have hα_pos : ∀ n, 0 < α n := by
    intro n
    dsimp [α]
    positivity
  have hα_nonneg : ∀ n, 0 ≤ α n := by
    intro n
    exact (hα_pos n).le
  have hα_le : ∀ n, α n ≤ 1 := by
    intro n
    dsimp [α]
    have hden0 : 0 < (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_pos n
    have hden : 1 ≤ (n : ℝ) + 1 := by linarith
    simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden)
  have hα_tendsto : Tendsto α atTop (nhds 0) := by
    -- The explicit choice `αₙ = 1 / (n + 1)` tends to zero.
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa [α, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  let hMap : ∀ n, MapsTo (fun x ↦ α n • x0 + (1 - α n) • T x) D D := by
    intro n
    exact regularized_map_mapsTo hD_convex hTD hx0 ⟨hα_nonneg n, hα_le n⟩
  let F : ℕ → D → D := fun n ↦ regularized_selfMap (hMap n)
  have hcontract : ∀ n, ContractingWith (Real.toNNReal (1 - α n)) (F n) := by
    intro n
    -- Each regularization is a strict contraction on the complete subtype `D`.
    simpa [F, hMap] using
      regularized_map_contractingWith hD_convex hTD hT hx0 (hα_pos n) (hα_le n)
  let xSeq : ℕ → D := fun n ↦ ContractingWith.fixedPoint (F n) (hcontract n)
  have hxSeq_fixed :
      ∀ n, (xSeq n : H) = α n • x0 + (1 - α n) • T (xSeq n) := by
    intro n
    -- The Banach fixed point of the `n`-th regularization satisfies the displayed affine equation.
    simpa [xSeq, F, regularized_selfMap] using
      congrArg Subtype.val ((hcontract n).fixedPoint_isFixedPt.eq.symm)
  obtain ⟨R, -, hR_sub⟩ := hD_bounded.subset_closedBall_lt 0 x0
  have hTxSeq_bound : ∀ n, ‖x0 - T (xSeq n)‖ ≤ R := by
    intro n
    have hmem : T (xSeq n) ∈ D := hTD (xSeq n).2
    -- Boundedness gives a uniform radius around `x₀` for all images `T xₙ`.
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hR_sub hmem
  have hresidual :
      Tendsto (fun n ↦ (xSeq n : H) - T (xSeq n)) atTop (nhds 0) :=
    residual_tendsto_zero_of_regularized_fixed_points hTxSeq_bound hxSeq_fixed hα_nonneg
      hα_tendsto
  have hweakClosed : IsClosed ((toWeakSpace ℝ H) '' D) :=
    (isClosed_iff_weak_image_isClosed_of_convex hD_convex).1 hD_closed
  have hweakCompact : IsCompact ((toWeakSpace ℝ H) '' D) := by
    exact
      (weaklyCompact_iff_weaklyClosed_and_bounded :
        IsCompact ((toWeakSpace ℝ H) '' D) ↔
          IsClosed ((toWeakSpace ℝ H) '' D) ∧ Bornology.IsBounded D).2
        ⟨hweakClosed, hD_bounded⟩
  have hweakSeqCompact : IsSeqCompact ((toWeakSpace ℝ H) '' D) :=
    (weaklyCompact_iff_weaklySeqCompact D).1 hweakCompact
  have hxSeq_mem : ∀ n, toWeakSpace ℝ H (xSeq n : H) ∈ ((toWeakSpace ℝ H) '' D) := by
    intro n
    exact ⟨xSeq n, (xSeq n).2, rfl⟩
  obtain ⟨xWeak, hxWeak_mem, φ, hφ, hφconv⟩ := hweakSeqCompact hxSeq_mem
  rcases hxWeak_mem with ⟨x, hxD, rfl⟩
  let ySeq : ℕ → H := fun n ↦ xSeq (φ n)
  have hySeq_mem : ∀ n, ySeq n ∈ D := by
    intro n
    exact (xSeq (φ n)).2
  have hySeq_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (ySeq n)) atTop (nhds (x : WeakSpace ℝ H)) := by
    -- Sequential compactness provides a weakly convergent ambient subsequence.
    simpa [ySeq, Function.comp] using hφconv
  have hySeq_residual :
      Tendsto (fun n ↦ ySeq n - T (ySeq n)) atTop (nhds 0) := by
    -- Strong convergence of the residuals is preserved under subsequences.
    simpa [ySeq] using hresidual.comp hφ.tendsto_atTop
  have hweakSeqClosed : IsSeqClosed ((toWeakSpace ℝ H) '' D) :=
    hweakClosed.isSeqClosed
  have hlimit_residual : x - T x = 0 := by
    -- Apply Browder demiclosedness to the weakly convergent approximate fixed-point subsequence.
    exact
      browder_demiclosedness_principle hweakSeqClosed hT hySeq_mem hySeq_weak hySeq_residual
  have hfix : x ∈ fixedPoints T := by
    -- A zero residual is exactly the fixed-point condition.
    exact Function.mem_fixedPoints_iff.mpr (sub_eq_zero.mp hlimit_residual).symm
  exact ⟨x, ⟨hxD, hfix⟩⟩

end

/-! Source item: Chap04/Proposition_4_31 -/


section

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- The Douglas--Rachford combination `T₁ (2T₂ - Id) + Id - T₂` of two self-maps. -/
def douglasRachfordOperator (T₁ T₂ : H → H) : H → H :=
  fun x ↦ T₁ ((2 : ℝ) • T₂ x - x) + x - T₂ x

/-- The Douglas--Rachford operator acts by `x ↦ T₁ (2 • T₂ x - x) + x - T₂ x`. -/
theorem douglasRachfordOperator_apply (T₁ T₂ : H → H) (x : H) :
    douglasRachfordOperator T₁ T₂ x = T₁ ((2 : ℝ) • T₂ x - x) + x - T₂ x := by
  rfl

/-- Proposition 4.31 (1): for any self-maps `T₁` and `T₂`, the reflector of
`T = T₁ (2T₂ - Id) + Id - T₂` is the composition `(2T₁ - Id) ∘ (2T₂ - Id)`. -/
theorem reflected_douglasRachfordOperator_eq_comp_reflectedMap
    {T₁ T₂ : H → H} :
    (fun x ↦ (2 : ℝ) • douglasRachfordOperator T₁ T₂ x - x) =
      (fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x := by
  funext x
  simp [douglasRachfordOperator, two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- On the whole space, firm nonexpansiveness is equivalent to the canonical
`LipschitzWith 1` condition for the reflector `x ↦ 2 • T x - x`. -/
private theorem firmlyNonexpansive_iff_lipschitzWith_one_reflectedMap {T : H → H} :
    FirmlyNonexpansive T ↔ LipschitzWith 1 (fun x ↦ (2 : ℝ) • T x - x) := by
  rw [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ]
  rw [← reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn (Set.univ : Set H)
    (fun x : Set.univ ↦ T x)]
  constructor
  · intro hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [reflectedMap, Subtype.dist_eq, dist_eq_norm, one_mul] using
      hT ⟨x, by simp⟩ ⟨y, by simp⟩
  · intro hR x y
    simpa [reflectedMap, Subtype.dist_eq, dist_eq_norm, one_mul] using
      hR.dist_le_mul x y

/-- Proposition 4.31 (2): the Douglas--Rachford operator associated to firmly nonexpansive `T₁`
and `T₂` is firmly nonexpansive. -/
theorem douglasRachfordOperator_firmlyNonexpansive
    {T₁ T₂ : H → H}
    (hT₁ : FirmlyNonexpansive T₁) (hT₂ : FirmlyNonexpansive T₂) :
    FirmlyNonexpansive (douglasRachfordOperator T₁ T₂) := by
  rw [firmlyNonexpansive_iff_lipschitzWith_one_reflectedMap]
  have hR₁ :
      LipschitzWith 1 (fun x ↦ (2 : ℝ) • T₁ x - x) :=
    firmlyNonexpansive_iff_lipschitzWith_one_reflectedMap.1 hT₁
  have hR₂ :
      LipschitzWith 1 (fun x ↦ (2 : ℝ) • T₂ x - x) :=
    firmlyNonexpansive_iff_lipschitzWith_one_reflectedMap.1 hT₂
  simpa [reflected_douglasRachfordOperator_eq_comp_reflectedMap] using hR₁.comp hR₂

end

section

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [NoZeroSMulDivisors ℝ H]

/-- A self-map and its reflector `x ↦ 2 • T x - x` have the same fixed points. -/
private lemma fixedPoints_reflectedMap_eq_fixedPoints
    (T : H → H) :
    Function.fixedPoints (fun x ↦ (2 : ℝ) • T x - x) = Function.fixedPoints T := by
  ext y
  constructor
  · intro hy
    rw [Function.mem_fixedPoints_iff] at hy ⊢
    change (2 : ℝ) • T y - y = y at hy
    have hzero : (2 : ℝ) • (T y - y) = 0 := by
      calc
        (2 : ℝ) • (T y - y) = (2 : ℝ) • T y - (2 : ℝ) • y := by
          rw [smul_sub]
        _ = ((2 : ℝ) • T y - y) - y := by
          simp [two_smul, sub_eq_add_neg, add_assoc]
        _ = 0 := by
          rw [hy, sub_self]
    rcases smul_eq_zero.mp hzero with htwo | hsub
    · norm_num at htwo
    · exact sub_eq_zero.mp hsub
  · intro hy
    rw [Function.mem_fixedPoints_iff] at hy ⊢
    change T y = y at hy
    rw [hy]
    simp [two_smul]

/-- Proposition 4.31 (3): for any self-maps `T₁` and `T₂`, the fixed points of the
Douglas--Rachford operator coincide with the fixed points of the composed reflected maps
`(2T₁ - Id) ∘ (2T₂ - Id)`. -/
theorem fixedPoints_douglasRachfordOperator_eq_fixedPoints_reflected_comp
    {T₁ T₂ : H → H} :
    Function.fixedPoints (douglasRachfordOperator T₁ T₂) =
      Function.fixedPoints ((fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x) := by
  calc
    Function.fixedPoints (douglasRachfordOperator T₁ T₂) =
        Function.fixedPoints (fun x ↦ (2 : ℝ) • douglasRachfordOperator T₁ T₂ x - x) := by
          symm
          exact fixedPoints_reflectedMap_eq_fixedPoints _
    _ =
        Function.fixedPoints ((fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x) := by
          rw [reflected_douglasRachfordOperator_eq_comp_reflectedMap]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 4.31 (4): if `T₁` is the orthogonal projection onto an affine subspace `A`, then
the fixed points of the corresponding Douglas--Rachford operator are exactly the points where
`T₁` and `T₂` agree. -/
theorem fixedPoints_douglasRachfordOperator_eq_agreement_set_of_affine_projector
    {A : AffineSubspace ℝ H} [Nonempty A] [A.direction.HasOrthogonalProjection] {T₂ : H → H} :
    Function.fixedPoints
        (douglasRachfordOperator (fun x ↦ (orthogonalProjection A x : H)) T₂) =
      {x : H | (orthogonalProjection A x : H) = T₂ x} := by
  ext x
  rw [Function.mem_fixedPoints_iff]
  change
    douglasRachfordOperator (fun z ↦ (orthogonalProjection A z : H)) T₂ x = x ↔
      (orthogonalProjection A x : H) = T₂ x
  constructor
  · intro hx
    have hproj : (orthogonalProjection A ((2 : ℝ) • T₂ x - x) : H) = T₂ x := by
      have hdx : (orthogonalProjection A ((2 : ℝ) • T₂ x - x) : H) + x - T₂ x = x := by
        simpa [douglasRachfordOperator] using hx
      have hsub : (orthogonalProjection A ((2 : ℝ) • T₂ x - x) : H) + x = T₂ x + x := by
        exact sub_eq_iff_eq_add'.mp hdx
      exact add_right_cancel hsub
    have hchar :
        T₂ x ∈ (A : Set H) ∧ ((2 : ℝ) • T₂ x - x) - T₂ x ∈ A.directionᗮ := by
      exact (coe_orthogonalProjection_eq_iff_mem).mp hproj
    refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
    rcases hchar with ⟨hyA, horth⟩
    refine ⟨hyA, ?_⟩
    have hneg : -(((2 : ℝ) • T₂ x - x) - T₂ x) ∈ A.directionᗮ := Submodule.neg_mem _ horth
    simpa [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg
  · intro hx
    have hxchar : T₂ x ∈ (A : Set H) ∧ x - T₂ x ∈ A.directionᗮ := by
      exact (coe_orthogonalProjection_eq_iff_mem).mp hx
    have hproj : (orthogonalProjection A ((2 : ℝ) • T₂ x - x) : H) = T₂ x := by
      refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
      rcases hxchar with ⟨hyA, horth⟩
      refine ⟨hyA, ?_⟩
      have hneg : -(x - T₂ x) ∈ A.directionᗮ := Submodule.neg_mem _ horth
      simpa [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg
    simp [douglasRachfordOperator, hproj]

end

/-! Source item: Chap04/Corollary_4_32 -/


section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

private instance (V : ClosedSubmodule ℝ 𝓗) : Nonempty V.toSubmodule.toAffineSubspace := by
  refine ⟨⟨0, ?_⟩⟩
  exact (Submodule.mem_toAffineSubspace).2 (by simp)

private instance (V : ClosedSubmodule ℝ 𝓗) :
    V.toSubmodule.toAffineSubspace.direction.HasOrthogonalProjection := by
  rw [Submodule.toAffineSubspace_direction]
  infer_instance

/-- Helper for Corollary 4.32: the orthogonal projector onto a closed linear subspace is firmly
nonexpansive. -/
private theorem starProjection_isFirmlyNonexpansive
    (V : ClosedSubmodule ℝ 𝓗) : FirmlyNonexpansive V.starProjection := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  -- Reduce to the standard orthogonal-projection identity on `x - y`.
  have hproj := norm_sq_orthogonalProjection_eq_inner_starProjection V (x - y)
  simpa [map_sub] using hproj.le

/-- Helper for Corollary 4.32: on the affine subspace underlying `V`, the canonical affine
orthogonal projection agrees with the subspace star projection. -/
private theorem coe_orthogonalProjection_toAffineSubspace_eq_starProjection
    (V : ClosedSubmodule ℝ 𝓗) (x : 𝓗) :
    (orthogonalProjection V.toSubmodule.toAffineSubspace x : 𝓗) = V.starProjection x := by
  refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
  constructor
  · exact (Submodule.mem_toAffineSubspace).2
      (Submodule.starProjection_apply_mem V.toSubmodule x)
  · rw [Submodule.toAffineSubspace_direction]
    exact Submodule.sub_starProjection_mem_orthogonal x

-- Proof sketch: apply Proposition 4.31 directly to the orthogonal projector `P_V`. Since
-- `douglasRachfordOperator V.starProjection T₂ x = P_V (2 • T₂ x - x) + x - T₂ x`, the canonical
-- Douglas--Rachford operator is exactly the textbook map
-- `x ↦ P_V (T₂ x) + P_{Vᗮ} (x - T₂ x)`.
/-- Corollary 4.32: if `V` is a closed linear subspace of a real Hilbert space and `T₂` is firmly
nonexpansive, then the Douglas--Rachford operator attached to `P_V` and `T₂`, equivalently the
map `x ↦ P_V (T₂ x) + P_{Vᗮ} (x - T₂ x)`, is firmly nonexpansive and its fixed point set is
`{x | P_V x = T₂ x}`. -/
theorem orthogonal_projector_residual_combination_firmlyNonexpansive_and_fixedPoints
    (V : ClosedSubmodule ℝ 𝓗) {T₂ : 𝓗 → 𝓗}
    (hT₂ : FirmlyNonexpansive T₂) :
    FirmlyNonexpansive (douglasRachfordOperator V.starProjection T₂) ∧
      fixedPoints (douglasRachfordOperator V.starProjection T₂) =
        {x : 𝓗 | V.starProjection x = T₂ x} := by
  have hfirm : FirmlyNonexpansive (douglasRachfordOperator V.starProjection T₂) := by
    exact douglasRachfordOperator_firmlyNonexpansive
      (starProjection_isFirmlyNonexpansive V) hT₂
  have hfix :
      fixedPoints (douglasRachfordOperator V.starProjection T₂) =
        {x : 𝓗 | V.starProjection x = T₂ x} := by
    have hfixA :
        fixedPoints
            (douglasRachfordOperator
              (fun x ↦ (orthogonalProjection V.toSubmodule.toAffineSubspace x : 𝓗)) T₂) =
          {x : 𝓗 | (orthogonalProjection V.toSubmodule.toAffineSubspace x : 𝓗) = T₂ x} :=
      fixedPoints_douglasRachfordOperator_eq_agreement_set_of_affine_projector
    simpa [coe_orthogonalProjection_toAffineSubspace_eq_starProjection] using hfixA
  constructor
  · exact hfirm
  · exact hfix

end

/-! Source item: Chap04/Proposition_4_47 -/

universe v

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {I : Type v} [Fintype I]

/-- Helper for Proposition 4.47: a quasinonexpansive map yields the residual inner-product
inequality from the textbook proof against any of its fixed points. -/
private lemma quasinonexpansive_residual_inner_nonpos {S : D → H} (hS : IsQuasinonexpansiveOn S)
    (x y : D) (hy : S y = (y : H)) :
    2 * inner ℝ (S x - (x : H)) ((x : H) - (y : H)) ≤ - ‖S x - (x : H)‖ ^ 2 := by
  -- First square the quasinonexpansive estimate relative to the fixed point `y`.
  have hsq : ‖S x - (y : H)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hS x y hy)
  -- Then expand the residual square and isolate the inner-product term.
  have hexpand :
      ‖S x - (x : H)‖ ^ 2 =
        ‖S x - (y : H)‖ ^ 2 - 2 * inner ℝ (S x - (y : H)) ((x : H) - (y : H)) +
          ‖(x : H) - y‖ ^ 2 := by
    have h := norm_sub_sq_real (S x - (y : H)) ((x : H) - (y : H))
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hinner :
      inner ℝ (S x - (y : H)) ((x : H) - (y : H)) =
        inner ℝ (S x - (x : H)) ((x : H) - (y : H)) + ‖(x : H) - y‖ ^ 2 := by
    calc
      inner ℝ (S x - (y : H)) ((x : H) - (y : H)) =
          inner ℝ ((S x - (x : H)) + ((x : H) - (y : H))) ((x : H) - (y : H)) := by
            congr 1
            abel
      _ = inner ℝ (S x - (x : H)) ((x : H) - (y : H)) +
            inner ℝ ((x : H) - (y : H)) ((x : H) - (y : H)) := by
            rw [inner_add_left]
      _ = inner ℝ (S x - (x : H)) ((x : H) - (y : H)) + ‖(x : H) - y‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq]
  nlinarith [hsq, hexpand, hinner]

/-- Helper for Proposition 4.47: if `x` is fixed by the weighted average, then the weighted sum of
the residual vectors `T i x - x` is zero. -/
private lemma weighted_residual_eq_zero_of_mem_fixedPointsWithin (ω : I → ℝ) (T : I → D → H)
    (hω_sum : ∑ i, ω i = 1) {x : D}
    (hx : x ∈ fixedPointsWithin (fun z : D ↦ ∑ i, ω i • T i z)) :
    ∑ i, ω i • (T i x - (x : H)) = 0 := by
  classical
  -- Rewrite the fixed-point equation of the average into the corresponding residual identity.
  have hfix : (∑ i, ω i • T i x) = (x : H) := (mem_fixedPointsWithin_iff _).mp hx
  calc
    ∑ i, ω i • (T i x - (x : H)) = (∑ i, ω i • T i x) - (∑ i, ω i) • (x : H) := by
      calc
        ∑ i, ω i • (T i x - (x : H)) = ∑ i, (ω i • T i x - ω i • (x : H)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [smul_sub]
        _ = (∑ i, ω i • T i x) - ∑ i, ω i • (x : H) := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ i, ω i • T i x) - (∑ i, ω i) • (x : H) := by
          rw [Finset.sum_smul]
    _ = (x : H) - (1 : ℝ) • (x : H) := by
      rw [hfix, hω_sum]
    _ = 0 := by
      simp

-- Proof sketch: the inclusion from right to left is immediate since every common fixed point is
-- fixed by the weighted average when the weights sum to `1`. For the reverse inclusion, choose a
-- common fixed point `y`, apply quasinonexpansiveness of each `T i` relative to `y`, expand the
-- polarization identity for `T i x - x` against `x - y`, sum with the positive weights `ω i`, and
-- use `∑ i, ω i = 1` to force each residual `T i x - x` to vanish.
/-- Proposition 4.47: the fixed points in `D` of the finite weighted average
`x ↦ ∑ i, ω i • T i x` of quasinonexpansive maps are exactly the common fixed points of the
family, provided the weights are positive, sum to `1`, and the family has a common fixed point. -/
theorem fixedPointsWithin_weightedAverage_eq_iInter
    (ω : I → ℝ) (T : I → D → H) (hT : ∀ i, IsQuasinonexpansiveOn (T i))
    (hFix : (⋂ i, fixedPointsWithin (T i)).Nonempty) (hω_pos : ∀ i, 0 < ω i)
    (hω_sum : ∑ i, ω i = 1) :
    fixedPointsWithin (fun x : D ↦ ∑ i, ω i • T i x) = ⋂ i, fixedPointsWithin (T i) := by
  classical
  ext x
  constructor
  · intro hx
    rcases hFix with ⟨y, hy⟩
    have hyi : ∀ i, T i y = (y : H) := by
      intro i
      exact (mem_fixedPointsWithin_iff _).mp ((Set.mem_iInter.mp hy) i)
    -- A fixed point of the average makes the weighted residual sum vanish.
    have hres0 : ∑ i, ω i • (T i x - (x : H)) = 0 :=
      weighted_residual_eq_zero_of_mem_fixedPointsWithin ω T hω_sum hx
    have hsum_inner_eq_zero :
        ∑ i, ω i * inner ℝ (T i x - (x : H)) ((x : H) - (y : H)) = 0 := by
      have hinner0 :
          inner ℝ (∑ i, ω i • (T i x - (x : H))) ((x : H) - (y : H)) = 0 := by
        rw [hres0, inner_zero_left]
      rw [sum_inner] at hinner0
      simpa [real_inner_smul_left] using hinner0
    -- Sum the pointwise residual inequalities against the positive weights.
    have hsum_sq_nonpos : ∑ i, ω i * ‖T i x - (x : H)‖ ^ 2 ≤ 0 := by
      have hpointwise :
          ∀ i, 2 * (ω i * inner ℝ (T i x - (x : H)) ((x : H) - (y : H))) ≤
            -(ω i * ‖T i x - (x : H)‖ ^ 2) := by
        intro i
        have hi := quasinonexpansive_residual_inner_nonpos (hT i) x y (hyi i)
        have hωi_nonneg : 0 ≤ ω i := (hω_pos i).le
        nlinarith
      have hsum_le :
          ∑ i, 2 * (ω i * inner ℝ (T i x - (x : H)) ((x : H) - (y : H))) ≤
            ∑ i, -(ω i * ‖T i x - (x : H)‖ ^ 2) := by
        exact Finset.sum_le_sum fun i hi ↦ hpointwise i
      have hleft_zero :
          ∑ i, 2 * (ω i * inner ℝ (T i x - (x : H)) ((x : H) - (y : H))) = 0 := by
        rw [← Finset.mul_sum, hsum_inner_eq_zero]
        ring
      have hright :
          ∑ i, -(ω i * ‖T i x - (x : H)‖ ^ 2) = - ∑ i, ω i * ‖T i x - (x : H)‖ ^ 2 := by
        rw [Finset.sum_neg_distrib]
      rw [hright] at hsum_le
      nlinarith [hsum_le, hleft_zero]
    -- Nonnegativity forces each weighted square to vanish, hence every residual is zero.
    have hsum_sq_nonneg : 0 ≤ ∑ i, ω i * ‖T i x - (x : H)‖ ^ 2 := by
      exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hω_pos i).le (sq_nonneg _)
    have hsum_sq_eq_zero : ∑ i, ω i * ‖T i x - (x : H)‖ ^ 2 = 0 := by
      linarith
    rw [Set.mem_iInter]
    intro i
    rw [mem_fixedPointsWithin_iff]
    have hterm_zero : ω i * ‖T i x - (x : H)‖ ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj ↦ mul_nonneg (hω_pos j).le (sq_nonneg _))).1 hsum_sq_eq_zero i
        (Finset.mem_univ i)
    have hnorm_sq_zero : ‖T i x - (x : H)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm_zero with hωi_zero | hsq_zero
      · exact (ne_of_gt (hω_pos i) hωi_zero).elim
      · exact hsq_zero
    have hnorm_zero : ‖T i x - (x : H)‖ = 0 := by
      have hnorm_nonneg : 0 ≤ ‖T i x - (x : H)‖ := norm_nonneg _
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  · intro hx
    -- Every common fixed point is fixed by the weighted average because the weights sum to `1`.
    rw [Set.mem_iInter] at hx
    rw [mem_fixedPointsWithin_iff]
    calc
      ∑ i, ω i • T i x = ∑ i, ω i • (x : H) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact congrArg (fun z : H ↦ ω i • z) ((mem_fixedPointsWithin_iff _).mp (hx i))
      _ = (∑ i, ω i) • (x : H) := by
        rw [Finset.sum_smul]
      _ = (x : H) := by
        simp [hω_sum]

end

/-! Source item: Chap04/Proposition_4_49 -/


section

variable {H : Type u}
variable {D : Set H} {T₁ T₂ : H → H}

/-- Helper for Proposition 4.49: the composition of two self-maps of `D` is again a self-map
of `D`. -/
private lemma mapsTo_comp (hT₁_maps : MapsTo T₁ D D) (hT₂_maps : MapsTo T₂ D D) :
    MapsTo (T₁ ∘ T₂) D D :=
  hT₁_maps.comp hT₂_maps

/-- Helper for Proposition 4.49: a common fixed point of `T₁` and `T₂` is fixed by the
composition `T₁ ∘ T₂`. -/
private lemma comp_mem_fixedPointSetOn_of_mem_inter
    {x : H} (hx : x ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂) :
    x ∈ fixedPointSetOn D (T₁ ∘ T₂) := by
  -- Unpack the two fixed-point conditions and rewrite the composition directly.
  rcases hx with ⟨hx₁, hx₂⟩
  rw [mem_fixedPointSetOn_iff] at hx₁ hx₂ ⊢
  rcases hx₁ with ⟨hxD, hxT₁⟩
  rcases hx₂ with ⟨_, hxT₂⟩
  constructor
  · exact hxD
  · simp [Function.comp, hxT₁, hxT₂]

end

section

variable {H : Type u} [NormedAddCommGroup H]
variable {D : Set H} {T₁ T₂ : H → H}

/-- Helper for Proposition 4.49: the two quasinonexpansive inequalities combine to bound the
distance to a common fixed point after applying `T₁ ∘ T₂`. -/
private lemma norm_comp_le_of_common_fixed
    (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁) (hT₂_qne : QuasinonexpansiveOn D T₂)
    {x y : H} (hx : x ∈ D) (hy₁ : y ∈ fixedPointSetOn D T₁) (hy₂ : y ∈ fixedPointSetOn D T₂) :
    ‖(T₁ ∘ T₂) x - y‖ ≤ ‖x - y‖ := by
  -- Apply quasinonexpansiveness first to `T₁` at `T₂ x`, then to `T₂` at `x`.
  rw [quasinonexpansiveOn_iff] at hT₁_qne hT₂_qne
  calc
    ‖(T₁ ∘ T₂) x - y‖ = ‖T₁ (T₂ x) - y‖ := rfl
    _ ≤ ‖T₂ x - y‖ := hT₁_qne (T₂ x) (hT₂_maps hx) y hy₁
    _ ≤ ‖x - y‖ := hT₂_qne x hx y hy₂

/-- Helper for Proposition 4.49: a fixed point of the composition is fixed by both factors when
the maps share a common fixed point and at least one factor is strictly quasinonexpansive. -/
private lemma mem_inter_fixedPointSetOn_of_mem_comp_of_one_strict
    (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁) (hT₂_qne : QuasinonexpansiveOn D T₂)
    (hFix : (fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂).Nonempty)
    (hstrict :
      StrictlyQuasinonexpansiveOn D T₁ ∨ StrictlyQuasinonexpansiveOn D T₂)
    {x : H} (hx : x ∈ fixedPointSetOn D (T₁ ∘ T₂)) :
    x ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂ := by
  -- Extract the composition fixed-point equation and choose a common fixed point `y`.
  rw [mem_fixedPointSetOn_iff] at hx
  rcases hx with ⟨hxD, hxcomp⟩
  rcases hFix with ⟨y, hy⟩
  rcases hy with ⟨hy₁, hy₂⟩
  rw [quasinonexpansiveOn_iff] at hT₁_qne hT₂_qne
  have hcomp_le : ‖(T₁ ∘ T₂) x - y‖ ≤ ‖T₂ x - y‖ := by
    -- The first inequality in the textbook chain comes from quasinonexpansiveness of `T₁`.
    simpa [Function.comp] using hT₁_qne (T₂ x) (hT₂_maps hxD) y hy₁
  have hT₂_le : ‖T₂ x - y‖ ≤ ‖x - y‖ := hT₂_qne x hxD y hy₂
  have hcomp_eq_norm : ‖(T₁ ∘ T₂) x - y‖ = ‖x - y‖ := by
    -- Rewrite the left endpoint of the chain using `(T₁ ∘ T₂) x = x`.
    simpa [Function.comp] using congrArg (fun z ↦ ‖z - y‖) hxcomp
  have hT₂_ge : ‖x - y‖ ≤ ‖T₂ x - y‖ := by
    -- Equality at the chain endpoints forces the middle term to have the same norm.
    calc
      ‖x - y‖ = ‖(T₁ ∘ T₂) x - y‖ := by simpa [Function.comp, hxcomp] using hcomp_eq_norm.symm
      _ ≤ ‖T₂ x - y‖ := hcomp_le
  have hT₂_eq : ‖T₂ x - y‖ = ‖x - y‖ := le_antisymm hT₂_le hT₂_ge
  have hcomp_ge : ‖T₂ x - y‖ ≤ ‖(T₁ ∘ T₂) x - y‖ := by
    -- The same endpoint equality also forces equality in the first inequality.
    calc
      ‖T₂ x - y‖ ≤ ‖x - y‖ := hT₂_le
      _ = ‖(T₁ ∘ T₂) x - y‖ := by simpa [Function.comp, hxcomp] using hcomp_eq_norm.symm
  have hcomp_eq_mid : ‖(T₁ ∘ T₂) x - y‖ = ‖T₂ x - y‖ := le_antisymm hcomp_le hcomp_ge
  rcases hstrict with hT₁_strict | hT₂_strict
  · rw [strictlyQuasinonexpansiveOn_iff] at hT₁_strict
    have hT₂x_fixed₁ : T₂ x ∈ fixedPointSetOn D T₁ := by
      -- If `T₂ x` were not fixed by `T₁`, strict quasinonexpansiveness of `T₁` would contradict
      -- equality in the first step of the chain.
      by_contra hnot
      have hlt : ‖T₁ (T₂ x) - y‖ < ‖T₂ x - y‖ := by
        exact hT₁_strict (T₂ x) ⟨hT₂_maps hxD, hnot⟩ y hy₁
      have hlt' : ‖(T₁ ∘ T₂) x - y‖ < ‖T₂ x - y‖ := by
        simpa [Function.comp] using hlt
      rw [hcomp_eq_mid] at hlt'
      exact lt_irrefl _ hlt'
    rw [mem_fixedPointSetOn_iff] at hT₂x_fixed₁
    rcases hT₂x_fixed₁ with ⟨_, hT₁T₂x⟩
    have hxT₂ : T₂ x = x := by
      -- Once `T₂ x` is fixed by `T₁`, the composition equation collapses to `T₂ x = x`.
      calc
        T₂ x = T₁ (T₂ x) := hT₁T₂x.symm
        _ = x := by simpa [Function.comp] using hxcomp
    have hx₂ : x ∈ fixedPointSetOn D T₂ := by
      rw [mem_fixedPointSetOn_iff]
      exact ⟨hxD, hxT₂⟩
    have hx₁ : x ∈ fixedPointSetOn D T₁ := by
      -- Rewrite the composition fixed-point equation using `T₂ x = x`.
      rw [mem_fixedPointSetOn_iff]
      constructor
      · exact hxD
      · simpa [Function.comp, hxT₂] using hxcomp
    exact ⟨hx₁, hx₂⟩
  · rw [strictlyQuasinonexpansiveOn_iff] at hT₂_strict
    have hx₂ : x ∈ fixedPointSetOn D T₂ := by
      -- If `x` were not fixed by `T₂`, strict quasinonexpansiveness of `T₂` would contradict
      -- equality in the second step of the chain.
      by_contra hnot
      have hlt : ‖T₂ x - y‖ < ‖x - y‖ := hT₂_strict x ⟨hxD, hnot⟩ y hy₂
      rw [hT₂_eq] at hlt
      exact lt_irrefl _ hlt
    rw [mem_fixedPointSetOn_iff] at hx₂
    rcases hx₂ with ⟨_, hxT₂⟩
    have hx₁ : x ∈ fixedPointSetOn D T₁ := by
      -- After proving `T₂ x = x`, the composition fixed-point equation reduces to `T₁ x = x`.
      rw [mem_fixedPointSetOn_iff]
      constructor
      · exact hxD
      · simpa [Function.comp, hxT₂] using hxcomp
    exact ⟨hx₁, ⟨hxD, hxT₂⟩⟩

/-- Helper for Proposition 4.49: if both factors are strictly quasinonexpansive, then every point
outside the fixed-point set of the composition moves strictly closer to each common fixed point. -/
private lemma norm_comp_lt_of_not_mem_comp_fixed
    (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁)
    (hT₁_strict : StrictlyQuasinonexpansiveOn D T₁)
    (hT₂_strict : StrictlyQuasinonexpansiveOn D T₂)
    {x y : H} (hx : x ∈ D \ fixedPointSetOn D (T₁ ∘ T₂))
    (hy : y ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂) :
    ‖(T₁ ∘ T₂) x - y‖ < ‖x - y‖ := by
  -- Split on whether `x` is already fixed by `T₂`, matching the textbook proof.
  rw [quasinonexpansiveOn_iff] at hT₁_qne
  rw [strictlyQuasinonexpansiveOn_iff] at hT₁_strict hT₂_strict
  rcases hy with ⟨hy₁, hy₂⟩
  by_cases hx₂ : x ∈ fixedPointSetOn D T₂
  · have hx₁_not : x ∉ fixedPointSetOn D T₁ := by
      -- If `x` were fixed by both factors, it would already be fixed by the composition.
      intro hx₁
      exact hx.2 (comp_mem_fixedPointSetOn_of_mem_inter ⟨hx₁, hx₂⟩)
    have hlt : ‖T₁ x - y‖ < ‖x - y‖ := hT₁_strict x ⟨hx.1, hx₁_not⟩ y hy₁
    rw [mem_fixedPointSetOn_iff] at hx₂
    rcases hx₂ with ⟨_, hxT₂⟩
    -- Replacing `T₂ x` by `x` reduces the composition to the strict `T₁` inequality.
    simpa [Function.comp, hxT₂] using hlt
  · have hlt₂ : ‖T₂ x - y‖ < ‖x - y‖ := hT₂_strict x ⟨hx.1, hx₂⟩ y hy₂
    have hle₁ : ‖(T₁ ∘ T₂) x - y‖ ≤ ‖T₂ x - y‖ := by
      -- The first map is only used quasinonexpansively in this branch.
      simpa [Function.comp] using hT₁_qne (T₂ x) (hT₂_maps hx.1) y hy₁
    exact lt_of_le_of_lt hle₁ hlt₂

-- Proof sketch: one inclusion is immediate from the definition of fixed points. For the reverse
-- inclusion, choose a common fixed point `y`; quasinonexpansiveness gives
-- `‖(T₁ ∘ T₂) x - y‖ ≤ ‖T₂ x - y‖ ≤ ‖x - y‖`, and the equality `(T₁ ∘ T₂) x = x` forces equality
-- throughout. The strict quasinonexpansiveness of at least one factor then shows first that
-- `x ∈ fixedPointSetOn D T₂` or `T₂ x ∈ fixedPointSetOn D T₁`, and hence `x` is fixed by both
-- maps.
/-- Proposition 4.49 (1): if `T₁` and `T₂` are quasinonexpansive self-maps of `D` with a common
fixed point, and at least one of them is strictly quasinonexpansive, then the fixed points of the
composition `T₁ ∘ T₂` are exactly the common fixed points of `T₁` and `T₂` in `D`. -/
theorem fixedPointSetOn_comp_eq_inter_of_one_strictlyQuasinonexpansive
    (_hT₁_maps : MapsTo T₁ D D) (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁) (hT₂_qne : QuasinonexpansiveOn D T₂)
    (hFix : (fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂).Nonempty)
    (hstrict :
      StrictlyQuasinonexpansiveOn D T₁ ∨ StrictlyQuasinonexpansiveOn D T₂) :
    fixedPointSetOn D (T₁ ∘ T₂) = fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂ := by
  -- Prove the two set inclusions separately, following the textbook chain-of-inequalities route.
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_inter_fixedPointSetOn_of_mem_comp_of_one_strict
      hT₂_maps hT₁_qne hT₂_qne hFix hstrict hx
  · intro x hx
    exact comp_mem_fixedPointSetOn_of_mem_inter hx

-- Proof sketch: let `y ∈ fixedPointSetOn D (T₁ ∘ T₂)`. By part (1), `y` is a common fixed point
-- of `T₁` and `T₂`. Then quasinonexpansiveness of `T₁` at `T₂ x` and of `T₂` at `x` gives
-- `‖(T₁ ∘ T₂) x - y‖ ≤ ‖T₂ x - y‖ ≤ ‖x - y‖`.
/-- Proposition 4.49 (2): under the same hypotheses, the composition `T₁ ∘ T₂` is a
quasinonexpansive self-map of `D`. -/
theorem quasinonexpansiveOn_comp_of_one_strictlyQuasinonexpansive
    (hT₁_maps : MapsTo T₁ D D) (hT₂_maps : MapsTo T₂ D D)
    (hT₁_qne : QuasinonexpansiveOn D T₁) (hT₂_qne : QuasinonexpansiveOn D T₂)
    (hFix : (fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂).Nonempty)
    (hstrict :
      StrictlyQuasinonexpansiveOn D T₁ ∨ StrictlyQuasinonexpansiveOn D T₂) :
    MapsTo (T₁ ∘ T₂) D D ∧ QuasinonexpansiveOn D (T₁ ∘ T₂) := by
  -- Rewrite fixed points of the composition as common fixed points, then apply the two-step norm
  -- estimate packaged in `norm_comp_le_of_common_fixed`.
  constructor
  · exact mapsTo_comp hT₁_maps hT₂_maps
  · rw [quasinonexpansiveOn_iff]
    intro x hx y hy
    have hy' : y ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂ := by
      rw [fixedPointSetOn_comp_eq_inter_of_one_strictlyQuasinonexpansive
        hT₁_maps hT₂_maps hT₁_qne hT₂_qne hFix hstrict] at hy
      exact hy
    exact norm_comp_le_of_common_fixed hT₂_maps hT₁_qne hT₂_qne hx hy'.1 hy'.2

-- Proof sketch: let `y ∈ fixedPointSetOn D (T₁ ∘ T₂)`. By part (1), `y` is fixed by both `T₁`
-- and `T₂`. If `x ∉ fixedPointSetOn D T₂`, apply strict quasinonexpansiveness of `T₂` and then
-- quasinonexpansiveness of `T₁`. If `x ∈ fixedPointSetOn D T₂`, then `x ∉ fixedPointSetOn D T₁`
-- because otherwise `x` would already be fixed by `T₁ ∘ T₂`; now strict quasinonexpansiveness of
-- `T₁` yields the desired strict inequality.
/-- Proposition 4.49 (3): if both `T₁` and `T₂` are strictly quasinonexpansive self-maps of `D`
with a common fixed point, then their composition `T₁ ∘ T₂` is a strictly quasinonexpansive
self-map of `D`. -/
theorem strictlyQuasinonexpansiveOn_comp
    (hT₁_maps : MapsTo T₁ D D) (hT₂_maps : MapsTo T₂ D D)
    (hFix : (fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂).Nonempty)
    (hT₁_strict : StrictlyQuasinonexpansiveOn D T₁)
    (hT₂_strict : StrictlyQuasinonexpansiveOn D T₂) :
    MapsTo (T₁ ∘ T₂) D D ∧ StrictlyQuasinonexpansiveOn D (T₁ ∘ T₂) := by
  -- Identify fixed points of the composition with common fixed points and then split on whether
  -- the current point is fixed by `T₂`.
  have hT₁_qne : QuasinonexpansiveOn D T₁ :=
    StrictlyQuasinonexpansiveOn.quasinonexpansiveOn hT₁_strict
  have hT₂_qne : QuasinonexpansiveOn D T₂ :=
    StrictlyQuasinonexpansiveOn.quasinonexpansiveOn hT₂_strict
  constructor
  · exact mapsTo_comp hT₁_maps hT₂_maps
  · rw [strictlyQuasinonexpansiveOn_iff]
    intro x hx y hy
    have hy' : y ∈ fixedPointSetOn D T₁ ∩ fixedPointSetOn D T₂ := by
      rw [fixedPointSetOn_comp_eq_inter_of_one_strictlyQuasinonexpansive
        hT₁_maps hT₂_maps hT₁_qne hT₂_qne hFix (.inl hT₁_strict)] at hy
      exact hy
    exact norm_comp_lt_of_not_mem_comp_fixed hT₂_maps hT₁_qne hT₁_strict hT₂_strict hx hy'

end
