import Mathlib
import Foundation.Analysis.ExtendedRealFunctions

/-!
# Strong convexity of extended-real-valued functions

Strong convexity with a quadratic parameter, expressed by its Jensen
inequality on the effective domain.
-/

/-- Strong convexity with parameter `ρ`, expressed by its Jensen inequality. -/
def IsStronglyConvexWith {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ x ∈ ERealFunction.dom f, ∀ y ∈ ERealFunction.dom f, ∀ t : ℝ,
    t ∈ Set.Icc 0 1 →
    f ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * f x + (t : EReal) * f y -
      ((ρ / 2 * t * (1 - t) * ‖x - y‖ ^ 2 : ℝ) : EReal)

/-- Real-valued strong convexity in the Jensen form of the dynamics literature
  (`f ((1-t)•x+t•y) ≤ (1-t) f x + t f y - (δ/2) t (1-t) ‖x-y‖²`) is exactly
  `IsStronglyConvexWith` of the pointwise `EReal` lift of `f`.  This is the
  readback bridge for papers that state strong convexity with real values. -/
theorem isStronglyConvexWith_iff_real_jensen {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (δ : ℝ) :
    IsStronglyConvexWith (fun x => (f x : EReal)) δ ↔
      0 < δ ∧ ∀ x y : H, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        f ((1 - t) • x + t • y) ≤ (1 - t) * f x + t * f y -
          (δ / 2) * t * (1 - t) * ‖x - y‖ ^ 2 := by
  constructor
  · rintro ⟨hδ, hJ⟩
    refine ⟨hδ, fun x y t ht => ?_⟩
    have hx : x ∈ ERealFunction.dom (fun x => (f x : EReal)) := by simp [ERealFunction.dom]
    have hy : y ∈ ERealFunction.dom (fun x => (f x : EReal)) := by simp [ERealFunction.dom]
    have hJ' := hJ x hx y hy t ht
    simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub] at hJ'
    exact EReal.coe_le_coe_iff.mp hJ'
  · rintro ⟨hδ, hJ⟩
    refine ⟨hδ, fun x hx y hy t ht => ?_⟩
    simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (hJ x y t ht)

/-- A support estimate for real-valued strongly convex functions: if `f` is
  strongly convex with parameter `μ` in the Jensen form, then for any point `u`
  at which the linear functional `inner ℝ p` is a (Fréchet) subgradient, one
  has `f u - f z + μ / 2 * ‖u - z‖² ≤ inner ℝ p (u - z)` for every `z`.

  Proof helper for Theorem 1 of Attouch, Balhag, Chbani, Riahi, "Damped
  inertial dynamics with vanishing Tikhonov regularization: Strong asymptotic
  convergence towards the minimum norm solution", J. Differential Equations
  311 (2022) 29-58. -/
theorem strongConvex_support_at
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (μ : ℝ)
    (hstrong : ∀ u v : H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • u + b • v) ≤ a * f u + b * f v - μ / 2 * a * b * ‖u - v‖ ^ 2)
    (u z p : H) (hderiv : HasFDerivAt f (innerSL ℝ p) u) :
    f u - f z + μ / 2 * ‖u - z‖ ^ 2 ≤ inner ℝ p (u - z) := by
  have hSC : StrongConvexOn Set.univ μ f := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    convert hstrong x y a b ha hb hab using 1
    all_goals ring
  have hconv : ConvexOn ℝ Set.univ (fun x : H => f x - μ / 2 * ‖x‖ ^ 2) :=
    strongConvexOn_iff_convex.mp hSC
  let d : H := z - u
  let ell : ℝ → H := fun s => u + s • d
  let phi : ℝ → ℝ := fun s => f (ell s) - μ / 2 * ‖ell s‖ ^ 2
  have hell : HasDerivAt ell d 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := u)).add
      ((hasDerivAt_id (x := (0 : ℝ))).smul_const d) using 1
    all_goals simp
  have hphi_conv : ConvexOn ℝ Set.univ phi := by
    rw [ConvexOn]
    refine ⟨convex_univ, ?_⟩
    intro r hr s hs a b ha hb hab
    have hline : ell (a * r + b * s) = a • ell r + b • ell s := by
      dsimp [ell]
      calc
        u + (a * r + b * s) • d = (a + b) • u + (a * r + b * s) • d := by rw [hab, one_smul]
        _ = a • (u + r • d) + b • (u + s • d) := by module
    change f (ell (a * r + b * s)) - μ / 2 * ‖ell (a * r + b * s)‖ ^ 2 ≤
      a * (f (ell r) - μ / 2 * ‖ell r‖ ^ 2) + b * (f (ell s) - μ / 2 * ‖ell s‖ ^ 2)
    rw [hline]
    exact hconv.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hfd : HasDerivAt (fun s : ℝ => f (ell s)) (inner ℝ p d) 0 := by
    have hderiv' : HasFDerivAt f (innerSL ℝ p) (ell 0) := by
      simpa [ell] using hderiv
    have h := hderiv'.comp 0 hell.hasFDerivAt
    simpa [ell, d, innerSL_apply_apply] using h.hasDerivAt
  have hnorm : HasDerivAt (fun s : ℝ => ‖ell s‖ ^ 2) (2 * inner ℝ u d) 0 := by
    simpa [ell, d, real_inner_comm] using hell.norm_sq
  have hphi_deriv : HasDerivAt phi (inner ℝ p d - μ * inner ℝ u d) 0 := by
    have h := hfd.sub (hnorm.const_mul (μ / 2))
    convert h using 1
    all_goals simp
    all_goals ring_nf
  have hslope := hphi_conv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    zero_lt_one hphi_deriv
  simp only [slope_def_field] at hslope
  have hnorm_expand : ‖u - z‖ ^ 2 = ‖u‖ ^ 2 - inner ℝ u z * 2 + ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm z u]
    ring
  dsimp [phi, ell, d] at hslope
  simp only [one_smul, add_sub_cancel, zero_smul, add_zero, sub_zero, div_one,
    tsub_le_iff_right] at hslope
  rw [hnorm_expand]
  simp only [inner_sub_right] at hslope ⊢
  rw [real_inner_self_eq_norm_sq] at hslope
  nlinarith
