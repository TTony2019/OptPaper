import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_1
import Mathlib

open scoped InnerProductSpace

open ERealFunction

/-- The dry-friction property: convexity, continuity, zero minimum, and an interior subgradient. -/
structure DryFriction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (phi : H → ℝ) : Prop where
  convex : ConvexOn ℝ Set.univ phi
  continuous : Continuous phi
  minimum_at_zero : ∀ x, phi 0 ≤ phi x
  value_at_zero : phi 0 = 0
  interior_subgradient : (0 : H) ∈ interior (subdifferential phi 0)

/-- A continuous convex real-valued function, viewed as an extended-real function, lies in `Γ₀(H)`,
so that Foundation's proximity operator `Prox[γ, phi.toEReal, _]` is available for it. -/
theorem toEReal_mem_gammaZero_of_continuous_convexOn_univ {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {phi : H → ℝ} (hcont : Continuous phi)
    (hconv : ConvexOn ℝ Set.univ phi) :
    phi.toEReal ∈ Γ₀(H) := by
  rw [ERealFunction.mem_gammaZero_iff]
  constructor
  · simpa using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨?_, ?_, ?_⟩
    · rw [Function.effectiveDomain_toEReal]
      exact Set.univ_nonempty
    · rw [Function.effectiveDomain_toEReal]
    · intro x _ y _ a ha0 ha1
      have hreal : phi (a • x + (1 - a) • y) ≤ a * phi x + (1 - a) * phi y := by
        simpa [smul_eq_mul] using
          hconv.2 (by simp : x ∈ (Set.univ : Set H)) (by simp : y ∈ (Set.univ : Set H))
            ha0.le (sub_pos.mpr ha1).le (by ring)
      have hcast : (((phi (a • x + (1 - a) • y) : ℝ) : EReal)) ≤
          (((a * phi x + (1 - a) * phi y : ℝ) : EReal)) := by
        exact_mod_cast hreal
      simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

/-- The dry-friction function lies in `Γ₀(H)`, so Foundation's proximity operator is available. -/
theorem DryFriction.toEReal_mem_gammaZero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {phi : H → ℝ} (h : DryFriction phi) :
    phi.toEReal ∈ Γ₀(H) :=
  toEReal_mem_gammaZero_of_continuous_convexOn_univ h.continuous h.convex

/-- Dry friction with an explicit sharpness radius `r`: the dry-friction property together with
the radius-`r` subgradient ball at the origin.  Equivalently (Lemma 1.1), `r ‖x‖ ≤ φ x` for all
`x`, i.e. `φ` has a sharp minimum at the origin with coefficient `r`. -/
structure DF_r {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (r : ℝ) : Prop extends DryFriction phi where
  radius_pos : 0 < r
  ball_subset : Metric.ball (0 : H) r ⊆ subdifferential phi 0

/-- A radius-`r` dry friction is in particular a `Γ₀` function. -/
theorem DF_r.toEReal_mem_gammaZero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {phi : H → ℝ} {r : ℝ} (h : DF_r phi r) : phi.toEReal ∈ Γ₀(H) :=
  h.toDryFriction.toEReal_mem_gammaZero
