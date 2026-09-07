import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_8

namespace Alvarez2002

/-- Product-space energy whose gradient flow is the rescaled `(g-DIN)` system. -/
noncomputable def gradientSystemEnergy {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : H → ℝ) (β a b : ℝ) (x z : H) : ℝ :=
  β * Φ x + (1 / 2) * ‖Real.sqrt a • x + Real.sqrt b • z‖ ^ 2

/-- The system obtained from `(g-DIN)` by setting `z = √(b/a) • y`.

This has the same convention as `IsSolution_gDIN`: derivatives are written with
`deriv`, equations are imposed on the nonnegative half-line, and initial data
are part of the predicate. -/
def IsRescaledGDINTrajectory {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ) (x₀ z₀ : H) (x z : ℝ → H) : Prop :=
  (∀ t, 0 ≤ t →
    deriv x t + β • gradient Φ (x t) + a • x t + Real.sqrt (a * b) • z t = 0) ∧
  (∀ t, 0 ≤ t →
    deriv z t + Real.sqrt (a * b) • x t + b • z t = 0) ∧
  (x 0 = x₀) ∧ (z 0 = z₀)

/-- The product-space gradient system for `gradientSystemEnergy`.

The two partial derivatives of the energy are recorded explicitly, together
with the gradient-flow equation and the initial data. -/
def IsGradientSystemTrajectory {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ) (x₀ z₀ : H) (x z : ℝ → H) : Prop :=
  (∀ t, 0 ≤ t →
    HasFDerivAt (fun u => gradientSystemEnergy Φ β a b u (z t))
      (innerSL ℝ (β • gradient Φ (x t) + a • x t + Real.sqrt (a * b) • z t)) (x t) ∧
    HasFDerivAt (fun w => gradientSystemEnergy Φ β a b (x t) w)
      (innerSL ℝ (Real.sqrt (a * b) • x t + b • z t)) (z t)) ∧
  (∀ t, 0 ≤ t →
    (deriv x t, deriv z t) +
        (β • gradient Φ (x t) + a • x t + Real.sqrt (a * b) • z t,
          Real.sqrt (a * b) • x t + b • z t) = 0) ∧
  (x 0 = x₀) ∧ (z 0 = z₀)

theorem gradientSystemEnergy_hasFDerivAt_fst
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (ha : 0 < a) (_hb : 0 < b)
    (hgradΦ : ∀ u, HasFDerivAt Φ (innerSL ℝ (gradient Φ u)) u)
    (u w : H) :
    HasFDerivAt (fun v => gradientSystemEnergy Φ β a b v w)
      (innerSL ℝ (β • gradient Φ u + a • u + Real.sqrt (a * b) • w)) u := by
  have haa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have haasq : Real.sqrt a ^ 2 = a := by simpa [pow_two] using haa
  have hab : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha.le b
  let q : H → H := fun v => Real.sqrt a • v + Real.sqrt b • w
  have hq : HasFDerivAt q ((Real.sqrt a) • (1 : H →L[ℝ] H)) u := by
    convert (((Real.sqrt a) • (1 : H →L[ℝ] H)).hasFDerivAt.add
      (hasFDerivAt_const (Real.sqrt b • w) u)) using 1
    all_goals
      ext v
      simp
  have hquadratic : HasFDerivAt (fun v => (1 / 2 : ℝ) * ‖q v‖ ^ 2)
      ((1 / 2 : ℝ) • (2 • (innerSL ℝ (q u)).comp ((Real.sqrt a) • (1 : H →L[ℝ] H)))) u := by
    simpa using (hq.norm_sq.const_mul (1 / 2 : ℝ))
  have hpotential := (hgradΦ u).const_mul β
  have hsum := hpotential.add hquadratic
  convert hsum using 1
  · ext h
    simp [q]
    ring_nf
    rw [haasq, hab]
    ring

theorem gradientSystemEnergy_hasFDerivAt_snd
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (u w : H) :
    HasFDerivAt (fun v => gradientSystemEnergy Φ β a b u v)
      (innerSL ℝ (Real.sqrt (a * b) • u + b • w)) w := by
  have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have hbbsq : Real.sqrt b ^ 2 = b := by simpa [pow_two] using hbb
  have hab : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha.le b
  let q : H → H := fun v => Real.sqrt a • u + Real.sqrt b • v
  have hq : HasFDerivAt q ((Real.sqrt b) • (1 : H →L[ℝ] H)) w := by
    convert ((hasFDerivAt_const (Real.sqrt a • u) w).add
      ((Real.sqrt b) • (1 : H →L[ℝ] H)).hasFDerivAt) using 1
    all_goals
      ext v
      simp
  have hquadratic : HasFDerivAt (fun v => (1 / 2 : ℝ) * ‖q v‖ ^ 2)
      ((1 / 2 : ℝ) • (2 • (innerSL ℝ (q w)).comp ((Real.sqrt b) • (1 : H →L[ℝ] H)))) w := by
    simpa using (hq.norm_sq.const_mul (1 / 2 : ℝ))
  have hsum := (hasFDerivAt_const (β * Φ u) w).add hquadratic
  convert hsum using 1
  · ext h
    simp [q]
    ring_nf
    rw [hbbsq, hab]
    ring

private theorem sqrt_ab_mul_sqrt_b_div_a (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) * Real.sqrt (b / a) = b := by
  rw [Real.sqrt_mul ha.le b, Real.sqrt_div hb.le a]
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  field_simp
  nlinarith [Real.sq_sqrt hb.le]

private theorem sqrt_b_div_a_mul_a (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (b / a) * a = Real.sqrt (a * b) := by
  rw [Real.sqrt_mul ha.le b, Real.sqrt_div hb.le a]
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  field_simp
  nlinarith [Real.sq_sqrt ha.le]

/-- Rescaling `y = √(a/b) • z` converts the definition from `def_8` into the
first-order system on `(x,z)`. -/
theorem isSolution_gDIN_iff_rescaled_gDIN
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (x₀ y₀ : H) (x y : ℝ → H) :
    IsSolution_gDIN Φ β a b x₀ y₀ x y ↔
      IsRescaledGDINTrajectory Φ β a b x₀
        (Real.sqrt (b / a) • y₀) x (fun t => Real.sqrt (b / a) • y t) := by
  have hcpos : 0 < Real.sqrt (b / a) := Real.sqrt_pos.2 (div_pos hb ha)
  have hcne : Real.sqrt (b / a) ≠ 0 := ne_of_gt hcpos
  constructor
  · rintro ⟨hx, hy, hx₀, hy₀⟩
    refine ⟨?_, ?_, hx₀, ?_⟩
    · intro t ht
      have h := hx t ht
      dsimp
      rw [smul_smul, sqrt_ab_mul_sqrt_b_div_a a b ha hb]
      simpa [add_assoc] using h
    · intro t ht
      have h := hy t ht
      have hscaled := congrArg (fun q : H => Real.sqrt (b / a) • q) h
      change deriv (Real.sqrt (b / a) • y) t +
        Real.sqrt (a * b) • x t + b • (Real.sqrt (b / a) • y t) = 0
      rw [deriv_const_smul_field]
      rw [← sqrt_b_div_a_mul_a a b ha hb]
      simpa [smul_add, smul_smul, mul_comm, add_assoc] using hscaled
    · simpa [hy₀]
  · rintro ⟨hx, hz, hx₀, hz₀⟩
    refine ⟨?_, ?_, hx₀, ?_⟩
    · intro t ht
      have h := hx t ht
      dsimp at h
      rw [smul_smul, sqrt_ab_mul_sqrt_b_div_a a b ha hb] at h
      simpa [add_assoc] using h
    · intro t ht
      have h := hz t ht
      change deriv (Real.sqrt (b / a) • y) t +
        Real.sqrt (a * b) • x t + b • (Real.sqrt (b / a) • y t) = 0 at h
      rw [deriv_const_smul_field] at h
      rw [← sqrt_b_div_a_mul_a a b ha hb] at h
      have hscaled : Real.sqrt (b / a) •
          (deriv y t + a • x t + b • y t) = 0 := by
        simpa [smul_add, smul_smul, mul_comm, add_assoc] using h
      exact (smul_eq_zero_iff_right hcne).mp hscaled
    · apply (smul_right_injective H hcne)
      simpa using hz₀

/-- Under positive coefficients, the rescaled equations are precisely the
product-space gradient flow of `gradientSystemEnergy`. -/
theorem rescaled_gDIN_iff_gradient_system
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hΦ : ContDiff ℝ 1 Φ)
    (x₀ z₀ : H) (x z : ℝ → H) :
    IsRescaledGDINTrajectory Φ β a b x₀ z₀ x z ↔
      IsGradientSystemTrajectory Φ β a b x₀ z₀ x z := by
  have hgradΦ : ∀ u, HasFDerivAt Φ (innerSL ℝ (gradient Φ u)) u := by
    intro u
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) u).hasGradientAt.hasFDerivAt)
  constructor
  · rintro ⟨hx, hz, hx₀, hz₀⟩
    refine ⟨?_, ?_, hx₀, hz₀⟩
    · intro t ht
      exact ⟨gradientSystemEnergy_hasFDerivAt_fst Φ β a b ha hb hgradΦ
          (x t) (z t),
        gradientSystemEnergy_hasFDerivAt_snd Φ β a b ha hb (x t) (z t)⟩
    · intro t ht
      apply Prod.ext
      · simpa [add_assoc] using hx t ht
      · simpa [add_assoc] using hz t ht
  · rintro ⟨_, hpair, hx₀, hz₀⟩
    refine ⟨?_, ?_, hx₀, hz₀⟩
    · intro t ht
      simpa [add_assoc] using congrArg Prod.fst (hpair t ht)
    · intro t ht
      simpa [add_assoc] using congrArg Prod.snd (hpair t ht)

end Alvarez2002
