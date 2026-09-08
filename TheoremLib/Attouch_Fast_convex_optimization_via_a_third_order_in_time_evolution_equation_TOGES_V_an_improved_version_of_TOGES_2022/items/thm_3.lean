import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_5
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_6
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_def_2
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_2
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_4

private theorem sInf_range_eq_value_of_global_min {H : Type*} (f : H → ℝ) (xStar : H)
    (hmin : ∀ x, f xStar ≤ f x) : sInf (Set.range f) = f xStar := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨f xStar, ?_⟩
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hmin x
    · exact ⟨xStar, rfl⟩
  · apply le_csInf
    · exact ⟨f xStar, ⟨xStar, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hmin x

/-- The standard change of variables for the strongly convex third-order equation. -/
private theorem strongly_convex_change_of_variables {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (u firstDerivative secondDerivative thirdDerivative : ℝ → H) (g : H → H)
    (mu t0 : ℝ) (hmu : 0 < mu) (hu : ∀ t, t0 ≤ t → HasDerivAt u (firstDerivative t) t)
    (hFirst : ∀ t, t0 ≤ t → HasDerivAt firstDerivative (secondDerivative t) t)
    (hSecond : ∀ t, t0 ≤ t → HasDerivAt secondDerivative (thirdDerivative t) t)
    (hTrajectory : 0 < mu ∧ ∀ t : ℝ,
      thirdDerivative t + (3 * Real.sqrt mu) • secondDerivative t + (2 * mu) • firstDerivative t +
        Real.sqrt mu • g (u t + (Real.sqrt mu)⁻¹ • firstDerivative t) = 0) :
    let a := Real.sqrt mu
    let y : ℝ → H := fun t => u t + a⁻¹ • firstDerivative t
    let yFirst : ℝ → H := fun t => firstDerivative t + a⁻¹ • secondDerivative t
    let ySecond : ℝ → H := fun t => secondDerivative t + a⁻¹ • thirdDerivative t
    (∀ t, t0 ≤ t → HasDerivAt y (yFirst t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt yFirst (ySecond t) t) ∧
      ∀ t, t0 ≤ t → ySecond t + (2 * a) • yFirst t + g (y t) = 0 := by
  dsimp
  let a := Real.sqrt mu
  have ha : 0 < a := by simpa [a] using Real.sqrt_pos.2 hmu
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha2 : a ^ 2 = mu := by simpa [a] using Real.sq_sqrt hmu.le
  constructor
  · intro t ht
    exact (hu t ht).add ((hFirst t ht).const_smul a⁻¹)
  constructor
  · intro t ht
    exact (hFirst t ht).add ((hSecond t ht).const_smul a⁻¹)
  · intro t ht
    have hscaled := congrArg (fun q : H => a⁻¹ • q) (hTrajectory.2 t)
    simp only [smul_zero, smul_add, smul_smul] at hscaled
    have hainv : a⁻¹ * mu = a := by
      rw [← ha2]
      field_simp [ha0]
    have hthree : a⁻¹ * (3 * a) = 3 := by
      field_simp [ha0]
    have hgrad : a⁻¹ * a = 1 := by field_simp [ha0]
    have hgrad' : a * a⁻¹ = 1 := by simpa [mul_comm] using hgrad
    have htwo : a⁻¹ * (2 * mu) = 2 * a := by
      rw [← ha2]
      field_simp [ha0]
    dsimp only [a] at hscaled hainv hthree hgrad hgrad' htwo ⊢
    calc
      _ = (Real.sqrt mu)⁻¹ • thirdDerivative t + (3 : ℝ) • secondDerivative t +
          ((Real.sqrt mu)⁻¹ * (2 * mu)) • firstDerivative t +
          ((Real.sqrt mu)⁻¹ * Real.sqrt mu) • g
            (u t + (Real.sqrt mu)⁻¹ • firstDerivative t) := by
        have hcross : (2 * Real.sqrt mu) * (Real.sqrt mu)⁻¹ = 2 := by
          rw [mul_assoc, hgrad']
          ring
        rw [htwo, hgrad]
        rw [smul_add, smul_smul, hcross]
        module
      _ = 0 := by simpa [hthree] using hscaled

private theorem strongly_convex_energy_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (g : H → H) (xStar : H) (a s : ℝ)
    (y yFirst ySecond : ℝ → H) (hGrad : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hy : HasDerivAt y (yFirst s) s) (hyFirst : HasDerivAt yFirst (ySecond s) s) :
    HasDerivAt
      (fun r => f (y r) - f xStar + (1 / 2 : ℝ) * ‖a • (y r - xStar) + yFirst r‖ ^ 2)
      (inner ℝ (g (y s)) (yFirst s) +
        inner ℝ (a • (y s - xStar) + yFirst s) (a • yFirst s + ySecond s)) s := by
  have hobj : HasDerivAt (fun r => f (y r) - f xStar)
      (inner ℝ (g (y s)) (yFirst s)) s := by
    simpa [innerSL_apply_apply] using ((hGrad (y s)).comp_hasDerivAt s hy).sub_const (f xStar)
  have hv : HasDerivAt (fun r => a • (y r - xStar) + yFirst r)
      (a • yFirst s + ySecond s) s := by
    simpa using ((hy.sub_const xStar).const_smul a).add hyFirst
  have hkin := hv.norm_sq.const_mul (1 / 2 : ℝ)
  convert hobj.add hkin using 1
  all_goals ring_nf

private theorem strongly_convex_energy_decay {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (g : H → H) (xStar : H) (a mu t0 : ℝ)
    (y yFirst ySecond : ℝ → H)
    (hStrong : ∀ x z : H, f z ≥ f x + inner ℝ (g x) (z - x) +
      (mu / 2) * ‖z - x‖ ^ 2)
    (hGrad : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x) (ha : 0 < a)
    (ha2 : a ^ 2 = mu) (hy : ∀ s, t0 ≤ s → HasDerivAt y (yFirst s) s)
    (hyFirst : ∀ s, t0 ≤ s → HasDerivAt yFirst (ySecond s) s)
    (hODE : ∀ s, t0 ≤ s → ySecond s + (2 * a) • yFirst s + g (y s) = 0) :
    ∀ s, t0 ≤ s →
      HasDerivAt (fun r => f (y r) - f xStar + (1 / 2 : ℝ) *
        ‖a • (y r - xStar) + yFirst r‖ ^ 2)
        (deriv (fun r => f (y r) - f xStar + (1 / 2 : ℝ) *
          ‖a • (y r - xStar) + yFirst r‖ ^ 2) s) s ∧
      deriv (fun r => f (y r) - f xStar + (1 / 2 : ℝ) *
        ‖a • (y r - xStar) + yFirst r‖ ^ 2) s +
        a * (f (y s) - f xStar + (1 / 2 : ℝ) *
          ‖a • (y s - xStar) + yFirst s‖ ^ 2) ≤ 0 := by
  intro s hs
  let E : ℝ → ℝ := fun r => f (y r) - f xStar + (1 / 2 : ℝ) *
    ‖a • (y r - xStar) + yFirst r‖ ^ 2
  have hderiv := strongly_convex_energy_hasDerivAt f g xStar a s y yFirst ySecond hGrad
    (hy s hs) (hyFirst s hs)
  have hD : deriv E s = inner ℝ (g (y s)) (yFirst s) +
      inner ℝ (a • (y s - xStar) + yFirst s) (a • yFirst s + ySecond s) := hderiv.deriv
  have hode0 : ySecond s + ((2 * a) • yFirst s + g (y s)) = 0 := by
    simpa [add_assoc] using hODE s hs
  have hode : ySecond s = -((2 * a) • yFirst s + g (y s)) :=
    (eq_neg_iff_add_eq_zero).2 hode0
  let d : H := y s - xStar
  let q : H := yFirst s
  let g : H := g (y s)
  have hD' : deriv E s = -a * inner ℝ g d - a ^ 2 * inner ℝ d q - a * ‖q‖ ^ 2 := by
    rw [hD, hode]
    change inner ℝ g q + inner ℝ (a • d + q)
      (a • q + -((2 * a) • q + g)) = _
    simp only [inner_add_left, inner_add_right, inner_neg_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm d g, real_inner_comm g q]
    ring
  have hstrong := hStrong (y s) xStar
  have hstrong' : f (y s) - f xStar + (a ^ 2 / 2) * ‖d‖ ^ 2 ≤ inner ℝ g d := by
    change f xStar ≥ f (y s) + inner ℝ g (xStar - y s) + (mu / 2) * ‖xStar - y s‖ ^ 2 at hstrong
    rw [show xStar - y s = -d by simp [d], inner_neg_right, norm_neg, ← ha2] at hstrong
    linarith
  have hnorm : ‖a • d + q‖ ^ 2 = a ^ 2 * ‖d‖ ^ 2 + 2 * a * inner ℝ d q + ‖q‖ ^ 2 := by
    rw [show ‖a • d + q‖ ^ 2 = inner ℝ (a • d + q) (a • d + q) by
      rw [real_inner_self_eq_norm_sq]]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm q d]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.le]
    ring
  have hnonneg : 0 ≤ ‖q‖ ^ 2 := sq_nonneg _
  constructor
  · rw [← hD] at hderiv
    exact hderiv
  · change deriv E s + a * E s ≤ 0
    rw [hD']
    change -a * inner ℝ g d - a ^ 2 * inner ℝ d q - a * ‖q‖ ^ 2 +
      a * (f (y s) - f xStar + (1 / 2 : ℝ) * ‖a • d + q‖ ^ 2) ≤ 0
    rw [hnorm]
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hstrong')]

private theorem strongly_convex_distance_decay {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (xStar : H) (a t0 C : ℝ) (y yFirst : ℝ → H) (ha : 0 < a)
    (hy : ∀ s, t0 ≤ s → HasDerivAt y (yFirst s) s)
    (hMomentum : ∀ s, t0 ≤ s →
      ‖a • (y s - xStar) + yFirst s‖ ^ 2 ≤ 2 * C * Real.exp (-a * s)) :
    ∀ s, t0 ≤ s →
      HasDerivAt (fun r => a * ‖y r - xStar‖ ^ 2)
        (deriv (fun r => a * ‖y r - xStar‖ ^ 2) s) s ∧
      deriv (fun r => a * ‖y r - xStar‖ ^ 2) s + a * (a * ‖y s - xStar‖ ^ 2) ≤
        2 * C * Real.exp (-a * s) := by
  intro s hs
  let Z : ℝ → ℝ := fun r => a * ‖y r - xStar‖ ^ 2
  let d : H := y s - xStar
  let q : H := yFirst s
  have hderiv := ((hy s hs).sub_const xStar).norm_sq.const_mul a
  have hD : deriv Z s = 2 * a * inner ℝ d q := by
    rw [hderiv.deriv]
    dsimp [d, q]
    ring
  have hnorm : ‖a • d + q‖ ^ 2 = a ^ 2 * ‖d‖ ^ 2 + 2 * a * inner ℝ d q + ‖q‖ ^ 2 := by
    rw [show ‖a • d + q‖ ^ 2 = inner ℝ (a • d + q) (a • d + q) by
      rw [real_inner_self_eq_norm_sq]]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm q d]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.le]
    ring
  have hmomentum := hMomentum s hs
  have hnonneg : 0 ≤ ‖q‖ ^ 2 := sq_nonneg _
  constructor
  · have hderiv' : HasDerivAt Z (2 * a * inner ℝ d q) s := by
      convert hderiv using 1
      all_goals simp [d, q]
      all_goals ring_nf
    rw [hD]
    exact hderiv'
  · change deriv Z s + a * (a * ‖d‖ ^ 2) ≤ _
    rw [hD]
    change ‖a • d + q‖ ^ 2 ≤ _ at hmomentum
    rw [hnorm] at hmomentum
    nlinarith

private theorem strongly_convex_objective_decay {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (g : H → H) (xStar : H)
    (a mu t0 C : ℝ) (u firstDerivative y : ℝ → H)
    (hStrong : ∀ x z : H, f z ≥ f x + inner ℝ (g x) (z - x) +
      (mu / 2) * ‖z - x‖ ^ 2)
    (hGrad : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x) (ha : 0 < a) (hmu : 0 ≤ mu)
    (hu : ∀ s, t0 ≤ s → HasDerivAt u (firstDerivative s) s)
    (hydef : ∀ s, y s = u s + a⁻¹ • firstDerivative s)
    (hValue : ∀ s, t0 ≤ s → f (y s) - f xStar ≤ C * Real.exp (-a * s)) :
    ∀ s, t0 ≤ s →
      HasDerivAt (fun r => f (u r) - f xStar)
        (deriv (fun r => f (u r) - f xStar) s) s ∧
      deriv (fun r => f (u r) - f xStar) s + a * (f (u s) - f xStar) ≤
        C * a * Real.exp (-a * s) := by
  intro s hs
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hvelocity : firstDerivative s = a • (y s - u s) := by
    calc
      firstDerivative s = a • (a⁻¹ • firstDerivative s) := by
        rw [smul_smul]
        field_simp [ha0]
        simp
      _ = a • (y s - u s) := by rw [hydef s]; module
  have hderiv := ((hGrad (u s)).comp_hasDerivAt s (hu s hs)).sub_const (f xStar)
  simp only [Function.comp_apply, innerSL_apply_apply] at hderiv
  have hD : deriv (fun r => f (u r) - f xStar) s =
      a * inner ℝ (g (u s)) (y s - u s) := by
    simpa [hvelocity, real_inner_smul_right] using hderiv.deriv
  have hstrong := hStrong (u s) (y s)
  have hsq : 0 ≤ ‖y s - u s‖ ^ 2 := sq_nonneg _
  have hval := hValue s hs
  constructor
  · have hderiv' : HasDerivAt (fun r => f (u r) - f xStar)
        (a * inner ℝ (g (u s)) (y s - u s)) s := by
      simpa [hvelocity, real_inner_smul_right] using hderiv
    rw [hD]
    exact hderiv'
  · rw [hD]
    have hinner : inner ℝ (g (u s)) (y s - u s) + (f (u s) - f xStar) ≤
        f (y s) - f xStar := by
      nlinarith [mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (mul_nonneg hmu hsq)]
    have hexp : 0 ≤ Real.exp (-a * s) := Real.exp_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hinner ha.le,
      mul_le_mul_of_nonneg_left hval ha.le]

private theorem strongly_convex_grad_eq_zero_of_global_min {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (g : H → H) (xStar : H)
    (hGrad : HasFDerivAt f (innerSL ℝ (g xStar)) xStar)
    (hmin : ∀ x : H, f xStar ≤ f x) : g xStar = 0 := by
  have hlocal : IsLocalMin f xStar := Filter.Eventually.of_forall hmin
  have hzero := hlocal.hasFDerivAt_eq_zero hGrad
  have hinner := congrArg (fun L : H →L[ℝ] ℝ => L (g xStar)) hzero
  have hnorm : ‖g xStar‖ ^ 2 = 0 := by
    simpa [innerSL, real_inner_self_eq_norm_sq] using hinner
  exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hnorm)

/-- The exponential estimates of Theorem 5.1 for the strongly convex evolution. -/
private theorem strongly_convex_third_order_exponential_estimates_core {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (u firstDerivative secondDerivative thirdDerivative : ℝ → H) (g : H → H)
    (xStar : H) (mu t0 : ℝ) (hStrong : IsStronglyConvexDifferentiable f mu)
    (hxStar : ∀ x : H, f xStar ≤ f x ∧ (f x = f xStar → x = xStar))
    (hTrajectory : IsStronglyConvexThirdOrderEvolution u mu f)
    (hGrad : ∀ x : H, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hu : ∀ t, t0 ≤ t → HasDerivAt u (firstDerivative t) t)
    (hFirst : ∀ t, t0 ≤ t → HasDerivAt firstDerivative (secondDerivative t) t)
    (hSecond : ∀ t, t0 ≤ t → HasDerivAt secondDerivative (thirdDerivative t) t)
    (hDerivative : ∀ t, deriv u t = firstDerivative t ∧ deriv (deriv u) t = secondDerivative t ∧
      deriv (deriv (deriv u)) t = thirdDerivative t) :
    ∀ t ≥ t0,
      f (u t + (Real.sqrt mu)⁻¹ • firstDerivative t) - sInf (Set.range f) ≤
        stronglyConvexLyapunov f u xStar mu t0 hxStar * Real.exp (-Real.sqrt mu * (t - t0)) ∧
      f (u t) - sInf (Set.range f) ≤
        (stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t +
          Real.exp (Real.sqrt mu * t0) * initialObjectiveGap f u xStar t0 -
          stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t0) *
          Real.exp (-Real.sqrt mu * t) ∧
      ‖u t + (Real.sqrt mu)⁻¹ • firstDerivative t - xStar‖ ^ 2 ≤
        (Real.exp (Real.sqrt mu * t0) / Real.sqrt mu) *
          (Real.sqrt mu * ‖u t0 + (Real.sqrt mu)⁻¹ • firstDerivative t0 - xStar‖ ^ 2 +
            2 * stronglyConvexLyapunov f u xStar mu t0 hxStar * (t - t0)) *
          Real.exp (-Real.sqrt mu * t) ∧
      ‖u t - xStar‖ ^ 2 ≤ (2 / mu) *
        (stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t +
          Real.exp (Real.sqrt mu * t0) * initialObjectiveGap f u xStar t0 -
          stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t0) *
          Real.exp (-Real.sqrt mu * t) := by
  rcases hStrong with ⟨hmu, hStrong⟩
  have hGradEq : ∀ x : H, gradient f x = g x := by
    intro x
    have hg : HasGradientAt f (g x) x := by
      rw [hasGradientAt_iff_hasFDerivAt]
      simpa only [InnerProductSpace.toDual_apply_eq_toDualMap_apply,
        InnerProductSpace.toContinuousLinearMap_toDualMap] using hGrad x
    exact (hg.unique ((hGrad x).differentiableAt.hasGradientAt)).symm
  have hStrongG : ∀ x z : H, f z ≥ f x + inner ℝ (g x) (z - x) +
      (mu / 2) * ‖z - x‖ ^ 2 := by
    intro x z
    simpa [hGradEq x] using hStrong x z
  have hTrajectory' : 0 < mu ∧ ∀ t : ℝ,
      thirdDerivative t + (3 * Real.sqrt mu) • secondDerivative t + (2 * mu) • firstDerivative t +
        Real.sqrt mu • g (u t + (Real.sqrt mu)⁻¹ • firstDerivative t) = 0 := by
    constructor
    · exact hTrajectory.1
    · intro t
      have heq := hTrajectory.2 t
      have hdu : deriv u t = firstDerivative t := (hDerivative t).1
      have hddu : deriv (deriv u) t = secondDerivative t := (hDerivative t).2.1
      have hdddu : deriv (deriv (deriv u)) t = thirdDerivative t := (hDerivative t).2.2
      rw [hdddu, hddu, hdu, hGradEq] at heq
      exact heq
  have hsInf : sInf (Set.range f) = f xStar :=
    sInf_range_eq_value_of_global_min f xStar (fun x => (hxStar x).1)
  have hchange := strongly_convex_change_of_variables u firstDerivative
    secondDerivative thirdDerivative g mu t0 hmu
    hu hFirst hSecond hTrajectory'
  let a : ℝ := Real.sqrt mu
  let y : ℝ → H := fun s => u s + a⁻¹ • firstDerivative s
  let yFirst : ℝ → H := fun s => firstDerivative s + a⁻¹ • secondDerivative s
  let ySecond : ℝ → H := fun s => secondDerivative s + a⁻¹ • thirdDerivative s
  have ha : 0 < a := by simpa [a] using Real.sqrt_pos.2 hmu
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha2 : a ^ 2 = mu := by simpa [a] using Real.sq_sqrt hmu.le
  have hy : ∀ s, t0 ≤ s → HasDerivAt y (yFirst s) s := by
    simpa only [a, y, yFirst] using hchange.1
  have hyFirst : ∀ s, t0 ≤ s → HasDerivAt yFirst (ySecond s) s := by
    simpa only [a, yFirst, ySecond] using hchange.2.1
  have hyeq : ∀ s, t0 ≤ s → ySecond s + (2 * a) • yFirst s + g (y s) = 0 := by
    simpa only [a, y, yFirst, ySecond] using hchange.2.2
  let v : ℝ → H := fun s => a • (y s - xStar) + yFirst s
  let E : ℝ → ℝ := fun s => f (y s) - f xStar + (1 / 2 : ℝ) * ‖v s‖ ^ 2
  have hv : ∀ s, t0 ≤ s → HasDerivAt v (a • yFirst s + ySecond s) s := by
    intro s hs
    simpa [v] using ((hy s hs).sub_const xStar |>.const_smul a).add (hyFirst s hs)
  have hEderiv : ∀ s, t0 ≤ s →
      HasDerivAt E
        (inner ℝ (g (y s)) (yFirst s) +
          inner ℝ (v s) (a • yFirst s + ySecond s)) s := by
    intro s hs
    simpa [E, v] using strongly_convex_energy_hasDerivAt f g xStar a s y yFirst ySecond
      hGrad (hy s hs) (hyFirst s hs)
  have hEdecay : ∀ s, t0 ≤ s → HasDerivAt E (deriv E s) s ∧
      deriv E s + a * E s ≤ 0 := by
    intro s hs
    simpa [E, v] using strongly_convex_energy_decay f g xStar a mu t0 y yFirst ySecond
      hStrongG hGrad ha ha2 hy hyFirst hyeq s hs
  intro t ht
  have hEnergy := scalar_differential_comparison E (fun _ : ℝ => 0) t0 a
    (fun s hs => intervalIntegrable_const) (fun s hs => (hEdecay s hs).1)
    (fun s hs => (hEdecay s hs).2) t ht
  simp only [mul_zero, intervalIntegral.integral_zero, add_zero] at hEnergy
  have hgap : f (y t) - f xStar ≤ E t := by
    dsimp [E, v]
    have hsq : 0 ≤ ‖a • (y t - xStar) + yFirst t‖ ^ 2 := sq_nonneg _
    nlinarith
  constructor
  · have hfirst : f (y t) - f xStar ≤ E t0 * Real.exp (-a * (t - t0)) := by
      calc
        f (y t) - f xStar ≤ E t := hgap
        _ ≤ Real.exp (-a * (t - t0)) * E t0 := hEnergy
        _ = E t0 * Real.exp (-a * (t - t0)) := by ring
    simpa [a, y, yFirst, E, v, hsInf, stronglyConvexLyapunov, add_assoc,
      (hDerivative t0).1, (hDerivative t0).2.1] using hfirst
  · let C : ℝ := E t0 * Real.exp (a * t0)
    have hEnergyAt : ∀ s, t0 ≤ s → E s ≤ E t0 * Real.exp (-a * (s - t0)) := by
      intro s hs
      have hcmp := scalar_differential_comparison E (fun _ : ℝ => 0) t0 a
        (fun r hr => intervalIntegrable_const) (fun r hr => (hEdecay r hr).1)
        (fun r hr => (hEdecay r hr).2) s hs
      simpa [mul_comm] using hcmp
    have hValue : ∀ s, t0 ≤ s → f (y s) - f xStar ≤ C * Real.exp (-a * s) := by
      intro s hs
      have hgap' : f (y s) - f xStar ≤ E s := by
        dsimp [E, v]
        have hsq : 0 ≤ ‖a • (y s - xStar) + yFirst s‖ ^ 2 := sq_nonneg _
        nlinarith
      calc
        f (y s) - f xStar ≤ E s := hgap'
        _ ≤ E t0 * Real.exp (-a * (s - t0)) := hEnergyAt s hs
        _ = C * Real.exp (-a * s) := by
          dsimp [C]
          have hexp : Real.exp (-a * (s - t0)) = Real.exp (a * t0) * Real.exp (-a * s) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
          ring
    have hMomentum : ∀ s, t0 ≤ s →
        ‖a • (y s - xStar) + yFirst s‖ ^ 2 ≤ 2 * C * Real.exp (-a * s) := by
      intro s hs
      have hkin : (1 / 2 : ℝ) * ‖a • (y s - xStar) + yFirst s‖ ^ 2 ≤ E s := by
        dsimp [E, v]
        have hmin := (hxStar (y s)).1
        nlinarith
      have hbound := hEnergyAt s hs
      have hrewrite : E t0 * Real.exp (-a * (s - t0)) = C * Real.exp (-a * s) := by
        dsimp [C]
        have hexp : Real.exp (-a * (s - t0)) = Real.exp (a * t0) * Real.exp (-a * s) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring
      rw [hrewrite] at hbound
      nlinarith
    have hZdecay := strongly_convex_distance_decay xStar a t0 C y yFirst ha hy hMomentum
    let Z : ℝ → ℝ := fun s => a * ‖y s - xStar‖ ^ 2
    have hZcmp := scalar_differential_comparison Z (fun s : ℝ => 2 * C * Real.exp (-a * s))
      t0 a
      (fun s hs => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).const_mul _
        |>.intervalIntegrable _ _)
      (fun s hs => (hZdecay s hs).1)
      (fun s hs => (hZdecay s hs).2) t ht
    have hZintegral : (∫ s in t0..t, Real.exp (-a * (t - s)) *
        (2 * C * Real.exp (-a * s))) = (t - t0) * (2 * C * Real.exp (-a * t)) := by
      have hconst : (fun s : ℝ => Real.exp (-a * (t - s)) *
          (2 * C * Real.exp (-a * s))) = fun _ => 2 * C * Real.exp (-a * t) := by
        funext s
        calc
          Real.exp (-a * (t - s)) * (2 * C * Real.exp (-a * s)) =
              (2 * C) * (Real.exp (-a * (t - s)) * Real.exp (-a * s)) := by ring
          _ = 2 * C * Real.exp (-a * t) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      rw [hconst, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    have hZbound : Z t ≤ Real.exp (-a * (t - t0)) * Z t0 +
        (t - t0) * (2 * C * Real.exp (-a * t)) := by
      rw [hZintegral] at hZcmp
      exact hZcmp
    have hthird : ‖y t - xStar‖ ^ 2 ≤
        (Real.exp (a * t0) / a) *
          (a * ‖y t0 - xStar‖ ^ 2 + 2 * E t0 * (t - t0)) * Real.exp (-a * t) := by
      have hexp : 0 < Real.exp (-a * t) := Real.exp_pos _
      dsimp [Z, C] at hZbound
      rw [show Real.exp (-a * (t - t0)) = Real.exp (a * t0) * Real.exp (-a * t) by
        rw [← Real.exp_add]
        congr 1
        ring] at hZbound
      field_simp [ha0]
      ring_nf at hZbound ⊢
      exact hZbound
    have hFdecay := strongly_convex_objective_decay f g xStar a mu t0 C u firstDerivative y hStrongG
      hGrad ha hmu.le hu (fun s => by simp [y]) hValue
    let F : ℝ → ℝ := fun s => f (u s) - f xStar
    have hFcmp := scalar_differential_comparison F (fun s : ℝ => C * a * Real.exp (-a * s))
      t0 a
      (fun s hs => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).const_mul
        _ |>.intervalIntegrable _ _)
      (fun s hs => (hFdecay s hs).1)
      (fun s hs => (hFdecay s hs).2) t ht
    have hFintegral : (∫ s in t0..t, Real.exp (-a * (t - s)) *
        (C * a * Real.exp (-a * s))) = (t - t0) * (C * a * Real.exp (-a * t)) := by
      have hconst : (fun s : ℝ => Real.exp (-a * (t - s)) *
          (C * a * Real.exp (-a * s))) = fun _ => C * a * Real.exp (-a * t) := by
        funext s
        calc
          Real.exp (-a * (t - s)) * (C * a * Real.exp (-a * s)) =
              (C * a) * (Real.exp (-a * (t - s)) * Real.exp (-a * s)) := by ring
          _ = C * a * Real.exp (-a * t) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      rw [hconst, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    have hFbound : F t ≤ Real.exp (-a * (t - t0)) * F t0 +
        (t - t0) * (C * a * Real.exp (-a * t)) := by
      rw [hFintegral] at hFcmp
      exact hFcmp
    have hsecond : f (u t) - f xStar ≤
        (C * a * t + Real.exp (a * t0) * F t0 - C * a * t0) * Real.exp (-a * t) := by
      dsimp [F] at hFbound
      rw [show Real.exp (-a * (t - t0)) = Real.exp (a * t0) * Real.exp (-a * t) by
        rw [← Real.exp_add]
        congr 1
        ring] at hFbound
      nlinarith
    have hgrad0 := strongly_convex_grad_eq_zero_of_global_min f g xStar (hGrad xStar)
      (fun x => (hxStar x).1)
    have hdist : (mu / 2) * ‖u t - xStar‖ ^ 2 ≤ f (u t) - f xStar := by
      have hstrong := hStrongG xStar (u t)
      rw [hgrad0, inner_zero_left] at hstrong
      nlinarith
    refine ⟨?_, ?_, ?_⟩
    · simpa [a, y, yFirst, E, v, C, F, hsInf, stronglyConvexEnergyConstant, initialObjectiveGap,
        stronglyConvexLyapunov, ← add_assoc, (hDerivative t0).1,
        (hDerivative t0).2.1] using hsecond
    · simpa [a, y, yFirst, E, v, hsInf, stronglyConvexLyapunov, ← add_assoc,
        (hDerivative t0).1, (hDerivative t0).2.1] using hthird
    · have hfourth : ‖u t - xStar‖ ^ 2 ≤ (2 / mu) *
          (C * a * t + Real.exp (a * t0) * F t0 - C * a * t0) * Real.exp (-a * t) := by
        have hmu0 : mu ≠ 0 := ne_of_gt hmu
        field_simp [hmu0]
        ring_nf at hdist hsecond ⊢
        nlinarith
      simpa [a, y, yFirst, E, v, C, F, hsInf, stronglyConvexEnergyConstant, initialObjectiveGap,
        stronglyConvexLyapunov, ← add_assoc, (hDerivative t0).1,
        (hDerivative t0).2.1] using hfourth

/-- Strongly convex estimates with the trajectory derivatives supplied directly. -/
theorem strongly_convex_third_order_exponential_estimates {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (u : ℝ → H) (xStar : H) (mu t0 : ℝ)
    (hStrong : IsStronglyConvexDifferentiable f mu)
    (hxStar : ∀ x : H, f xStar ≤ f x ∧ (f x = f xStar → x = xStar))
    (hTrajectory : IsStronglyConvexThirdOrderEvolution u mu f)
    (hFContDiff : ContDiff ℝ 1 f) (hUContDiff : ContDiff ℝ 3 u) :
    ∀ t ≥ t0,
      f (u t + (Real.sqrt mu)⁻¹ • deriv u t) - sInf (Set.range f) ≤
        stronglyConvexLyapunov f u xStar mu t0 hxStar * Real.exp (-Real.sqrt mu * (t - t0)) ∧
      f (u t) - sInf (Set.range f) ≤
        (stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t +
          Real.exp (Real.sqrt mu * t0) * initialObjectiveGap f u xStar t0 -
          stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t0) *
          Real.exp (-Real.sqrt mu * t) ∧
      ‖u t + (Real.sqrt mu)⁻¹ • deriv u t - xStar‖ ^ 2 ≤
        (Real.exp (Real.sqrt mu * t0) / Real.sqrt mu) *
          (Real.sqrt mu * ‖u t0 + (Real.sqrt mu)⁻¹ • deriv u t0 - xStar‖ ^ 2 +
            2 * stronglyConvexLyapunov f u xStar mu t0 hxStar * (t - t0)) *
          Real.exp (-Real.sqrt mu * t) ∧
      ‖u t - xStar‖ ^ 2 ≤ (2 / mu) *
        (stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t +
          Real.exp (Real.sqrt mu * t0) * initialObjectiveGap f u xStar t0 -
          stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t0) *
          Real.exp (-Real.sqrt mu * t) := by
  have hGradient : ∀ x : H, HasFDerivAt f (innerSL ℝ (gradient f x)) x := by
    intro x
    simpa [innerSL_apply_apply] using
      ((hFContDiff.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have huDiff : Differentiable ℝ u := hUContDiff.differentiable (by norm_num)
  have hFirstDiff : Differentiable ℝ (deriv u) :=
    (hUContDiff.of_le (by norm_num)).differentiable_deriv_two
  have hSecondDiff : Differentiable ℝ (deriv (deriv u)) := by
    exact hUContDiff.deriv'.differentiable_deriv_two
  have hRegularity :
      (∀ t, t0 ≤ t → HasDerivAt u (deriv u t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv u) (deriv (deriv u) t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv (deriv u))
        (deriv (deriv (deriv u)) t) t) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t _
      exact (huDiff t).hasDerivAt
    · intro t _
      exact (hFirstDiff t).hasDerivAt
    · intro t _
      exact (hSecondDiff t).hasDerivAt
  exact strongly_convex_third_order_exponential_estimates_core f u (deriv u)
    (deriv (deriv u)) (deriv (deriv (deriv u))) (gradient f) xStar mu t0 hStrong hxStar
    hTrajectory hGradient hRegularity.1 hRegularity.2.1 hRegularity.2.2
    (fun t => ⟨rfl, rfl, rfl⟩)
