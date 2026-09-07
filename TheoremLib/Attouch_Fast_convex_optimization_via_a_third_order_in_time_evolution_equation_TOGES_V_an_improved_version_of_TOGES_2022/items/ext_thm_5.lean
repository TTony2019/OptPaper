import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.SetValued.Resolvent
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_def_3

open scoped InnerProductSpace
open scoped Pointwise

open ERealFunction

/-- A point selected from the resolvent of the convex subdifferential satisfies
the usual scaled subgradient inequality. -/
theorem moreau_resolvent_subgradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (prox : H → H)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x) (x y : H) :
    f (prox x) + (inner ℝ ((1 / lam) • (x - prox x)) (y - prox x) : ℝ) ≤ f y := by
  classical
  have hpx := hprox x
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hpx
  rcases hpx with ⟨u, hu, hx⟩
  have hpdom : prox x ∈ ERealFunction.dom f :=
    mem_subdifferential_dom_of_mem_subdifferential f hProper hu
  have hu' : ∀ z : H, f (prox x) + (inner ℝ u (z - prox x) : ℝ) ≤ f z := by
    intro z
    have hz := hu z
    change (⟪z - prox x, u⟫_ℝ : EReal) + (f (prox x) : EReal) ≤ (f z : EReal) at hz
    simpa [real_inner_comm, add_comm] using hz
  have hdiff : x - prox x = lam • u := by
    calc
      x - prox x = (prox x + lam • u) - prox x := by rw [hx]
      _ = lam • u := by module
  have hgrad : (1 / lam) • (x - prox x) = u := by
    rw [hdiff, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hlam), one_smul]
  rw [hgrad]
  exact hu' y

/-- The resolvent point minimizes the quadratic perturbation of a convex function. -/
theorem moreau_proximal_objective_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (prox : H → H)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x) (x y : H) :
    f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) ≤
      f y + ((1 / (2 * lam) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
  have hsub := moreau_resolvent_subgradient f lam hlam hProper hconvex prox hprox x y
  have hquad : 1 / (2 * lam) * ‖x - prox x‖ ^ 2 ≤
      inner ℝ ((1 / lam) • (x - prox x)) (y - prox x) +
        1 / (2 * lam) * ‖x - y‖ ^ 2 := by
    have hsq : 0 ≤ ‖y - prox x‖ ^ 2 := sq_nonneg _
    have hxy : x - y = (x - prox x) - (y - prox x) := by module
    have hnorm : ‖x - y‖ ^ 2 = ‖x - prox x‖ ^ 2 -
        2 * inner ℝ (x - prox x) (y - prox x) + ‖y - prox x‖ ^ 2 := by
      rw [hxy]
      exact norm_sub_sq_real _ _
    rw [hnorm, real_inner_smul_left]
    field_simp [ne_of_gt hlam]
    nlinarith
  have hquadE : ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) ≤
      ((inner ℝ ((1 / lam) • (x - prox x)) (y - prox x) +
        1 / (2 * lam) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hquad
  calc
    f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) ≤
        f (prox x) +
          ((inner ℝ ((1 / lam) • (x - prox x)) (y - prox x) +
            1 / (2 * lam) * ‖x - y‖ ^ 2 : ℝ) : EReal) :=
      by simpa [add_comm] using add_le_add_left hquadE (f (prox x))
    _ = (f (prox x) + (inner ℝ ((1 / lam) • (x - prox x))
          (y - prox x) : ℝ)) + ((1 / (2 * lam) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
      rw [EReal.coe_add, add_assoc]
    _ ≤ f y + ((1 / (2 * lam) * ‖x - y‖ ^ 2 : ℝ) : EReal) :=
      by simpa [add_comm] using
        (add_le_add_right hsub ((1 / (2 * lam) * ‖x - y‖ ^ 2 : ℝ) : EReal))

/-- The Moreau envelope and its underlying proper convex function have the same infimum. -/
theorem moreau_infimum_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal)
    (prox : H → H) (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) :
    sInf (Set.range envelope) = sInf (Set.range f) := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨y, rfl⟩
    calc
      sInf (Set.range envelope) ≤ envelope y :=
        (isGLB_sInf (Set.range envelope)).1 ⟨y, rfl⟩
      _ = f (prox y) + ((1 / (2 * lam) * ‖y - prox y‖ ^ 2 : ℝ) : EReal) := henvelope y
      _ ≤ f y + ((1 / (2 * lam) * ‖y - y‖ ^ 2 : ℝ) : EReal) :=
        moreau_proximal_objective_le f lam hlam hProper hconvex prox hprox y y
      _ = f y := by simp
  · apply le_sInf
    rintro _ ⟨x, rfl⟩
    calc
      sInf (Set.range f) ≤ f (prox x) :=
        (isGLB_sInf (Set.range f)).1 ⟨prox x, rfl⟩
      _ ≤ f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) := by
        apply le_add_of_nonneg_right
        exact_mod_cast mul_nonneg (by positivity) (sq_nonneg ‖x - prox x‖)
      _ = envelope x := (henvelope x).symm

/-- Every value of the Moreau envelope is finite. -/
private theorem moreau_envelope_finite {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal)
    (prox : H → H) (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) (x : H) :
    envelope x ≠ ⊤ ∧ envelope x ≠ ⊥ ∧ ((envelope x).toReal : EReal) = envelope x := by
  rcases hProper.2 with ⟨z, hz⟩
  have hztop : f z ≠ ⊤ := ne_of_lt hz
  have hbound := moreau_proximal_objective_le f lam hlam hProper hconvex prox hprox x z
  have htop : envelope x ≠ ⊤ := by
    apply ne_of_lt
    calc
      envelope x = f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) :=
        henvelope x
      _ ≤ f z + ((1 / (2 * lam) * ‖x - z‖ ^ 2 : ℝ) : EReal) := hbound
      _ < ⊤ := EReal.add_lt_top hztop (EReal.coe_ne_top _)
  have hbot : envelope x ≠ ⊥ := by
    intro h
    rw [henvelope x, EReal.add_eq_bot_iff] at h
    rcases h with h | h
    · exact hProper.1 _ h
    · exact (EReal.coe_ne_bot _) h
  exact ⟨htop, hbot, EReal.coe_toReal htop hbot⟩

private theorem moreau_prox_mem_dom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (prox : H → H) (lam : ℝ)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x) (x : H) :
    prox x ∈ ERealFunction.dom f := by
  have hpx := hprox x
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hpx
  rcases hpx with ⟨u, hu, hx⟩
  exact mem_subdifferential_dom_of_mem_subdifferential f hProper hu

private theorem moreau_prox_firm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (prox : H → H)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x) (x y : H) :
    ‖prox x - prox y‖ ^ 2 ≤ inner ℝ (x - y) (prox x - prox y) := by
  have hxdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox x
  have hydom := moreau_prox_mem_dom f hProper hconvex prox lam hprox y
  have hxfin : ((f (prox x)).toReal : EReal) = f (prox x) :=
    EReal.coe_toReal (ne_of_lt hxdom) (hProper.1 _)
  have hyfin : ((f (prox y)).toReal : EReal) = f (prox y) :=
    EReal.coe_toReal (ne_of_lt hydom) (hProper.1 _)
  have hxy := moreau_resolvent_subgradient f lam hlam hProper hconvex prox hprox x (prox y)
  have hyx := moreau_resolvent_subgradient f lam hlam hProper hconvex prox hprox y (prox x)
  rw [← hxfin, ← hyfin, ← EReal.coe_add] at hxy hyx
  norm_cast at hxy hyx
  have hident :
      inner ℝ ((1 / lam) • (x - prox x)) (prox y - prox x) +
        inner ℝ ((1 / lam) • (y - prox y)) (prox x - prox y) =
        (1 / lam) * (inner ℝ (x - y) (prox y - prox x) + ‖prox x - prox y‖ ^ 2) := by
    have hneg : prox y - prox x = -(prox x - prox y) := by module
    rw [hneg]
    simp only [real_inner_smul_left, inner_sub_left, inner_neg_right]
    have hp : inner ℝ (prox x) (prox x - prox y) -
        inner ℝ (prox y) (prox x - prox y) = ‖prox x - prox y‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    linear_combination (1 / lam) * hp
  rw [← sub_nonneg] at hxy
  have hsum :
      inner ℝ ((1 / lam) • (x - prox x)) (prox y - prox x) +
        inner ℝ ((1 / lam) • (y - prox y)) (prox x - prox y) ≤ 0 := by
    linarith
  rw [hident] at hsum
  have hlam0 : 0 < 1 / lam := by positivity
  have hmain : inner ℝ (x - y) (prox y - prox x) + ‖prox x - prox y‖ ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hsum) hlam0
  have hneg : prox y - prox x = -(prox x - prox y) := by module
  rw [hneg, inner_neg_right] at hmain
  linarith

private theorem moreau_prox_nonexpansive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (prox : H → H)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x) (x y : H) :
    ‖prox x - prox y‖ ≤ ‖x - y‖ := by
  have hfirm := moreau_prox_firm f lam hlam hProper hconvex prox hprox x y
  have hcs := real_inner_le_norm (x - y) (prox x - prox y)
  nlinarith [norm_nonneg (x - y), norm_nonneg (prox x - prox y)]

private theorem moreau_residual_nonexpansive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (prox : H → H)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x) (x y : H) :
    ‖(x - prox x) - (y - prox y)‖ ≤ ‖x - y‖ := by
  have hfirm := moreau_prox_firm f lam hlam hProper hconvex prox hprox x y
  have hsq : ‖(x - prox x) - (y - prox y)‖ ^ 2 =
      ‖x - y‖ ^ 2 - 2 * inner ℝ (x - y) (prox x - prox y) + ‖prox x - prox y‖ ^ 2 := by
    have hident : (x - prox x) - (y - prox y) = (x - y) - (prox x - prox y) := by module
    rw [hident, norm_sub_sq_real]
  have hle : ‖(x - prox x) - (y - prox y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith [norm_nonneg ((x - prox x) - (y - prox y)), norm_nonneg (x - y)]

private theorem moreau_formula_toReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal)
    (prox : H → H) (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) (x : H) :
    (envelope x).toReal = (f (prox x)).toReal +
      1 / (2 * lam) * ‖x - prox x‖ ^ 2 := by
  have hpdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox x
  have hpfin : ((f (prox x)).toReal : EReal) = f (prox x) :=
    EReal.coe_toReal (ne_of_lt hpdom) (hProper.1 _)
  have henvfin := moreau_envelope_finite f lam hlam hProper hconvex envelope prox hprox henvelope x
  have h := congrArg EReal.toReal (henvelope x)
  rw [EReal.toReal_add, EReal.toReal_coe] at h
  · exact h
  · exact ne_of_lt hpdom
  · exact hProper.1 _
  · exact EReal.coe_ne_top _
  · exact EReal.coe_ne_bot _

private theorem moreau_norm_sq_convex {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (a b : H) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • a + t • b‖ ^ 2 ≤ (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hsq : 0 ≤ ‖a - b‖ ^ 2 := sq_nonneg _
  have hinter : 2 * inner ℝ a b ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [norm_sub_sq_real] at hsq
    nlinarith
  rw [norm_add_sq_real, inner_smul_left, inner_smul_right,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg h1t, abs_of_nonneg ht0]
  simp only [starRingEnd_apply, star_trivial]
  ring_nf
  nlinarith [mul_le_mul_of_nonneg_left hinter (mul_nonneg ht0 h1t)]

private theorem moreau_gradient_lipschitz {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (prox : H → H)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x) (x y : H) :
    ‖(1 / lam) • (x - prox x) - (1 / lam) • (y - prox y)‖ ≤
      (1 / lam) * ‖x - y‖ := by
  have hinv : 0 < 1 / lam := by positivity
  rw [show (1 / lam) • (x - prox x) - (1 / lam) • (y - prox y) =
      (1 / lam) • ((x - prox x) - (y - prox y)) by module,
    norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
  exact mul_le_mul_of_nonneg_left
    (moreau_residual_nonexpansive f lam hlam hProper hconvex prox hprox x y) hinv.le

private theorem moreau_upper_remainder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal)
    (prox : H → H) (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) (x h : H) :
    (envelope (x + h)).toReal - (envelope x).toReal -
        inner ℝ ((1 / lam) • (x - prox x)) h ≤ 1 / (2 * lam) * ‖h‖ ^ 2 := by
  have hineq := moreau_proximal_objective_le f lam hlam hProper hconvex prox hprox (x + h) (prox x)
  have hpdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox x
  have hqdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox (x + h)
  have hpfin : ((f (prox x)).toReal : EReal) = f (prox x) :=
    EReal.coe_toReal (ne_of_lt hpdom) (hProper.1 _)
  have hqfin : ((f (prox (x + h))).toReal : EReal) = f (prox (x + h)) :=
    EReal.coe_toReal (ne_of_lt hqdom) (hProper.1 _)
  rw [← hqfin, ← hpfin, ← EReal.coe_add, ← EReal.coe_add] at hineq
  norm_cast at hineq
  have hineqR : (envelope (x + h)).toReal ≤ (f (prox x)).toReal +
      1 / (2 * lam) * ‖(x + h) - prox x‖ ^ 2 := by
    rw [moreau_formula_toReal f lam hlam hProper hconvex envelope prox hprox henvelope (x + h)]
    exact hineq
  have hx := moreau_formula_toReal f lam hlam hProper hconvex envelope prox hprox henvelope x
  have hsplit : (x + h) - prox x = (x - prox x) + h := by module
  rw [hsplit, norm_add_sq_real] at hineqR
  rw [hx, real_inner_smul_left]
  field_simp [ne_of_gt hlam] at hineqR ⊢
  nlinarith

private theorem moreau_lower_remainder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal)
    (prox : H → H) (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) (x h : H) :
    -(3 * ‖h‖ ^ 2 / (2 * lam)) ≤ (envelope (x + h)).toReal - (envelope x).toReal -
        inner ℝ ((1 / lam) • (x - prox x)) h := by
  have hineq := moreau_proximal_objective_le f lam hlam hProper hconvex prox hprox x (prox (x + h))
  have hpdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox x
  have hqdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox (x + h)
  have hpfin : ((f (prox x)).toReal : EReal) = f (prox x) :=
    EReal.coe_toReal (ne_of_lt hpdom) (hProper.1 _)
  have hqfin : ((f (prox (x + h))).toReal : EReal) = f (prox (x + h)) :=
    EReal.coe_toReal (ne_of_lt hqdom) (hProper.1 _)
  rw [← hpfin, ← hqfin, ← EReal.coe_add, ← EReal.coe_add] at hineq
  norm_cast at hineq
  have hineqR : (envelope x).toReal ≤ (f (prox (x + h))).toReal +
      1 / (2 * lam) * ‖x - prox (x + h)‖ ^ 2 := by
    rw [moreau_formula_toReal f lam hlam hProper hconvex envelope prox hprox henvelope x]
    exact hineq
  have hx := moreau_formula_toReal f lam hlam hProper hconvex envelope prox hprox henvelope x
  have hxh := moreau_formula_toReal f lam hlam hProper hconvex envelope prox hprox henvelope (x + h)
  have hlip := moreau_gradient_lipschitz f lam hlam hProper hconvex prox hprox x (x + h)
  have hlip' : ‖(1 / lam) • ((x + h) - prox (x + h)) -
      (1 / lam) • (x - prox x)‖ ≤ (1 / lam) * ‖h‖ := by
    calc
      ‖(1 / lam) • ((x + h) - prox (x + h)) - (1 / lam) • (x - prox x)‖ =
          ‖- ((1 / lam) • (x - prox x) - (1 / lam) • ((x + h) - prox (x + h)))‖ := by
            congr 1
            module
      _ = ‖(1 / lam) • (x - prox x) - (1 / lam) • ((x + h) - prox (x + h))‖ := norm_neg _
      _ ≤ (1 / lam) * ‖x - (x + h)‖ := hlip
      _ = (1 / lam) * ‖h‖ := by
        rw [show x - (x + h) = -h by module, norm_neg]
  have hsplit : x - prox (x + h) = ((x + h) - prox (x + h)) - h := by module
  rw [hsplit, norm_sub_sq_real] at hineqR
  rw [hx, hxh, real_inner_smul_left]
  have hinner := neg_le_of_abs_le
    (abs_real_inner_le_norm ((1 / lam) • ((x + h) - prox (x + h)) -
      (1 / lam) • (x - prox x)) h)
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hinner
  rw [hx] at hineqR
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  field_simp [hlam0] at hineqR hinner hlip' ⊢
  have hprod := mul_le_mul_of_nonneg_right hlip' hnorm
  nlinarith [hprod]

private theorem moreau_envelope_hasFDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal)
    (prox : H → H) (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) (x : H) :
    HasFDerivAt (fun y => (envelope y).toReal)
      (innerSL ℝ ((1 / lam) • (x - prox x))) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let C : ℝ := 3 / (2 * lam)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine Metric.eventually_nhds_iff.2 ⟨ε / C, div_pos hε hC, ?_⟩
  intro h hh
  have hdist : ‖h‖ < ε / C := by simpa [dist_eq_norm] using hh
  have hupper := moreau_upper_remainder f lam hlam hProper hconvex envelope prox hprox henvelope x h
  have hlower := moreau_lower_remainder f lam hlam hProper hconvex envelope prox hprox henvelope x h
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hsmall : C * ‖h‖ ≤ ε := by
    simpa [mul_comm] using le_of_lt ((lt_div_iff₀ hC).1 hdist)
  have hquad : C * ‖h‖ ^ 2 ≤ ε * ‖h‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall hnorm]
  rw [Real.norm_eq_abs, innerSL_apply_apply]
  apply abs_le.mpr
  constructor
  · dsimp [C] at hlower hquad ⊢
    have hlow_eq : 3 * ‖h‖ ^ 2 / (2 * lam) = 3 / (2 * lam) * ‖h‖ ^ 2 := by
      field_simp [ne_of_gt hlam]
    rw [hlow_eq] at hlower
    nlinarith
  · dsimp [C] at hupper hquad ⊢
    have hupper' : 1 / (2 * lam) * ‖h‖ ^ 2 ≤ 3 / (2 * lam) * ‖h‖ ^ 2 := by
      have hsq : 0 ≤ ‖h‖ ^ 2 := sq_nonneg _
      field_simp [ne_of_gt hlam]
      nlinarith
    exact hupper.trans (hupper'.trans hquad)

private theorem moreau_envelope_contDiff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal)
    (prox : H → H) (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) :
    ContDiff ℝ 1 (fun x => (envelope x).toReal) := by
  rw [contDiff_one_iff_hasFDerivAt]
  let G : H → H := fun x => (1 / lam) • (x - prox x)
  let K : NNReal := ⟨1 / lam, (one_div_pos.mpr hlam).le⟩
  have hG_lip : LipschitzWith K G := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [G, K, dist_eq_norm] using
      moreau_gradient_lipschitz f lam hlam hProper hconvex prox hprox x y
  have hG_cont : Continuous G := hG_lip.continuous
  refine ⟨fun x => innerSL ℝ (G x), (innerSL ℝ).continuous.comp hG_cont, ?_⟩
  intro x
  simpa [G] using moreau_envelope_hasFDerivAt f lam hlam hProper hconvex envelope prox hprox henvelope x

private theorem moreau_envelope_convex {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal)
    (prox : H → H) (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) :
    Convex ℝ (ERealFunction.epigraph envelope) := by
  rintro ⟨a, r⟩ har ⟨b, s⟩ hbs α t hα ht0 hsum
  have ht1 : t ≤ 1 := by linarith
  have hα : α = 1 - t := by linarith
  subst α
  rw [ERealFunction.mem_epigraph_iff] at har hbs ⊢
  let p := prox a
  let q := prox b
  let m := (1 - t) • p + t • q
  let u := (1 - t) • a + t • b
  have hpdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox a
  have hqdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox b
  have hpfin : ((f p).toReal : EReal) = f p := EReal.coe_toReal (ne_of_lt (by simpa [p] using hpdom)) (hProper.1 _)
  have hqfin : ((f q).toReal : EReal) = f q := EReal.coe_toReal (ne_of_lt (by simpa [q] using hqdom)) (hProper.1 _)
  have hcomb := hconvex (show (p, (f p).toReal) ∈ ERealFunction.epigraph f from
      EReal.le_coe_toReal (ne_of_lt (by simpa [p] using hpdom)))
    (show (q, (f q).toReal) ∈ ERealFunction.epigraph f from
      EReal.le_coe_toReal (ne_of_lt (by simpa [q] using hqdom)))
    (sub_nonneg.mpr ht1) ht0 (by ring)
  rw [ERealFunction.mem_epigraph_iff] at hcomb
  have hm_top : f m ≠ ⊤ := by
    apply ne_top_of_le_ne_top (EReal.coe_ne_top _)
    simpa [m, Prod.smul_mk] using hcomb
  have hphi : (f m).toReal ≤ (1 - t) * (f p).toReal + t * (f q).toReal := by
    apply EReal.toReal_le_toReal hcomb (hProper.1 _) (EReal.coe_ne_top _)
  have hvec : u - m = (1 - t) • (a - p) + t • (b - q) := by
    dsimp [u, m, p, q]
    module
  have hquad : ‖u - m‖ ^ 2 ≤ (1 - t) * ‖a - p‖ ^ 2 + t * ‖b - q‖ ^ 2 := by
    rw [hvec]
    exact moreau_norm_sq_convex (a - p) (b - q) t ht0 ht1
  have hc : 0 ≤ 1 / (2 * lam) := by positivity
  have hreal : (f m).toReal + 1 / (2 * lam) * ‖u - m‖ ^ 2 ≤
      (1 - t) * ((f p).toReal + 1 / (2 * lam) * ‖a - p‖ ^ 2) +
        t * ((f q).toReal + 1 / (2 * lam) * ‖b - q‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hquad hc]
  have hsel : f m + ((1 / (2 * lam) * ‖u - m‖ ^ 2 : ℝ) : EReal) ≤
      (((1 - t) * ((f p).toReal + 1 / (2 * lam) * ‖a - p‖ ^ 2) +
        t * ((f q).toReal + 1 / (2 * lam) * ‖b - q‖ ^ 2) : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hm_top (hProper.1 _), ← EReal.coe_add]
    exact_mod_cast hreal
  have hu : envelope u ≤ f m + ((1 / (2 * lam) * ‖u - m‖ ^ 2 : ℝ) : EReal) :=
    calc
      envelope u = f (prox u) + ((1 / (2 * lam) * ‖u - prox u‖ ^ 2 : ℝ) : EReal) := henvelope u
      _ ≤ f m + ((1 / (2 * lam) * ‖u - m‖ ^ 2 : ℝ) : EReal) :=
        moreau_proximal_objective_le f lam hlam hProper hconvex prox hprox u m
  have hpa : envelope a = (((f p).toReal + 1 / (2 * lam) * ‖a - p‖ ^ 2 : ℝ) : EReal) := by
    rw [henvelope a, ← hpfin]
    norm_cast
  have hqb : envelope b = (((f q).toReal + 1 / (2 * lam) * ‖b - q‖ ^ 2 : ℝ) : EReal) := by
    rw [henvelope b, ← hqfin]
    norm_cast
  have henv : envelope u ≤ (↑(1 - t) : EReal) * envelope a + (↑t : EReal) * envelope b := by
    calc
      envelope u ≤ f m + ((1 / (2 * lam) * ‖u - m‖ ^ 2 : ℝ) : EReal) := hu
      _ ≤ (((1 - t) * ((f p).toReal + 1 / (2 * lam) * ‖a - p‖ ^ 2) +
        t * ((f q).toReal + 1 / (2 * lam) * ‖b - q‖ ^ 2) : ℝ) : EReal) := hsel
      _ = (↑(1 - t) : EReal) * envelope a + (↑t : EReal) * envelope b := by
        rw [hpa, hqb]
        push_cast
        ring
  have h1tE : (0 : EReal) ≤ ↑(1 - t) := by exact_mod_cast sub_nonneg.mpr ht1
  have htE : (0 : EReal) ≤ ↑t := by exact_mod_cast ht0
  have hbound := add_le_add
    (mul_le_mul_of_nonneg_left har h1tE)
    (mul_le_mul_of_nonneg_left hbs htE)
  have hucoord : u = ((1 - t) • (a, r) + t • (b, s)).1 := by simp [u]
  have hheight : ((1 - t) • (a, r) + t • (b, s)).2 = (1 - t) * r + t * s := by simp
  rw [← hucoord, hheight]
  exact henv.trans (by simpa [EReal.coe_add, EReal.coe_mul] using hbound)

/-- Moreau envelope regularity, equality of infima and minimizers, and the proximal formula. -/
theorem moreau_envelope_regularity_and_minimizers {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f) (_hlsc : LowerSemicontinuous f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal) (prox : H → H)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) :
    Convex ℝ (ERealFunction.epigraph envelope) ∧
    ContDiff ℝ 1 (fun x => (envelope x).toReal) ∧
    sInf (Set.range envelope) = sInf (Set.range f) ∧
    {x | envelope x = sInf (Set.range envelope)} =
      {x | f x = sInf (Set.range f)} ∧
    (∀ x, f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) =
      envelope x) := by
  refine ⟨?_, ?_, moreau_infimum_eq f lam hlam hProper hconvex envelope prox hprox henvelope,
    ?_, ?_⟩
  · exact moreau_envelope_convex f lam hlam hProper hconvex envelope prox hprox henvelope
  · exact moreau_envelope_contDiff f lam hlam hProper hconvex envelope prox hprox henvelope
  · ext x
    constructor
    · intro hx
      have hinfs := moreau_infimum_eq f lam hlam hProper hconvex envelope prox hprox henvelope
      have hpdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox x
      have hpfin : ((f (prox x)).toReal : EReal) = f (prox x) :=
        EReal.coe_toReal (ne_of_lt hpdom) (hProper.1 _)
      have hp_le_env : f (prox x) ≤ envelope x := by
        rw [henvelope x]
        exact le_add_of_nonneg_right (by
          exact_mod_cast mul_nonneg (by positivity) (sq_nonneg ‖x - prox x‖))
      have henv_eq : envelope x = sInf (Set.range f) := hx.trans hinfs
      have hp_eq : f (prox x) = sInf (Set.range f) := by
        apply le_antisymm
        · calc
            f (prox x) ≤ envelope x := hp_le_env
            _ = sInf (Set.range f) := henv_eq
        · exact (isGLB_sInf (Set.range f)).1 ⟨prox x, rfl⟩
      have hsum : f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) =
          f (prox x) := by
        calc
          f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) = envelope x :=
            (henvelope x).symm
          _ = sInf (Set.range f) := henv_eq
          _ = f (prox x) := hp_eq.symm
      rw [← hpfin, ← EReal.coe_add] at hsum
      norm_cast at hsum
      have hq : 1 / (2 * lam) * ‖x - prox x‖ ^ 2 = 0 := by linarith
      have hcoeff : 0 < 1 / (2 * lam) := by positivity
      have hsq : ‖x - prox x‖ ^ 2 = 0 := by nlinarith
      have hnorm : ‖x - prox x‖ = 0 := by nlinarith [norm_nonneg (x - prox x)]
      have hxp : x = prox x := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
      rw [hxp]
      exact hp_eq
    · intro hx
      have hinfs := moreau_infimum_eq f lam hlam hProper hconvex envelope prox hprox henvelope
      have henv_le : envelope x ≤ f x := by
        calc
          envelope x = f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) :=
            henvelope x
          _ ≤ f x + ((1 / (2 * lam) * ‖x - x‖ ^ 2 : ℝ) : EReal) :=
            moreau_proximal_objective_le f lam hlam hProper hconvex prox hprox x x
          _ = f x := by simp
      apply le_antisymm
      · calc
          envelope x ≤ f x := henv_le
          _ = sInf (Set.range f) := hx
          _ = sInf (Set.range envelope) := hinfs.symm
      · exact (isGLB_sInf (Set.range envelope)).1 ⟨x, rfl⟩
  · intro x
    exact (henvelope x).symm
