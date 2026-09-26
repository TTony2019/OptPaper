import Mathlib
import Foundation.Analysis.ProductQuadratic
import Foundation.Convex.FiberwiseDuality
import Foundation.SetValued.MaximalMonotone

/-!
# Fitzpatrick functions for maximal monotone operators

Definitions and reusable analytic properties of the Fitzpatrick function of a
set-valued operator on a real Hilbert space.
-/

open SetValuedOperator
open scoped InnerProductSpace Pointwise

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def fitzpatrick (A : SetValuedOperator H H) (x u : H) : EReal :=
  sSup {r : EReal | ∃ z v : H, v ∈ A z ∧
    r = ((inner ℝ x v + inner ℝ z u - inner ℝ z v : ℝ) : EReal)}

noncomputable def fitzpatrickProd (A : SetValuedOperator H H) (p : H × H) :
    EReal :=
  fitzpatrick A p.1 p.2

/- The Chapter 20 notation is useful in the Chapter 25 owner statements. -/
notation:max "F[" A:max "]" => fitzpatrickProd A

omit [CompleteSpace H] in
theorem fitzpatrick_graph_eq_inner
    {A : SetValuedOperator H H} (hmono : IsMonotone A)
    {z v : H} (hv : v ∈ A z) :
    fitzpatrick A z v = (inner ℝ z v : EReal) := by
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨y, w, hw, rfl⟩
    have hmw := hmono w hw v hv
    have hle : inner ℝ z w + inner ℝ y v - inner ℝ y w ≤ inner ℝ z v := by
      have hmw' : inner ℝ z w ≤ inner ℝ y w - inner ℝ v y + inner ℝ z v := by
        simpa [inner_sub_left, inner_sub_right, real_inner_comm] using hmw
      have hyv : inner ℝ y v = inner ℝ v y := (real_inner_comm y v).symm
      nlinarith [hmw']
    exact EReal.coe_le_coe hle
  · exact le_sSup ⟨z, v, hv, by ring_nf⟩

omit [CompleteSpace H] in
theorem fitzpatrick_eq_iSup_graph (A : SetValuedOperator H H) (x u : H) :
    fitzpatrick A x u =
      ⨆ p : {p : H × H // p.2 ∈ A p.1},
        (((inner ℝ x p.val.2 + inner ℝ p.val.1 u -
            inner ℝ p.val.1 p.val.2 : ℝ) : EReal)) := by
  dsimp [fitzpatrick]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨z, v, hv, rfl⟩
    exact le_iSup_of_le (⟨(z, v), hv⟩ : {p : H × H // p.2 ∈ A p.1}) le_rfl
  · refine iSup_le ?_
    intro p
    exact le_sSup ⟨p.val.1, p.val.2, p.property, by rfl⟩

omit [CompleteSpace H] in
theorem inner_le_fitzpatrick_of_maximal
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) :
    ∀ x u : H, (inner ℝ x u : EReal) ≤ fitzpatrick A x u := by
  intro x u
  by_cases hrel : ∀ z v, v ∈ A z → 0 ≤ inner ℝ (u - v) (x - z)
  · have hu : u ∈ A x := mem_of_monotonically_related_to_graph (T := A) hA hrel
    rw [fitzpatrick_graph_eq_inner hA.1 hu]
  · push Not at hrel
    rcases hrel with ⟨z, v, hv, hlt⟩
    refine le_sSup_of_le ⟨z, v, hv, rfl⟩ ?_
    have hle : inner ℝ x u ≤ inner ℝ x v + inner ℝ z u - inner ℝ z v := by
      have hpos : 0 < inner ℝ (v - u) (x - z) := by
        have hEq : -inner ℝ (u - v) (x - z) = inner ℝ (v - u) (x - z) := by
          calc
            -inner ℝ (u - v) (x - z) = inner ℝ (-(u - v)) (x - z) := by
              rw [inner_neg_left]
            _ = inner ℝ (v - u) (x - z) := by
              congr 1
              abel
        simpa [hEq] using neg_pos.mpr hlt
      have hpos' : inner ℝ z v - inner ℝ u z < inner ℝ x v - inner ℝ x u := by
        simpa [inner_sub_left, inner_sub_right, real_inner_comm] using hpos
      have huz : inner ℝ u z = inner ℝ z u := (real_inner_comm u z).symm
      nlinarith [hpos']
    exact EReal.coe_le_coe hle

omit [CompleteSpace H] in
theorem fitzpatrick_plus_quad_nonneg
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) :
    ∀ x u : H,
      (0 : EReal) ≤
        fitzpatrick A x u + (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) := by
  intro x u
  have hfitz : (inner ℝ x u : EReal) ≤ fitzpatrick A x u :=
    inner_le_fitzpatrick_of_maximal (A := A) hA x u
  have hreal : 0 ≤ inner ℝ x u + (1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) := by
    have hsq : 0 ≤ ‖x + u‖ ^ 2 := sq_nonneg _
    have hnorm : ‖x + u‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x u + ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm]
      ring
    nlinarith [hsq, hnorm]
  calc
    (0 : EReal) = ((0 : ℝ) : EReal) := rfl
    _ ≤ ((inner ℝ x u + (1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) :=
      EReal.coe_le_coe hreal
    _ = (inner ℝ x u : EReal) +
        (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) := by
      rw [EReal.coe_add]
    _ ≤ fitzpatrick A x u +
        (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) := by
      exact add_le_add hfitz le_rfl

omit [CompleteSpace H] in
theorem fitzpatrick_ne_bot
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) (x u : H) :
    fitzpatrick A x u ≠ ⊥ := by
  intro hbot
  have hle : (inner ℝ x u : EReal) ≤ fitzpatrick A x u :=
    inner_le_fitzpatrick_of_maximal (A := A) hA x u
  rw [hbot] at hle
  exact not_le_of_gt (EReal.bot_lt_coe (inner ℝ x u)) hle

omit [CompleteSpace H] in
theorem fitzpatrickProd_proper
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) :
    ERealFunction.IsProper (fitzpatrickProd A) := by
  constructor
  · intro p
    exact fitzpatrick_ne_bot (A := A) hA p.1 p.2
  · rcases maximalMonotone_graph_nonempty (A := A) hA with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    change fitzpatrickProd A p < ⊤
    dsimp [fitzpatrickProd]
    rw [fitzpatrick_graph_eq_inner hA.1 hp]
    exact EReal.coe_lt_top (inner ℝ p.1 p.2)

omit [CompleteSpace H] in
theorem fitzpatrickProd_lowerSemicontinuous
    {A : SetValuedOperator H H} (_hA : IsMaximalMonotone A) :
    LowerSemicontinuous (fitzpatrickProd A) := by
  have hlsc :
      LowerSemicontinuous (fun p : H × H =>
        ⨆ q : {q : H × H // q.2 ∈ A q.1},
          (((inner ℝ p.1 q.val.2 + inner ℝ q.val.1 p.2 -
              inner ℝ q.val.1 q.val.2 : ℝ) : EReal))) := by
    refine lowerSemicontinuous_iSup ?_
    intro q
    have hcont : Continuous (fun p : H × H =>
        inner ℝ p.1 q.val.2 + inner ℝ q.val.1 p.2 -
          inner ℝ q.val.1 q.val.2) := by
      exact ((continuous_fst.inner continuous_const).add
        (continuous_const.inner continuous_snd)).sub continuous_const
    exact (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  convert hlsc using 1
  ext p
  exact fitzpatrick_eq_iSup_graph A p.1 p.2

omit [CompleteSpace H] in
theorem fitzpatrickProd_convex
    {A : SetValuedOperator H H} :
    ∀ p q : H × H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      fitzpatrickProd A (a • p + b • q) ≤
        (a : EReal) * fitzpatrickProd A p + (b : EReal) * fitzpatrickProd A q := by
  intro p q a b ha hb hab
  dsimp [fitzpatrickProd]
  rw [fitzpatrick_eq_iSup_graph A (a • p.1 + b • q.1) (a • p.2 + b • q.2)]
  refine iSup_le ?_
  intro r
  let z : H := r.val.1
  let v : H := r.val.2
  have hreal :
      inner ℝ (a • p.1 + b • q.1) v + inner ℝ z (a • p.2 + b • q.2) -
          inner ℝ z v =
        a * (inner ℝ p.1 v + inner ℝ z p.2 - inner ℝ z v) +
          b * (inner ℝ q.1 v + inner ℝ z q.2 - inner ℝ z v) := by
    dsimp [z, v]
    rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right]
    ring_nf
    have hconst : a * inner ℝ z v + b * inner ℝ z v = inner ℝ z v := by
      rw [← add_mul, hab, one_mul]
    nlinarith [hconst]
  have hp :
      (((inner ℝ p.1 v + inner ℝ z p.2 - inner ℝ z v : ℝ) : EReal) ≤
        fitzpatrick A p.1 p.2) := by
    rw [fitzpatrick_eq_iSup_graph A p.1 p.2]
    exact le_iSup_of_le r le_rfl
  have hq :
      (((inner ℝ q.1 v + inner ℝ z q.2 - inner ℝ z v : ℝ) : EReal) ≤
        fitzpatrick A q.1 q.2) := by
    rw [fitzpatrick_eq_iSup_graph A q.1 q.2]
    exact le_iSup_of_le r le_rfl
  calc
    (((inner ℝ (a • p.1 + b • q.1) v + inner ℝ z (a • p.2 + b • q.2) -
        inner ℝ z v : ℝ) : EReal))
        = (a : EReal) *
            (((inner ℝ p.1 v + inner ℝ z p.2 - inner ℝ z v : ℝ) : EReal)) +
          (b : EReal) *
            (((inner ℝ q.1 v + inner ℝ z q.2 - inner ℝ z v : ℝ) : EReal)) := by
          rw [hreal, EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    _ ≤ (a : EReal) * fitzpatrick A p.1 p.2 +
          (b : EReal) * fitzpatrick A q.1 q.2 := by
        gcongr

omit [CompleteSpace H] in
/-- For a maximally monotone operator, equality in the Fitzpatrick lower bound is exactly graph
membership. -/
theorem fitzpatrick_eq_inner_iff_mem_graph_of_maximal
    {A : SetValuedOperator H H} (hA : Maximal SetValuedOperator.IsMonotone A) {x u : H} :
    fitzpatrick A x u = (inner ℝ x u : EReal) ↔ u ∈ A x := by
  have hA' : IsMaximalMonotone A :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).2 hA
  constructor
  · intro hEq
    apply (Maximal.mem_iff hA x u).2
    intro y v hv
    have hterm :
        (((inner ℝ x v + inner ℝ y u - inner ℝ y v : ℝ) : EReal)) ≤
          fitzpatrick A x u := by
      exact le_sSup ⟨y, v, hv, rfl⟩
    rw [hEq] at hterm
    have hterm' : inner ℝ x v + inner ℝ y u - inner ℝ y v ≤ inner ℝ x u :=
      (EReal.coe_le_coe_iff.mp hterm)
    have hexpand :
        inner ℝ (u - v) (x - y) =
          inner ℝ x u - inner ℝ x v - inner ℝ y u + inner ℝ y v := by
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring_nf
    rw [hexpand]
    linarith
  · intro hu
    exact fitzpatrick_graph_eq_inner hA'.1 hu

/-! ## Conjugate contact for one operator -/

section ConjugateContact

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- The transpose of the conjugate of a Fitzpatrick function dominates the original function. -/
theorem fitzpatrick_le_conjugate_swap
    {A : SetValuedOperator H H} (hA : IsMonotone A) (x u : H) :
    fitzpatrick A x u ≤ ERealFunction.conjugate (fitzpatrickProd A) (u, x) := by
  rw [fitzpatrick_eq_iSup_graph A x u, ERealFunction.conjugate_apply]
  refine iSup_le fun p ↦ ?_
  have hp : fitzpatrickProd A p.val = (inner ℝ p.val.1 p.val.2 : EReal) :=
    fitzpatrick_graph_eq_inner hA p.property
  have hterm := le_iSup
    (fun q : H × H ↦ ((inner ℝ q (u, x) : ℝ) : EReal) - fitzpatrickProd A q)
    p.val
  calc
    ((inner ℝ x p.val.2 + inner ℝ p.val.1 u -
        inner ℝ p.val.1 p.val.2 : ℝ) : EReal) =
        ((inner ℝ p.val (u, x) : ℝ) : EReal) - fitzpatrickProd A p.val := by
          rw [hp, ERealFunction.prod_inner_l2_apply, ← EReal.coe_sub]
          congr 1
          rw [real_inner_comm p.val.2 x]
          ring
    _ ≤ _ := hterm

/-- At a graph point, the swapped Fenchel conjugate also equals the pairing. -/
theorem fitzpatrick_conjugate_swap_eq_inner_of_mem
    {A : SetValuedOperator H H} (hA : IsMonotone A)
    {x u : H} (hu : u ∈ A x) :
    ERealFunction.conjugate (fitzpatrickProd A) (u, x) =
      (inner ℝ x u : EReal) := by
  apply le_antisymm
  · rw [ERealFunction.conjugate_apply]
    refine iSup_le fun p ↦ ?_
    have hsupport :
        ((inner ℝ p.1 u + inner ℝ x p.2 - inner ℝ x u : ℝ) : EReal) ≤
          fitzpatrickProd A p := by
      exact le_sSup ⟨x, u, hu, rfl⟩
    calc
      ((inner ℝ p (u, x) : ℝ) : EReal) - fitzpatrickProd A p ≤
          ((inner ℝ p (u, x) : ℝ) : EReal) -
            ((inner ℝ p.1 u + inner ℝ x p.2 - inner ℝ x u : ℝ) : EReal) :=
        EReal.sub_le_sub le_rfl hsupport
      _ = (inner ℝ x u : EReal) := by
        rw [ERealFunction.prod_inner_l2_apply, ← EReal.coe_sub]
        congr 1
        rw [real_inner_comm p.2 x]
        ring
  · calc
      (inner ℝ x u : EReal) = fitzpatrick A x u :=
        (fitzpatrick_graph_eq_inner hA hu).symm
      _ ≤ ERealFunction.conjugate (fitzpatrickProd A) (u, x) :=
        fitzpatrick_le_conjugate_swap hA x u

/-- Equality in the swapped conjugate lower bound characterizes the maximal monotone graph. -/
theorem fitzpatrick_conjugate_swap_eq_inner_iff_mem
    {A : SetValuedOperator H H} (hA : Maximal SetValuedOperator.IsMonotone A) (x u : H) :
    ERealFunction.conjugate (fitzpatrickProd A) (u, x) =
      (inner ℝ x u : EReal) ↔ u ∈ A x := by
  constructor
  · intro hcontact
    have hfitz :
        fitzpatrick A x u ≤ (inner ℝ x u : EReal) := by
      rw [← hcontact]
      exact fitzpatrick_le_conjugate_swap hA.1 x u
    have hAmax : IsMaximalMonotone A :=
      (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).2 hA
    have hpair := inner_le_fitzpatrick_of_maximal hAmax x u
    exact (fitzpatrick_eq_inner_iff_mem_graph_of_maximal hA).1
      (le_antisymm hfitz hpair)
  · exact fitzpatrick_conjugate_swap_eq_inner_of_mem hA.1

/-- The swapped conjugate satisfies the same pairing lower bound as the Fitzpatrick function. -/
theorem inner_le_fitzpatrick_conjugate_swap_of_maximal
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) (x u : H) :
    (inner ℝ x u : EReal) ≤ ERealFunction.conjugate (fitzpatrickProd A) (u, x) :=
  (inner_le_fitzpatrick_of_maximal hA x u).trans
    (fitzpatrick_le_conjugate_swap hA.1 x u)

/-- The conjugate of a maximal monotone Fitzpatrick function is proper. -/
theorem fitzpatrickProd_conjugate_isProper
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) :
    ERealFunction.IsProper (ERealFunction.conjugate (fitzpatrickProd A)) := by
  constructor
  · exact ERealFunction.conjugate_ne_bot_of_isProper
      (fitzpatrickProd_proper hA)
  · rcases maximalMonotone_graph_nonempty (A := A) hA with ⟨p, hp⟩
    refine ⟨(p.2, p.1), ?_⟩
    rw [ERealFunction.mem_dom_iff]
    rw [fitzpatrick_conjugate_swap_eq_inner_of_mem hA.1 hp]
    exact EReal.coe_lt_top _

omit [CompleteSpace H] in
/-- The Fitzpatrick function of a maximal monotone operator belongs to `Γ₀` after packaging
its exclusion of `-∞`. -/
theorem fitzpatrickProd_properIoi_mem_gammaZero
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) :
    ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA) ∈
      ERealFunction.gammaZero (H × H) := by
  have hgamma : fitzpatrickProd A ∈ ERealFunction.gamma (H × H) := by
    rw [ERealFunction.mem_gamma_iff]
    constructor
    · intro p q a ha ha1
      exact fitzpatrickProd_convex p q a (1 - a) ha
        (sub_nonneg.mpr ha1) (by ring)
    · exact fitzpatrickProd_lowerSemicontinuous hA
  exact ERealFunction.properIoi_mem_gammaZero_of_mem_gamma
    (fitzpatrickProd_proper hA) hgamma

/-- The projected Fitzpatrick-domain regularity condition lifts to the pullback domains used in
fiberwise conjugation. -/
theorem fitzpatrick_lifted_sri_of_projected_sri
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hsri : (0 : H) ∈ Set.strongRelativeInterior
      (Prod.fst '' (ERealFunction.dom (fitzpatrickProd A) -
        ERealFunction.dom (fitzpatrickProd B)))) :
    let φ := ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA)
    let ψ := ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB)
    (0 : (H × H) × H) ∈ Set.strongRelativeInterior
      (ERealFunction.effectiveDomain (φ ∘ ERealFunction.firstLastPullbackMap) -
        ERealFunction.effectiveDomain
          (ψ ∘ ERealFunction.firstDifferencePullbackMap)) := by
  let φ := ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA)
  let ψ := ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB)
  have hφ : φ ∈ ERealFunction.gammaZero (H × H) :=
    fitzpatrickProd_properIoi_mem_gammaZero hA
  have hψ : ψ ∈ ERealFunction.gammaZero (H × H) :=
    fitzpatrickProd_properIoi_mem_gammaZero hB
  have hdomA : ERealFunction.effectiveDomain φ =
      ERealFunction.dom (fitzpatrickProd A) := by
    ext p
    simp [φ, ERealFunction.mem_effectiveDomain_iff, ERealFunction.mem_dom_iff]
  have hdomB : ERealFunction.effectiveDomain ψ =
      ERealFunction.dom (fitzpatrickProd B) := by
    ext p
    simp [ψ, ERealFunction.mem_effectiveDomain_iff, ERealFunction.mem_dom_iff]
  have hsri' : (0 : H) ∈ Set.strongRelativeInterior
      (Prod.fst '' (ERealFunction.effectiveDomain φ -
        ERealFunction.effectiveDomain ψ)) := by
    simpa [hdomA, hdomB] using hsri
  exact ERealFunction.zero_mem_sri_lifted_effectiveDomain_difference_of_gammaZero
    φ ψ hφ hψ hsri'

end ConjugateContact

/-! ## Fiberwise Fitzpatrick sums

The Chapter 25 sum theorem works with the infimal convolution in the second
coordinate of two Fitzpatrick functions.  Keep this owner on the raw pair
space; the later duality files can choose whichever product-space model they
need.
-/

noncomputable def fitzpatrickFiberwiseInfimalConvolution
    (A B : SetValuedOperator H H) : H × H → EReal :=
  fun p ↦ ⨅ v : H, fitzpatrick A p.1 v + fitzpatrick B p.1 (p.2 - v)

omit [CompleteSpace H] in
theorem fitzpatrickFiberwiseInfimalConvolution_apply
    (A B : SetValuedOperator H H) (x u : H) :
    fitzpatrickFiberwiseInfimalConvolution A B (x, u) =
      ⨅ v : H, fitzpatrick A x v + fitzpatrick B x (u - v) :=
  rfl

omit [CompleteSpace H] in
theorem pairing_le_fitzpatrickFiberwiseInfimalConvolution
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) (x u : H) :
    (inner ℝ x u : EReal) ≤
      fitzpatrickFiberwiseInfimalConvolution A B (x, u) := by
  rw [fitzpatrickFiberwiseInfimalConvolution_apply]
  refine le_iInf fun v ↦ ?_
  have hAv : (inner ℝ x v : EReal) ≤ fitzpatrick A x v :=
    inner_le_fitzpatrick_of_maximal (A := A) hA x v
  have hBuv : (inner ℝ x (u - v) : EReal) ≤ fitzpatrick B x (u - v) :=
    inner_le_fitzpatrick_of_maximal (A := B) hB x (u - v)
  have hpair :
      (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) =
        (inner ℝ x u : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    rw [inner_sub_right]
    ring
  rw [← hpair]
  exact add_le_add hAv hBuv

omit [CompleteSpace H] in
/-- The fiberwise Fitzpatrick infimal convolution is never `-∞`; a common finite slice point
gives a nonempty effective domain. -/
theorem fitzpatrickFiberwiseInfimalConvolution_isProper_of_common_finite
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hfinite : ∃ x uA uB : H,
      fitzpatrick A x uA < (⊤ : EReal) ∧ fitzpatrick B x uB < (⊤ : EReal)) :
    ERealFunction.IsProper (fitzpatrickFiberwiseInfimalConvolution A B) := by
  constructor
  · intro p hbot
    have hpair :
        (inner ℝ p.1 p.2 : EReal) ≤
          fitzpatrickFiberwiseInfimalConvolution A B p :=
      pairing_le_fitzpatrickFiberwiseInfimalConvolution hA hB p.1 p.2
    rw [hbot] at hpair
    exact (not_le_of_gt (EReal.bot_lt_coe (inner ℝ p.1 p.2))) hpair
  · rcases hfinite with ⟨x, uA, uB, hA_top, hB_top⟩
    refine ⟨(x, uA + uB), ?_⟩
    rw [ERealFunction.mem_dom_iff]
    rw [fitzpatrickFiberwiseInfimalConvolution_apply]
    have hsplit : (uA + uB) - uA = uB := by abel
    calc
      (⨅ v : H, fitzpatrick A x v + fitzpatrick B x ((uA + uB) - v)) ≤
          fitzpatrick A x uA + fitzpatrick B x ((uA + uB) - uA) :=
        iInf_le (fun v : H ↦ fitzpatrick A x v + fitzpatrick B x ((uA + uB) - v)) uA
      _ = fitzpatrick A x uA + fitzpatrick B x uB := by rw [hsplit]
      _ < (⊤ : EReal) := EReal.add_lt_top hA_top.ne hB_top.ne

omit [CompleteSpace H] in
/-- A zero point in the projected difference of the two Fitzpatrick effective domains provides a
common first coordinate with finite values for both Fitzpatrick functions. -/
theorem exists_common_finite_fitzpatrick_slice_of_zero_mem_projected_dom_difference
    {A B : SetValuedOperator H H}
    (hzero : (0 : H) ∈
      Prod.fst ''
        (ERealFunction.dom (fun p : H × H ↦ fitzpatrick A p.1 p.2) -
          ERealFunction.dom (fun p : H × H ↦ fitzpatrick B p.1 p.2))) :
    ∃ x uA uB : H,
      fitzpatrick A x uA < (⊤ : EReal) ∧ fitzpatrick B x uB < (⊤ : EReal) := by
  rcases hzero with ⟨d, hd, hd0⟩
  rcases Set.mem_sub.mp hd with ⟨p, hp, q, hq, hpq⟩
  have hpfin : fitzpatrick A p.1 p.2 < (⊤ : EReal) :=
    (ERealFunction.mem_dom_iff _ p).mp hp
  have hqfin : fitzpatrick B q.1 q.2 < (⊤ : EReal) :=
    (ERealFunction.mem_dom_iff _ q).mp hq
  have hfirst : p.1 = q.1 := by
    have hsub : p.1 - q.1 = (0 : H) := by
      calc
        p.1 - q.1 = (p - q).1 := by rfl
        _ = d.1 := by rw [hpq]
        _ = 0 := hd0
    exact sub_eq_zero.mp hsub
  refine ⟨p.1, p.2, q.2, hpfin, ?_⟩
  simpa [hfirst] using hqfin

omit [CompleteSpace H] in
/-- The projected zero-domain condition is enough to make the fiberwise Fitzpatrick owner proper. -/
theorem fitzpatrickFiberwiseInfimalConvolution_isProper_of_zero_mem_projected_dom_difference
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hzero : (0 : H) ∈
      Prod.fst ''
        (ERealFunction.dom (fun p : H × H ↦ fitzpatrick A p.1 p.2) -
          ERealFunction.dom (fun p : H × H ↦ fitzpatrick B p.1 p.2))) :
    ERealFunction.IsProper (fitzpatrickFiberwiseInfimalConvolution A B) := by
  exact fitzpatrickFiberwiseInfimalConvolution_isProper_of_common_finite hA hB
    (exists_common_finite_fitzpatrick_slice_of_zero_mem_projected_dom_difference hzero)

omit [CompleteSpace H] in
theorem fitzpatrickFiberwiseInfimalConvolution_eq_pairing_of_mem_graph_add
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    {x u uA uB : H} (huA : uA ∈ A x) (huB : uB ∈ B x)
    (hu : u = uA + uB) :
    fitzpatrickFiberwiseInfimalConvolution A B (x, u) = (inner ℝ x u : EReal) := by
  have hlower :
      (inner ℝ x u : EReal) ≤
        fitzpatrickFiberwiseInfimalConvolution A B (x, u) := by
    exact pairing_le_fitzpatrickFiberwiseInfimalConvolution
      hA hB x u
  have hupper :
    fitzpatrickFiberwiseInfimalConvolution A B (x, u) ≤
        (inner ℝ x u : EReal) := by
    rw [fitzpatrickFiberwiseInfimalConvolution_apply]
    refine iInf_le_of_le uA ?_
    have huv : u - uA = uB := by
      rw [hu]
      abel
    rw [huv]
    rw [fitzpatrick_graph_eq_inner hA.1 huA, fitzpatrick_graph_eq_inner hB.1 huB]
    rw [← EReal.coe_add]
    rw [hu, inner_add_right]
  exact le_antisymm hupper hlower

omit [CompleteSpace H] in
/-- A attained fiber split at a Fitzpatrick contact point yields membership in the operator sum. -/
theorem mem_graph_add_of_fitzpatrickFiberwiseInfimalConvolution_eq_pairing_of_exists_split
    {A B : SetValuedOperator H H}
    (hA : Maximal SetValuedOperator.IsMonotone A)
    (hB : Maximal SetValuedOperator.IsMonotone B)
    {x u : H}
    (hcontact :
      fitzpatrickFiberwiseInfimalConvolution A B (x, u) = (inner ℝ x u : EReal))
    (hsplit : ∃ v : H,
      fitzpatrick A x v + fitzpatrick B x (u - v) =
        fitzpatrickFiberwiseInfimalConvolution A B (x, u)) :
    u ∈ (A x + B x : Set H) := by
  rcases hsplit with ⟨v, hv⟩
  have hAmax : IsMaximalMonotone A :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).2 hA
  have hBmax : IsMaximalMonotone B :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone B).2 hB
  have hsum :
      fitzpatrick A x v + fitzpatrick B x (u - v) = (inner ℝ x u : EReal) :=
    hv.trans hcontact
  have hpair :
      (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) =
        (inner ℝ x u : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    rw [inner_sub_right]
    ring
  have hA_lower : (inner ℝ x v : EReal) ≤ fitzpatrick A x v :=
    inner_le_fitzpatrick_of_maximal hAmax x v
  have hB_lower : (inner ℝ x (u - v) : EReal) ≤ fitzpatrick B x (u - v) :=
    inner_le_fitzpatrick_of_maximal hBmax x (u - v)
  have htotal :
      fitzpatrick A x v + fitzpatrick B x (u - v) =
        (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) :=
    hsum.trans hpair.symm
  have hA_le : fitzpatrick A x v ≤ (inner ℝ x v : EReal) := by
    apply (EReal.addLECancellable_coe (inner ℝ x (u - v))).add_le_add_iff_right.mp
    calc
      fitzpatrick A x v + (inner ℝ x (u - v) : EReal) ≤
          fitzpatrick A x v + fitzpatrick B x (u - v) :=
        add_le_add_right hB_lower _
      _ = (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) := htotal
  have hA_eq : fitzpatrick A x v = (inner ℝ x v : EReal) :=
    le_antisymm hA_le hA_lower
  have hB_le : fitzpatrick B x (u - v) ≤ (inner ℝ x (u - v) : EReal) := by
    apply (EReal.addLECancellable_coe (inner ℝ x v)).add_le_add_iff_left.mp
    calc
      (inner ℝ x v : EReal) + fitzpatrick B x (u - v) ≤
          fitzpatrick A x v + fitzpatrick B x (u - v) :=
        add_le_add_left hA_lower _
      _ = (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) := htotal
  have hB_eq : fitzpatrick B x (u - v) = (inner ℝ x (u - v) : EReal) :=
    le_antisymm hB_le hB_lower
  have hvA : v ∈ A x :=
    (fitzpatrick_eq_inner_iff_mem_graph_of_maximal hA).1 hA_eq
  have hvB : u - v ∈ B x :=
    (fitzpatrick_eq_inner_iff_mem_graph_of_maximal hB).1 hB_eq
  exact Set.mem_add.mpr ⟨v, hvA, u - v, hvB, by abel⟩

omit [CompleteSpace H] in
/-- Exact fiberwise infimal convolution identifies its pairing contact set with the graph of
the operator sum. -/
theorem fitzpatrickFiberwiseInfimalConvolution_eq_pairing_iff_mem_add_of_exact
    {A B : SetValuedOperator H H}
    (hA : Maximal SetValuedOperator.IsMonotone A)
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hexact : ∀ x u : H,
      fitzpatrickFiberwiseInfimalConvolution A B (x, u) = (inner ℝ x u : EReal) →
        ∃ v : H,
          fitzpatrick A x v + fitzpatrick B x (u - v) =
            fitzpatrickFiberwiseInfimalConvolution A B (x, u))
    (x u : H) :
    fitzpatrickFiberwiseInfimalConvolution A B (x, u) = (inner ℝ x u : EReal) ↔
      u ∈ (A x + B x : Set H) := by
  constructor
  · intro hcontact
    exact mem_graph_add_of_fitzpatrickFiberwiseInfimalConvolution_eq_pairing_of_exists_split
      hA hB hcontact (hexact x u hcontact)
  · intro hu
    rcases Set.mem_add.mp hu with ⟨uA, huA, uB, huB, hsum⟩
    exact fitzpatrickFiberwiseInfimalConvolution_eq_pairing_of_mem_graph_add
      ((SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).2 hA)
      ((SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone B).2 hB)
      huA huB hsum.symm

section FiberwiseConjugateContact

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Every dual split gives the unconditional upper bound for the fiberwise conjugate. -/
theorem fitzpatrickFiberwise_conjugate_swap_le_split
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (x u v : H) :
    ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) ≤
      ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
        ERealFunction.conjugate (fitzpatrickProd B) (u - v, x) := by
  let φ := ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA)
  let ψ := ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB)
  simpa [φ, ψ, fitzpatrickFiberwiseInfimalConvolution, fitzpatrickProd,
    ERealFunction.properIoi_apply, ERealFunction.asEReal_properIoi] using
    (ERealFunction.conjugate_secondVariableFiberwiseInfimalConvolution_le_split
      φ ψ (u, x) v)

/-- Every point in the graph of the operator sum is a contact point of the fiberwise conjugate. -/
theorem fitzpatrickFiberwise_conjugate_swap_eq_inner_of_mem_add
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    {x u : H} (hu : u ∈ (A x + B x : Set H)) :
    ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
      (inner ℝ x u : EReal) := by
  rcases Set.mem_add.mp hu with ⟨v, hv, w, hw, hsum⟩
  have hupper :=
    fitzpatrickFiberwise_conjugate_swap_le_split hA hB x u v
  have huw : u - v = w := by rw [← hsum]; abel
  rw [huw, fitzpatrick_conjugate_swap_eq_inner_of_mem hA.1 hv,
    fitzpatrick_conjugate_swap_eq_inner_of_mem hB.1 hw] at hupper
  have hupper' :
      ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) ≤
        (inner ℝ x u : EReal) := by
    calc
      _ ≤ (inner ℝ x v : EReal) + (inner ℝ x w : EReal) := hupper
      _ = (inner ℝ x u : EReal) := by
        rw [← EReal.coe_add, ← hsum, inner_add_right]
  have hgraph :
      fitzpatrickFiberwiseInfimalConvolution A B (x, u) =
        (inner ℝ x u : EReal) :=
    fitzpatrickFiberwiseInfimalConvolution_eq_pairing_of_mem_graph_add
      hA hB hv hw hsum.symm
  have hlower :
      (inner ℝ x u : EReal) ≤
        ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) := by
    rw [ERealFunction.conjugate_apply]
    have hterm := le_iSup
      (fun p : H × H ↦
        ((inner ℝ p (u, x) : ℝ) : EReal) -
          fitzpatrickFiberwiseInfimalConvolution A B p) (x, u)
    convert hterm using 1
    rw [hgraph, ERealFunction.prod_inner_l2_apply, ← EReal.coe_sub]
    congr 1
    rw [real_inner_comm u x]
    ring
  exact le_antisymm hupper' hlower

/-- An attained dual split of a fiberwise conjugate contact point belongs to the operator sum. -/
theorem mem_add_of_fitzpatrickFiberwise_conjugate_swap_contact_of_split
    {A B : SetValuedOperator H H}
    (hA : Maximal SetValuedOperator.IsMonotone A)
    (hB : Maximal SetValuedOperator.IsMonotone B)
    {x u v : H}
    (hcontact :
      ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
        (inner ℝ x u : EReal))
    (hsplit :
      ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
        ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
          ERealFunction.conjugate (fitzpatrickProd B) (u - v, x)) :
    u ∈ (A x + B x : Set H) := by
  have hAmax : IsMaximalMonotone A :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).2 hA
  have hBmax : IsMaximalMonotone B :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone B).2 hB
  have hA_lower := inner_le_fitzpatrick_conjugate_swap_of_maximal hAmax x v
  have hB_lower := inner_le_fitzpatrick_conjugate_swap_of_maximal hBmax x (u - v)
  have hpair :
      (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) =
        (inner ℝ x u : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    rw [inner_sub_right]
    ring
  have hsum :
      ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
        ERealFunction.conjugate (fitzpatrickProd B) (u - v, x) =
          (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) :=
    hsplit.symm.trans (hcontact.trans hpair.symm)
  have hA_upper :
      ERealFunction.conjugate (fitzpatrickProd A) (v, x) ≤
        (inner ℝ x v : EReal) := by
    apply (EReal.addLECancellable_coe (inner ℝ x (u - v))).add_le_add_iff_right.mp
    calc
      ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
          (inner ℝ x (u - v) : EReal) ≤
          ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
            ERealFunction.conjugate (fitzpatrickProd B) (u - v, x) :=
        add_le_add_right hB_lower _
      _ = (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) := hsum
  have hB_upper :
      ERealFunction.conjugate (fitzpatrickProd B) (u - v, x) ≤
        (inner ℝ x (u - v) : EReal) := by
    apply (EReal.addLECancellable_coe (inner ℝ x v)).add_le_add_iff_left.mp
    calc
      (inner ℝ x v : EReal) +
          ERealFunction.conjugate (fitzpatrickProd B) (u - v, x) ≤
          ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
            ERealFunction.conjugate (fitzpatrickProd B) (u - v, x) :=
        add_le_add_left hA_lower _
      _ = (inner ℝ x v : EReal) + (inner ℝ x (u - v) : EReal) := hsum
  have hvA : v ∈ A x :=
    (fitzpatrick_conjugate_swap_eq_inner_iff_mem hA x v).1
      (le_antisymm hA_upper hA_lower)
  have hvB : u - v ∈ B x :=
    (fitzpatrick_conjugate_swap_eq_inner_iff_mem hB x (u - v)).1
      (le_antisymm hB_upper hB_lower)
  exact Set.mem_add.mpr ⟨v, hvA, u - v, hvB, by abel⟩

/-- Dual exactness only at pairing contact points identifies the contact set with the sum graph. -/
theorem fitzpatrickFiberwise_conjugate_swap_eq_inner_iff_mem_add_of_contact_split
    {A B : SetValuedOperator H H}
    (hA : Maximal SetValuedOperator.IsMonotone A)
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (hexact : ∀ x u : H,
      ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
        (inner ℝ x u : EReal) →
      ∃ v : H,
        ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
          ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
            ERealFunction.conjugate (fitzpatrickProd B) (u - v, x))
    (x u : H) :
    ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
      (inner ℝ x u : EReal) ↔ u ∈ (A x + B x : Set H) := by
  constructor
  · intro hcontact
    rcases hexact x u hcontact with ⟨v, hsplit⟩
    exact mem_add_of_fitzpatrickFiberwise_conjugate_swap_contact_of_split
      hA hB hcontact hsplit
  · intro hu
    exact fitzpatrickFiberwise_conjugate_swap_eq_inner_of_mem_add
      ((SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).2 hA)
      ((SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone B).2 hB) hu

end FiberwiseConjugateContact

/-! ## Attained lifted Fitzpatrick duality

The following wrapper specializes the abstract lifted fiberwise conjugation theorem to
Fitzpatrick functions.  It isolates the remaining analytic input in the explicit split
attainment hypothesis, while hiding the `properIoi` representation used by `Γ₀`. -/

section AttainedLiftedFitzpatrick

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

theorem fitzpatrickFiberwise_conjugate_swap_eq_firstVariableInfimalConvolution_of_split_attainment
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hsri : (0 : H) ∈ Set.strongRelativeInterior
      (Prod.fst '' (ERealFunction.dom (fitzpatrickProd A) -
        ERealFunction.dom (fitzpatrickProd B))))
    (hattain : ∀ q : (H × H) × H, ∃ r : (H × H) × H,
      ERealFunction.conjugate
          ((ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA) ∘
              ERealFunction.firstLastPullbackMap) +
            (ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB) ∘
              ERealFunction.firstDifferencePullbackMap)).asEReal q =
        ERealFunction.conjugate
            (ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA) ∘
              ERealFunction.firstLastPullbackMap).asEReal r +
          ERealFunction.conjugate
            (ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB) ∘
              ERealFunction.firstDifferencePullbackMap).asEReal (q - r)) :
    ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) =
      fun q : H × H ↦
        ((fun v : H ↦ ERealFunction.conjugate (fitzpatrickProd A) (v, q.2)) □
          fun v ↦ ERealFunction.conjugate (fitzpatrickProd B) (v, q.2)) q.1 := by
  let φ : H × H → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA)
  let ψ : H × H → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB)
  have hφ : φ ∈ ERealFunction.gammaZero (H × H) := by
    exact fitzpatrickProd_properIoi_mem_gammaZero hA
  have hψ : ψ ∈ ERealFunction.gammaZero (H × H) := by
    exact fitzpatrickProd_properIoi_mem_gammaZero hB
  have hdomA : ERealFunction.effectiveDomain φ = ERealFunction.dom (fitzpatrickProd A) := by
    ext p
    simp [φ, ERealFunction.mem_effectiveDomain_iff, ERealFunction.mem_dom_iff]
  have hdomB : ERealFunction.effectiveDomain ψ = ERealFunction.dom (fitzpatrickProd B) := by
    ext p
    simp [ψ, ERealFunction.mem_effectiveDomain_iff, ERealFunction.mem_dom_iff]
  have hsri' : (0 : H) ∈ Set.strongRelativeInterior
      (Prod.fst '' (ERealFunction.effectiveDomain φ - ERealFunction.effectiveDomain ψ)) := by
    simpa [hdomA, hdomB] using hsri
  have hattain' : ∀ q : (H × H) × H, ∃ r : (H × H) × H,
      ERealFunction.conjugate ((φ ∘ ERealFunction.firstLastPullbackMap) +
        (ψ ∘ ERealFunction.firstDifferencePullbackMap)).asEReal q =
        ERealFunction.conjugate (φ ∘ ERealFunction.firstLastPullbackMap).asEReal r +
          ERealFunction.conjugate (ψ ∘ ERealFunction.firstDifferencePullbackMap).asEReal (q - r) := by
    simpa [φ, ψ] using hattain
  simpa [φ, ψ, fitzpatrickFiberwiseInfimalConvolution, fitzpatrickProd,
    ERealFunction.properIoi_apply, ERealFunction.asEReal_properIoi] using
    (ERealFunction.conjugate_secondVariableFiberwiseInfimalConvolution_eq_firstVariableInfimalConvolution_of_split_attainment
      φ ψ hφ hψ hsri' hattain')

end AttainedLiftedFitzpatrick

section AttainedLiftedFitzpatrickContact

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

theorem exists_fitzpatrickFiberwise_conjugate_swap_split_of_contact_of_split_attainment
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hattain : ∀ q : (H × H) × H, ∃ r : (H × H) × H,
      ERealFunction.conjugate
          ((ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA) ∘
              ERealFunction.firstLastPullbackMap) +
            (ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB) ∘
              ERealFunction.firstDifferencePullbackMap)).asEReal q =
        ERealFunction.conjugate
            (ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA) ∘
              ERealFunction.firstLastPullbackMap).asEReal r +
          ERealFunction.conjugate
            (ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB) ∘
              ERealFunction.firstDifferencePullbackMap).asEReal (q - r))
    {x u : H}
    (hcontact :
      ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
        (inner ℝ x u : EReal)) :
    ∃ v : H,
      ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
        ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
          ERealFunction.conjugate (fitzpatrickProd B) (u - v, x) := by
  let φ : H × H → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA)
  let ψ : H × H → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB)
  let Φ : (H × H) × H → Set.Ioi (⊥ : EReal) :=
    φ ∘ ERealFunction.firstLastPullbackMap
  let Ψ : (H × H) × H → Set.Ioi (⊥ : EReal) :=
    ψ ∘ ERealFunction.firstDifferencePullbackMap
  have hφ : φ ∈ ERealFunction.gammaZero (H × H) := by
    exact fitzpatrickProd_properIoi_mem_gammaZero hA
  have hψ : ψ ∈ ERealFunction.gammaZero (H × H) := by
    exact fitzpatrickProd_properIoi_mem_gammaZero hB
  have hΦ : Φ ∈ ERealFunction.gammaZero ((H × H) × H) := by
    exact ERealFunction.firstLastPullback_mem_gammaZero φ hφ
  have hΨ : Ψ ∈ ERealFunction.gammaZero ((H × H) × H) := by
    exact ERealFunction.firstDifferencePullback_mem_gammaZero ψ hψ
  have hrepr :
      (fun p : H × H ↦
        ERealFunction.infimalConvolution
          (fun z : H ↦ (φ (p.1, z) : EReal))
          (fun z : H ↦ (ψ (p.1, z) : EReal)) p.2) =
        ERealFunction.infimalPostcomposition Prod.fst
          (Φ.asEReal + Ψ.asEReal) := by
    simpa [Φ, Ψ, Function.asEReal_apply, Pi.add_apply, Function.comp] using
      (ERealFunction.secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted
        φ ψ)
  have hcontact0 :
      ERealFunction.conjugate
          (fun p : H × H ↦
            ERealFunction.infimalConvolution
              (fun z : H ↦ (φ (p.1, z) : EReal))
              (fun z : H ↦ (ψ (p.1, z) : EReal)) p.2) (u, x) =
        (inner ℝ x u : EReal) := by
    simpa [fitzpatrickFiberwiseInfimalConvolution, φ, ψ,
      ERealFunction.properIoi_apply] using hcontact
  rw [hrepr, ERealFunction.conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond]
    at hcontact0
  have hcontact' :
      ERealFunction.conjugate (Φ.asEReal + Ψ.asEReal) ((u, x), (0 : H)) =
        (inner ℝ x u : EReal) := by
    simpa using hcontact0
  rcases hattain ((u, x), (0 : H)) with ⟨r, hr⟩
  have hr' :
      ERealFunction.conjugate (Φ.asEReal + Ψ.asEReal) ((u, x), (0 : H)) =
        ERealFunction.conjugate Φ.asEReal r +
          ERealFunction.conjugate Ψ.asEReal (((u, x), (0 : H)) - r) := by
    simpa [Φ, Ψ, φ, ψ, Function.asEReal_apply, Pi.add_apply] using hr
  rcases r with ⟨⟨v, b⟩, c⟩
  have harg : ((u, x), (0 : H)) - ((v, b), c) =
      ((u - v, x - b), -c) := by
    ext <;> simp
  rw [harg] at hr'
  have hsum_eq :
      ERealFunction.conjugate Φ.asEReal ((v, b), c) +
          ERealFunction.conjugate Ψ.asEReal ((u - v, x - b), -c) =
        (inner ℝ x u : EReal) := hr'.symm.trans hcontact'
  have hterms_ne_top :
      ERealFunction.conjugate Φ.asEReal ((v, b), c) +
          ERealFunction.conjugate Ψ.asEReal ((u - v, x - b), -c) ≠ (⊤ : EReal) := by
    rw [hsum_eq]
    exact EReal.coe_ne_top _
  by_cases hb : b = 0
  · subst b
    by_cases hc : c = x
    · subst c
      refine ⟨v, ?_⟩
      have hΦslice : ERealFunction.conjugate Φ.asEReal ((v, (0 : H)), x) =
          ERealFunction.conjugate φ.asEReal (v, x) := by
        simpa [Φ] using ERealFunction.conjugate_firstLastPullback_zeroSlice φ v x
      have hΨslice : ERealFunction.conjugate Ψ.asEReal ((u - v, x), -x) =
          ERealFunction.conjugate ψ.asEReal (u - v, x) := by
        simpa [Ψ] using ERealFunction.conjugate_firstDifferencePullback_negSlice ψ (u - v) x
      have hsum_phi :
          ERealFunction.conjugate φ.asEReal (v, x) +
              ERealFunction.conjugate ψ.asEReal (u - v, x) =
            (inner ℝ x u : EReal) := by
        have htmp := hsum_eq
        simp only [sub_zero] at htmp
        rw [hΦslice, hΨslice] at htmp
        exact htmp
      have hsum_raw :
          ERealFunction.conjugate (fitzpatrickProd A) (v, x) +
              ERealFunction.conjugate (fitzpatrickProd B) (u - v, x) =
            (inner ℝ x u : EReal) := by
        simpa [φ, ψ, fitzpatrickProd,
          ERealFunction.properIoi_apply, ERealFunction.asEReal_properIoi] using hsum_phi
      exact hcontact.trans hsum_raw.symm
    · have htop :
          ERealFunction.conjugate Ψ.asEReal ((u - v, x), -c) = (⊤ : EReal) := by
        simpa [Ψ] using
          ERealFunction.conjugate_firstDifferencePullback_top_of_ne_neg ψ hψ
            (u - v) x (-c) (by
              intro heq
              apply hc
              simpa using congrArg Neg.neg heq)
      have hnebot : ERealFunction.conjugate Φ.asEReal ((v, (0 : H)), c) ≠ (⊥ : EReal) :=
        ERealFunction.conjugate_ne_bot_of_isProper
          (ERealFunction.isProper_of_mem_gammaZero hΦ) ((v, (0 : H)), c)
      have htop_sum :
          ERealFunction.conjugate Φ.asEReal ((v, (0 : H)), c) +
              ERealFunction.conjugate Ψ.asEReal ((u - v, x), -c) = (⊤ : EReal) := by
        rw [htop, EReal.add_top_of_ne_bot hnebot]
      exact (hterms_ne_top (by simpa using htop_sum)).elim
  · have htop : ERealFunction.conjugate Φ.asEReal ((v, b), c) = (⊤ : EReal) := by
      simpa [Φ] using
        ERealFunction.conjugate_firstLastPullback_top_of_ne_zero φ hφ v b c hb
    have hnebot :
        ERealFunction.conjugate Ψ.asEReal ((u - v, x - b), -c) ≠ (⊥ : EReal) :=
      ERealFunction.conjugate_ne_bot_of_isProper
        (ERealFunction.isProper_of_mem_gammaZero hΨ) ((u - v, x - b), -c)
    have htop_sum :
        ERealFunction.conjugate Φ.asEReal ((v, b), c) +
            ERealFunction.conjugate Ψ.asEReal ((u - v, x - b), -c) = (⊤ : EReal) := by
      rw [htop, EReal.top_add_of_ne_bot hnebot]
    exact (hterms_ne_top htop_sum).elim

end AttainedLiftedFitzpatrickContact

section AttainedLiftedFitzpatrickSum

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

theorem fitzpatrickFiberwise_conjugate_swap_eq_inner_iff_mem_add_of_split_attainment
    {A B : SetValuedOperator H H}
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hattain : ∀ q : (H × H) × H, ∃ r : (H × H) × H,
      ERealFunction.conjugate
          ((ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA) ∘
              ERealFunction.firstLastPullbackMap) +
            (ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB) ∘
              ERealFunction.firstDifferencePullbackMap)).asEReal q =
        ERealFunction.conjugate
            (ERealFunction.properIoi (fitzpatrickProd A) (fitzpatrickProd_proper hA) ∘
              ERealFunction.firstLastPullbackMap).asEReal r +
          ERealFunction.conjugate
            (ERealFunction.properIoi (fitzpatrickProd B) (fitzpatrickProd_proper hB) ∘
              ERealFunction.firstDifferencePullbackMap).asEReal (q - r))
    (x u : H) :
    ERealFunction.conjugate (fitzpatrickFiberwiseInfimalConvolution A B) (u, x) =
        (inner ℝ x u : EReal) ↔ u ∈ (A x + B x : Set H) := by
  let hAm : Maximal SetValuedOperator.IsMonotone A :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone A).1 hA
  let hBm : Maximal SetValuedOperator.IsMonotone B :=
    (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone B).1 hB
  apply fitzpatrickFiberwise_conjugate_swap_eq_inner_iff_mem_add_of_contact_split
    hAm hBm
  intro x' u' hcontact
  exact exists_fitzpatrickFiberwise_conjugate_swap_split_of_contact_of_split_attainment
    hA hB hattain hcontact

end AttainedLiftedFitzpatrickSum

theorem corollary15_17_fitzpatrick_product_specialized
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A)
    (hnonneg :
      ∀ x u : H,
        (0 : EReal) ≤
          fitzpatrick A x u +
            (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal)) :
    ∃ a b : H, ∀ x u : H,
      fitzpatrick A x u + (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) ≥
        (((1 / 2 : ℝ) * (‖x + a‖ ^ 2 + ‖u + b‖ ^ 2) : ℝ) : EReal) := by
  have hsupport :
      ∃ w : H × H, ∀ p : H × H,
        (((productInner (H := H) p w +
            (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) : ℝ) : EReal) ≤
          fitzpatrickProd A p) :=
    corollary15_16_support_productQuadratic
      (f := fitzpatrickProd A)
      (fitzpatrickProd_proper (A := A) hA)
      (fitzpatrickProd_convex (A := A))
      (fitzpatrickProd_lowerSemicontinuous (A := A) hA)
      (by
        intro p
        exact hnonneg p.1 p.2)
  simpa [fitzpatrickProd, productQuadratic] using
    corollary15_17_productQuadratic (H := H) (f := fitzpatrickProd A) hsupport

theorem exists_fitzpatrick_quadratic_minorant_pair
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) :
    ∃ a b : H, ∀ x u : H,
      fitzpatrick A x u + (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) ≥
        (((1 / 2 : ℝ) * (‖x + a‖ ^ 2 + ‖u + b‖ ^ 2) : ℝ) : EReal) := by
  classical
  have hnonneg :
      ∀ x u : H,
        (0 : EReal) ≤
          fitzpatrick A x u + (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) :=
    fitzpatrick_plus_quad_nonneg (A := A) hA
  exact corollary15_17_fitzpatrick_product_specialized (A := A) hA hnonneg

omit [CompleteSpace H] in
theorem fitzpatrick_affine_lower_bound_of_minorant
    {A : SetValuedOperator H H} {a b : H}
    (hminor : ∀ x u : H,
      fitzpatrick A x u + (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) ≥
        (((1 / 2 : ℝ) * (‖x + a‖ ^ 2 + ‖u + b‖ ^ 2) : ℝ) : EReal)) :
    ∀ x u : H,
      (((inner ℝ x a + inner ℝ b u +
          (1 / 2 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2) : ℝ) : EReal)
        ≤ fitzpatrick A x u) := by
  intro x u
  let q : ℝ := (1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2)
  let affine : ℝ :=
    inner ℝ x a + inner ℝ b u + (1 / 2 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2)
  have hshift :
      (1 / 2 : ℝ) * (‖x + a‖ ^ 2 + ‖u + b‖ ^ 2) = affine + q := by
    have hx : ‖x + a‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x a + ‖a‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_comm a x]
      ring
    have hu : ‖u + b‖ ^ 2 = ‖u‖ ^ 2 + 2 * inner ℝ b u + ‖b‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_comm u b]
      ring
    dsimp [affine, q]
    nlinarith
  have hle_add : (affine : EReal) + (q : EReal) ≤ fitzpatrick A x u + (q : EReal) := by
    calc
      (affine : EReal) + (q : EReal) = ((affine + q : ℝ) : EReal) := by
        exact (EReal.coe_add affine q).symm
      _ = (((1 / 2 : ℝ) * (‖x + a‖ ^ 2 + ‖u + b‖ ^ 2) : ℝ) : EReal) := by
        rw [hshift]
      _ ≤ fitzpatrick A x u +
          (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) := hminor x u
      _ = fitzpatrick A x u + (q : EReal) := by rfl
  exact (EReal.addLECancellable_coe q).add_le_add_iff_right.mp hle_add

omit [CompleteSpace H] in
theorem fitzpatrick_weak_affine_lower_bound_of_minorant
    {A : SetValuedOperator H H} {a b : H}
    (hminor : ∀ x u : H,
      fitzpatrick A x u + (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) ≥
        (((1 / 2 : ℝ) * (‖x + a‖ ^ 2 + ‖u + b‖ ^ 2) : ℝ) : EReal)) :
    ∀ x u : H,
      (((inner ℝ x a + inner ℝ b u - inner ℝ b a : ℝ) : EReal)
        ≤ fitzpatrick A x u) := by
  intro x u
  have hconst :
      -inner ℝ b a ≤ (1 / 2 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    have hsq : 0 ≤ ‖a + b‖ ^ 2 := sq_nonneg _
    have hnorm : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ b a + ‖b‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_comm a b]
      ring
    nlinarith
  calc
    (((inner ℝ x a + inner ℝ b u - inner ℝ b a : ℝ) : EReal)
      ≤ ((inner ℝ x a + inner ℝ b u +
          (1 / 2 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2) : ℝ) : EReal)) := by
        exact EReal.coe_le_coe (by nlinarith)
    _ ≤ fitzpatrick A x u :=
        fitzpatrick_affine_lower_bound_of_minorant (A := A) (a := a) (b := b) hminor x u

omit [CompleteSpace H] in
theorem monotonically_related_of_minorant
    {A : SetValuedOperator H H} (hmono : IsMonotone A) {a b : H}
    (hminor : ∀ x u : H,
      fitzpatrick A x u + (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) ≥
        (((1 / 2 : ℝ) * (‖x + a‖ ^ 2 + ‖u + b‖ ^ 2) : ℝ) : EReal)) :
    ∀ z v, v ∈ A z → 0 ≤ inner ℝ (a - v) (b - z) := by
  intro z v hv
  have hweak :=
    fitzpatrick_weak_affine_lower_bound_of_minorant (A := A) (a := a) (b := b) hminor z v
  rw [fitzpatrick_graph_eq_inner hmono hv] at hweak
  have hreal :
      inner ℝ z a + inner ℝ b v - inner ℝ b a ≤ inner ℝ z v :=
    EReal.coe_le_coe_iff.mp hweak
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  have hza : inner ℝ z a = inner ℝ a z := (real_inner_comm z a).symm
  have hbv : inner ℝ b v = inner ℝ v b := (real_inner_comm b v).symm
  have hba : inner ℝ b a = inner ℝ a b := (real_inner_comm b a).symm
  have hzv : inner ℝ z v = inner ℝ v z := (real_inner_comm z v).symm
  nlinarith

omit [CompleteSpace H] in
theorem eq_neg_of_minorant_and_mem
    {A : SetValuedOperator H H} (hmono : IsMonotone A) {a b : H}
    (hminor : ∀ x u : H,
      fitzpatrick A x u + (((1 / 2 : ℝ) * (‖x‖ ^ 2 + ‖u‖ ^ 2) : ℝ) : EReal) ≥
        (((1 / 2 : ℝ) * (‖x + a‖ ^ 2 + ‖u + b‖ ^ 2) : ℝ) : EReal))
    (haA : a ∈ A b) :
    b = -a := by
  have hstrong :=
    fitzpatrick_affine_lower_bound_of_minorant (A := A) (a := a) (b := b) hminor b a
  rw [fitzpatrick_graph_eq_inner hmono haA] at hstrong
  have hreal :
      inner ℝ b a + inner ℝ b a + (1 / 2 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
        inner ℝ b a :=
    EReal.coe_le_coe_iff.mp hstrong
  have hnorm : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ b a + ‖b‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm a b]
    ring
  have hle : ‖a + b‖ ^ 2 ≤ 0 := by nlinarith
  have hzero : ‖a + b‖ ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  have hsum : a + b = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  calc
    b = (a + b) - a := by abel
    _ = -a := by rw [hsum]; abel
