import Mathlib
import Foundation.Analysis.ProductQuadratic
import Foundation.SetValued.MaximalMonotone

/-!
# Fitzpatrick functions for maximal monotone operators

Definitions and reusable analytic properties of the Fitzpatrick function of a
set-valued operator on a real Hilbert space.
-/

open SetValuedOperator
open scoped InnerProductSpace

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def fitzpatrick (A : SetValuedOperator H H) (x u : H) : EReal :=
  sSup {r : EReal | ∃ z v : H, v ∈ A z ∧
    r = ((inner ℝ x v + inner ℝ z u - inner ℝ z v : ℝ) : EReal)}

noncomputable def fitzpatrickProd (A : SetValuedOperator H H) (p : H × H) :
    EReal :=
  fitzpatrick A p.1 p.2

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
