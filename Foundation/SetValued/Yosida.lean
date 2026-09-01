import Mathlib.Analysis.InnerProductSpace.Basic
import Foundation.SetValued.Monotone
import Foundation.SetValued.Minty
import Foundation.SetValued.Resolvent
import Foundation.FixedPoint.Nonexpansive

/-!
# Yosida approximation of maximal monotone operators

The Yosida approximation of a maximal monotone operator is cocoercive and its
scaled residual is firmly nonexpansive (Attouch--Svaiter, Proposition 3.10).
-/

namespace SetValuedOperator

open scoped Pointwise


/-- Proposition 3.10: the Yosida approximation is cocoercive. -/
theorem yosida_is_cocoercive :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone) (mu : ℝ) (hmu : 0 < mu),
      CocoerciveOn mu Set.univ
          (fun x : Set.univ => mu⁻¹ • ((x : H) - resolventMap T hT mu hmu x)) ∧
      IsFirmlyNonexpansiveOn
          (fun x : Set.univ => mu • (mu⁻¹ • ((x : H) - resolventMap T hT mu hmu x))) := by
  intro H _ _ _ T hT mu hmu
  let J : H → H := resolventMap T hT mu hmu
  have hJ : ∀ x : H, J x ∈ J[(mu • T)] x := by
    intro x
    exact resolventMap_mem T hT mu hmu x
  have hresidual : ∀ x y : H,
      ‖((x - y) - (J x - J y))‖ ^ 2 ≤
        inner ℝ (x - y) ((x - y) - (J x - J y)) := by
    intro x y
    have hx : x ∈ T.identityAddScaled mu (J x) :=
      (mem_resolvent_smul_iff T mu x (J x)).1 (hJ x)
    have hy : y ∈ T.identityAddScaled mu (J y) :=
      (mem_resolvent_smul_iff T mu y (J y)).1 (hJ y)
    rcases hx with ⟨a, ha, hxa⟩
    rcases hy with ⟨b, hb, hyb⟩
    have hmono : 0 ≤ inner ℝ (a - b) (J x - J y) := hT.1 a ha b hb
    have hxa' : x - J x = mu • a := by
      calc x - J x = (J x + mu • a) - J x := (congrArg (fun z => z - J x) hxa).symm
           _ = mu • a := by module
    have hyb' : y - J y = mu • b := by
      calc y - J y = (J y + mu • b) - J y := (congrArg (fun z => z - J y) hyb).symm
           _ = mu • b := by module
    have hr : (x - y) - (J x - J y) = mu • (a - b) := by
      calc
        (x - y) - (J x - J y) = (x - J x) - (y - J y) := by module
        _ = mu • (a - b) := by rw [hxa', hyb', smul_sub]
    have hcross : 0 ≤ inner ℝ ((x - y) - (J x - J y)) (J x - J y) := by
      rw [hr, real_inner_smul_left]
      exact mul_nonneg hmu.le hmono
    have hdecomp : x - y = ((x - y) - (J x - J y)) + (J x - J y) := by module
    let r := (x - y) - (J x - J y)
    let s := J x - J y
    have hsr : 0 ≤ inner ℝ s r := by simpa [r, s, real_inner_comm] using hcross
    calc
      ‖(x - y) - (J x - J y)‖ ^ 2 = inner ℝ r r := by simp [r]
      _ ≤ inner ℝ r r + inner ℝ s r := by linarith
      _ = inner ℝ (r + s) r := by rw [inner_add_left]
      _ = inner ℝ (x - y) ((x - y) - (J x - J y)) := by
        exact congrArg (fun z => inner ℝ z ((x - y) - (J x - J y))) hdecomp.symm
  constructor
  · refine ⟨hmu, ?_⟩
    intro x y
    have hr := hresidual (x : H) (y : H)
    have hinv : 0 ≤ mu⁻¹ := (inv_pos.mpr hmu).le
    have hs := mul_le_mul_of_nonneg_left hr hinv
    have hd : mu⁻¹ • ((x : H) - J x) - mu⁻¹ • ((y : H) - J y) =
        mu⁻¹ • ((x : H) - y - (J x - J y)) := by module
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmu), real_inner_smul_right]
    convert hs using 1 <;> field_simp [hmu.ne'] <;> ring
  · intro x y
    have hr := hresidual (x : H) (y : H)
    have hJmemx : (x : H) ∈ T.identityAddScaled mu (J x) :=
      (mem_resolvent_smul_iff T mu x (J x)).1 (hJ x)
    have hJmemy : (y : H) ∈ T.identityAddScaled mu (J y) :=
      (mem_resolvent_smul_iff T mu y (J y)).1 (hJ y)
    rcases hJmemx with ⟨a, ha, hxa⟩
    rcases hJmemy with ⟨b, hb, hyb⟩
    have hxa' : (x : H) - J x = mu • a := by
      calc (x : H) - J x = (J x + mu • a) - J x :=
        (congrArg (fun z => z - J x) hxa).symm
           _ = mu • a := by module
    have hyb' : (y : H) - J y = mu • b := by
      calc (y : H) - J y = (J y + mu • b) - J y :=
        (congrArg (fun z => z - J y) hyb).symm
           _ = mu • b := by module
    have hr_eq : ((x : H) - y) - (J x - J y) = mu • (a - b) := by
      calc
        ((x : H) - y) - (J x - J y) = ((x : H) - J x) - ((y : H) - J y) := by module
        _ = mu • (a - b) := by rw [hxa', hyb', smul_sub]
    have hcross : 0 ≤ inner ℝ (((x : H) - y) - (J x - J y)) (J x - J y) := by
      rw [hr_eq, real_inner_smul_left]
      exact mul_nonneg hmu.le (hT.1 a ha b hb)
    have hnorm : ‖(x : H) - y‖ ^ 2 =
        ‖((x : H) - y) - (J x - J y)‖ ^ 2 +
          2 * inner ℝ (((x : H) - y) - (J x - J y)) (J x - J y) + ‖J x - J y‖ ^ 2 := by
      let r := ((x : H) - y) - (J x - J y)
      let s := J x - J y
      have hdecomp : (x : H) - y = r + s := by dsimp [r, s]; module
      calc
        ‖(x : H) - y‖ ^ 2 = inner ℝ ((x : H) - y) ((x : H) - y) := by simp
        _ = inner ℝ (r + s) (r + s) := by rw [hdecomp]
        _ = inner ℝ r r + inner ℝ r s + inner ℝ s r + inner ℝ s s := by
          rw [inner_add_left, inner_add_right, inner_add_right]
          ring
        _ = ‖r‖ ^ 2 + 2 * inner ℝ r s + ‖s‖ ^ 2 := by
          rw [show inner ℝ r r = ‖r‖ ^ 2 by simp, show inner ℝ s s = ‖s‖ ^ 2 by simp,
            real_inner_comm s r]
          ring
        _ = _ := by simp [r, s]
    have hsq : ‖((x : H) - y) - (J x - J y)‖ ^ 2 ≤
        ‖(x : H) - y‖ ^ 2 - ‖J x - J y‖ ^ 2 := by
      rw [hnorm]
      nlinarith
    have hF : mu • (mu⁻¹ • ((x : H) - J x)) - mu • (mu⁻¹ • ((y : H) - J y)) =
        ((x : H) - y) - (J x - J y) := by
      simp [smul_sub, smul_smul, mul_inv_cancel₀ hmu.ne']
      module
    have hR : ((x : H) - mu • (mu⁻¹ • ((x : H) - J x))) -
        ((y : H) - mu • (mu⁻¹ • ((y : H) - J y))) = J x - J y := by
      simp [smul_smul, mul_inv_cancel₀ hmu.ne']
    rw [hF, hR]
    exact hsq
/-! ### Canonical Yosida regularization operator
Source item: Attouch_Convergence_of_a_Relaxed_Inertial_Forward_Backward_Algorithm_for
_Structured_Monotone_Inclusions_2019 items/ext_def_5 -/

/-- The Yosida regularization `A_μ x = μ⁻¹ • (x - J_{μA} x)` of a maximal
monotone operator `A`, the canonical resolvent-representative-based
single-valued Yosida operator (`resolventMap` supplies the resolvent point
`J_{μA} x`).  Cocoercivity of this operator is `yosida_is_cocoercive`.

This is the canonical choice-based form: the paper's selection-parameterized
form (an arbitrary resolvent selection `J` with
`∀ x, J x ∈ (mu • A).resolvent x`) is strictly more general (choice-free, no
`CompleteSpace`/`IsMaximalMonotone` hypotheses), and the generality reduction
to the canonical resolvent form is a deliberate user decision (2026-08-17). -/
noncomputable def yosidaRegularization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (mu : ℝ) (hmu : 0 < mu) : H → H :=
  fun x => mu⁻¹ • (x - resolventMap A hA mu hmu x)

/-- The norm of the canonical Yosida regularization is antitone in its positive
parameter. -/
theorem yosidaRegularization_norm_antitone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone) (x : H)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    ‖yosidaRegularization A hA s (lt_of_lt_of_le hr hrs) x‖ ≤
      ‖yosidaRegularization A hA r hr x‖ := by
  let hs : 0 < s := lt_of_lt_of_le hr hrs
  change ‖s⁻¹ • (x - resolventMap A hA s hs x)‖ ≤
    ‖r⁻¹ • (x - resolventMap A hA r hr x)‖
  have hrmem := resolventMap_mem A hA r hr x
  have hsmem := resolventMap_mem A hA s hs x
  rw [mem_resolvent_smul_iff] at hrmem hsmem
  dsimp [identityAddScaled] at hrmem hsmem
  rcases hrmem with ⟨a, ha, hxr⟩
  rcases hsmem with ⟨b, hb, hxs⟩
  have har : r⁻¹ • (x - resolventMap A hA r hr x) = a := by
    calc
      r⁻¹ • (x - resolventMap A hA r hr x) =
          r⁻¹ • ((resolventMap A hA r hr x + r • a) - resolventMap A hA r hr x) := by
            rw [hxr]
      _ = a := by
        rw [show (resolventMap A hA r hr x + r • a) - resolventMap A hA r hr x = r • a by
          abel, smul_smul, inv_mul_cancel₀ hr.ne']
        simp
  have hbs : s⁻¹ • (x - resolventMap A hA s hs x) = b := by
    calc
      s⁻¹ • (x - resolventMap A hA s hs x) =
          s⁻¹ • ((resolventMap A hA s hs x + s • b) - resolventMap A hA s hs x) := by
            rw [hxs]
      _ = b := by
        rw [show (resolventMap A hA s hs x + s • b) - resolventMap A hA s hs x = s • b by
          abel, smul_smul, inv_mul_cancel₀ hs.ne']
        simp
  rw [har, hbs]
  have hj : resolventMap A hA s hs x - resolventMap A hA r hr x = r • a - s • b := by
    calc
      resolventMap A hA s hs x - resolventMap A hA r hr x =
          (resolventMap A hA s hs x + s • b) - s • b -
            ((resolventMap A hA r hr x + r • a) - r • a) := by abel
      _ = r • a - s • b := by rw [hxs, hxr]; abel
  have hm : 0 ≤ inner ℝ (b - a) (resolventMap A hA s hs x - resolventMap A hA r hr x) :=
    hA.1 b hb a ha
  rw [hj, inner_sub_right, real_inner_smul_right] at hm
  have hm' : 0 ≤ r * inner ℝ (b - a) a - s * inner ℝ (b - a) b := by
    simpa [real_inner_smul_right] using hm
  have hcross : inner ℝ b a ≤ ‖b‖ * ‖a‖ := real_inner_le_norm _ _
  have hpoly : 0 ≤ (r + s) * ‖b‖ * ‖a‖ - s * ‖b‖ ^ 2 - r * ‖a‖ ^ 2 := by
    have hba : inner ℝ (b - a) a = inner ℝ b a - ‖a‖ ^ 2 := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have hbb : inner ℝ (b - a) b = ‖b‖ ^ 2 - inner ℝ b a := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm a b]
    rw [hba, hbb] at hm'
    have hsum : 0 ≤ r + s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hcross hsum]
  by_contra hnot
  have hlt : ‖a‖ < ‖b‖ := lt_of_not_ge hnot
  have hfac : (r + s) * ‖b‖ * ‖a‖ - s * ‖b‖ ^ 2 - r * ‖a‖ ^ 2 =
      (‖a‖ - ‖b‖) * (s * ‖b‖ - r * ‖a‖) := by ring
  have hpos : 0 < s * ‖b‖ - r * ‖a‖ := by
    have h1 : r * ‖a‖ < r * ‖b‖ := mul_lt_mul_of_pos_left hlt hr
    have h2 : r * ‖b‖ ≤ s * ‖b‖ := mul_le_mul_of_nonneg_right hrs (norm_nonneg _)
    linarith
  rw [hfac] at hpoly
  have hneg : (‖a‖ - ‖b‖) * (s * ‖b‖ - r * ‖a‖) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hpos
  linarith

/-! ### Yosida regularization properties
Source item: Attouch_Convergence_of_a_Relaxed_Inertial_Forward_Backward_Algorithm_for
_Structured_Monotone_Inclusions_2019 items/rem_6 -/

/-- The Yosida value belongs to the operator at the shifted argument:
`A_μ x ∈ A (x - μ A_μ x)`.  Canonical form of the paper's selection-based
`yosida_selection_mem_original_rem6`: the resolvent selection `J` with
`hJ : ∀ x, J x ∈ (mu • A).resolvent x` is replaced by the canonical
`resolventMap` representative. -/
theorem yosida_selection_mem_original_rem6 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (mu : ℝ) (hmu : 0 < mu) (x : H) :
    yosidaRegularization A hA mu hmu x ∈ A (x - mu • yosidaRegularization A hA mu hmu x) := by
  have hmem := resolventMap_mem A hA mu hmu x
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hmem
  dsimp [SetValuedOperator.identityAddScaled] at hmem
  rcases hmem with ⟨a, ha, hxa⟩
  have hdiff : x - resolventMap A hA mu hmu x = mu • a := by
    calc
      x - resolventMap A hA mu hmu x =
          (resolventMap A hA mu hmu x + mu • a) - resolventMap A hA mu hmu x := by rw [hxa]
      _ = mu • a := by module
  have hyos : yosidaRegularization A hA mu hmu x = a := by
    simp only [yosidaRegularization, hdiff, smul_smul]
    rw [inv_mul_cancel₀ hmu.ne', one_smul]
  have harg : x - mu • a = resolventMap A hA mu hmu x := by
    calc
      x - mu • a = (resolventMap A hA mu hmu x + mu • a) - mu • a := by rw [hxa]
      _ = resolventMap A hA mu hmu x := by module
  rw [hyos, harg]
  exact ha

/-- Remark 6.3 on parameter interpretation and Yosida regularization, in
canonical form: the Yosida regularization `A_μ` of a maximal monotone operator
is `mu`-cocoercive, `1 / mu`-Lipschitz, belongs to `A (x - mu • A_μ x)`, has
zeros exactly the zeros of `A`, and satisfies the theta-convolution resolvent
identity. -/
theorem yosidaRegularization_properties {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone) (mu : ℝ) (hmu : 0 < mu) :
    (∀ x y : H, inner ℝ (yosidaRegularization A hA mu hmu y - yosidaRegularization A hA mu hmu x)
        (y - x) ≥
          mu * ‖yosidaRegularization A hA mu hmu y - yosidaRegularization A hA mu hmu x‖ ^ 2) ∧
    (∀ x y : H, ‖yosidaRegularization A hA mu hmu y - yosidaRegularization A hA mu hmu x‖ ≤
        (1 / mu) * ‖y - x‖) ∧
    (∀ x : H, yosidaRegularization A hA mu hmu x ∈
        A (x - mu • yosidaRegularization A hA mu hmu x)) ∧
    (∀ x : H, yosidaRegularization A hA mu hmu x = 0 ↔ 0 ∈ A x) ∧
    (∀ theta : ℝ, 0 < theta → ∃ Jtheta JthetaMu : H → H,
      (∀ x : H, Jtheta x ∈ (theta • SetValuedOperator.ofFunction Set.univ
        (fun u : Set.univ => yosidaRegularization A hA mu hmu (u : H))).resolvent x) ∧
      (∀ x : H, JthetaMu x ∈ ((theta + mu) • A).resolvent x) ∧
      ∀ x : H, Jtheta x = (mu / (theta + mu)) • x + (theta / (theta + mu)) • JthetaMu x) := by
  have hcoco : ∀ x y : H,
      mu * ‖yosidaRegularization A hA mu hmu y - yosidaRegularization A hA mu hmu x‖ ^ 2 ≤
        inner ℝ (yosidaRegularization A hA mu hmu y - yosidaRegularization A hA mu hmu x)
          (y - x) := by
    have hC : CocoerciveOn mu Set.univ
        (fun x : Set.univ => yosidaRegularization A hA mu hmu (x : H)) := by
      simpa [yosidaRegularization] using (yosida_is_cocoercive A hA mu hmu).1
    exact (CocoerciveOn.pointwise_iff (fun z : H => yosidaRegularization A hA mu hmu z)
      mu hmu).mp hC
  refine ⟨?_, ?_, yosida_selection_mem_original_rem6 A hA mu hmu, ?_, ?_⟩
  · intro x y
    exact hcoco x y
  · intro x y
    let d : H := yosidaRegularization A hA mu hmu y - yosidaRegularization A hA mu hmu x
    let e : H := y - x
    have hbound : mu * ‖d‖ ^ 2 ≤ ‖d‖ * ‖e‖ := by
      calc
        mu * ‖d‖ ^ 2 ≤ inner ℝ d e := hcoco x y
        _ ≤ ‖d‖ * ‖e‖ := real_inner_le_norm _ _
    by_cases hd : ‖d‖ = 0
    · rw [show yosidaRegularization A hA mu hmu y - yosidaRegularization A hA mu hmu x = d by rfl,
        hd]
      exact mul_nonneg (one_div_nonneg.mpr hmu.le) (norm_nonneg _)
    · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd)
      have hmul : mu * ‖d‖ ≤ ‖e‖ := by nlinarith
      have hdiv : ‖d‖ ≤ ‖e‖ / mu := (le_div_iff₀ hmu).mpr (by simpa [mul_comm] using hmul)
      simpa [d, e, one_div, div_eq_mul_inv, mul_comm] using hdiv
  · intro x
    constructor
    · intro h
      simpa [h] using yosida_selection_mem_original_rem6 A hA mu hmu x
    · intro h
      have hx : x ∈ J[(mu • A)] x := by
        rw [SetValuedOperator.mem_resolvent_smul_iff]
        dsimp [SetValuedOperator.identityAddScaled]
        exact ⟨(0 : H), h, by simp⟩
      have hJeq : resolventMap A hA mu hmu x = x :=
        resolvent_unique_of_monotone hA.1 hmu (resolventMap_mem A hA mu hmu x) hx
      simp [yosidaRegularization, hJeq]
  · intro theta htheta
    let s : ℝ := theta + mu
    have hs : 0 < s := by dsimp [s]; linarith
    let JthetaMu : H → H := maximal_monotone_resolvent_choice A hA s
    have hJthetaMu : ∀ x : H, JthetaMu x ∈ ((theta + mu) • A).resolvent x := by
      intro x
      simpa [JthetaMu, s] using (maximal_monotone_resolvent_choice_mem A hA s hs x)
    let Jtheta : H → H := fun z =>
      (mu / (theta + mu)) • z + (theta / (theta + mu)) • JthetaMu z
    refine ⟨Jtheta, JthetaMu, ?_, hJthetaMu, ?_⟩
    · intro x
      have hq := hJthetaMu x
      rw [SetValuedOperator.mem_resolvent_smul_iff] at hq
      dsimp [SetValuedOperator.identityAddScaled] at hq
      rcases hq with ⟨a, ha, hqx⟩
      have hcoef : mu / (theta + mu) + theta / (theta + mu) = 1 := by
        calc
          mu / (theta + mu) + theta / (theta + mu) = (mu + theta) / (theta + mu) := by ring
          _ = 1 := by rw [add_comm mu theta, div_self hs.ne']
      have hprod : (mu / (theta + mu)) * (theta + mu) = mu := by
        field_simp [hs.ne']
      have hJtheta_eq : Jtheta x = JthetaMu x + mu • a := by
        dsimp [Jtheta]
        nth_rw 1 [← hqx]
        simp only [smul_add, smul_smul]
        calc
          (mu / (theta + mu)) • JthetaMu x +
              ((mu / (theta + mu)) * (theta + mu)) • a +
              (theta / (theta + mu)) • JthetaMu x =
              (mu / (theta + mu) + theta / (theta + mu)) • JthetaMu x +
                ((mu / (theta + mu)) * (theta + mu)) • a := by module
          _ = JthetaMu x + mu • a := by rw [hcoef, hprod, one_smul]
      have hq_mu : JthetaMu x ∈ (mu • A).resolvent (Jtheta x) := by
        rw [SetValuedOperator.mem_resolvent_smul_iff]
        dsimp [SetValuedOperator.identityAddScaled]
        exact ⟨a, ha, hJtheta_eq.symm⟩
      have hJ_eq : resolventMap A hA mu hmu (Jtheta x) = JthetaMu x :=
        (resolvent_unique_of_monotone hA.1 hmu (resolventMap_mem A hA mu hmu (Jtheta x)) hq_mu)
      have hdiff_yos : Jtheta x - resolventMap A hA mu hmu (Jtheta x) = mu • a := by
        rw [hJ_eq, hJtheta_eq]
        module
      have hY_eq : yosidaRegularization A hA mu hmu (Jtheta x) = a := by
        simp only [yosidaRegularization, hdiff_yos, smul_smul]
        rw [inv_mul_cancel₀ hmu.ne', one_smul]
      have hfinal : Jtheta x + theta • yosidaRegularization A hA mu hmu (Jtheta x) = x := by
        calc
          Jtheta x + theta • yosidaRegularization A hA mu hmu (Jtheta x) =
              Jtheta x + theta • a := by rw [hY_eq]
          _ = JthetaMu x + mu • a + theta • a := by rw [hJtheta_eq]
          _ = JthetaMu x + (theta + mu) • a := by module
          _ = x := hqx
      rw [SetValuedOperator.mem_resolvent_smul_iff]
      dsimp [SetValuedOperator.identityAddScaled]
      refine ⟨yosidaRegularization A hA mu hmu (Jtheta x), ?_, hfinal⟩
      simp [SetValuedOperator.ofFunction_apply_of_mem]
    · intro x
      rfl


private theorem resolventDistance_sup_pos_mul {S : Set ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hne : S.Nonempty) (hS : BddAbove S) :
    lam * sSup S = sSup ((fun q : ℝ => lam * q) '' S) := by
  have hIne : ((fun q : ℝ => lam * q) '' S).Nonempty := hne.image _
  have hIbdd : BddAbove ((fun q : ℝ => lam * q) '' S) := by
    rcases hS with ⟨b, hb⟩
    refine ⟨lam * b, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact mul_le_mul_of_nonneg_left (hb hq) hlam.le
  apply le_antisymm
  · have hdiv : sSup S ≤ sSup ((fun q : ℝ => lam * q) '' S) / lam := by
      apply csSup_le hne
      intro q hq
      apply (le_div_iff₀ hlam).mpr
      simpa [mul_comm] using le_csSup hIbdd ⟨q, hq, rfl⟩
    calc
      lam * sSup S ≤ lam * (sSup ((fun q : ℝ => lam * q) '' S) / lam) :=
        mul_le_mul_of_nonneg_left hdiv hlam.le
      _ = sSup ((fun q : ℝ => lam * q) '' S) := by field_simp
  · apply csSup_le hIne
    rintro _ ⟨q, hq, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup hS hq) hlam.le

end SetValuedOperator
