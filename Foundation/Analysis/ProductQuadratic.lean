import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Analysis.Semicontinuity
import Foundation.Separation.Hyperplanes

/-!
# Product-space quadratic estimates

Auxiliary product-space quadratic functions and separation lemmas used by
Fitzpatrick-function arguments.
-/

open scoped InnerProductSpace

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def productQuadratic (p : H × H) : EReal :=
  (((1 / 2 : ℝ) * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) : ℝ) : EReal)

noncomputable def productQuadraticReal (p : H × H) : ℝ :=
  (1 / 2 : ℝ) * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem productQuadraticReal_coe (p : H × H) :
    ((productQuadraticReal (H := H) p : ℝ) : EReal) = productQuadratic (H := H) p := by
  rfl

def productInner (p w : H × H) : ℝ :=
  inner ℝ p.1 w.1 + inner ℝ p.2 w.2

omit [CompleteSpace H] in
theorem norm_sq_combo_le (x y : H) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
  have hsq : 0 ≤ a * b * ‖x - y‖ ^ 2 := by positivity
  have hident :
      ‖a • x + b • y‖ ^ 2 =
        a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← real_inner_self_eq_norm_sq x, ← real_inner_self_eq_norm_sq y,
      ← real_inner_self_eq_norm_sq (x - y)]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_sub_left, inner_sub_right]
    simp only [Real.ringHom_apply, inner_self_eq_norm_sq_to_K]
    rw [real_inner_comm y x]
    ring_nf
    have ha2 : a ^ 2 = a - a * b := by nlinarith [hab]
    have hb2 : b ^ 2 = b - a * b := by nlinarith [hab]
    rw [ha2, hb2]
    ring
  rw [hident]
  nlinarith

omit [CompleteSpace H] in
theorem productQuadraticReal_convex (p q : H × H) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    productQuadraticReal (H := H) (a • p + b • q) ≤
      a * productQuadraticReal (H := H) p + b * productQuadraticReal (H := H) q := by
  have h1 := norm_sq_combo_le (H := H) p.1 q.1 a b ha hb hab
  have h2 := norm_sq_combo_le (H := H) p.2 q.2 a b ha hb hab
  dsimp [productQuadraticReal]
  nlinarith

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem support_epigraph_nonempty {f : H × H → EReal}
    (hproper : ERealFunction.IsProper f) :
    ({s : (H × H) × ℝ | f s.1 ≤ (s.2 : EReal)}).Nonempty := by
  rcases hproper.2 with ⟨p, hpdom⟩
  have hpbot : f p ≠ ⊥ := hproper.1 p
  have hpeff : p ∈ ERealFunction.effectiveDom f := by
    rw [ERealFunction.effectiveDom_eq_dom_inter_neBot]
    exact ⟨hpdom, hpbot⟩
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real f p).1 hpeff with ⟨r, hr⟩
  refine ⟨(p, r), ?_⟩
  simp [hr]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem support_epigraph_closed {f : H × H → EReal}
    (hlsc : LowerSemicontinuous f) :
    IsClosed ({s : (H × H) × ℝ | f s.1 ≤ (s.2 : EReal)}) := by
  exact (ERealFunction.lowerSemicontinuous_iff_isClosed_epigraph f).1 hlsc

omit [CompleteSpace H] in
theorem support_epigraph_convex {f : H × H → EReal}
    (hconv : ∀ p q : H × H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • p + b • q) ≤ (a : EReal) * f p + (b : EReal) * f q) :
    Convex ℝ ({s : (H × H) × ℝ | f s.1 ≤ (s.2 : EReal)}) := by
  intro x hx y hy a b ha hb hab
  change f ((a • x + b • y).1) ≤ (((a • x + b • y).2 : ℝ) : EReal)
  have hf := hconv x.1 y.1 a b ha hb hab
  have hx' : f x.1 ≤ (x.2 : EReal) := hx
  have hy' : f y.1 ≤ (y.2 : EReal) := hy
  calc
    f ((a • x + b • y).1) = f (a • x.1 + b • y.1) := rfl
    _ ≤ (a : EReal) * f x.1 + (b : EReal) * f y.1 := hf
    _ ≤ (a : EReal) * (x.2 : EReal) + (b : EReal) * (y.2 : EReal) := by
      gcongr
    _ = (((a * x.2 + b * y.2 : ℝ) : EReal)) := by
      rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    _ = (((a • x + b • y).2 : ℝ) : EReal) := rfl

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem continuous_productQuadraticReal :
    Continuous (productQuadraticReal (H := H)) := by
  unfold productQuadraticReal
  exact continuous_const.mul (((continuous_fst.norm.pow 2).add (continuous_snd.norm.pow 2)))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem strictHypographNegProductQuadratic_open :
    IsOpen ({s : (H × H) × ℝ | s.2 < -productQuadraticReal (H := H) s.1}) := by
  have hcont : Continuous (fun s : (H × H) × ℝ =>
      s.2 + productQuadraticReal (H := H) s.1) :=
    continuous_snd.add (continuous_productQuadraticReal.comp continuous_fst)
  have hpre : ({s : (H × H) × ℝ | s.2 < -productQuadraticReal (H := H) s.1}) =
      (fun s : (H × H) × ℝ => s.2 + productQuadraticReal (H := H) s.1) ⁻¹'
        Set.Iio 0 := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
    constructor <;> intro hs <;> linarith
  rw [hpre]
  exact isOpen_Iio.preimage hcont

omit [CompleteSpace H] in
theorem strictHypographNegProductQuadratic_convex :
    Convex ℝ ({s : (H × H) × ℝ | s.2 < -productQuadraticReal (H := H) s.1}) := by
  intro x hx y hy a b ha hb hab
  change (a • x + b • y).2 <
    -productQuadraticReal (H := H) ((a • x + b • y).1)
  have hq := productQuadraticReal_convex (H := H) x.1 y.1 a b ha hb hab
  have hstrict :
      a * x.2 + b * y.2 <
        -(a * productQuadraticReal (H := H) x.1 +
          b * productQuadraticReal (H := H) y.1) := by
    have hpos : 0 < a ∨ 0 < b := by
      by_contra h
      push Not at h
      have ha0 : a = 0 := le_antisymm h.1 ha
      have hb0 : b = 0 := le_antisymm h.2 hb
      nlinarith
    cases hpos with
    | inl ha_pos =>
        have hxmul : a * x.2 < a * (-productQuadraticReal (H := H) x.1) :=
          mul_lt_mul_of_pos_left hx ha_pos
        have hymul : b * y.2 ≤ b * (-productQuadraticReal (H := H) y.1) :=
          mul_le_mul_of_nonneg_left hy.le hb
        nlinarith
    | inr hb_pos =>
        have hxmul : a * x.2 ≤ a * (-productQuadraticReal (H := H) x.1) :=
          mul_le_mul_of_nonneg_left hx.le ha
        have hymul : b * y.2 < b * (-productQuadraticReal (H := H) y.1) :=
          mul_lt_mul_of_pos_left hy hb_pos
        nlinarith
  calc
    (a • x + b • y).2 = a * x.2 + b * y.2 := rfl
    _ < -(a * productQuadraticReal (H := H) x.1 +
          b * productQuadraticReal (H := H) y.1) := hstrict
    _ ≤ -productQuadraticReal (H := H) ((a • x + b • y).1) := by
      dsimp
      nlinarith [hq]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem epigraph_disjoint_strictHypographNegProductQuadratic {f : H × H → EReal}
    (hnonneg : ∀ p : H × H, (0 : EReal) ≤ f p + productQuadratic (H := H) p) :
    Disjoint
      ({s : (H × H) × ℝ | s.2 < -productQuadraticReal (H := H) s.1})
      ({s : (H × H) × ℝ | f s.1 ≤ (s.2 : EReal)}) := by
  rw [Set.disjoint_left]
  intro s hsD hsC
  have hsD' : (s.2 : EReal) < (-(productQuadraticReal (H := H) s.1) : ℝ) := by
    exact_mod_cast hsD
  have hlt_add : (s.2 : EReal) + productQuadratic (H := H) s.1 < 0 := by
    rw [← productQuadraticReal_coe (H := H) s.1]
    let q := productQuadraticReal (H := H) s.1
    have h := EReal.add_lt_add_right_coe hsD' q
    have hrhs : -((q : ℝ) : EReal) + (q : EReal) = 0 := by
      rw [← EReal.coe_neg, ← EReal.coe_add]
      simp
    simpa [q, hrhs] using h
  have hle_add : f s.1 + productQuadratic (H := H) s.1 ≤
      (s.2 : EReal) + productQuadratic (H := H) s.1 := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hsC (productQuadratic (H := H) s.1)
  have hlt : f s.1 + productQuadratic (H := H) s.1 < 0 :=
    lt_of_le_of_lt hle_add hlt_add
  exact not_le_of_gt hlt (hnonneg s.1)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem productQuadratic_nonneg (p : H × H) :
    (0 : EReal) ≤ productQuadratic (H := H) p := by
  exact EReal.coe_nonneg.mpr (by positivity)

omit [CompleteSpace H] in
theorem productQuadratic_add (p w : H × H) :
    productQuadratic (H := H) (p + w) =
      productQuadratic (H := H) p +
        (((productInner (H := H) p w : ℝ) : EReal) + productQuadratic (H := H) w) := by
  have hreal :
      (1 / 2 : ℝ) * (‖p.1 + w.1‖ ^ 2 + ‖p.2 + w.2‖ ^ 2) =
        (1 / 2 : ℝ) * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) +
          ((inner ℝ p.1 w.1 + inner ℝ p.2 w.2) +
            (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2)) := by
    have h1 :
        ‖p.1 + w.1‖ ^ 2 = ‖p.1‖ ^ 2 + 2 * inner ℝ p.1 w.1 + ‖w.1‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm w.1 p.1]
      ring
    have h2 :
        ‖p.2 + w.2‖ ^ 2 = ‖p.2‖ ^ 2 + 2 * inner ℝ p.2 w.2 + ‖w.2‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm w.2 p.2]
      ring
    rw [h1, h2]
    ring
  calc
    productQuadratic (H := H) (p + w) =
        (((1 / 2 : ℝ) * (‖p.1 + w.1‖ ^ 2 + ‖p.2 + w.2‖ ^ 2) : ℝ) : EReal) := rfl
    _ = (((1 / 2 : ℝ) * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) +
          ((inner ℝ p.1 w.1 + inner ℝ p.2 w.2) +
            (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2)) : ℝ) : EReal) := by
        rw [hreal]
    _ = productQuadratic (H := H) p +
        (((productInner (H := H) p w : ℝ) : EReal) + productQuadratic (H := H) w) := by
        dsimp [productQuadratic, productInner]

theorem corollary15_16_support_productQuadratic
    {f : H × H → EReal}
    (hproper : ERealFunction.IsProper f)
    (hconv : ∀ p q : H × H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • p + b • q) ≤ (a : EReal) * f p + (b : EReal) * f q)
    (hlsc : LowerSemicontinuous f)
    (hnonneg : ∀ p : H × H, (0 : EReal) ≤ f p + productQuadratic (H := H) p) :
    ∃ w : H × H, ∀ p : H × H,
      (((productInner (H := H) p w +
          (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) : ℝ) : EReal) ≤ f p) := by
  classical
  let C : Set ((H × H) × ℝ) := {s | f s.1 ≤ (s.2 : EReal)}
  let D : Set ((H × H) × ℝ) := {s | s.2 < -productQuadraticReal (H := H) s.1}
  have hC_nonempty : C.Nonempty := support_epigraph_nonempty (H := H) hproper
  have hC_closed : IsClosed C := support_epigraph_closed (H := H) hlsc
  have hC_convex : Convex ℝ C := support_epigraph_convex (H := H) hconv
  have hD_open : IsOpen D := strictHypographNegProductQuadratic_open (H := H)
  have hD_convex : Convex ℝ D := strictHypographNegProductQuadratic_convex (H := H)
  have hDC_disjoint : Disjoint D C :=
    epigraph_disjoint_strictHypographNegProductQuadratic (H := H) hnonneg
  obtain ⟨ell, beta, hD_sep, hC_sep⟩ :=
    geometric_hahn_banach_open hD_convex hD_open hC_convex hDC_disjoint
  -- At this point the plan requires normalizing the separator.  The separator is a
  -- `StrongDual ℝ ((H × H) × ℝ)`, but `H × H` is not an `InnerProductSpace` in this
  -- project, so the product-space Riesz step from the plan must be replaced by a
  -- coordinatewise decomposition of `ell`.
  let embed₁ : H →L[ℝ] ((H × H) × ℝ) :=
    (ContinuousLinearMap.inl ℝ (H × H) ℝ).comp (ContinuousLinearMap.inl ℝ H H)
  let embed₂ : H →L[ℝ] ((H × H) × ℝ) :=
    (ContinuousLinearMap.inl ℝ (H × H) ℝ).comp (ContinuousLinearMap.inr ℝ H H)
  let phi₁ : StrongDual ℝ H := ell.comp embed₁
  let phi₂ : StrongDual ℝ H := ell.comp embed₂
  let c₁ : H := (InnerProductSpace.toDual ℝ H).symm phi₁
  let c₂ : H := (InnerProductSpace.toDual ℝ H).symm phi₂
  let c : H × H := (c₁, c₂)
  let alpha : ℝ := ell ((0 : H × H), (1 : ℝ))
  have hell_decomp : ∀ p : H × H, ∀ r : ℝ,
      ell (p, r) = productInner (H := H) p c + alpha * r := by
    intro p r
    let a : (H × H) × ℝ := ((p.1, 0), 0)
    let b : (H × H) × ℝ := ((0, p.2), 0)
    let v : (H × H) × ℝ := ((0, 0), 1)
    have hsplit : (p, r) = a + b + r • v := by
      ext <;> simp [a, b, v]
    have h1 : ell a = inner ℝ c₁ p.1 := by
      have h :=
        InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H) (x := p.1) (y := phi₁)
      have hphi : phi₁ p.1 = ell a := by
        simp [phi₁, embed₁, a]
      rw [hphi] at h
      simpa [c₁] using h.symm
    have h2 : ell b = inner ℝ c₂ p.2 := by
      have h :=
        InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H) (x := p.2) (y := phi₂)
      have hphi : phi₂ p.2 = ell b := by
        simp [phi₂, embed₂, b]
      rw [hphi] at h
      simpa [c₂] using h.symm
    have h3 : ell (r • v) = r * alpha := by
      simpa [v, alpha] using (ell.map_smul r v)
    calc
      ell (p, r) = ell (a + b + r • v) := by rw [hsplit]
      _ = ell a + ell b + ell (r • v) := by simp [map_add]
      _ = inner ℝ c₁ p.1 + inner ℝ c₂ p.2 + r * alpha := by rw [h1, h2, h3]
      _ = productInner (H := H) p c + alpha * r := by
        dsimp [productInner, c]
        rw [real_inner_comm c₁ p.1, real_inner_comm c₂ p.2]
        ring
  obtain ⟨p₀, hp₀dom⟩ := hproper.2
  have hp₀neBot : f p₀ ≠ ⊥ := hproper.1 p₀
  have hp₀eff : p₀ ∈ ERealFunction.effectiveDom f := by
    rw [ERealFunction.effectiveDom_eq_dom_inter_neBot]
    exact ⟨hp₀dom, hp₀neBot⟩
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real f p₀).1 hp₀eff with ⟨r₀, hr₀⟩
  have halpha_nonneg : 0 ≤ alpha := by
    by_contra hnot
    have hαneg : alpha < 0 := lt_of_not_ge hnot
    let A : ℝ := productInner (H := H) p₀ c -
      alpha * productQuadraticReal (H := H) p₀
    let M : ℝ := max 0 (beta - A) + 1
    let t : ℝ := M / (-alpha)
    have hMpos : 0 < M := by
      have hmax0 : (0 : ℝ) ≤ max 0 (beta - A) := le_max_left _ _
      dsimp [M]
      linarith
    have htpos : 0 < t := by
      have hden : 0 < -alpha := by linarith
      exact div_pos hMpos hden
    have hd : (p₀, -productQuadraticReal (H := H) p₀ - t) ∈ D := by
      change -productQuadraticReal (H := H) p₀ - t <
        -productQuadraticReal (H := H) p₀
      linarith
    have hsep := hD_sep (p₀, -productQuadraticReal (H := H) p₀ - t) hd
    have hdec := hell_decomp p₀ (-productQuadraticReal (H := H) p₀ - t)
    have hsep' :
        productInner (H := H) p₀ c +
            alpha * (-productQuadraticReal (H := H) p₀ - t) < beta := by
      simpa [hdec] using hsep
    have htcalc : -alpha * t = M := by
      dsimp [t]
      field_simp [hαneg.ne]
    have hmax : beta - A ≤ max 0 (beta - A) := le_max_right _ _
    dsimp [A, M] at htcalc hmax hsep'
    nlinarith
  have halpha_ne_zero : alpha ≠ 0 := by
    intro hzero
    have hCmem : (p₀, r₀) ∈ C := by
      change f p₀ ≤ (r₀ : EReal)
      rw [hr₀]
    have hCineq := hC_sep (p₀, r₀) hCmem
    have hCineq' : beta ≤ productInner (H := H) p₀ c := by
      have hdec := hell_decomp p₀ r₀
      simpa [hdec, hzero] using hCineq
    have hDmem : (p₀, -productQuadraticReal (H := H) p₀ - 1) ∈ D := by
      change -productQuadraticReal (H := H) p₀ - 1 <
        -productQuadraticReal (H := H) p₀
      linarith
    have hDineq := hD_sep (p₀, -productQuadraticReal (H := H) p₀ - 1) hDmem
    have hDineq' : productInner (H := H) p₀ c < beta := by
      have hdec := hell_decomp p₀ (-productQuadraticReal (H := H) p₀ - 1)
      simpa [hdec, hzero] using hDineq
    linarith
  have halpha_pos : 0 < alpha := lt_of_le_of_ne halpha_nonneg (Ne.symm halpha_ne_zero)
  have hD_limit : ∀ p : H × H,
      productInner (H := H) p c - alpha * productQuadraticReal (H := H) p ≤ beta := by
    intro p
    by_contra hnot
    have hlt : beta < productInner (H := H) p c -
        alpha * productQuadraticReal (H := H) p := lt_of_not_ge hnot
    let t : ℝ :=
      (productInner (H := H) p c - alpha * productQuadraticReal (H := H) p - beta) /
        (2 * alpha)
    have htpos : 0 < t := by
      have hnum : 0 <
          productInner (H := H) p c - alpha * productQuadraticReal (H := H) p - beta := by
        linarith
      have hden : 0 < 2 * alpha := by positivity
      dsimp [t]
      exact div_pos hnum hden
    have hd : (p, -productQuadraticReal (H := H) p - t) ∈ D := by
      change -productQuadraticReal (H := H) p - t <
        -productQuadraticReal (H := H) p
      linarith
    have hsep := hD_sep (p, -productQuadraticReal (H := H) p - t) hd
    have hsep' :
        productInner (H := H) p c +
            alpha * (-productQuadraticReal (H := H) p - t) < beta := by
      have hdec := hell_decomp p (-productQuadraticReal (H := H) p - t)
      simpa [hdec] using hsep
    dsimp [t] at hsep'
    field_simp [halpha_pos.ne'] at hsep'
    nlinarith [halpha_pos, hlt]
  have hquad_at_c :
      productInner (H := H) ((1 / alpha) • c) c -
          alpha * productQuadraticReal (H := H) ((1 / alpha) • c)
        = alpha * productQuadraticReal (H := H) ((1 / alpha) • c) := by
    dsimp [productInner, productQuadraticReal]
    rw [inner_smul_left, inner_smul_left]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have hαne : alpha ≠ 0 := halpha_pos.ne'
    have habsα : |alpha| = alpha := abs_of_pos halpha_pos
    simp [norm_smul, habsα]
    field_simp [hαne]
    ring_nf
  have hbeta_ge_quad :
      alpha * productQuadraticReal (H := H) ((1 / alpha) • c) ≤ beta := by
    have hlim := hD_limit ((1 / alpha) • c)
    rw [hquad_at_c] at hlim
    exact hlim
  have hfinite_bound : ∀ p : H × H, ∀ r : ℝ, f p = (r : EReal) →
      productQuadraticReal (H := H) ((1 / alpha) • c) -
          (1 / alpha) * productInner (H := H) p c ≤ r := by
    intro p r hr
    have hCmem : (p, r) ∈ C := by
      change f p ≤ (r : EReal)
      rw [hr]
    have hCineq := hC_sep (p, r) hCmem
    have hCineq' : beta ≤ productInner (H := H) p c + alpha * r := by
      have hdec := hell_decomp p r
      simpa [hdec] using hCineq
    have hαne : alpha ≠ 0 := halpha_pos.ne'
    have hchain :
        alpha * productQuadraticReal (H := H) ((1 / alpha) • c) ≤
          productInner (H := H) p c + alpha * r :=
      le_trans hbeta_ge_quad hCineq'
    have hmul :
        alpha *
            (productQuadraticReal (H := H) ((1 / alpha) • c) -
              (1 / alpha) * productInner (H := H) p c) ≤ alpha * r := by
      have hrewrite :
          alpha *
              (productQuadraticReal (H := H) ((1 / alpha) • c) -
                (1 / alpha) * productInner (H := H) p c) =
            alpha * productQuadraticReal (H := H) ((1 / alpha) • c) -
              productInner (H := H) p c := by
        field_simp [hαne]
      rw [hrewrite]
      nlinarith
    exact le_of_mul_le_mul_left hmul halpha_pos
  let w : H × H := -((1 / alpha) • c)
  have hquad_w :
      productQuadraticReal (H := H) w =
        productQuadraticReal (H := H) ((1 / alpha) • c) := by
    dsimp [w, productQuadraticReal]
    simp [norm_neg]
  have hinner_w : ∀ p : H × H,
      productInner (H := H) p w =
        -((1 / alpha) * productInner (H := H) p c) := by
    intro p
    dsimp [w, productInner]
    simp [inner_neg_right, inner_smul_right]
    ring
  refine ⟨w, ?_⟩
  intro p
  by_cases hptop : f p = ⊤
  · simp [hptop]
  · have hpneBot : f p ≠ ⊥ := hproper.1 p
    have hpeff : p ∈ ERealFunction.effectiveDom f := by
      rw [ERealFunction.effectiveDom_eq_dom_inter_neBot]
      exact ⟨lt_top_iff_ne_top.mpr hptop, hpneBot⟩
    rcases (ERealFunction.mem_effectiveDom_iff_exists_real f p).1 hpeff with ⟨r, hr⟩
    have hbound := hfinite_bound p r hr
    have hreal :
        productInner (H := H) p w +
            (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) ≤ r := by
      have hq :
          (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) =
            productQuadraticReal (H := H) w := by
        rfl
      rw [hq, hquad_w, hinner_w p]
      linarith
    calc
      (((productInner (H := H) p w +
          (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) : ℝ) : EReal)
          ≤ (r : EReal)) := EReal.coe_le_coe hreal
      _ = f p := hr.symm

omit [CompleteSpace H] in
theorem corollary15_17_productQuadratic
    {f : H × H → EReal}
    (hsupport :
      ∃ w : H × H, ∀ p : H × H,
        (((productInner (H := H) p w +
            (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) : ℝ) : EReal) ≤ f p)) :
    ∃ a b : H, ∀ x u : H,
      f (x, u) + productQuadratic (H := H) (x, u) ≥
        productQuadratic (H := H) (x + a, u + b) := by
  rcases hsupport with ⟨w, hw⟩
  refine ⟨w.1, w.2, ?_⟩
  intro x u
  let p : H × H := (x, u)
  have hsupport_p := hw p
  have hsum :
      (((productInner (H := H) p w : ℝ) : EReal) + productQuadratic (H := H) w) =
        (((productInner (H := H) p w +
            (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) : ℝ) : EReal)) := by
    dsimp [productQuadratic]
  calc
    productQuadratic (H := H) (x + w.1, u + w.2)
        = productQuadratic (H := H) (p + w) := rfl
    _ = productQuadratic (H := H) p +
          (((productInner (H := H) p w : ℝ) : EReal) + productQuadratic (H := H) w) :=
        productQuadratic_add (H := H) p w
    _ = productQuadratic (H := H) p +
          (((productInner (H := H) p w +
            (1 / 2 : ℝ) * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) : ℝ) : EReal)) := by
        rw [hsum]
    _ ≤ productQuadratic (H := H) p + f p := by
        exact add_le_add_right hsupport_p (productQuadratic (H := H) p)
    _ = f (x, u) + productQuadratic (H := H) (x, u) := by
        dsimp [p]
        rw [add_comm]
