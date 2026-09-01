import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Convex.Gamma0
import Foundation.Convex.InfimalConvolution

/-!
# The Moreau envelope

The quadratic kernel `x ↦ (1 / (2γ)) ‖x‖²`, the Moreau envelope
`{}^[γ] f := f □ (1 / (2γ)) ‖·‖²`, and the scaling/iteration identities
relating envelopes at different parameters.
-/

universe u

namespace ERealFunction

variable {H : Type u}

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap02/Corollary_2_15 -/

/-- Corollary 2.15: in a real inner product space, the squared norm of an affine combination plus
the weighted squared distance equals the corresponding affine combination of squared norms. -/
theorem norm_sq_affine_combination_add_weighted_norm_sub_sq
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (α : ℝ) :
    ‖α • x + (1 - α) • y‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 =
      α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs]
  simp [real_inner_smul_left, real_inner_smul_right]
  nlinarith [sq_abs α, sq_abs (1 - α)]

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Definition_12_20_Core -/

variable [NormedAddCommGroup H]

/-- The quadratic kernel `x ↦ (1 / (2γ)) ‖x‖^2` used in the definition
of the Moreau envelope. -/
noncomputable def moreauQuadraticKernel (γ : Set.Ioi (0 : ℝ)) : H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ (1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2).toEReal

/-- Coercing the Moreau quadratic kernel to `EReal` recovers the function
`x ↦ (1 / (2γ)) ‖x‖^2`. -/
@[simp]
theorem moreauQuadraticKernel_apply (γ : Set.Ioi (0 : ℝ)) (x : H) :
    (moreauQuadraticKernel γ x : EReal) =
      (((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal) := by
  simp [moreauQuadraticKernel]

/-- The quadratic function `x ↦ ‖x‖² / 2`, viewed as a positive
extended-real-valued function. -/
noncomputable abbrev halfSquaredNorm : H → Set.Ioi (⊥ : EReal) :=
  moreauQuadraticKernel ⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩

/-- Definition 12 20 Core: coercing `halfSquaredNorm` to `EReal` recovers the quadratic function
`x ↦ ‖x‖² / 2`. -/
@[simp] theorem halfSquaredNorm_apply (x : H) :
    (halfSquaredNorm x : EReal) = ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) := by
  change (((1 / (2 * (1 : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal) =
    ((((‖x‖ ^ 2) / 2 : ℝ) : EReal))
  congr 1
  ring

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Definition_12_20 -/

/-- The Moreau envelope of a function with parameter `γ`, written `{}^[γ] f`, is the infimal
convolution of `f` with the quadratic kernel. -/
noncomputable abbrev moreauEnvelope {α : Type*} [CoeTC α EReal] (f : H → α)
    (γ : Set.Ioi (0 : ℝ)) : H → EReal :=
  f □ moreauQuadraticKernel γ

notation:max "{}^[" γ:max "]" f:max => ERealFunction.moreauEnvelope f γ

/-- The value of the Moreau envelope at `x` is the infimum of `f y + (1 / (2γ)) ‖x - y‖²`. -/
theorem moreauEnvelope_apply {α : Type*} [CoeTC α EReal] (f : H → α)
    (γ : Set.Ioi (0 : ℝ)) (x : H) :
    ({}^[γ] f) x = ⨅ y : H, (f y : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
  rw [moreauEnvelope]
  simp [infimalConvolution_apply, moreauQuadraticKernel_apply]

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Proposition_12_22 -/

section

/-- Helper for Proposition 12 22: multiplying an indexed `EReal` infimum by a positive real can be
transported through the infimum. -/
private theorem coe_real_mul_iInf_ereal_of_pos
    {ι : Sort*} {a : ℝ} (ha : 0 < a) (φ : ι → EReal) :
    (a : EReal) * (⨅ i, φ i) = ⨅ i, (a : EReal) * φ i := by
  let F : EReal → EReal := fun t ↦ (a : EReal) * t
  have hcont_mul :
      ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) ((a : EReal), ⨅ i, φ i) := by
    refine EReal.continuousAt_mul ?_ ?_ ?_ ?_
    · left
      norm_num [ha.ne']
    · left
      norm_num [ha.ne']
    · left
      exact EReal.coe_ne_bot a
    · left
      exact EReal.coe_ne_top a
  have hcont : ContinuousAt F (⨅ i, φ i) := by
    simpa [F] using hcont_mul.comp (Continuous.prodMk_right (a : EReal)).continuousAt
  have hmono : Monotone F := by
    intro x y hxy
    exact mul_le_mul_of_nonneg_left hxy (EReal.coe_nonneg.mpr ha.le)
  have htop : F ⊤ = ⊤ := by
    simpa [F] using EReal.coe_mul_top_of_pos ha
  simpa [F, Function.comp] using
    (Monotone.map_iInf_of_continuousAt hcont hmono htop)

/-- Helper for Proposition 12.22: adding a finite real constant commutes with an indexed infimum in
`EReal`. -/
private theorem iInf_add_real_const
    {ι : Sort*} (Φ : ι → EReal) (c : ℝ) :
    (⨅ i, Φ i + ((c : ℝ) : EReal)) = (⨅ i, Φ i) + ((c : ℝ) : EReal) := by
  have hright :
      (⨅ i, Φ i) + ((c : ℝ) : EReal) ≤ (⨅ i, Φ i + ((c : ℝ) : EReal)) := by
    refine le_iInf fun i ↦ ?_
    exact add_le_add (iInf_le Φ i) le_rfl
  have hleft_sub :
      (⨅ i, Φ i + ((c : ℝ) : EReal)) - ((c : ℝ) : EReal) ≤ (⨅ i, Φ i) := by
    refine le_iInf fun i ↦ ?_
    exact (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).2
      (iInf_le (fun i ↦ Φ i + ((c : ℝ) : EReal)) i)
  have hleft :
      (⨅ i, Φ i + ((c : ℝ) : EReal)) ≤ (⨅ i, Φ i) + ((c : ℝ) : EReal) := by
    exact (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).1 hleft_sub
  exact le_antisymm hleft hright

/-- Helper for Proposition 12.22: translating Corollary 2.15 by a base point `z` gives the
textbook squared-distance identity for affine combinations. -/
private theorem sqdist_affine_combination_identity
    [InnerProductSpace ℝ H] (x y z : H) (α : ℝ) :
    ‖((α • x + (1 - α) • y) - z)‖ ^ (2 : ℕ) + α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) =
      α * ‖x - z‖ ^ (2 : ℕ) + (1 - α) * ‖y - z‖ ^ (2 : ℕ) := by
  have htranslate :
      α • (x - z) + (1 - α) • (y - z) = (α • x + (1 - α) • y) - z := by
    calc
      α • (x - z) + (1 - α) • (y - z)
          = α • x - α • z + ((1 - α) • y - (1 - α) • z) := by
            rw [smul_sub, smul_sub]
      _ = α • x + (1 - α) • y - (α • z + (1 - α) • z) := by
            abel
      _ = (α • x + (1 - α) • y) - z := by
            rw [← add_smul, show α + (1 - α) = (1 : ℝ) by ring, one_smul]
  have hnorm_sub : ‖x - z - (y - z)‖ = ‖x - y‖ := by
    congr 1
    abel
  have h := norm_sq_affine_combination_add_weighted_norm_sub_sq (x - z) (y - z) α
  have hnorm1 : ‖α • (x - z) + (1 - α) • (y - z)‖ = ‖(α • x + (1 - α) • y) - z‖ := by
    rw [htranslate]
  calc
    ‖((α • x + (1 - α) • y) - z)‖ ^ (2 : ℕ) + α * (1 - α) * ‖x - y‖ ^ (2 : ℕ)
        = ‖α • (x - z) + (1 - α) • (y - z)‖ ^ (2 : ℕ) +
            α * (1 - α) * ‖x - z - (y - z)‖ ^ (2 : ℕ) := by
          rw [← hnorm1, ← hnorm_sub]
    _ = α * ‖x - z‖ ^ (2 : ℕ) + (1 - α) * ‖y - z‖ ^ (2 : ℕ) := h

/-- Helper for Proposition 12.22: the sum of the `μ`- and `γ`-quadratic penalties is bounded below
by the single quadratic penalty with parameter `γ + μ`. -/
private theorem moreau_quadratic_sum_ge_add_parameter
    [InnerProductSpace ℝ H] (x y z : H) (γ μ : PosReal) :
    (1 / (2 * (μ : ℝ))) * ‖z - y‖ ^ (2 : ℕ) +
      (1 / (2 * (γ : ℝ))) * ‖x - z‖ ^ (2 : ℕ) ≥
    (1 / (2 * (((γ + μ : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) := by
  let α : ℝ := (μ : ℝ) / ((μ : ℝ) + (γ : ℝ))
  have hsum_ne : (μ : ℝ) + (γ : ℝ) ≠ 0 := by
    linarith [γ.2, μ.2]
  have hsum_ne_comm : (γ : ℝ) + (μ : ℝ) ≠ 0 := by
    simpa [add_comm] using hsum_ne
  have hsq :
      ‖((α • x + (1 - α) • y) - z)‖ ^ (2 : ℕ) + α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) =
        α * ‖x - z‖ ^ (2 : ℕ) + (1 - α) * ‖z - y‖ ^ (2 : ℕ) := by
    have h := sqdist_affine_combination_identity x y z α
    rw [norm_sub_rev y z] at h
    simpa using h
  have hgap :
      α * ‖x - z‖ ^ (2 : ℕ) + (1 - α) * ‖z - y‖ ^ (2 : ℕ) ≥
        α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) := by
    have hnonneg : 0 ≤ ‖((α • x + (1 - α) • y) - z)‖ ^ (2 : ℕ) := by
      positivity
    linarith
  have hone_sub :
      1 - α = (γ : ℝ) / ((μ : ℝ) + (γ : ℝ)) := by
    dsimp [α]
    field_simp [hsum_ne]
    ring
  have hfactor :
      (1 / (2 * (μ : ℝ))) * ‖z - y‖ ^ (2 : ℕ) +
        (1 / (2 * (γ : ℝ))) * ‖x - z‖ ^ (2 : ℕ) =
      (((γ : ℝ) + (μ : ℝ)) / (2 * (γ : ℝ) * (μ : ℝ))) *
        (α * ‖x - z‖ ^ (2 : ℕ) + (1 - α) * ‖z - y‖ ^ (2 : ℕ)) := by
    dsimp [α]
    field_simp [hsum_ne, γ.2.ne', μ.2.ne']
    ring
  have hfactor_nonneg :
      0 ≤ (((γ : ℝ) + (μ : ℝ)) / (2 * (γ : ℝ) * (μ : ℝ))) := by
    have hnum_nonneg : 0 ≤ (γ : ℝ) + (μ : ℝ) := by
      linarith [γ.2, μ.2]
    have hden_pos : 0 < 2 * (γ : ℝ) * (μ : ℝ) := by
      nlinarith [γ.2, μ.2]
    have hden_nonneg : 0 ≤ 2 * (γ : ℝ) * (μ : ℝ) := hden_pos.le
    exact div_nonneg hnum_nonneg hden_nonneg
  calc
    (1 / (2 * (μ : ℝ))) * ‖z - y‖ ^ (2 : ℕ) +
        (1 / (2 * (γ : ℝ))) * ‖x - z‖ ^ (2 : ℕ)
        =
      (((γ : ℝ) + (μ : ℝ)) / (2 * (γ : ℝ) * (μ : ℝ))) *
        (α * ‖x - z‖ ^ (2 : ℕ) + (1 - α) * ‖z - y‖ ^ (2 : ℕ)) := hfactor
    _ ≥ (((γ : ℝ) + (μ : ℝ)) / (2 * (γ : ℝ) * (μ : ℝ))) *
          (α * (1 - α) * ‖x - y‖ ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hgap hfactor_nonneg
    _ = (1 / (2 * (((γ + μ : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) := by
          rw [hone_sub]
          dsimp [α]
          field_simp [hsum_ne, hsum_ne_comm, γ.2.ne', μ.2.ne']
          ring_nf

/-- Helper for Proposition 12.22: the real quadratic comparison lifts directly to `EReal`. -/
private theorem moreau_quadratic_sum_ge_add_parameter_ereal
    [InnerProductSpace ℝ H] (x y z : H) (γ μ : PosReal) :
    ((((1 / (2 * (((γ + μ : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      (((1 / (2 * (μ : ℝ))) * ‖z - y‖ ^ (2 : ℕ) : ℝ) : EReal) +
        (((1 / (2 * (γ : ℝ))) * ‖x - z‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  rw [← EReal.coe_add]
  exact_mod_cast moreau_quadratic_sum_ge_add_parameter x y z γ μ

/-- Helper for Proposition 12.22: at the affine-combination minimizer from the source proof, the
two quadratic penalties collapse exactly to the single `(γ + μ)`-quadratic. -/
private theorem moreau_quadratic_sum_eq_add_parameter_at_affine_combination
    [InnerProductSpace ℝ H] (x y : H) (γ μ : PosReal) :
    let α : ℝ := (μ : ℝ) / ((μ : ℝ) + (γ : ℝ))
    let z0 : H := α • x + (1 - α) • y
    (1 / (2 * (μ : ℝ))) * ‖z0 - y‖ ^ (2 : ℕ) +
      (1 / (2 * (γ : ℝ))) * ‖x - z0‖ ^ (2 : ℕ) =
    (1 / (2 * (((γ + μ : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) := by
  let α : ℝ := (μ : ℝ) / ((μ : ℝ) + (γ : ℝ))
  let z0 : H := α • x + (1 - α) • y
  have hsum_ne : (μ : ℝ) + (γ : ℝ) ≠ 0 := by
    linarith [γ.2, μ.2]
  have hsum_ne_comm : (γ : ℝ) + (μ : ℝ) ≠ 0 := by
    simpa [add_comm] using hsum_ne
  have hsq :
      α * ‖x - z0‖ ^ (2 : ℕ) + (1 - α) * ‖z0 - y‖ ^ (2 : ℕ) =
        α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) := by
    have h := (sqdist_affine_combination_identity x y z0 α).symm
    rw [norm_sub_rev y z0] at h
    have hnorm0 : ‖(α • x + (1 - α) • y) - z0‖ = (0 : ℝ) := by
      simp [z0]
    rw [hnorm0] at h
    simpa using h
  have hone_sub :
      1 - α = (γ : ℝ) / ((μ : ℝ) + (γ : ℝ)) := by
    dsimp [α]
    field_simp [hsum_ne]
    ring
  have hfactor :
      (1 / (2 * (μ : ℝ))) * ‖z0 - y‖ ^ (2 : ℕ) +
        (1 / (2 * (γ : ℝ))) * ‖x - z0‖ ^ (2 : ℕ) =
      (((γ : ℝ) + (μ : ℝ)) / (2 * (γ : ℝ) * (μ : ℝ))) *
        (α * ‖x - z0‖ ^ (2 : ℕ) + (1 - α) * ‖z0 - y‖ ^ (2 : ℕ)) := by
    dsimp [α]
    field_simp [hsum_ne, γ.2.ne', μ.2.ne']
    ring
  calc
    (1 / (2 * (μ : ℝ))) * ‖z0 - y‖ ^ (2 : ℕ) +
        (1 / (2 * (γ : ℝ))) * ‖x - z0‖ ^ (2 : ℕ)
        =
      (((γ : ℝ) + (μ : ℝ)) / (2 * (γ : ℝ) * (μ : ℝ))) *
        (α * ‖x - z0‖ ^ (2 : ℕ) + (1 - α) * ‖z0 - y‖ ^ (2 : ℕ)) := hfactor
    _ = (((γ : ℝ) + (μ : ℝ)) / (2 * (γ : ℝ) * (μ : ℝ))) *
          (α * (1 - α) * ‖x - y‖ ^ (2 : ℕ)) := by
            rw [hsq]
    _ = (1 / (2 * (((γ + μ : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) := by
          rw [hone_sub]
          dsimp [α]
          field_simp [hsum_ne, hsum_ne_comm, γ.2.ne', μ.2.ne']
          ring_nf

/-- Helper for Proposition 12.22: lower semicontinuity is preserved by positive pointwise
multiplication of the `EReal` representative. -/
private theorem lowerSemicontinuous_coe_mul_of_pos {X : Type*} [TopologicalSpace X]
    {a : ℝ} (ha : 0 < a) {f : X → EReal} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun x : X ↦ (a : EReal) * f x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  have haE : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha.le
  calc
    (a : EReal) * f x ≤ (a : EReal) * Filter.liminf f (nhds x) :=
      (monotone_mul_left_of_nonneg haE) (hf.le_liminf x)
    _ = Filter.liminf (fun y : X ↦ (a : EReal) * f y) (nhds x) := by
      symm
      exact EReal.liminf_const_mul_of_nonneg_of_ne_top haE (EReal.coe_ne_top a)

/-- Helper for Proposition 12.22: positive scaling preserves the effective domain. -/
private theorem mem_effectiveDomain_smul_iff
    (γ : PosReal) (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ effectiveDomain (γ • f) ↔ x ∈ effectiveDomain f := by
  rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, posReal_smul_apply,
    lt_top_iff_ne_top, lt_top_iff_ne_top]
  constructor
  · intro hmul htop
    exact hmul (by simpa [htop] using EReal.coe_mul_top_of_pos γ.2)
  · intro hf
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
      Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hf⟩


end

section

variable [InnerProductSpace ℝ H]


/-- Helper for Proposition 8.17: multiplying by a strictly positive real preserves the effective
domain. -/
private theorem mem_dom_smul_iff (a : PosReal)
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ dom (fun y : H ↦ ((a • f) y : EReal)) ↔
      x ∈ dom (fun y : H ↦ (f y : EReal)) := by
  rw [mem_dom_iff, mem_dom_iff, posReal_smul_apply, lt_top_iff_ne_top, lt_top_iff_ne_top]
  constructor
  · intro hmul htop
    exact hmul (by simpa [htop] using EReal.coe_mul_top_of_pos a.2)
  · intro hf
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (a : ℝ)), Or.inl (EReal.coe_nonneg.mpr a.2.le),
      Or.inl (EReal.coe_ne_top (a : ℝ)), Or.inr hf⟩

/-- Proposition 8.17 (2): every positive pointwise scalar multiple of a convex
`]-∞,+∞]`-valued function is convex. -/
theorem convex_epigraph_smul
    {f : H → Set.Ioi (⊥ : EReal)}
    (hf : Convex ℝ (epigraph fun x : H ↦ (f x : EReal)))
    (a : PosReal) :
    Convex ℝ (epigraph fun x : H ↦ ((a • f) x : EReal)) := by
  refine (convex_epigraph_iff_jensen_on_dom _).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hx' := (mem_dom_smul_iff a f x).1 hx
  have hy' := (mem_dom_smul_iff a f y).1 hy
  have ha_nonneg : (0 : EReal) ≤ (a : EReal) := EReal.coe_nonneg.mpr a.2.le
  have ha_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top (a : ℝ)
  have hJ :=
    (convex_epigraph_iff_jensen_on_dom (fun z : H ↦ (f z : EReal))).1 hf
      hx' hy' hα hα_lt_one
  have hscaled :
      (a : EReal) * (f (α • x + (1 - α) • y) : EReal) ≤
        (a : EReal) *
          ((α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal))) :=
    mul_le_mul_of_nonneg_left hJ ha_nonneg
  calc
    ((a • f) (α • x + (1 - α) • y) : EReal)
        = (a : EReal) * (f (α • x + (1 - α) • y) : EReal) := by
            rw [posReal_smul_apply]
    _ ≤ (a : EReal) *
          ((α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal))) := hscaled
    _ = (a : EReal) * ((α : EReal) * (f x : EReal)) +
          (a : EReal) * ((((1 - α : ℝ) : EReal) * (f y : EReal))) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top]
    _ = (α : EReal) * ((a • f) x : EReal) +
          (((1 - α : ℝ) : EReal) * ((a • f) y : EReal)) := by
            rw [posReal_smul_apply, posReal_smul_apply]
            simp [mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 12 22: scaling the coefficient `γ` of the Moreau envelope by a
positive real preserves membership in `Γ₀(H)`. -/
theorem smul_mem_gammaZero
    [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    γ • f ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · simpa [posReal_smul_apply] using
      lowerSemicontinuous_coe_mul_of_pos γ.2 hf.1
  · have hconv_epigraph :
        Convex ℝ (epigraph fun x : H ↦ ((γ • f) x : EReal)) :=
      convex_epigraph_smul hf.2.convex_epigraph_asEReal γ
    have hJensen :=
      (convex_epigraph_iff_jensen_on_dom (fun x : H ↦ ((γ • f) x : EReal))).1 hconv_epigraph
    refine ⟨?_, subset_rfl, ?_⟩
    · rcases hf.2.nonempty with ⟨x, hx⟩
      exact ⟨x, (mem_effectiveDomain_smul_iff γ f x).2 hx⟩
    · intro x hx y hy α hα0 hα1
      have hx_dom : x ∈ dom (fun z : H ↦ ((γ • f) z : EReal)) := by
        simpa [effectiveDomain, dom] using hx
      have hy_dom : y ∈ dom (fun z : H ↦ ((γ • f) z : EReal)) := by
        simpa [effectiveDomain, dom] using hy
      simpa [effectiveDomain, dom] using hJensen hx_dom hy_dom hα0 hα1



end

section

variable [InnerProductSpace ℝ H]

/-- Proposition 12.22 (1): clause (i). For `f : H → ]-∞,+∞]` and `γ, μ ∈ ℝ_{++}`,
scaling `f` by `γ` scales its `μ`-Moreau envelope, with the envelope parameter changing from `μ`
to `γμ`. -/
theorem moreauEnvelope_smul_eq_smul_moreauEnvelope
    (f : H → Set.Ioi (⊥ : EReal)) (γ μ : PosReal) :
    {}^[μ] (γ • f) = (γ : EReal) • {}^[(γ * μ)] f := by
  ext x
  have hγ_nonneg : (0 : EReal) ≤ (γ : EReal) := EReal.coe_nonneg.mpr γ.2.le
  have hγ_ne_top : (γ : EReal) ≠ ⊤ := EReal.coe_ne_top (γ : ℝ)
  let qμ : H → EReal := fun y ↦
    ((((1 / (2 * (μ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal))
  let qγμ : H → EReal := fun y ↦
    ((((1 / (2 * (((γ * μ : PosReal) : ℝ)))) * ‖x - y‖ ^ 2 : ℝ) : EReal))
  rw [Pi.smul_apply, moreauEnvelope_apply, moreauEnvelope_apply]
  calc
    (⨅ y : H, ((γ • f) y : EReal) + qμ y) =
        ⨅ y : H, (γ : EReal) * ((f y : EReal) + qγμ y) := by
          refine iInf_congr fun y ↦ ?_
          have hquadratic :
              qμ y = (γ : EReal) * qγμ y := by
            dsimp [qμ, qγμ]
            rw [← EReal.coe_mul]
            congr 1
            calc
              (1 / (2 * (μ : ℝ))) * ‖x - y‖ ^ 2
                  = ((γ : ℝ) * (1 / (2 * (((γ * μ : PosReal) : ℝ))))) * ‖x - y‖ ^ 2 := by
                      rw [posReal_coe_mul]
                      field_simp [γ.2.ne', μ.2.ne']
              _ = (γ : ℝ) * ((1 / (2 * (((γ * μ : PosReal) : ℝ)))) * ‖x - y‖ ^ 2) := by
                    ring
          rw [posReal_smul_apply, hquadratic]
          symm
          rw [EReal.left_distrib_of_nonneg_of_ne_top hγ_nonneg hγ_ne_top]
    _ = (γ : EReal) * (⨅ y : H, (f y : EReal) + qγμ y) := by
          symm
          exact coe_real_mul_iInf_ereal_of_pos γ.2 _

/-- Proposition 12.22 (2): clause (ii). For `f : H → ]-∞,+∞]` and `γ, μ ∈ ℝ_{++}`,
taking the `γ`-Moreau envelope of the `μ`-Moreau envelope yields the `(γ + μ)`-Moreau envelope. -/
theorem iterated_moreauEnvelope_eq_moreauEnvelope_add
    (f : H → Set.Ioi (⊥ : EReal)) (γ μ : PosReal) :
    {}^[γ] ({}^[μ] f) = {}^[(γ + μ)] f := by
  ext x
  simp_rw [moreauEnvelope_apply]
  set qμ : H → H → EReal := fun z y ↦
    (((1 / (2 * (μ : ℝ))) * ‖z - y‖ ^ (2 : ℕ) : ℝ) : EReal)
  set qγ : H → ℝ := fun z ↦
    (1 / (2 * (γ : ℝ))) * ‖x - z‖ ^ (2 : ℕ)
  set qγμ : H → EReal := fun y ↦
    (((1 / (2 * (((γ + μ : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)
  refine le_antisymm ?_ ?_
  · refine le_iInf fun y ↦ ?_
    let α : ℝ := (μ : ℝ) / ((μ : ℝ) + (γ : ℝ))
    let z0 : H := α • x + (1 - α) • y
    calc
      (⨅ z : H, (⨅ y' : H, (f y' : EReal) + qμ z y') + ((qγ z : ℝ) : EReal))
          ≤ (⨅ y' : H, (f y' : EReal) + qμ z0 y') + ((qγ z0 : ℝ) : EReal) := by
            exact iInf_le _ z0
      _ = ⨅ y' : H, ((f y' : EReal) + qμ z0 y') + ((qγ z0 : ℝ) : EReal) := by
            symm
            exact iInf_add_real_const
              (Φ := fun y' : H ↦ (f y' : EReal) + qμ z0 y') (c := qγ z0)
      _ ≤ ((f y : EReal) + qμ z0 y) + ((qγ z0 : ℝ) : EReal) := by
            exact iInf_le _ y
      _ = (f y : EReal) + (qμ z0 y + ((qγ z0 : ℝ) : EReal)) := by
            rw [add_assoc]
      _ = (f y : EReal) + qγμ y := by
            have hquad :
                qμ z0 y + ((qγ z0 : ℝ) : EReal) = qγμ y := by
              have hquad_real :
                  (((1 / (2 * (μ : ℝ))) * ‖z0 - y‖ ^ (2 : ℕ) +
                      (1 / (2 * (γ : ℝ))) * ‖x - z0‖ ^ (2 : ℕ) : ℝ) : EReal) =
                    (((1 / (2 * (((γ + μ : PosReal) : ℝ)))) *
                      ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) := by
                    exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) <|
                      moreau_quadratic_sum_eq_add_parameter_at_affine_combination x y γ μ
              dsimp [qμ, qγ, qγμ, z0, α] at hquad_real ⊢
              simpa [← EReal.coe_add] using hquad_real
            rw [hquad]
  · refine le_iInf fun z ↦ ?_
    calc
      (⨅ y' : H, (f y' : EReal) + qγμ y') ≤
          ⨅ y : H, ((f y : EReal) + qμ z y) + ((qγ z : ℝ) : EReal) := by
            refine le_iInf fun y ↦ ?_
            have hquad :
                qγμ y ≤ qμ z y + ((qγ z : ℝ) : EReal) := by
              dsimp [qμ, qγ, qγμ]
              simpa [← EReal.coe_mul] using
                moreau_quadratic_sum_ge_add_parameter_ereal x y z γ μ
            calc
              (⨅ y' : H, (f y' : EReal) + qγμ y') ≤ (f y : EReal) + qγμ y := by
                exact iInf_le _ y
              _ ≤ ((f y : EReal) + qμ z y) + ((qγ z : ℝ) : EReal) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_left hquad (f y : EReal)
      _ ≤ (⨅ y : H, (f y : EReal) + qμ z y) + ((qγ z : ℝ) : EReal) := by
            simpa using
              le_of_eq (iInf_add_real_const
                (Φ := fun y : H ↦ (f y : EReal) + qμ z y) (c := qγ z))

end

end ERealFunction
