import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_lem_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_3
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open scoped ContinuousLinearMap

/-- The first-order field in the gradient-system representation of `DIN`. -/
noncomputable def DINGradientField {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (gradφ : M → H → H) (β γ : ℝ) (μ : M) (p : H × H) : H × H :=
  (β • gradφ μ p.1 +
      Real.sqrt (γ - 1 / β) •
        (Real.sqrt (γ - 1 / β) • p.1 + Real.sqrt (1 / β) • p.2),
    Real.sqrt (1 / β) •
      (Real.sqrt (γ - 1 / β) • p.1 + Real.sqrt (1 / β) • p.2))

/-- The algebraic identity behind the first flow equation of the change of
variables: `√a • x + √b • (-(√(ab))⁻¹ • (y + a • x)) = -(√a)⁻¹ • y`. -/
theorem aux_smul_identity {H : Type*} [NormedAddCommGroup H] [Module ℝ H] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y : H) :
    Real.sqrt a • x + Real.sqrt b • (-(Real.sqrt (a * b))⁻¹ • (y + a • x)) =
      -(Real.sqrt a)⁻¹ • y := by
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hsb : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hmul : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := (Real.sqrt_mul ha.le b).symm
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hcoef : Real.sqrt b * (Real.sqrt (a * b))⁻¹ = (Real.sqrt a)⁻¹ := by
    rw [← hmul, mul_inv]
    field_simp
  have hcoef2 : (Real.sqrt a)⁻¹ * a = Real.sqrt a := by
    rw [inv_mul_eq_iff_eq_mul₀ hsa, hsq]
  calc Real.sqrt a • x + Real.sqrt b • (-(Real.sqrt (a * b))⁻¹ • (y + a • x))
      = Real.sqrt a • x + -((Real.sqrt b * (Real.sqrt (a * b))⁻¹) • (y + a • x)) := by
        rw [← mul_smul, mul_neg, neg_smul]
    _ = Real.sqrt a • x + -((Real.sqrt a)⁻¹ • (y + a • x)) := by rw [hcoef]
    _ = -(Real.sqrt a)⁻¹ • y := by
        rw [smul_add, ← mul_smul, hcoef2]
        module

/-- The algebraic identity behind the second flow equation: if
`s = -(√a)⁻¹ • (u + β • v)` then `-√b • s = (√(ab))⁻¹ • ((1/β) • u + v)`
(the factor `1/β` being `b`). -/
theorem aux_smul_identity₂ {H : Type*} [NormedAddCommGroup H] [Module ℝ H] {a b β : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β) (hb' : b = 1 / β) (s u v : H)
    (hs : s = -((Real.sqrt a)⁻¹) • (u + β • v)) :
    -Real.sqrt b • s = (Real.sqrt (a * b))⁻¹ • (b • u + v) := by
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hsb : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hmul : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := (Real.sqrt_mul ha.le b).symm
  have hβb : β * b = 1 := by rw [hb']; field_simp
  have h1 : β * Real.sqrt b = (Real.sqrt b)⁻¹ := by
    field_simp
    rw [Real.sq_sqrt hb.le]
    exact hβb
  have hcoef : (Real.sqrt (a * b))⁻¹ = β * Real.sqrt b * (Real.sqrt a)⁻¹ := by
    rw [← hmul, mul_inv, h1]
    ring
  rw [hs, neg_smul, neg_smul, smul_neg, neg_neg, smul_smul, hcoef, smul_add, smul_add,
    ← mul_smul, ← mul_smul]
  rw [show β * Real.sqrt b * (Real.sqrt a)⁻¹ * b = Real.sqrt b * (Real.sqrt a)⁻¹ by
    rw [show β * Real.sqrt b * (Real.sqrt a)⁻¹ * b =
      (β * b) * (Real.sqrt b * (Real.sqrt a)⁻¹) by ring, hβb, one_mul]]
  module

/-- The auxiliary coordinate of the paper's change of variables for (DIN):
  `z = -(ẋ + β∇φ(x) + (γ-1/β)x)/√((γ-1/β)·(1/β))`.  Its value at time `0` is
  recorded separately as `dinAuxInitial` (it is *not* the initial velocity `v₀`). -/
noncomputable def dinAux {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (gradφ : M → H → H) (β γ : ℝ) (x dx : M → ℝ → H) (μ : M) (t : ℝ) : H :=
  -(Real.sqrt ((γ - 1 / β) * (1 / β)))⁻¹ •
    (dx μ t + β • gradφ μ (x μ t) + (γ - 1 / β) • x μ t)

/-- The auxiliary coordinate at time `0`, expressed through the initial data:
  `z₀ = -(v₀ + β∇φ(u₀) + (γ-1/β)u₀)/√((γ-1/β)·(1/β))`. -/
noncomputable def dinAuxInitial {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (gradφ : M → H → H) (β γ : ℝ) (u₀ v₀ : M → H) (μ : M) : H :=
  -(Real.sqrt ((γ - 1 / β) * (1 / β)))⁻¹ •
    (v₀ μ + β • gradφ μ (u₀ μ) + (γ - 1 / β) • u₀ μ)

/-- The equivalent first-order gradient system used in the proof of Theorem 6.1.
    This records the paper's change of variables for a `DIN` trajectory; the
    auxiliary coordinate starts at `dinAuxInitial`, the value of `dinAux`
    determined by the initial data, and *not* at `v₀` as in the paper's
    slightly abusive notation. -/
structure DINGradientLift {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (gradφ : M → H → H) (x : M → ℝ → H)
    (u₀ v₀ : M → H) (β γ : ℝ) where
  X : M → ℝ → H × H
  fst_eq : ∀ μ t, (X μ t).1 = x μ t
  initial : ∀ μ, X μ 0 = (u₀ μ, dinAuxInitial gradφ β γ u₀ v₀ μ)
  locally_ac : ∀ μ T, 0 < T → AbsolutelyContinuousOnInterval (X μ) 0 T
  flow : ∀ μ T, 0 < T →
    ∀ᵐ t ∂ MeasureTheory.volume.restrict (Set.Icc 0 T),
      HasDerivAt (X μ) (-DINGradientField gradφ β γ μ (X μ t)) t

/-- Vector-valued version of `ac_comp_of_lipschitzOn_image`. -/
theorem ac_comp_of_lipschitzOn_image_vec {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {f : ℝ → E} {phi : E → F} {l u : ℝ} {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f l u)
    (hphi : LipschitzOnWith K phi (f '' Set.uIcc l u)) :
    AbsolutelyContinuousOnInterval (fun s => phi (f s)) l u := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  rcases (absolutelyContinuousOnInterval_iff _ _ _).mp hf (ε / (K + 1))
      (by positivity) with ⟨δ, hδ, hδ_bound⟩
  refine ⟨δ, hδ, fun (n, I) hnI₁ hnI₂ => ?_⟩
  calc
    ∑ i ∈ Finset.range n, dist (phi (f (I i).1)) (phi (f (I i).2))
        ≤ ∑ i ∈ Finset.range n, K * dist (f (I i).1) (f (I i).2) := by
          apply Finset.sum_le_sum
          intro i hi
          have h := hphi ⟨(I i).1, (hnI₁.left i hi).left, rfl⟩
            ⟨(I i).2, (hnI₁.left i hi).right, rfl⟩
          apply ENNReal.toReal_mono
            (ENNReal.mul_ne_top (by simp) (edist_ne_top _ _)) at h
          rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at h
    _ = K * ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) := by
          rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by
          gcongr
          simpa using (hδ_bound (n, I) hnI₁ hnI₂).le
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field

/-- A pair-valued path is absolutely continuous when both components are. -/
theorem ac_prod {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℝ → E} {g : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => (f t, g t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at *
  intro ε hε
  rcases hf (ε / 2) (by positivity) with ⟨δ₁, hδ₁, h₁⟩
  rcases hg (ε / 2) (by positivity) with ⟨δ₂, hδ₂, h₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun (n, I) hnI₁ hnI₂ => ?_⟩
  calc
    ∑ i ∈ Finset.range n, dist ((f (I i).1, g (I i).1)) ((f (I i).2, g (I i).2))
        ≤ ∑ i ∈ Finset.range n,
            (dist (f (I i).1) (f (I i).2) + dist (g (I i).1) (g (I i).2)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Prod.dist_eq]
          exact max_le (le_add_of_nonneg_right dist_nonneg) (le_add_of_nonneg_left dist_nonneg)
    _ = ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) +
          ∑ i ∈ Finset.range n, dist (g (I i).1) (g (I i).2) := Finset.sum_add_distrib
    _ < ε / 2 + ε / 2 :=
          add_lt_add (h₁ (n, I) hnI₁ (lt_of_lt_of_le hnI₂ (min_le_left _ _)))
            (h₂ (n, I) hnI₁ (lt_of_lt_of_le hnI₂ (min_le_right _ _)))
    _ = ε := by ring

/-- **The change of variables of Theorem 6.1 follows from the `DIN` equation.**
  A strong solution whose Hessian field `hessφ μ` is the derivative of `∇φ μ`
  (and whose gradient is Lipschitz along the trajectory, for the absolute
  continuity of the auxiliary coordinate) gives a `DINGradientLift`. -/
noncomputable def dinGradientLift_of_DIN {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (β γ : ℝ)
    (hβ : 0 < β) (hβγ : 1 < β * γ)
    (hDIN : ∀ μ, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T, 0 < T → ∃ K : NNReal, LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T)) :
    DINGradientLift gradφ x u₀ v₀ β γ := by
  have ha : (0 : ℝ) < γ - 1 / β := by
    have h1 : 1 / β < γ := by
      rw [div_lt_iff₀ hβ]
      linarith
    linarith
  have hb : (0 : ℝ) < 1 / β := by positivity
  have hsa : Real.sqrt (γ - 1 / β) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  refine ⟨fun μ t => (x μ t, dinAux gradφ β γ x dx μ t), fun μ t => rfl, ?_, ?_, ?_⟩
  · -- initial condition
    intro μ
    obtain ⟨-, hx0, hdx0, -⟩ := hDIN μ
    simp only [dinAux, dinAuxInitial, hx0, hdx0]
  · -- local absolute continuity
    intro μ T hT
    obtain ⟨hlac, -⟩ := hDIN μ
    obtain ⟨hxac, hdxac⟩ := hlac T hT
    have hgac : AbsolutelyContinuousOnInterval (fun t => gradφ μ (x μ t)) 0 T :=
      ac_comp_of_lipschitzOn_image_vec hxac (hlip μ T hT).choose_spec
    have hsum_ac : AbsolutelyContinuousOnInterval
        (fun t => dx μ t + β • gradφ μ (x μ t) + (γ - 1 / β) • x μ t) 0 T :=
      (hdxac.fun_add (hgac.const_smul β)).fun_add (hxac.const_smul (γ - 1 / β))
    have hz_ac : AbsolutelyContinuousOnInterval (dinAux gradφ β γ x dx μ) 0 T := by
      unfold dinAux
      exact hsum_ac.const_smul (-(Real.sqrt ((γ - 1 / β) * (1 / β)))⁻¹)
    exact ac_prod hxac hz_ac
  · -- the first-order flow
    intro μ T hT
    obtain ⟨-, -, -, hode⟩ := hDIN μ
    have hode' : ∀ᵐ t ∂ MeasureTheory.volume.restrict (Set.Icc 0 T),
        ddx μ t + γ • dx μ t + β • (hessφ μ (x μ t) (dx μ t)) + gradφ μ (x μ t) = 0 :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Icc_subset_Ici_self
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr hode)
    have hd' : ∀ᵐ t ∂ MeasureTheory.volume.restrict (Set.Icc 0 T),
        HasDerivAt (x μ) (dx μ t) t :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Icc_subset_Ici_self (hderiv μ)
    have hdd' : ∀ᵐ t ∂ MeasureTheory.volume.restrict (Set.Icc 0 T),
        HasDerivAt (dx μ) (ddx μ t) t :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Icc_subset_Ici_self (hddx μ)
    filter_upwards [hd', hdd', hode'] with t hdx_t hddx_t hode_t
    obtain ⟨L, hL, hLv⟩ := hhess μ (x μ t)
    have hgrad_t : HasDerivAt (fun s => gradφ μ (x μ s)) (hessφ μ (x μ t) (dx μ t)) t := by
      have h := hL.comp_hasDerivAt t hdx_t
      rw [hLv] at h
      exact h
    have hz_t : HasDerivAt (fun s => dinAux gradφ β γ x dx μ s)
        (-(Real.sqrt ((γ - 1 / β) * (1 / β)))⁻¹ •
          (ddx μ t + β • (hessφ μ (x μ t) (dx μ t)) + (γ - 1 / β) • dx μ t)) t := by
      have h1 : HasDerivAt (fun s => dx μ s + β • gradφ μ (x μ s) + (γ - 1 / β) • x μ s)
          (ddx μ t + β • (hessφ μ (x μ t) (dx μ t)) + (γ - 1 / β) • dx μ t) t :=
        (hddx_t.add (hgrad_t.const_smul β)).add (hdx_t.const_smul (γ - 1 / β))
      have h2 := h1.const_smul (-(Real.sqrt ((γ - 1 / β) * (1 / β)))⁻¹)
      unfold dinAux
      convert h2 using 1
    have hddx_eq : ddx μ t =
        -(γ • dx μ t + β • (hessφ μ (x μ t) (dx μ t)) + gradφ μ (x μ t)) :=
      eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hode_t)
    -- the auxiliary combination in terms of the velocity
    have hs_eq : Real.sqrt (γ - 1 / β) • x μ t +
        Real.sqrt (1 / β) • dinAux gradφ β γ x dx μ t =
        -((Real.sqrt (γ - 1 / β))⁻¹) • (dx μ t + β • gradφ μ (x μ t)) := by
      rw [dinAux]
      exact aux_smul_identity ha hb (x μ t) (dx μ t + β • gradφ μ (x μ t))
    -- the two flow equations
    have hx_val : dx μ t = -(β • gradφ μ (x μ t) +
        Real.sqrt (γ - 1 / β) • (Real.sqrt (γ - 1 / β) • x μ t +
          Real.sqrt (1 / β) • dinAux gradφ β γ x dx μ t)) := by
      rw [hs_eq, ← mul_smul, mul_neg, mul_inv_cancel₀ hsa, neg_one_smul]
      module
    have hz_val : -(Real.sqrt ((γ - 1 / β) * (1 / β)))⁻¹ •
          (ddx μ t + β • (hessφ μ (x μ t) (dx μ t)) + (γ - 1 / β) • dx μ t) =
        -Real.sqrt (1 / β) • (Real.sqrt (γ - 1 / β) • x μ t +
          Real.sqrt (1 / β) • dinAux gradφ β γ x dx μ t) := by
      have h := aux_smul_identity₂ ha hb hβ (b := 1 / β) rfl
        (Real.sqrt (γ - 1 / β) • x μ t + Real.sqrt (1 / β) • dinAux gradφ β γ x dx μ t)
        (dx μ t) (gradφ μ (x μ t)) hs_eq
      rw [h, hddx_eq]
      module
    have hpair : HasDerivAt (fun s => (x μ s, dinAux gradφ β γ x dx μ s))
        (-DINGradientField gradφ β γ μ (x μ t, dinAux gradφ β γ x dx μ t)) t := by
      have h := hdx_t.prodMk hz_t
      refine h.congr_deriv ?_
      refine Prod.ext ?_ ?_
      · dsimp [DINGradientField]
        exact hx_val
      · dsimp [DINGradientField]
        simpa [neg_smul, add_comm, add_left_comm, add_assoc] using hz_val
    exact hpair

/-- Absolute continuity of the first component of a product-valued path. -/
theorem ac_fst {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℝ → E × F} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => (f t).1) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun E => ?_) hf
  apply Finset.sum_le_sum
  intro i hi
  simpa [Prod.dist_eq] using
    (le_max_left (dist (f (E.2 i).1).1 (f (E.2 i).2).1)
      (dist (f (E.2 i).1).2 (f (E.2 i).2).2))

/-- Absolute continuity of the second component of a product-valued path. -/
theorem ac_snd {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℝ → E × F} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => (f t).2) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun E => ?_) hf
  apply Finset.sum_le_sum
  intro i hi
  simpa [Prod.dist_eq] using
    (le_max_right (dist (f (E.2 i).1).1 (f (E.2 i).2).1)
      (dist (f (E.2 i).1).2 (f (E.2 i).2).2))

/-- Integral of a scalar exponential-decay kernel. -/
theorem exp_decay_kernel_integral (c D t : ℝ) (hc : 0 < c) :
    (∫ s in 0..t, Real.exp (-c * (t - s)) * D) =
      c⁻¹ * (1 - Real.exp (-c * t)) * D := by
  let F : ℝ → ℝ := fun s => c⁻¹ * D * Real.exp (-c * (t - s))
  have hderiv : ∀ s : ℝ, HasDerivAt F (Real.exp (-c * (t - s)) * D) s := by
    intro s
    dsimp [F]
    convert (((Real.hasDerivAt_exp (-c * (t - s))).comp s
      (((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-c))).const_mul
        (c⁻¹ * D)) using 1
    all_goals field_simp [hc.ne']
    all_goals ring
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp (-c * (t - s)) * D)
      MeasureTheory.volume 0 t := by
    exact ((Real.continuous_exp.comp
      ((continuous_const.sub continuous_id).const_mul (-c))).mul
        continuous_const).intervalIntegrable 0 t
  have hcalc : ∫ s in 0..t, Real.exp (-c * (t - s)) * D = F t - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hint
  rw [hcalc]
  dsimp [F]
  rw [show -c * (t - t) = 0 by ring, Real.exp_zero]
  field_simp [hc.ne']
  ring

/-- Stability of two product-valued gradient flows, expressed with the
componentwise Hilbert energy rather than the product's sup norm.  The
trajectories are compared on `[0,T]`; the discrepancy bound is only needed on
that interval, which is what the ball-localized estimate of Corollary 6.5
supplies. -/
theorem two_component_flow_estimate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (X Y : ℝ → H × H) (F G : H × H → H × H)
    (u₀ v₀ u₀' v₀' : H) (c D T : ℝ)
    (hc : 0 < c) (hD : 0 ≤ D) (hT : 0 < T)
    (hX0 : X 0 = (u₀, v₀)) (hY0 : Y 0 = (u₀', v₀'))
    (hXac : AbsolutelyContinuousOnInterval X 0 T)
    (hYac : AbsolutelyContinuousOnInterval Y 0 T)
    (hXflow : ∀ᵐ t ∂ MeasureTheory.volume.restrict (Set.Icc 0 T),
      HasDerivAt X (-F (X t)) t)
    (hYflow : ∀ᵐ t ∂ MeasureTheory.volume.restrict (Set.Icc 0 T),
      HasDerivAt Y (-G (Y t)) t)
    (hGstrong : ∀ p q,
      c * (‖p.1 - q.1‖ ^ 2 + ‖p.2 - q.2‖ ^ 2) ≤
        inner ℝ ((G p).1 - (G q).1) (p.1 - q.1) +
          inner ℝ ((G p).2 - (G q).2) (p.2 - q.2))
    (hFG : ∀ᵐ t ∂ MeasureTheory.volume.restrict (Set.Icc 0 T),
      Real.sqrt (‖(F (X t)).1 - (G (X t)).1‖ ^ 2 +
        ‖(F (X t)).2 - (G (X t)).2‖ ^ 2) ≤ D) :
    ∀ t, 0 ≤ t → t ≤ T →
      ‖(X t).1 - (Y t).1‖ ≤
        Real.exp (-c * t) *
          Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
        c⁻¹ * (1 - Real.exp (-c * t)) * D := by
  intro t ht htT
  let y₁ : ℝ → H := fun s => (X s).1 - (Y s).1
  let y₂ : ℝ → H := fun s => (X s).2 - (Y s).2
  let w : ℝ → ℝ := fun s => ‖y₁ s‖ ^ 2 + ‖y₂ s‖ ^ 2
  have hy₁ac : AbsolutelyContinuousOnInterval y₁ 0 T := by
    simpa [y₁] using (ac_fst hXac).fun_sub (ac_fst hYac)
  have hy₂ac : AbsolutelyContinuousOnInterval y₂ 0 T := by
    simpa [y₂] using (ac_snd hXac).fun_sub (ac_snd hYac)
  have hwac : AbsolutelyContinuousOnInterval w 0 T := by
    simpa [w] using (ac_norm_sq hy₁ac).fun_add (ac_norm_sq hy₂ac)
  have hw_nonneg (s : ℝ) : 0 ≤ w s := by
    dsimp [w]
    positivity
  have hw0 : w 0 = ‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2 := by
    simp only [w, y₁, y₂, hX0, hY0]
  have hXflow' : ∀ᵐ s ∂ MeasureTheory.volume, s ∈ Set.Icc (0 : ℝ) T →
      HasDerivAt X (-F (X s)) s :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hXflow
  have hYflow' : ∀ᵐ s ∂ MeasureTheory.volume, s ∈ Set.Icc (0 : ℝ) T →
      HasDerivAt Y (-G (Y s)) s :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hYflow
  have hFG' : ∀ᵐ s ∂ MeasureTheory.volume, s ∈ Set.Icc (0 : ℝ) T →
      Real.sqrt (‖(F (X s)).1 - (G (X s)).1‖ ^ 2 +
        ‖(F (X s)).2 - (G (X s)).2‖ ^ 2) ≤ D :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hFG
  have hwDeriv : ∀ᵐ s ∂ MeasureTheory.volume, s ∈ Set.Icc (0 : ℝ) T →
      HasDerivAt w
        (2 * inner ℝ (y₁ s) ((-F (X s)).1 - (-G (Y s)).1) +
          2 * inner ℝ (y₂ s) ((-F (X s)).2 - (-G (Y s)).2)) s := by
    filter_upwards [hXflow', hYflow'] with s hXs hYs
    intro hs
    have hX₁ : HasDerivAt (fun r => (X r).1) ((-F (X s)).1) s := by
      simpa using (hasDerivAt_const s (ContinuousLinearMap.fst ℝ H H)).clm_apply (hXs hs)
    have hY₁ : HasDerivAt (fun r => (Y r).1) ((-G (Y s)).1) s := by
      simpa using (hasDerivAt_const s (ContinuousLinearMap.fst ℝ H H)).clm_apply (hYs hs)
    have hX₂ : HasDerivAt (fun r => (X r).2) ((-F (X s)).2) s := by
      simpa using (hasDerivAt_const s (ContinuousLinearMap.snd ℝ H H)).clm_apply (hXs hs)
    have hY₂ : HasDerivAt (fun r => (Y r).2) ((-G (Y s)).2) s := by
      simpa using (hasDerivAt_const s (ContinuousLinearMap.snd ℝ H H)).clm_apply (hYs hs)
    have hy₁D : HasDerivAt y₁ ((-F (X s)).1 - (-G (Y s)).1) s := by
      simpa [y₁] using hX₁.sub hY₁
    have hy₂D : HasDerivAt y₂ ((-F (X s)).2 - (-G (Y s)).2) s := by
      simpa [y₂] using hX₂.sub hY₂
    simpa [w] using hy₁D.norm_sq.add hy₂D.norm_sq
  have hineq : ∀ᵐ s ∂ MeasureTheory.volume, s ∈ Set.Icc (0 : ℝ) T →
      (1 - (1 / 2 : ℝ)) * deriv w s ≤
        (-c) * w s + D * w s ^ (1 / 2 : ℝ) := by
    filter_upwards [hwDeriv, hFG'] with s hws hFGs
    intro hs
    let e₁ : H := (F (X s)).1 - (G (X s)).1
    let e₂ : H := (F (X s)).2 - (G (X s)).2
    have hstrong := hGstrong (X s) (Y s)
    have hstrong' : c * w s ≤
        inner ℝ (y₁ s) ((G (X s)).1 - (G (Y s)).1) +
          inner ℝ (y₂ s) ((G (X s)).2 - (G (Y s)).2) := by
      calc
        c * w s = c * (‖(X s).1 - (Y s).1‖ ^ 2 +
            ‖(X s).2 - (Y s).2‖ ^ 2) := by rfl
        _ ≤ inner ℝ ((G (X s)).1 - (G (Y s)).1) ((X s).1 - (Y s).1) +
            inner ℝ ((G (X s)).2 - (G (Y s)).2) ((X s).2 - (Y s).2) := hstrong
        _ = inner ℝ (y₁ s) ((G (X s)).1 - (G (Y s)).1) +
            inner ℝ (y₂ s) ((G (X s)).2 - (G (Y s)).2) := by
          dsimp [y₁, y₂]
          rw [real_inner_comm ((G (X s)).1 - (G (Y s)).1),
            real_inner_comm ((G (X s)).2 - (G (Y s)).2)]
    have hfixed :
        inner ℝ (y₁ s) (-((G (X s)).1 - (G (Y s)).1)) +
          inner ℝ (y₂ s) (-((G (X s)).2 - (G (Y s)).2)) ≤ -c * w s := by
      simp only [inner_neg_right]
      linarith
    have hfield : Real.sqrt (‖e₁‖ ^ 2 + ‖e₂‖ ^ 2) ≤ D := by
      simpa [e₁, e₂] using hFGs hs
    have hpair := two_pairing_le (y₁ s) (y₂ s) (-e₁) (-e₂)
    have hparam : inner ℝ (y₁ s) (-e₁) + inner ℝ (y₂ s) (-e₂) ≤
        D * Real.sqrt (w s) := by
      calc
        inner ℝ (y₁ s) (-e₁) + inner ℝ (y₂ s) (-e₂) ≤
            Real.sqrt (‖y₁ s‖ ^ 2 + ‖y₂ s‖ ^ 2) *
              Real.sqrt (‖-e₁‖ ^ 2 + ‖-e₂‖ ^ 2) := hpair
        _ ≤ Real.sqrt (w s) * D := by
          dsimp [w]
          gcongr
          simpa only [norm_neg] using hfield
        _ = D * Real.sqrt (w s) := by ring
    have hparam' : -inner ℝ (y₁ s) e₁ - inner ℝ (y₂ s) e₂ ≤
        D * Real.sqrt (w s) := by
      simpa only [inner_neg_right] using hparam
    have hd₁ : (-F (X s)).1 - (-G (Y s)).1 =
        -((G (X s)).1 - (G (Y s)).1) - e₁ := by
      dsimp [e₁]
      module
    have hd₂ : (-F (X s)).2 - (-G (Y s)).2 =
        -((G (X s)).2 - (G (Y s)).2) - e₂ := by
      dsimp [e₂]
      module
    have hderiv : deriv w s =
        2 * (inner ℝ (y₁ s) ((-F (X s)).1 - (-G (Y s)).1) +
          inner ℝ (y₂ s) ((-F (X s)).2 - (-G (Y s)).2)) := by
      rw [(hws hs).deriv]
      ring
    rw [hderiv, hd₁, hd₂]
    simp only [inner_sub_right]
    rw [← Real.sqrt_eq_rpow]
    nlinarith [hfixed, hparam']
  have hgronwall := ext_lem_1 (w := w) (a := fun _ : ℝ => -c)
    (b := fun _ : ℝ => D) (t₀ := 0) (T := T) (α := (1 / 2 : ℝ))
    hT (by norm_num) (by norm_num) (by simpa using hwac)
    (by intro s _; exact hw_nonneg s) (by simp) (by simp)
    (Filter.Eventually.of_forall fun _ _ => hD) (by simpa using hineq)
  have hgr := hgronwall t ht (by linarith)
  norm_num at hgr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hw0] at hgr
  have hkernel : (∫ s in 0..t, Real.exp (-((t - s) * c))) =
      c⁻¹ * (1 - Real.exp (-c * t)) := by
    calc
      (∫ s in 0..t, Real.exp (-((t - s) * c))) =
          ∫ s in 0..t, Real.exp (-c * (t - s)) * 1 := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with s _
            congr 1
            ring
      _ = c⁻¹ * (1 - Real.exp (-c * t)) * 1 :=
        exp_decay_kernel_integral c 1 t hc
      _ = c⁻¹ * (1 - Real.exp (-c * t)) := by ring
  rw [hkernel] at hgr
  have hfirst : ‖(X t).1 - (Y t).1‖ ≤ Real.sqrt (w t) := by
    apply Real.le_sqrt_of_sq_le
    dsimp [w, y₁, y₂]
    nlinarith [sq_nonneg ‖(X t).2 - (Y t).2‖]
  calc
    ‖(X t).1 - (Y t).1‖ ≤ Real.sqrt (w t) := hfirst
    _ ≤ Real.exp (-c * t) *
          Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
        c⁻¹ * (1 - Real.exp (-c * t)) * D := by
      calc
        Real.sqrt (w t) ≤
            Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) *
              Real.exp (-(t * c)) +
            c⁻¹ * (1 - Real.exp (-c * t)) * D := hgr
        _ = _ := by ring

/-- Removing the strong quadratic term leaves a convex function. -/
private theorem strongConvex_shift_convex {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] {f : K → ℝ} {δ : ℝ} (hsc : IsStronglyConvex f δ) :
    ConvexOn ℝ Set.univ (fun x => f x - δ / 2 * ‖x‖ ^ 2) := by
  constructor
  · exact convex_univ
  intro x _ y _ a b ha hb hab
  have hs := hsc.2 x y a ha (by linarith)
  have hb_eq : b = 1 - a := by linarith
  have hnorm : a * b * ‖x - y‖ ^ 2 + ‖a • x + b • y‖ ^ 2 =
      a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    simp only [real_inner_smul_left, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    rw [hb_eq]
    ring
  calc
    f (a • x + b • y) - δ / 2 * ‖a • x + b • y‖ ^ 2 ≤
        a * f x + b * f y - δ / 2 *
          (a * b * ‖x - y‖ ^ 2 + ‖a • x + b • y‖ ^ 2) := by
      rw [hb_eq]
      linarith
    _ = a * (f x - δ / 2 * ‖x‖ ^ 2) + b * (f y - δ / 2 * ‖y‖ ^ 2) := by
      rw [hnorm]
      ring

/-- First-order lower bound associated with strong convexity. -/
theorem strong_convex_gradient_gap {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] {f : K → ℝ} {g : K → K}
    {δ : ℝ} {z q : K} (hsc : IsStronglyConvex f δ)
    (hg : HasGradientAt f (g z) z) :
    f z - f q + δ / 2 * ‖z - q‖ ^ 2 ≤ inner ℝ (g z) (z - q) := by
  let h : K → ℝ := fun y => f y - δ / 2 * ‖y‖ ^ 2
  have hhconv : ConvexOn ℝ Set.univ h := strongConvex_shift_convex hsc
  have hline : ∀ v : K, HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    intro v
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := z)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;> simp
  have hdir : ∀ v : K, HasDerivAt (fun s : ℝ => h (z + s • v))
      (inner ℝ (g z - δ • z) v) 0 := by
    intro v
    have hg' : HasFDerivAt f (InnerProductSpace.toDual ℝ K (g z))
        ((fun s : ℝ => z + s • v) 0) := by
      simpa using hg.hasFDerivAt
    have hf := hg'.comp_hasDerivAt 0 (hline v)
    have hf' : HasDerivAt (fun s : ℝ => f (z + s • v)) (inner ℝ (g z) v) 0 := by
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hf
    have hq := (hline v).norm_sq
    change HasDerivAt (fun s : ℝ => f (z + s • v) - δ / 2 * ‖z + s • v‖ ^ 2)
      (inner ℝ (g z - δ • z) v) 0
    convert hf'.sub (HasDerivAt.const_mul (δ / 2) hq) using 1 <;>
      simp only [inner_sub_left, real_inner_smul_left, zero_smul, add_zero] <;> ring
  let line : ℝ →ᵃ[ℝ] K := AffineMap.lineMap z q
  have hlineconv : ConvexOn ℝ Set.univ (fun s : ℝ => h (z + s • (q - z))) := by
    simpa [line, Function.comp_def, AffineMap.lineMap_apply_module, sub_eq_add_neg,
      add_smul, one_smul, add_assoc, add_left_comm, add_comm] using hhconv.comp_affineMap line
  have hslope := hlineconv.le_slope_of_hasDerivAt (show (0 : ℝ) ∈ Set.univ by simp)
    (show (1 : ℝ) ∈ Set.univ by simp) zero_lt_one (hdir (q - z))
  rw [slope] at hslope
  norm_num [h, vsub_eq_sub, sub_eq_add_neg, add_smul] at hslope
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at hslope
  rw [inner_sub_right, norm_sub_sq_real]
  nlinarith

/-! ### The corrected strong-convexity constant of the energy

For `βγ > 1` the system (DIN) is equivalent to the gradient system
`Ẋ = -∇ε(X)` with `X = (x,z)` and `ε(x,z) = βφ(x) + ½‖√a x + √b z‖²`, where
`a = γ - 1/β` and `b = 1/β`.  The paper asserts that `ε` is `βδ`-strongly convex
in the product norm, hence that `∇ε` is `βδ`-strongly monotone.  That constant is
too large: the quadratic form of `ε` is the block matrix
`[[βδ + a, √(ab)], [√(ab), b]]`, whose smaller eigenvalue `energyRate β γ δ` is
strictly smaller than `βδ` as soon as `βγ > 1`.  The sharp statement is
`energyStrong_of_strongConvex` below. -/

/-- The sharp strong-monotonicity constant of `∇ε`: the smaller eigenvalue of
`[[βδ + (γ - 1/β), √((γ - 1/β)/β)], [√((γ - 1/β)/β), 1/β]]`. -/
noncomputable def energyRate (β γ δ : ℝ) : ℝ :=
  ((β * δ + γ) - Real.sqrt ((β * δ + γ) ^ 2 - 4 * δ)) / 2

/-- `energyRate` satisfies the characteristic equation of that matrix. -/
theorem energyRate_char {β γ δ : ℝ} (hδ : 0 < δ) (hβγ : 1 < β * γ) :
    energyRate β γ δ ^ 2 - (β * δ + γ) * energyRate β γ δ + δ = 0 := by
  have hT : 0 ≤ (β * δ + γ) ^ 2 - 4 * δ := by nlinarith [sq_nonneg (β * δ - γ)]
  have hsq : Real.sqrt ((β * δ + γ) ^ 2 - 4 * δ) ^ 2 = (β * δ + γ) ^ 2 - 4 * δ :=
    Real.sq_sqrt hT
  rw [energyRate]
  nlinarith [hsq]

/-- The energy rate is positive under the paper's assumptions. -/
theorem energyRate_pos {β γ δ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hβγ : 1 < β * γ) : 0 < energyRate β γ δ := by
  have hchar := energyRate_char hδ hβγ
  have hT : 0 < β * δ + γ := by positivity
  have hprod : energyRate β γ δ * (energyRate β γ δ - (β * δ + γ)) = -δ := by nlinarith [hchar]
  have hneg : energyRate β γ δ * (energyRate β γ δ - (β * δ + γ)) < 0 := by
    rw [hprod]
    linarith
  rcases mul_neg_iff.mp hneg with h | h
  · exact h.1
  · linarith [h.1, h.2, hT]

/-- Both diagonal entries of that matrix dominate `energyRate`. -/
theorem energyRate_le_diag {β γ δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hβγ : 1 < β * γ) :
    energyRate β γ δ ≤ β * δ + (γ - 1 / β) ∧ energyRate β γ δ ≤ 1 / β := by
  have hchar := energyRate_char hδ hβγ
  have hsq : 0 ≤ Real.sqrt ((β * δ + γ) ^ 2 - 4 * δ) := Real.sqrt_nonneg _
  have hsum : 0 ≤ (β * δ + (γ - 1 / β) - energyRate β γ δ) + (1 / β - energyRate β γ δ) := by
    have h : energyRate β γ δ = ((β * δ + γ) - Real.sqrt ((β * δ + γ) ^ 2 - 4 * δ)) / 2 := rfl
    linarith [hsq]
  have hβinv : β * (1 / β) = 1 := by field_simp
  have ha : 0 < γ - 1 / β := by
    have h1 : 1 / β < γ := by
      rw [div_lt_iff₀ hβ]
      linarith [hβγ]
    linarith
  have hb : 0 < 1 / β := by positivity
  have hprod : 0 ≤ (β * δ + (γ - 1 / β) - energyRate β γ δ) * (1 / β - energyRate β γ δ) := by
    have h : (β * δ + (γ - 1 / β) - energyRate β γ δ) * (1 / β - energyRate β γ δ) =
        (γ - 1 / β) * (1 / β) := by nlinarith [hchar, hβinv]
    rw [h]
    exact mul_nonneg ha.le hb.le
  rcases mul_nonneg_iff.mp hprod with h | h
  · exact ⟨sub_nonneg.mp h.1, sub_nonneg.mp h.2⟩
  · have hzero : (β * δ + (γ - 1 / β) - energyRate β γ δ) +
        (1 / β - energyRate β γ δ) = 0 := le_antisymm (by linarith [h.1, h.2]) hsum
    exact ⟨sub_nonneg.mp (by linarith [hzero, h.1]), sub_nonneg.mp (by linarith [hzero, h.2])⟩

/-- The scalar inequality behind `energyQuadraticBound`: for `p r ≥ 0`, `q ≥ 0`,
`p r - q² = D > 0` and `λ` the *smaller* root of `λ² - (p+r)λ + D = 0`, the
quadratic form `p x² - 2qxy + r y²` dominates `λ (x² + y²)`. -/
theorem scalar_quadratic_bound {p q r T D lam x y : ℝ} (hq : 0 ≤ q)
    (hpr : p * r - q ^ 2 = D) (hT : T = p + r) (hchar : lam ^ 2 - T * lam + D = 0)
    (hsmall : lam ≤ T / 2) :
    lam * (x ^ 2 + y ^ 2) ≤ p * x ^ 2 - 2 * q * x * y + r * y ^ 2 := by
  have hprod : (p - lam) * (r - lam) = q ^ 2 := by
    have hexp : (p - lam) * (r - lam) =
        (p * r - q ^ 2) + q ^ 2 + (lam ^ 2 - T * lam + D) - D := by
      rw [hT]
      ring
    rw [hexp, hpr, hchar]
    ring
  have hsum : 0 ≤ (p - lam) + (r - lam) := by
    have h : (p - lam) + (r - lam) = T - 2 * lam := by
      rw [hT]
      ring
    rw [h]
    linarith
  have hp0 : 0 ≤ p - lam := by
    rcases mul_nonneg_iff.mp (by rw [hprod]; positivity) with h | h
    · exact h.1
    · have hzero : (p - lam) + (r - lam) = 0 := le_antisymm (by linarith [h.1, h.2]) hsum
      linarith [h.1]
  have hr0 : 0 ≤ r - lam := by
    rcases mul_nonneg_iff.mp (by rw [hprod]; positivity) with h | h
    · exact h.2
    · have hzero : (p - lam) + (r - lam) = 0 := le_antisymm (by linarith [h.1, h.2]) hsum
      linarith [h.2]
  have hsq : 0 ≤ (Real.sqrt (p - lam) * x - Real.sqrt (r - lam) * y) ^ 2 := sq_nonneg _
  have hexpand : (Real.sqrt (p - lam) * x - Real.sqrt (r - lam) * y) ^ 2 =
      (p - lam) * x ^ 2 - 2 * Real.sqrt ((p - lam) * (r - lam)) * x * y +
        (r - lam) * y ^ 2 := by
    rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt hp0, Real.sq_sqrt hr0,
      Real.sqrt_mul hp0 (r - lam)]
    ring
  rw [hexpand, hprod, Real.sqrt_sq hq] at hsq
  nlinarith [hsq]

/-- **The corrected energy bound.**  The energy `ε(x,z) = βφ(x) + ½‖√a x + √b z‖²`
(`a = γ - 1/β`, `b = 1/β`) grows at least like `energyRate β γ δ` in the product
norm, instead of the `βδ` claimed in the paper. -/
theorem energyQuadraticBound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {β γ δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hβγ : 1 < β * γ) (u w : H) :
    energyRate β γ δ * (‖u‖ ^ 2 + ‖w‖ ^ 2) ≤
      β * δ * ‖u‖ ^ 2 + ‖Real.sqrt (γ - 1 / β) • u + Real.sqrt (1 / β) • w‖ ^ 2 := by
  have hβpos : (0 : ℝ) < β := hβ
  have ha : 0 < γ - 1 / β := by
    have h1 : 1 / β < γ := by
      rw [div_lt_iff₀ hβ]
      linarith [hβγ]
    linarith
  have hb : 0 < 1 / β := by positivity
  have hchar := energyRate_char hδ hβγ
  have hdiag := energyRate_le_diag hβ hδ hβγ
  have hcs : -(‖u‖ * ‖w‖) ≤ inner ℝ u w := by
    have h1 := abs_real_inner_le_norm u w
    have h2 := neg_abs_le (inner ℝ u w)
    linarith
  have hexpand : ‖Real.sqrt (γ - 1 / β) • u + Real.sqrt (1 / β) • w‖ ^ 2 =
      (γ - 1 / β) * ‖u‖ ^ 2 + 2 * Real.sqrt ((γ - 1 / β) * (1 / β)) * inner ℝ u w +
        (1 / β) * ‖w‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg (γ - 1 / β)),
      Real.norm_of_nonneg (Real.sqrt_nonneg (1 / β)), mul_pow, mul_pow,
      Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sqrt_mul ha.le (1 / β),
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hscalar := scalar_quadratic_bound (p := β * δ + (γ - 1 / β))
    (q := Real.sqrt ((γ - 1 / β) * (1 / β))) (r := 1 / β) (T := β * δ + γ) (D := δ)
    (lam := energyRate β γ δ) (x := ‖u‖) (y := ‖w‖) (Real.sqrt_nonneg _) (by
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (γ - 1 / β) * (1 / β))]
      field_simp
      ring) (by ring) hchar (by
      have hsq : 0 ≤ Real.sqrt ((β * δ + γ) ^ 2 - 4 * δ) := Real.sqrt_nonneg _
      have h : energyRate β γ δ = ((β * δ + γ) - Real.sqrt ((β * δ + γ) ^ 2 - 4 * δ)) / 2 :=
        rfl
      linarith)
  have hcs' : 2 * Real.sqrt ((γ - 1 / β) * (1 / β)) * (-(‖u‖ * ‖w‖)) ≤
      2 * Real.sqrt ((γ - 1 / β) * (1 / β)) * inner ℝ u w :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  rw [hexpand]
  nlinarith [hscalar, hcs']


/-- The gradient of a differentiable strongly convex function is strongly monotone. -/
theorem strongConvex_gradient_strongMonotone {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] {f : K → ℝ} {g : K → K}
    {δ : ℝ} (hsc : IsStronglyConvex f δ) (hg : ∀ z, HasGradientAt f (g z) z)
    (p q : K) : δ * ‖p - q‖ ^ 2 ≤ inner ℝ (g p - g q) (p - q) := by
  have hp := strong_convex_gradient_gap hsc (hg p) (q := q)
  have hq := strong_convex_gradient_gap hsc (hg q) (q := p)
  rw [show q - p = -(p - q) by module, inner_neg_right] at hq
  rw [norm_neg] at hq
  rw [inner_sub_left]
  nlinarith

/-- **The strong monotonicity of the energy field, with the sharp constant.**
  If `φ_μ` is `δ_μ`-strongly convex and differentiable, then the first-order
  reformulation field `∇ε_μ` is `energyRate β γ δ_μ`-strongly monotone in the
  product norm.  This is the corrected form of the paper's claim that the
  constant is `βδ_μ`. -/
theorem energyStrong_of_strongConvex {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {φ : M → H → ℝ} {gradφ : M → H → H} {β γ δ : ℝ} {μ : M}
    (hβ : 0 < β) (hβγ : 1 < β * γ)
    (hstrong : IsStronglyConvex (φ μ) δ)
    (hgrad : ∀ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (p q : H × H) :
    energyRate β γ δ * (‖p.1 - q.1‖ ^ 2 + ‖p.2 - q.2‖ ^ 2) ≤
      inner ℝ ((DINGradientField gradφ β γ μ p).1 - (DINGradientField gradφ β γ μ q).1) (p.1 - q.1) +
        inner ℝ ((DINGradientField gradφ β γ μ p).2 - (DINGradientField gradφ β γ μ q).2) (p.2 - q.2) := by
  obtain ⟨x, z⟩ := p
  obtain ⟨x', z'⟩ := q
  have hδ : 0 < δ := hstrong.1
  have hfst : (DINGradientField gradφ β γ μ (x, z)).1 -
      (DINGradientField gradφ β γ μ (x', z')).1 =
      β • (gradφ μ x - gradφ μ x') +
        Real.sqrt (γ - 1 / β) • (Real.sqrt (γ - 1 / β) • (x - x') + Real.sqrt (1 / β) • (z - z')) := by
    dsimp [DINGradientField]
    module
  have hsnd : (DINGradientField gradφ β γ μ (x, z)).2 -
      (DINGradientField gradφ β γ μ (x', z')).2 =
      Real.sqrt (1 / β) • (Real.sqrt (γ - 1 / β) • (x - x') + Real.sqrt (1 / β) • (z - z')) := by
    dsimp [DINGradientField]
    module
  rw [hfst, hsnd]
  have hinner : inner ℝ (β • (gradφ μ x - gradφ μ x') +
        Real.sqrt (γ - 1 / β) • (Real.sqrt (γ - 1 / β) • (x - x') + Real.sqrt (1 / β) • (z - z')))
        (x - x') +
      inner ℝ (Real.sqrt (1 / β) • (Real.sqrt (γ - 1 / β) • (x - x') + Real.sqrt (1 / β) • (z - z')))
        (z - z') =
      β * inner ℝ (gradφ μ x - gradφ μ x') (x - x') +
        ‖Real.sqrt (γ - 1 / β) • (x - x') + Real.sqrt (1 / β) • (z - z')‖ ^ 2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      ← real_inner_self_eq_norm_sq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    ring
  rw [hinner]
  have hmono := strongConvex_gradient_strongMonotone hstrong hgrad x x'
  have hquad := energyQuadraticBound hβ hδ hβγ (x - x') (z - z')
  have hmono' : β * (δ * ‖x - x'‖ ^ 2) ≤ β * inner ℝ (gradφ μ x - gradφ μ x') (x - x') :=
    mul_le_mul_of_nonneg_left hmono hβ.le
  nlinarith [hmono', hquad]

/-- Oriented comparison of two `DIN` trajectories in the first-order gradient
reformulation of Theorem 6.1, with an abstract discrepancy bound `D` for the two
gradient fields and the sharp energy rate `c` (see `energyStrong_of_strongConvex`).
The bound is only required along the first trajectory, which is what the
ball-localized estimate of Corollary 6.5 supplies. -/
theorem din_oriented_comparison {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup M]
    (gradφ : M → H → H) (x : M → ℝ → H) (u₀ v₀ : M → H) (β γ : ℝ) (c : M → ℝ)
    (a b : M) (hlift : DINGradientLift gradφ x u₀ v₀ β γ)
    (henergyStrong : ∀ (p q : H × H),
      c b * (‖p.1 - q.1‖ ^ 2 + ‖p.2 - q.2‖ ^ 2) ≤
        inner ℝ ((DINGradientField gradφ β γ b p).1 -
          (DINGradientField gradφ β γ b q).1) (p.1 - q.1) +
        inner ℝ ((DINGradientField gradφ β γ b p).2 -
          (DINGradientField gradφ β γ b q).2) (p.2 - q.2))
    (hcb : 0 < c b) (D : ℝ) (hD : 0 ≤ D)
    (T : ℝ) (hT : 0 < T)
    (hFG : ∀ᵐ t ∂ MeasureTheory.volume.restrict (Set.Icc 0 T),
      Real.sqrt (‖(DINGradientField gradφ β γ a (hlift.X a t)).1 -
          (DINGradientField gradφ β γ b (hlift.X a t)).1‖ ^ 2 +
        ‖(DINGradientField gradφ β γ a (hlift.X a t)).2 -
          (DINGradientField gradφ β γ b (hlift.X a t)).2‖ ^ 2) ≤ D) :
    ∀ t, 0 ≤ t → t ≤ T → ‖x a t - x b t‖ ≤
      Real.exp (-(c b) * t) *
          Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
            dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
        (c b)⁻¹ * (1 - Real.exp (-(c b) * t)) * D := by
  intro t ht htT
  have hraw := two_component_flow_estimate (hlift.X a) (hlift.X b)
    (DINGradientField gradφ β γ a) (DINGradientField gradφ β γ b)
    (u₀ a) (dinAuxInitial gradφ β γ u₀ v₀ a) (u₀ b) (dinAuxInitial gradφ β γ u₀ v₀ b)
    (c b) D T hcb hD hT
    (hlift.initial a) (hlift.initial b) (hlift.locally_ac a T hT) (hlift.locally_ac b T hT)
    (hlift.flow a T hT) (hlift.flow b T hT)
    (by intro p q; simpa using henergyStrong p q) hFG t ht htT
  rw [hlift.fst_eq a t, hlift.fst_eq b t] at hraw
  exact hraw

/-- The oriented form of the Theorem 6.1 estimate, with the sharp energy rate
`energyRate β γ (δ b)` and the true initial auxiliary coordinate `z₀`. -/
theorem thm_5_oriented {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (β γ : ℝ)
    (δ : M → ℝ) (k₁ γ₁ : ℝ)
    (hβγ : β * γ > 1)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (a b : M) : ∀ t, 0 ≤ t →
      ‖x a t - x b t‖ ≤
        Real.exp (-(energyRate β γ (δ b)) * t) *
            Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
              dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
          (β * k₁ / energyRate β γ (δ b)) *
            (1 - Real.exp (-(energyRate β γ (δ b)) * t)) * ‖a - b‖ ^ γ₁ := by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  intro t ht
  have hcb : 0 < energyRate β γ (δ b) := energyRate_pos hβ hγ (hstrong b).1 hβγ
  have hD : 0 ≤ β * k₁ * ‖a - b‖ ^ γ₁ := by positivity
  have hFG : ∀ᵐ s ∂ MeasureTheory.volume.restrict (Set.Icc 0 (t + 1)),
      Real.sqrt (‖(DINGradientField gradφ β γ a (hlift.X a s)).1 -
          (DINGradientField gradφ β γ b (hlift.X a s)).1‖ ^ 2 +
        ‖(DINGradientField gradφ β γ a (hlift.X a s)).2 -
          (DINGradientField gradφ β γ b (hlift.X a s)).2‖ ^ 2) ≤ β * k₁ * ‖a - b‖ ^ γ₁ := by
    filter_upwards with s
    have hfst : (DINGradientField gradφ β γ a (hlift.X a s)).1 -
        (DINGradientField gradφ β γ b (hlift.X a s)).1 =
        β • (gradφ a (hlift.X a s).1 - gradφ b (hlift.X a s).1) := by
      dsimp [DINGradientField]
      module
    have hsnd : (DINGradientField gradφ β γ a (hlift.X a s)).2 -
        (DINGradientField gradφ β γ b (hlift.X a s)).2 = 0 := by
      dsimp [DINGradientField]
      simp
    rw [hfst, hsnd, norm_zero, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), norm_smul,
      Real.norm_of_nonneg hβ.le]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left (h9 (hlift.X a s).1 a b) hβ.le
  have hraw := din_oriented_comparison gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ))
    a b hlift (fun p q => energyStrong_of_strongConvex hβ hβγ (hstrong b) (hgrad b) p q) hcb
    (β * k₁ * ‖a - b‖ ^ γ₁) hD (t + 1) (by linarith) hFG t ht (by linarith)
  calc
    ‖x a t - x b t‖ ≤
        Real.exp (-(energyRate β γ (δ b)) * t) *
          Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
            dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
        (energyRate β γ (δ b))⁻¹ * (1 - Real.exp (-(energyRate β γ (δ b)) * t)) *
          (β * k₁ * ‖a - b‖ ^ γ₁) := hraw
    _ = Real.exp (-(energyRate β γ (δ b)) * t) *
          Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
            dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
        (β * k₁ / energyRate β γ (δ b)) *
          (1 - Real.exp (-(energyRate β γ (δ b)) * t)) * ‖a - b‖ ^ γ₁ := by
      congr 1
      field_simp [hcb.ne']

/-- The Theorem 6.1 estimate in the symmetric form, with the sharp energy rate
`max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))`, valid at *every* `t ≥ 0`
(not only almost every `t`); this pointwise form is what the limit arguments in
Theorem 6.2 and Corollary 6.5 use. -/
theorem thm_5_estimate_all {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (β γ : ℝ)
    (δ : M → ℝ) (k₁ γ₁ : ℝ)
    (hβγ : β * γ > 1)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁) :
    ∀ μ μ' : M, let cmax := max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ∀ t, 0 ≤ t →
        ‖x μ t - x μ' t‖ ≤ Real.exp (-cmax * t) *
            Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
          (β * k₁ / cmax) * (1 - Real.exp (-cmax * t)) * ‖μ - μ'‖ ^ γ₁ := by
  intro μ μ'
  dsimp only
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  intro t ht
  by_cases hc : energyRate β γ (δ μ) ≤ energyRate β γ (δ μ')
  · simpa [max_eq_right hc] using
      thm_5_oriented φ gradφ hessφ x dx ddx u₀ v₀ β γ δ k₁ γ₁ hβγ hβ hγ hdiff hgrad
        hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 μ μ' t ht
  · have hc' : energyRate β γ (δ μ') ≤ energyRate β γ (δ μ) := le_of_not_ge hc
    simpa [max_eq_left hc', norm_sub_rev] using
      thm_5_oriented φ gradφ hessφ x dx ddx u₀ v₀ β γ δ k₁ γ₁ hβγ hβ hγ hdiff hgrad
        hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 μ' μ t ht

/-- **Theorem 6.1, corrected.** For each μ, let x_μ be the solution of DIN(φ,μ).
  Assume βγ>1, each φ(⋅,μ) is differentiable and δ_μ-strongly convex, and (9).
  Then the estimate (17) holds with the sharp energy rate
  `max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))` and the initial auxiliary
  coordinates `z₀^μ = -(v₀^μ + β∇φ_μ(u₀^μ) + (γ-1/β)u₀^μ)/√((γ-1/β)/β)`.

  Deviations from the paper: the paper claims the rate `βδ` and writes the
  initial-data term with `v₀^μ - v₀^{μ'}`; both are corrected here — the
  strong-monotonicity constant of `∇ε` is `energyRate β γ δ < βδ`, and the
  second coordinate of the change of variables starts at `z₀` (see
  `dinAuxInitial`), not at `v₀`. -/
theorem thm_5 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (β γ : ℝ)
    (δ : M → ℝ) (k₁ γ₁ : ℝ)
    (hβγ : β * γ > 1)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁) :
    ∀ μ μ' : M, let cmax := max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
        ‖x μ t - x μ' t‖ ≤ Real.exp (-cmax * t) *
            Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
          (β * k₁ / cmax) * (1 - Real.exp (-cmax * t)) * ‖μ - μ'‖ ^ γ₁ := by
  intro μ μ'
  filter_upwards [] with t
  intro ht
  exact thm_5_estimate_all φ gradφ hessφ x dx ddx u₀ v₀ β γ δ k₁ γ₁ hβγ hβ hγ hdiff
    hgrad hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 μ μ' t ht

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
