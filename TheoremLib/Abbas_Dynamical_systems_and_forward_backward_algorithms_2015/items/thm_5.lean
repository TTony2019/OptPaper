import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_7
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_6
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.def_5
import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Hilbert.WeakTopology
import Foundation.Convex.ProximalOperator
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open MeasureTheory Filter Gradient

private theorem proximal_gradient_classical_subgradient
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (x : ℝ → H) (mu : ℝ) (hmu : 0 < mu)
    (_hderiv : ∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t)
    (hdynamics : ∀ t, 0 ≤ t → deriv x t + x t -
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
        (x t - mu • B (x t)) = 0) :
    ∀ t, 0 ≤ t → -B (x t) - mu⁻¹ • deriv x t ∈
      ERealFunction.subdifferential Phi (x t + deriv x t) := by
  intro t ht
  have hres := ERealFunction.scaledProximityOperator_residual_mem hPhi ⟨mu, hmu⟩
    (x t - mu • B (x t))
  have hprox : ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
      (x t - mu • B (x t)) = x t + deriv x t := by
    calc
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
          (x t - mu • B (x t)) = deriv x t + x t := (sub_eq_zero.mp (hdynamics t ht)).symm
      _ = x t + deriv x t := by ac_rfl
  rw [hprox] at hres
  have hrewrite : (mu : ℝ)⁻¹ • ((x t - mu • B (x t)) - (x t + deriv x t)) =
      -B (x t) - mu⁻¹ • deriv x t := by
    rw [show (x t - mu • B (x t)) - (x t + deriv x t) =
      -(mu • B (x t)) - deriv x t by module]
    rw [smul_sub, smul_neg, smul_smul, inv_mul_cancel₀ hmu.ne', one_smul]
  rw [hrewrite] at hres
  exact hres

private theorem proximal_gradient_pointwise_lyapunov
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (x : ℝ → H) (mu : ℝ) (hmu : 0 < mu)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t)
    (hdynamics : ∀ t, 0 ≤ t → deriv x t + x t -
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
        (x t - mu • B (x t)) = 0) :
    ∀ z ∈ S, ∀ t, 0 ≤ t →
      deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t + mu⁻¹ * ‖deriv x t‖ ^ 2 +
        inner ℝ (B (x t) - B z) (x t - z) +
          inner ℝ (deriv x t) (B (x t) - B z) ≤ 0 := by
  intro z hz t ht
  have hmono := ERealFunction.isMonotone_subdifferential (fun y : H => (Phi y : EReal))
    (ERealFunction.isProper_of_mem_gammaZero hPhi)
    (-B (x t) - mu⁻¹ • deriv x t)
    (proximal_gradient_classical_subgradient Phi hPhi B x mu hmu hderiv hdynamics t ht)
    (-B z) ((hsolution z).mp hz)
  have hE : deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t =
      mu⁻¹ * inner ℝ (x t - z) (deriv x t) := by
    rw [(((hderiv t ht).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹)).deriv]
    field_simp [hmu.ne']
  rw [hE]
  have hident :
      mu⁻¹ * inner ℝ (x t - z) (deriv x t) + mu⁻¹ * ‖deriv x t‖ ^ 2 +
          inner ℝ (B (x t) - B z) (x t - z) +
            inner ℝ (deriv x t) (B (x t) - B z) =
        -inner ℝ ((-B (x t) - mu⁻¹ • deriv x t) - (-B z))
          ((x t + deriv x t) - z) := by
    rw [← real_inner_self_eq_norm_sq (deriv x t)]
    simp [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_right, real_inner_comm]
    ring
  rw [hident]
  linarith

private theorem proximal_gradient_cocoercive_lyapunov
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (x : ℝ → H) (mu beta : ℝ) (hmu : 0 < mu)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t)
    (hdynamics : ∀ t, 0 ≤ t → deriv x t + x t -
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
        (x t - mu • B (x t)) = 0) :
    ∀ z ∈ S, ∀ t, 0 ≤ t →
      deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t + mu⁻¹ * ‖deriv x t‖ ^ 2 +
        beta * ‖B (x t) - B z‖ ^ 2 +
          inner ℝ (deriv x t) (B (x t) - B z) ≤ 0 := by
  intro z hz t ht
  have hpre := proximal_gradient_pointwise_lyapunov Phi hPhi B S x mu hmu hsolution
    hderiv hdynamics z hz t ht
  have hcoco' : beta * ‖B (x t) - B z‖ ^ 2 ≤
      inner ℝ (B (x t) - B z) (x t - z) := by
    simpa only [real_inner_comm] using hB.ineq ⟨x t, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
  linarith

private theorem proximal_gradient_young_lyapunov
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (x : ℝ → H) (mu beta alpha : ℝ)
    (hmu : 0 < mu) (halpha : 0 < alpha)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t)
    (hdynamics : ∀ t, 0 ≤ t → deriv x t + x t -
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
        (x t - mu • B (x t)) = 0) :
    ∀ z ∈ S, ∀ t, 0 ≤ t →
      deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t +
          (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
          (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 ≤ 0 := by
  intro z hz t ht
  have hpre := proximal_gradient_cocoercive_lyapunov Phi hPhi B S x mu beta hmu hB
    hsolution hderiv hdynamics z hz t ht
  let dx : H := deriv x t
  let dB : H := B (x t) - B z
  have hsq : 0 ≤ ‖dx + alpha • dB‖ ^ 2 := sq_nonneg _
  have hsq' : -(‖dx‖ ^ 2) - alpha ^ 2 * ‖dB‖ ^ 2 ≤ 2 * alpha * inner ℝ dx dB := by
    dsimp [dx, dB] at hsq ⊢
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos halpha] at hsq
    nlinarith
  have hYoung : -(2 * alpha)⁻¹ * ‖dx‖ ^ 2 - alpha / 2 * ‖dB‖ ^ 2 ≤
      inner ℝ dx dB := by
    rw [show -(2 * alpha)⁻¹ * ‖dx‖ ^ 2 - alpha / 2 * ‖dB‖ ^ 2 =
      (-(‖dx‖ ^ 2) - alpha ^ 2 * ‖dB‖ ^ 2) / (2 * alpha) by
        field_simp [halpha.ne']]
    exact (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hsq')
  change deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t +
      (mu⁻¹ - (2 * alpha)⁻¹) * ‖dx‖ ^ 2 +
      (beta - alpha / 2) * ‖dB‖ ^ 2 ≤ 0
  change deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t + mu⁻¹ * ‖dx‖ ^ 2 +
      beta * ‖dB‖ ^ 2 + inner ℝ dx dB ≤ 0 at hpre
  linarith

private theorem gradient_bregman_energy_deriv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Psi : H → ℝ) (x : ℝ → H) (z : H) (t : ℝ)
    (hPsi_grad : ∀ y, HasGradientAt Psi (∇ Psi y) y)
    (hxt : HasDerivAt x (deriv x t) t) :
    deriv (fun s => Psi (x s) - inner ℝ (∇ Psi z) (x s - z)) t =
      inner ℝ (deriv x t) (∇ Psi (x t) - ∇ Psi z) := by
  have hcomp := ((hPsi_grad (x t)).hasFDerivAt.comp t hxt.hasFDerivAt).hasDerivAt
  have hcomp' : HasDerivAt (fun s => Psi (x s))
      (inner ℝ (∇ Psi (x t)) (deriv x t)) t := by
    simpa [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      real_inner_comm] using hcomp
  have hlin' : HasDerivAt (fun s => inner ℝ (∇ Psi z) (x s - z))
      (inner ℝ (∇ Psi z) (deriv x t)) t := by
    simpa using (hasDerivAt_const (x := t) (∇ Psi z)).inner ℝ (hxt.sub_const z)
  simpa [inner_sub_right, real_inner_comm] using (hcomp'.sub hlin').deriv

private theorem proximal_gradient_field_continuous
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu beta : ℝ) (hmu : 0 < mu)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w)) :
    Continuous (fun u => ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
      (u - mu • B u) - u) := by
  have hBcont : Continuous B := by
    change Continuous (fun u : H => (fun w : Set.univ => B w) ⟨u, Set.mem_univ u⟩)
    exact (lipschitzWith_of_cocoercive hB).continuous.comp
      (continuous_id.subtype_mk fun _ => Set.mem_univ _)
  have hprox : FirmlyNonexpansive
      (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩) := by
    unfold ERealFunction.scaledProximityOperator
    exact ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
      (ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, hmu⟩)
  exact ((lipschitzWith_one_of_firmlyNonexpansive hprox).continuous.comp
    (continuous_id.sub (continuous_const.smul hBcont))).sub continuous_id

private theorem proximal_gradient_field_lipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu beta : ℝ) (hmu : 0 < mu)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w)) :
    ∃ L : NNReal, LipschitzWith L (fun u =>
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ (u - mu • B u) - u) := by
  have hsub : LipschitzWith 1 (fun u : H => (⟨u, Set.mem_univ u⟩ : Set.univ)) :=
    LipschitzWith.id.subtype_mk fun _ => Set.mem_univ _
  have hBlip : LipschitzWith (1 / beta).toNNReal B := by
    simpa [Function.comp_def] using (lipschitzWith_of_cocoercive hB).comp hsub
  let K : NNReal := 1 + |mu|.toNNReal * (1 / beta).toNNReal
  have hforward : LipschitzWith K (fun u : H => u - mu • B u) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖(u - mu • B u) - (v - mu • B v)‖ = ‖(u - v) - mu • (B u - B v)‖ := by
        congr 1
        rw [smul_sub]
        module
      _ ≤ ‖u - v‖ + ‖mu • (B u - B v)‖ := norm_sub_le _ _
      _ = ‖u - v‖ + |mu| * ‖B u - B v‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖u - v‖ + |mu| * (((1 / beta).toNNReal : ℝ) * ‖u - v‖) := by
        gcongr
        exact hBlip.norm_sub_le u v
      _ = (K : ℝ) * ‖u - v‖ := by
        simp [K]
        ring
  have hprox : FirmlyNonexpansive
      (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩) := by
    unfold ERealFunction.scaledProximityOperator
    exact ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
      (ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, hmu⟩)
  refine ⟨1 * K + 1, ?_⟩
  simpa only [Function.comp_apply, one_mul] using
    ((lipschitzWith_one_of_firmlyNonexpansive hprox).comp hforward).sub LipschitzWith.id

private theorem cocoercive_uniformContinuous
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {beta : ℝ} {B : H → H}
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w)) :
    UniformContinuous B := by
  change UniformContinuous (fun u : H => (fun w : Set.univ => B w) ⟨u, Set.mem_univ u⟩)
  exact (lipschitzWith_of_cocoercive hB).uniformContinuous.comp
    (uniformContinuous_id.subtype_mk fun _ => Set.mem_univ _)

private theorem integrableOn_Ici_of_nonneg_interval_bound
    {g : ℝ → ℝ} {a C : ℝ}
    (hlocal : ∀ T, IntegrableOn g (Set.Ioc a T))
    (hnonneg : ∀ s, a ≤ s → 0 ≤ g s)
    (hbound : ∀ T, a ≤ T → ∫ s in a..T, g s ≤ C) :
    IntegrableOn g (Set.Ici a) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded C a hlocal
    Filter.tendsto_id
  filter_upwards [Filter.eventually_ge_atTop a] with T hT
  have hnorm : (∫ s in a..T, ‖g s‖) = ∫ s in a..T, g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le hT] at hs
    exact Real.norm_of_nonneg (hnonneg s hs.1.le)
  rw [hnorm]
  exact hbound T hT

private theorem integrable_components_of_sum_bound
    {A B : ℝ → ℝ} {a C : ℝ}
    (hAcont : Continuous A) (hBcont : Continuous B)
    (hA : ∀ t, a ≤ t → 0 ≤ A t) (hB : ∀ t, a ≤ t → 0 ≤ B t)
    (hsum : ∀ T, a ≤ T → ∫ t in a..T, (A t + B t) ≤ C) :
    IntegrableOn A (Set.Ici a) ∧ IntegrableOn B (Set.Ici a) := by
  constructor
  · apply integrableOn_Ici_of_nonneg_interval_bound (C := C)
      (fun T => hAcont.integrableOn_Ioc) hA
    intro T hT
    have hAint : IntervalIntegrable A volume a T := hAcont.continuousOn.intervalIntegrable
    calc
      (∫ t in a..T, A t) ≤ ∫ t in a..T, (A t + B t) := by
        apply intervalIntegral.integral_mono_on hT hAint
          (hAcont.add hBcont).continuousOn.intervalIntegrable
        intro t ht
        change A t ≤ A t + B t
        linarith [hB t ht.1]
      _ ≤ C := hsum T hT
  · apply integrableOn_Ici_of_nonneg_interval_bound (C := C)
      (fun T => hBcont.integrableOn_Ioc) hB
    intro T hT
    have hBint : IntervalIntegrable B volume a T := hBcont.continuousOn.intervalIntegrable
    calc
      (∫ t in a..T, B t) ≤ ∫ t in a..T, (A t + B t) := by
        apply intervalIntegral.integral_mono_on hT hBint
          (hAcont.add hBcont).continuousOn.intervalIntegrable
        intro t ht
        change B t ≤ A t + B t
        linarith [hA t ht.1]
      _ ≤ C := hsum T hT

/- The half-line Barbalat argument is kept local because it only bridges the
   Lyapunov estimates below to the asserted strong limits. -/
private theorem uniformContinuousOn_sq_integrable_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E)
    (huc : UniformContinuousOn f (Set.Ici 0))
    (hint : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Set.Ici 0)) :
    Tendsto f atTop (nhds 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  by_contra h
  rw [Metric.tendsto_atTop] at h
  push Not at h
  rcases h with ⟨ε, hε, hbad⟩
  have htail : Tendsto (fun n : ℕ => ∫ x in Set.Ici (n : ℝ), ‖f x‖ ^ 2)
      atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_setIntegral_of_antitone
      (f := fun x : ℝ => ‖f x‖ ^ 2) (fun n : ℕ => measurableSet_Ici)
      (fun m n hmn => Set.Ici_subset_Ici.mpr (Nat.cast_le.mpr hmn))
      ⟨0, hint.mono_set (Set.Ici_subset_Ici.mpr (by norm_num))⟩
    have hempty : (⋂ n : ℕ, Set.Ici (n : ℝ)) = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt x
        exact False.elim ((not_le_of_gt hn) (Set.mem_iInter.mp hx n))
      · simp
    simpa [hempty] using h
  have hδ := (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) (by linarith)
  rcases hδ with ⟨δ, hδ, hδprop⟩
  have hc : 0 < (ε / 2) ^ 2 * (δ / 2) := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htail) _ hc
  obtain ⟨u, huN, hubad⟩ := hbad (N : ℝ)
  have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg N) huN
  have hlow : ∀ x ∈ Set.Ioc u (u + δ / 2), (ε / 2) ^ 2 ≤ ‖f x‖ ^ 2 := by
    intro x hx
    have hxu : |x - u| < δ := by
      rw [abs_of_nonneg (le_of_lt (sub_pos.mpr hx.1))]
      linarith [hx.2, hδ]
    have hfx : dist (f x) (f u) < ε / 2 := by
      exact hδprop x (le_trans hu0 (le_of_lt hx.1)) u hu0
        (by simpa [Real.dist_eq] using hxu)
    have hub : ε ≤ ‖f u‖ := by simpa using hubad
    have htri : ‖f u‖ ≤ ‖f x‖ + ‖f x - f u‖ := by
      calc
        ‖f u‖ = ‖f x + (f u - f x)‖ := by congr 1; abel
        _ ≤ ‖f x‖ + ‖f u - f x‖ := norm_add_le _ _
        _ = ‖f x‖ + ‖f x - f u‖ := by rw [norm_sub_rev]
    have hnorm : ε / 2 < ‖f x‖ := by
      rw [dist_eq_norm] at hfx
      linarith
    nlinarith [norm_nonneg (f x)]
  have hint_lower : (ε / 2) ^ 2 * (δ / 2) ≤
      ∫ x in Set.Ioc u (u + δ / 2), ‖f x‖ ^ 2 := by
    calc
      (ε / 2) ^ 2 * (δ / 2) = ∫ x in Set.Ioc u (u + δ / 2), (ε / 2) ^ 2 := by
        rw [MeasureTheory.integral_const]
        simp [max_eq_left (by linarith : 0 ≤ δ / 2)]
        ring
      _ ≤ ∫ x in Set.Ioc u (u + δ / 2), ‖f x‖ ^ 2 := by
        apply MeasureTheory.integral_mono_ae
        · exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
        · exact hint.mono_set (by
            intro x hx
            exact le_trans hu0 (le_of_lt hx.1))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
          exact hlow x hx
  have hinter : Set.Ioc u (u + δ / 2) ⊆ Set.Ici (N : ℝ) := by
    intro x hx
    exact le_trans huN (le_of_lt hx.1)
  have hint_upper : ∫ x in Set.Ioc u (u + δ / 2), ‖f x‖ ^ 2 ≤
      ∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2 := by
    apply MeasureTheory.setIntegral_mono_set
    · exact hint.mono_set (Set.Ici_subset_Ici.mpr (Nat.cast_nonneg N))
    · filter_upwards with x
      exact sq_nonneg _
    · exact hinter.eventuallyLE
  have hN' := hN N le_rfl
  have htail_nonneg : 0 ≤ ∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2 := by
    apply MeasureTheory.integral_nonneg
    intro x
    exact sq_nonneg _
  change |(∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2) - 0| < _ at hN'
  simp only [sub_zero, abs_of_nonneg htail_nonneg] at hN'
  linarith

private theorem tendsto_of_antitone_nonneg_on_Ici (F : ℝ → ℝ)
    (hanti : AntitoneOn F (Set.Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ F t) :
    ∃ L, Tendsto F atTop (nhds L) := by
  let G : ℝ → ℝ := fun t => F (max t 0)
  have hGanti : Antitone G := by
    intro s t hst
    exact hanti (le_max_right s 0) (le_max_right t 0) (max_le_max_right 0 hst)
  have hGbelow : BddBelow (Set.range G) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hnonneg _ (le_max_right _ _)
  refine ⟨⨅ t, G t, ?_⟩
  apply (tendsto_atTop_ciInf hGanti hGbelow).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [G, max_eq_left ht]

/-- Theorem 5.2 for a classical solution of the proximal-gradient system (88). -/
theorem proximal_gradient_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (x : ℝ → H) (mu beta : ℝ)
    (hS : S.Nonempty) (hbeta : 0 < beta)
    (hmu : 0 < mu ∧ mu < 4 * beta)
    (hB_maximal_monotone : Maximal SetValuedOperator.IsMonotone B.toSetValuedOperator)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t)
    (hAC : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hdynamics : ∀ t, 0 ≤ t → deriv x t + x t -
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
        (x t - mu • B (x t)) = 0) :
    (∃ xinf ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H xinf))) ∧
    (∀ z ∈ S, Tendsto (fun t ↦ B (x t)) atTop (nhds (B z)) ∧
      IntegrableOn (fun t ↦ ‖B (x t) - B z‖ ^ 2) (Set.Ioi 0)) ∧
    Tendsto (deriv x) atTop (nhds 0) ∧
      IntegrableOn (fun t ↦ ‖deriv x t‖ ^ 2) (Set.Ioi 0) := by
  let alpha : ℝ := mu / 4 + beta
  have halpha : 0 < alpha := by
    dsimp [alpha]
    nlinarith [hmu.1, hbeta]
  have hdxcoef : 0 < mu⁻¹ - (2 * alpha)⁻¹ := by
    rw [show mu⁻¹ - (2 * alpha)⁻¹ = (2 * alpha - mu) / (mu * (2 * alpha)) by
      field_simp [hmu.1.ne', halpha.ne']]
    apply div_pos
    · dsimp [alpha]
      nlinarith [hmu.2]
    · exact mul_pos hmu.1 (mul_pos (by norm_num) halpha)
  have hBcoef : 0 < beta - alpha / 2 := by
    dsimp [alpha]
    nlinarith [hmu.2]
  have hlyap : ∀ z ∈ S, ∀ t, 0 ≤ t →
      deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t +
          (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
          (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 ≤ 0 := by
    exact proximal_gradient_young_lyapunov Phi hPhi B S x mu beta alpha hmu.1 halpha hB
      hsolution hderiv hdynamics
  have hfield_cont : Continuous (fun u =>
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩ (u - mu • B u) - u) :=
    proximal_gradient_field_continuous Phi hPhi B mu beta hmu.1 hB
  have hB_cont : Continuous B := by
    change Continuous (fun u : H => (fun w : Set.univ => B w) ⟨u, Set.mem_univ u⟩)
    exact (lipschitzWith_of_cocoercive hB).continuous.comp
      (continuous_id.subtype_mk fun _ => Set.mem_univ _)
  have hdx_eq : ∀ t, 0 ≤ t → deriv x t =
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
        (x t - mu • B (x t)) - x t := by
    intro t ht
    apply (eq_sub_iff_add_eq).mpr
    simpa [add_comm] using (sub_eq_zero.mp (hdynamics t ht))
  have hdx_continuous : ∀ T, 0 < T → ContinuousOn (deriv x) (Set.Icc 0 T) := by
    intro T hT
    have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
    have hcomp : ContinuousOn (fun t =>
        ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
          (x t - mu • B (x t)) - x t) (Set.Icc 0 T) := by
      simpa only [Function.comp_apply] using
        (hfield_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
    exact hcomp.congr fun t ht => hdx_eq t ht.1
  have hdiss_continuous : ∀ z : H, ∀ T, 0 < T → ContinuousOn (fun t =>
      (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
        (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) := by
    intro z T hT
    have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
    have hBx_cont : ContinuousOn (fun t => B (x t)) (Set.Icc 0 T) := by
      simpa only [Function.comp_apply] using
        (hB_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
    exact (continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2)).add
      (continuousOn_const.mul ((hBx_cont.sub continuousOn_const).norm.pow 2))
  have hfinite : ∀ z ∈ S, ∀ T, 0 < T →
      ∫ t in 0..T, (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
        (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 ≤
        (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2 := by
    intro z hz T hT
    have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
    have hD_cont : ContinuousOn (fun t =>
        (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
          (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      hdiss_continuous z T hT
    have hE_cont : ContinuousOn (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2)
        (Set.Icc 0 T) :=
      continuousOn_const.mul ((hx_cont.sub continuousOn_const).norm.pow 2)
    have hEderiv_eq : ∀ t ∈ Set.Icc 0 T,
        deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t =
          mu⁻¹ * inner ℝ (x t - z) (deriv x t) := by
      intro t ht
      rw [(((hderiv t ht.1).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹)).deriv]
      field_simp [hmu.1.ne']
    have hEderiv_cont : ContinuousOn
        (fun t => deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t) (Set.Icc 0 T) := by
      have hcont : ContinuousOn (fun t => mu⁻¹ * inner ℝ (x t - z) (deriv x t))
          (Set.Icc 0 T) :=
        continuousOn_const.mul ((hx_cont.sub continuousOn_const).inner (hdx_continuous T hT))
      exact hcont.congr fun t ht => hEderiv_eq t ht
    have hD_int : IntervalIntegrable (fun t =>
        (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
          (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2) volume 0 T :=
      hD_cont.intervalIntegrable_of_Icc (le_of_lt hT)
    have hderiv_int : IntervalIntegrable
        (fun t => -deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t) volume 0 T :=
      (hEderiv_cont.intervalIntegrable_of_Icc (le_of_lt hT)).neg
    have hpoint : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
          (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 ≤
          -deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      linarith [hlyap z hz t ht.1]
    have hint := intervalIntegral.integral_mono_ae_restrict (le_of_lt hT) hD_int hderiv_int hpoint
    calc
      ∫ t in 0..T, (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
          (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 ≤
          ∫ t in 0..T, -deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t := hint
      _ = -(∫ t in 0..T, deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t) := by
        rw [intervalIntegral.integral_neg]
      _ = -((2 * mu)⁻¹ * ‖x T - z‖ ^ 2 - (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hT) hE_cont]
        · intro t ht
          have hs := ((hderiv t ht.1.le).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹)
          simpa only [hs.deriv] using hs
        · exact hEderiv_cont.intervalIntegrable_of_Icc (le_of_lt hT)
      _ ≤ (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2 := by
        have hcoef : 0 ≤ (2 * mu)⁻¹ := by
          exact inv_nonneg.mpr (mul_nonneg (by norm_num) hmu.1.le)
        have : 0 ≤ (2 * mu)⁻¹ * ‖x T - z‖ ^ 2 :=
          mul_nonneg hcoef (sq_nonneg _)
        linarith
  have hdiss_integrable : ∀ z ∈ S, IntegrableOn (fun t =>
      (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
        (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2) (Set.Ici 0) := by
    intro z hz
    apply integrableOn_Ici_of_nonneg_interval_bound (C := (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2)
    · intro T
      by_cases hT : 0 < T
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
          ((hdiss_continuous z T hT).intervalIntegrable_of_Icc hT.le)
      · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
        exact integrableOn_empty
    · intro t ht
      exact add_nonneg
        (mul_nonneg hdxcoef.le (sq_nonneg _))
        (mul_nonneg hBcoef.le (sq_nonneg _))
    · intro T hT
      rcases hT.eq_or_lt with rfl | hT
      · simpa using (show 0 ≤ (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2 from
          mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hmu.1.le)) (sq_nonneg _))
      · exact hfinite z hz T hT
  have hdx_sq_integrable : ∀ z ∈ S,
      IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
    intro z hz
    have hscaled : IntegrableOn (fun t =>
        (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
      apply integrableOn_Ici_of_nonneg_interval_bound
        (C := (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2)
      · intro T
        by_cases hT : 0 < T
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
            ((continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le)
        · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
          exact integrableOn_empty
      · intro t ht
        exact mul_nonneg hdxcoef.le (sq_nonneg _)
      · intro T hT
        rcases hT.eq_or_lt with rfl | hT
        · simpa using (show 0 ≤ (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2 from
            mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hmu.1.le)) (sq_nonneg _))
        · have hAint : IntervalIntegrable (fun t =>
              (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2) volume 0 T :=
            (continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le
          have hDint : IntervalIntegrable (fun t =>
              (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
                (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2) volume 0 T :=
            (hdiss_continuous z T hT).intervalIntegrable_of_Icc hT.le
          calc
            ∫ t in 0..T, (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 ≤
                ∫ t in 0..T, (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
                  (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 := by
              apply intervalIntegral.integral_mono_on hT.le hAint hDint
              intro t ht
              exact le_add_of_nonneg_right (mul_nonneg hBcoef.le (sq_nonneg _))
            _ ≤ (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2 := hfinite z hz T hT
    change Integrable (fun t => ‖deriv x t‖ ^ 2) (volume.restrict (Set.Ici 0))
    have hres := hscaled.const_mul (mu⁻¹ - (2 * alpha)⁻¹)⁻¹
    change Integrable (fun t => (mu⁻¹ - (2 * alpha)⁻¹)⁻¹ *
      ((mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2)) (volume.restrict (Set.Ici 0)) at hres
    convert hres using 1
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ hdxcoef.ne', one_mul]
  have hB_sq_integrable : ∀ z ∈ S,
      IntegrableOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Ici 0) := by
    intro z hz
    have hscaled : IntegrableOn (fun t =>
        (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2) (Set.Ici 0) := by
      apply integrableOn_Ici_of_nonneg_interval_bound
        (C := (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2)
      · intro T
        by_cases hT : 0 < T
        · have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
            simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
          have hBx_cont : ContinuousOn (fun t => B (x t)) (Set.Icc 0 T) := by
            simpa only [Function.comp_apply] using
              (hB_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
            ((continuousOn_const.mul ((hBx_cont.sub continuousOn_const).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le)
        · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
          exact integrableOn_empty
      · intro t ht
        exact mul_nonneg hBcoef.le (sq_nonneg _)
      · intro T hT
        rcases hT.eq_or_lt with rfl | hT
        · simpa using (show 0 ≤ (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2 from
            mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hmu.1.le)) (sq_nonneg _))
        · have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
            simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
          have hBx_cont : ContinuousOn (fun t => B (x t)) (Set.Icc 0 T) := by
            simpa only [Function.comp_apply] using
              (hB_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
          have hAint : IntervalIntegrable (fun t =>
              (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2) volume 0 T :=
            (continuousOn_const.mul ((hBx_cont.sub continuousOn_const).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le
          have hDint : IntervalIntegrable (fun t =>
              (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
                (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2) volume 0 T :=
            (hdiss_continuous z T hT).intervalIntegrable_of_Icc hT.le
          calc
            ∫ t in 0..T, (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 ≤
                ∫ t in 0..T, (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 +
                  (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 := by
              apply intervalIntegral.integral_mono_on hT.le hAint hDint
              intro t ht
              exact le_add_of_nonneg_left (mul_nonneg hdxcoef.le (sq_nonneg _))
            _ ≤ (2 * mu)⁻¹ * ‖x 0 - z‖ ^ 2 := hfinite z hz T hT
    change Integrable (fun t => ‖B (x t) - B z‖ ^ 2) (volume.restrict (Set.Ici 0))
    have hres := hscaled.const_mul (beta - alpha / 2)⁻¹
    change Integrable (fun t => (beta - alpha / 2)⁻¹ *
      ((beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2)) (volume.restrict (Set.Ici 0)) at hres
    convert hres using 1
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ hBcoef.ne', one_mul]
  have henergy_antitone : ∀ z ∈ S,
      AntitoneOn (fun t => (2 * mu)⁻¹ * ‖x t - z‖ ^ 2) (Set.Ici 0) := by
    intro z hz
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (((hderiv t ht).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹))
        |>.continuousAt.continuousWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      exact (((hderiv t ht0).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹))
        |>.differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      have h := hlyap z hz t ht0
      have hdxnonneg : 0 ≤ (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 :=
        mul_nonneg hdxcoef.le (sq_nonneg _)
      have hBnonneg : 0 ≤ (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 :=
        mul_nonneg hBcoef.le (sq_nonneg _)
      linarith
  have hnorm_bound : ∀ z ∈ S, ∀ t, 0 ≤ t → ‖x t - z‖ ≤ ‖x 0 - z‖ := by
    intro z hz t ht
    have h := henergy_antitone z hz (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hcoef : 0 < (2 * mu)⁻¹ :=
      inv_pos.mpr (mul_pos (by norm_num) hmu.1)
    have hsq : ‖x t - z‖ ^ 2 ≤ ‖x 0 - z‖ ^ 2 := by
      exact le_of_mul_le_mul_left h hcoef
    nlinarith [norm_nonneg (x t - z), norm_nonneg (x 0 - z)]
  have hdist : ∀ z ∈ S, ∃ l : ℝ,
      Tendsto (fun t => ‖x t - z‖) atTop (nhds l) := by
    intro z hz
    let E : ℝ → ℝ := fun t => (2 * mu)⁻¹ * ‖x t - z‖ ^ 2
    have hEanti : AntitoneOn E (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · intro t ht
        simpa [E] using
          (((hderiv t ht).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹))
            |>.continuousAt.continuousWithinAt
      · intro t ht
        have ht0 : 0 ≤ t := interior_subset ht
        simpa [E] using
          (((hderiv t ht0).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹))
            |>.differentiableAt.differentiableWithinAt
      · intro t ht
        have ht0 : 0 ≤ t := interior_subset ht
        have h := hlyap z hz t ht0
        have hdxnonneg : 0 ≤ (mu⁻¹ - (2 * alpha)⁻¹) * ‖deriv x t‖ ^ 2 :=
          mul_nonneg hdxcoef.le (sq_nonneg _)
        have hBnonneg : 0 ≤ (beta - alpha / 2) * ‖B (x t) - B z‖ ^ 2 :=
          mul_nonneg hBcoef.le (sq_nonneg _)
        simpa [E] using (show deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t ≤ 0 by
          linarith)
    have hEnonneg : ∀ t, 0 ≤ t → 0 ≤ E t := by
      intro t ht
      dsimp [E]
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hmu.1.le)) (sq_nonneg _)
    obtain ⟨L, hL⟩ := tendsto_of_antitone_nonneg_on_Ici E hEanti hEnonneg
    refine ⟨Real.sqrt (2 * mu * L), ?_⟩
    have hsqrt := (Real.continuous_sqrt.tendsto (2 * mu * L)).comp (hL.const_mul (2 * mu))
    have heq : (fun t => ‖x t - z‖) = fun t => Real.sqrt (2 * mu * E t) := by
      funext t
      have hident : 2 * mu * E t = ‖x t - z‖ ^ 2 := by
        dsimp [E]
        field_simp [hmu.1.ne']
      rw [hident, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [heq]
    simpa only [Function.comp_def] using hsqrt
  rcases hS with ⟨z0, hz0⟩
  obtain ⟨L, hfield_lip⟩ := proximal_gradient_field_lipschitz Phi hPhi B mu beta hmu.1 hB
  let V : H → H := fun u =>
    ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩ (u - mu • B u) - u
  let K : NNReal := ‖V z0‖₊ + L * ‖x 0 - z0‖₊
  have hdx_bound : ∀ t, 0 ≤ t → ‖deriv x t‖ ≤ K := by
    intro t ht
    rw [hdx_eq t ht]
    change ‖V (x t)‖ ≤ K
    calc
      ‖V (x t)‖ = ‖(V (x t) - V z0) + V z0‖ := by congr 1; abel
      _ ≤ ‖V (x t) - V z0‖ + ‖V z0‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖x t - z0‖ + ‖V z0‖ := by
        gcongr
        simpa [V] using hfield_lip.norm_sub_le (x t) z0
      _ ≤ (L : ℝ) * ‖x 0 - z0‖ + ‖V z0‖ := by
        gcongr
        exact hnorm_bound z0 hz0 t ht
      _ = K := by simp [K]; ring
  have hx_lip : LipschitzOnWith K x (Set.Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (hderiv t ht).differentiableAt
    · intro t ht
      apply NNReal.coe_le_coe.mpr
      exact hdx_bound t ht
  have hB_uc : UniformContinuous B := by
    change UniformContinuous (fun u : H => (fun w : Set.univ => B w) ⟨u, Set.mem_univ u⟩)
    exact (lipschitzWith_of_cocoercive hB).uniformContinuous.comp
      (uniformContinuous_id.subtype_mk fun _ => Set.mem_univ _)
  have hBres_uc : UniformContinuousOn (fun t => B (x t) - B z0) (Set.Ici 0) := by
    simpa only [Function.comp_def] using
      (uniformContinuous_id.sub uniformContinuous_const).comp_uniformContinuousOn
        (hB_uc.comp_uniformContinuousOn hx_lip.uniformContinuousOn)
  have hBzero : Tendsto (fun t => B (x t) - B z0) atTop (nhds 0) :=
    uniformContinuousOn_sq_integrable_tendsto_zero _ hBres_uc (hB_sq_integrable z0 hz0)
  have hBlim : Tendsto (fun t => B (x t)) atTop (nhds (B z0)) := by
    have h := hBzero.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => B z0) atTop (nhds (B z0)))
    simpa only [sub_add_cancel, zero_add] using h
  have hVuc : UniformContinuousOn (fun t : ℝ => V (x t)) (Set.Ici 0) := by
    exact (by simpa [V] using hfield_lip : LipschitzWith L V)
      |>.uniformContinuous.comp_uniformContinuousOn hx_lip.uniformContinuousOn
  have hdx_uc : UniformContinuousOn (deriv x) (Set.Ici 0) := by
    apply hVuc.congr
    intro t ht
    exact (hdx_eq t ht).symm
  have hdxzero : Tendsto (deriv x) atTop (nhds 0) :=
    uniformContinuousOn_sq_integrable_tendsto_zero _ hdx_uc (hdx_sq_integrable z0 hz0)
  have hBstrong : ∀ z ∈ S, Tendsto (fun t => B (x t)) atTop (nhds (B z)) ∧
      IntegrableOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Ioi 0) := by
    intro z hz
    have hres_uc : UniformContinuousOn (fun t => B (x t) - B z) (Set.Ici 0) := by
      simpa only [Function.comp_def] using
        (uniformContinuous_id.sub uniformContinuous_const).comp_uniformContinuousOn
          (hB_uc.comp_uniformContinuousOn hx_lip.uniformContinuousOn)
    have hzero : Tendsto (fun t => B (x t) - B z) atTop (nhds 0) :=
      uniformContinuousOn_sq_integrable_tendsto_zero _ hres_uc (hB_sq_integrable z hz)
    constructor
    · have h := hzero.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => B z) atTop (nhds (B z)))
      simpa only [sub_add_cancel, zero_add] using h
    · exact (integrableOn_Ici_iff_integrableOn_Ioi).mp (hB_sq_integrable z hz)
  have hdx_integrable : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ioi 0) := by
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mp (hdx_sq_integrable z0 hz0)
  refine ⟨?_, hBstrong, hdxzero, hdx_integrable⟩
  have hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n => f (x (u n))) atTop (nhds (f z))) → z ∈ S := by
    intro zbar hz
    rcases hz with ⟨u, hu, hfun⟩
    have hweak : Tendsto (fun n => toWeakSpace ℝ H (x (u n))) atTop
        (nhds (toWeakSpace ℝ H zbar)) := by
      refine (weakConvergence_iff_forall_tendsto_inner_right (fun n => x (u n)) zbar).2 ?_
      intro v
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        hfun (InnerProductSpace.toDual ℝ H v)
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hu.eventually (eventually_ge_atTop (0 : ℝ)))
    have hweak_shift : Tendsto (fun n => toWeakSpace ℝ H (x (u (n + N)))) atTop
        (nhds (toWeakSpace ℝ H zbar)) := by
      simpa only [Function.comp_def] using hweak.comp (Filter.tendsto_add_atTop_nat N)
    have hB_shift : Tendsto (fun n => B (x (u (n + N)))) atTop (nhds (B z0)) := by
      simpa only [Function.comp_def] using hBlim.comp hu |>.comp (Filter.tendsto_add_atTop_nat N)
    have hdx_shift : Tendsto (fun n => deriv x (u (n + N))) atTop (nhds 0) := by
      simpa only [Function.comp_def] using hdxzero.comp hu |>.comp (Filter.tendsto_add_atTop_nat N)
    have hy : Tendsto (fun n => toWeakSpace ℝ H
        (x (u (n + N)) + deriv x (u (n + N)))) atTop
        (nhds (toWeakSpace ℝ H zbar)) := by
      refine (weakConvergence_iff_forall_tendsto_inner_right _ zbar).2 ?_
      intro v
      have hweak_inner :=
        (weakConvergence_iff_forall_tendsto_inner_right _ zbar).1 hweak_shift v
      have hdx_inner : Tendsto (fun n => inner ℝ (deriv x (u (n + N))) v) atTop
          (nhds (inner ℝ (0 : H) v)) :=
        hdx_shift.inner (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (nhds v))
      simpa only [inner_add_left, inner_zero_left, add_zero] using hweak_inner.add hdx_inner
    have hq : Tendsto (fun n =>
        -B (x (u (n + N))) - mu⁻¹ • deriv x (u (n + N))) atTop (nhds (-B z0)) := by
      have hsmul : Tendsto (fun n => (mu⁻¹ : ℝ) • deriv x (u (n + N))) atTop (nhds 0) := by
        simpa using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (mu⁻¹ : ℝ)) atTop (nhds mu⁻¹)).smul hdx_shift
      have hsum := hB_shift.neg.sub hsmul
      simpa using hsum
    have hsub : -B z0 ∈ ERealFunction.subdifferential Phi zbar := by
      apply maximal_monotone_graph_weak_strong_closed (ERealFunction.subdifferential Phi)
        (ERealFunction.subdifferential_isMaximalMonotone_of_mem_gammaZero hPhi)
        (fun n => x (u (n + N)) + deriv x (u (n + N)))
        (fun n => -B (x (u (n + N))) - mu⁻¹ • deriv x (u (n + N))) zbar (-B z0) hy hq
      intro n
      apply proximal_gradient_classical_subgradient Phi hPhi B x mu hmu.1 hderiv hdynamics
      exact hN (n + N) (Nat.le_add_left _ _)
    have hBmax : B.toSetValuedOperator.IsMaximalMonotone :=
      (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone B.toSetValuedOperator).mpr
        hB_maximal_monotone
    have hBmem : B z0 ∈ B.toSetValuedOperator zbar := by
      apply maximal_monotone_graph_weak_strong_closed B.toSetValuedOperator hBmax
        (fun n => x (u (n + N))) (fun n => B (x (u (n + N)))) zbar (B z0)
        hweak_shift hB_shift
      intro n
      simp
    have hBeq : B zbar = B z0 := by
      have hBeq' : B z0 = B zbar := by
        simpa [Function.toSetValuedOperator_apply] using hBmem
      exact hBeq'.symm
    exact (hsolution zbar).mpr (by simpa [hBeq] using hsub)
  obtain ⟨xinf, hxinfS, hfun⟩ :=
    _root_.opial_lemma_continuous_weak x S ⟨z0, hz0⟩ hdist hcluster
  refine ⟨xinf, hxinfS, ?_⟩
  refine (weakConvergence_iff_forall_tendsto_inner_right x xinf).2 ?_
  intro v
  simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    hfun (InnerProductSpace.toDual ℝ H v)

private theorem inner_tendsto_zero_of_strong_left_of_bounded_right_local
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℕ → H} (ha : Tendsto a atTop (nhds 0))
    (hb : Bornology.IsBounded (Set.range b)) :
    Tendsto (fun n => inner ℝ (a n) (b n)) atTop (nhds 0) := by
  rcases (isBounded_iff_forall_norm_le (s := Set.range b)).mp hb with ⟨C, hC⟩
  let M : ℝ := max C 0
  have hM (n : ℕ) : ‖b n‖ ≤ M :=
    (hC (b n) ⟨n, rfl⟩).trans (le_max_left _ _)
  have hbound (n : ℕ) : |inner ℝ (a n) (b n)| ≤ ‖a n‖ * M := by
    calc
      |inner ℝ (a n) (b n)| ≤ ‖a n‖ * ‖b n‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (a n) (b n)
      _ ≤ ‖a n‖ * M := mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _)
  have hanorm : Tendsto (fun n => ‖a n‖) atTop (nhds 0) := by
    simpa using ha.norm
  have hprod : Tendsto (fun n => ‖a n‖ * M) atTop (nhds 0) := by
    simpa using hanorm.mul tendsto_const_nhds
  have habs : Tendsto (fun n => |inner ℝ (a n) (b n)|) atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hbound hprod
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using habs.neg) habs
    (fun n => neg_abs_le _) (fun n => le_abs_self _)

private theorem cocoercive_weak_strong_closed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {beta : ℝ} {B : H → H} (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (u : ℕ → H) (x0 b0 : H)
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop
      (nhds (toWeakSpace ℝ H x0)))
    (hBu : Tendsto (fun n ↦ B (u n)) atTop (nhds b0)) : B x0 = b0 := by
  have hubdd : Bornology.IsBounded (Set.range u) := bounded_range_of_tendsto_weakly hu
  have hstrong : Tendsto (fun n => B (u n) - b0) atTop (nhds 0) := by
    simpa using hBu.sub (tendsto_const_nhds (x := b0))
  have hfirst : Tendsto (fun n => inner ℝ (B (u n) - b0) (u n - x0)) atTop
      (nhds 0) := by
    apply inner_tendsto_zero_of_strong_left_of_bounded_right_local hstrong
    exact (hubdd.sub Bornology.isBounded_singleton).subset (by
      rintro q ⟨n, rfl⟩
      exact Set.sub_mem_sub ⟨n, rfl⟩ (Set.mem_singleton x0))
  let d : H := b0 - B x0
  have hcoord := (weakConvergence_iff_forall_tendsto_inner_right (𝓗 := H) u x0).1 hu d
  have hsecond : Tendsto (fun n => inner ℝ d (u n - x0)) atTop (nhds 0) := by
    have h := hcoord.sub (tendsto_const_nhds (x := inner ℝ x0 d))
    simpa [d, inner_sub_right, real_inner_comm, sub_self] using h
  have hcross : Tendsto (fun n => inner ℝ (B (u n) - B x0) (u n - x0)) atTop
      (nhds 0) := by
    have hsum := hfirst.add hsecond
    convert hsum using 1
    · ext n
      dsimp [d]
      rw [← inner_add_left]
      congr 1
      abel
    · simp
  have hleft : Tendsto (fun n => beta * ‖B (u n) - B x0‖ ^ 2) atTop
      (nhds (beta * ‖b0 - B x0‖ ^ 2)) := by
    simpa using (hBu.sub tendsto_const_nhds).norm.pow 2 |>.const_mul beta
  have hineq : ∀ n, beta * ‖B (u n) - B x0‖ ^ 2 ≤
      inner ℝ (B (u n) - B x0) (u n - x0) := by
    intro n
    simpa [real_inner_comm] using hB.ineq ⟨u n, Set.mem_univ _⟩ ⟨x0, Set.mem_univ _⟩
  have hzero : beta * ‖b0 - B x0‖ ^ 2 = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto hleft hcross (Filter.Eventually.of_forall hineq)
    · exact mul_nonneg hbeta.le (sq_nonneg _)
  have hd : b0 - B x0 = 0 := by
    apply (norm_eq_zero).mp
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left hbeta.ne')
  exact (sub_eq_zero.mp hd).symm

private theorem tendsto_of_tendsto_add_nat_local
    {X : Type*} [TopologicalSpace X] {f : ℕ → X} {a : X} (N : ℕ)
    (h : Tendsto (fun n ↦ f (n + N)) atTop (nhds a)) : Tendsto f atTop (nhds a) := by
  rw [Filter.tendsto_def]
  intro s hs
  rcases eventually_atTop.1 (h.eventually hs) with ⟨M, hM⟩
  filter_upwards [eventually_ge_atTop (M + N)] with n hn
  let k := n - N
  have hk : M ≤ k := by dsimp [k]; omega
  have hkn : k + N = n := by dsimp [k]; omega
  rw [← hkn]
  exact hM k hk

private theorem real_tendsto_atTop_of_all_divergent_sequences_local {f : ℝ → ℝ} {a : ℝ}
    (h : ∀ t : ℕ → ℝ, Tendsto t atTop atTop → Tendsto (f ∘ t) atTop (nhds a)) :
    Tendsto f atTop (nhds a) := by
  by_contra hf
  rw [Metric.tendsto_atTop] at hf
  push Not at hf
  rcases hf with ⟨eps, heps, hbad⟩
  choose s hs_ge hs_bad using hbad
  let t : ℕ → ℝ := fun n ↦ s n
  have ht : Tendsto t atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro R
    obtain ⟨N, hN⟩ := exists_nat_ge R
    refine ⟨N, fun n hn ↦ le_trans (le_trans hN (Nat.cast_le.2 hn)) (hs_ge n)⟩
  have hconv := h t ht
  rw [Metric.tendsto_atTop] at hconv
  rcases hconv eps heps with ⟨N, hN⟩
  exact (not_lt_of_ge (hs_bad N)) (by simpa [Function.comp, t] using hN N le_rfl)

/-- In the gradient case the same conclusions hold for every positive `mu`. -/
theorem proximal_gradient_gradient_case {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (Psi : H → ℝ)
    (S : Set H) (x : ℝ → H) (mu beta : ℝ)
    (hPsi_convex : ConvexOn ℝ Set.univ Psi)
    (hPsi_grad : ∀ z, HasGradientAt Psi (∇ Psi z) z) (hS : S.Nonempty)
    (hbeta : 0 < beta) (hmu : 0 < mu)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ ∇ Psi w))
    (hsolution : ∀ z, z ∈ S ↔ -∇ Psi z ∈ ERealFunction.subdifferential Phi z)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t)
    (hAC : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hdynamics : ∀ t, 0 ≤ t → deriv x t + x t -
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
        (x t - mu • ∇ Psi (x t)) = 0) :
    (∃ xinf ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H xinf))) ∧
    (∀ z ∈ S, Tendsto (fun t ↦ ∇ Psi (x t)) atTop (nhds (∇ Psi z)) ∧
      IntegrableOn (fun t ↦ ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (Set.Ioi 0)) ∧
    Tendsto (deriv x) atTop (nhds 0) := by
  have hlyap_base : ∀ z ∈ S, ∀ t, 0 ≤ t →
      deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t + mu⁻¹ * ‖deriv x t‖ ^ 2 +
        beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 +
          inner ℝ (deriv x t) (∇ Psi (x t) - ∇ Psi z) ≤ 0 := by
    exact proximal_gradient_cocoercive_lyapunov Phi hPhi (fun y => ∇ Psi y) S x mu beta hmu
      hB hsolution hderiv hdynamics
  let E : H → ℝ → ℝ := fun z t =>
    (2 * mu)⁻¹ * ‖x t - z‖ ^ 2 +
      (Psi (x t) - inner ℝ (∇ Psi z) (x t - z) - Psi z)
  have hE_nonneg : ∀ z : H, ∀ t : ℝ, 0 ≤ E z t := by
    intro z t
    have hsupport := convex_supporting_baillon_haddad Psi (fun y => ∇ Psi y)
      hPsi_convex hPsi_grad z (x t)
    have hquad : 0 ≤ (2 * mu)⁻¹ * ‖x t - z‖ ^ 2 := by
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hmu.le)) (sq_nonneg _)
    dsimp [E]
    linarith
  have hE_hasDeriv : ∀ z : H, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (E z)
        (mu⁻¹ * inner ℝ (x t - z) (deriv x t) +
          inner ℝ (deriv x t) (∇ Psi (x t) - ∇ Psi z)) t := by
    intro z t ht
    have hcomp := ((hPsi_grad (x t)).hasFDerivAt.comp t (hderiv t ht).hasFDerivAt).hasDerivAt
    have hcomp' : HasDerivAt (fun s => Psi (x s))
        (inner ℝ (∇ Psi (x t)) (deriv x t)) t := by
      simpa [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
        real_inner_comm] using hcomp
    have hlin' : HasDerivAt (fun s => inner ℝ (∇ Psi z) (x s - z))
        (inner ℝ (∇ Psi z) (deriv x t)) t := by
      simpa using (hasDerivAt_const (x := t) (∇ Psi z)).inner ℝ ((hderiv t ht).sub_const z)
    convert (((hderiv t ht).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹)).add
        ((hcomp'.sub hlin').sub_const (Psi z)) using 1
    simp [inner_sub_right, real_inner_comm]; ring
  have hlyap : ∀ z ∈ S, ∀ t, 0 ≤ t →
      deriv (E z) t + mu⁻¹ * ‖deriv x t‖ ^ 2 +
        beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤ 0 := by
    intro z hz t ht
    rw [(hE_hasDeriv z t ht).deriv]
    have hquad : deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t =
        mu⁻¹ * inner ℝ (x t - z) (deriv x t) := by
      rw [(((hderiv t ht).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹)).deriv]
      field_simp [hmu.ne']
    have hbase := hlyap_base z hz t ht
    rw [hquad] at hbase
    linarith
  have hE_antitone : ∀ z ∈ S, AntitoneOn (E z) (Set.Ici 0) := by
    intro z hz
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (hE_hasDeriv z t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      exact (hE_hasDeriv z t ht0).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      have h := hlyap z hz t ht0
      have hdxnonneg : 0 ≤ mu⁻¹ * ‖deriv x t‖ ^ 2 := by
        exact mul_nonneg (inv_nonneg.mpr hmu.le) (sq_nonneg _)
      have hgradnonneg : 0 ≤ beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 :=
        mul_nonneg hbeta.le (sq_nonneg _)
      linarith
  have hE_limit : ∀ z ∈ S, ∃ l : ℝ, Tendsto (E z) atTop (nhds l) := by
    intro z hz
    exact tendsto_of_antitone_nonneg_on_Ici (E z) (hE_antitone z hz)
      (fun t ht => hE_nonneg z t)
  have hgrad_cont : Continuous (∇ Psi) := by
    change Continuous (fun u : H => (fun w : Set.univ => ∇ Psi w) ⟨u, Set.mem_univ u⟩)
    exact (lipschitzWith_of_cocoercive hB).continuous.comp
      (continuous_id.subtype_mk fun _ => Set.mem_univ _)
  have hfield_cont : Continuous (fun u =>
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ (u - mu • ∇ Psi u) - u) :=
    proximal_gradient_field_continuous Phi hPhi (∇ Psi) mu beta hmu hB
  have hdx_eq : ∀ t, 0 ≤ t → deriv x t =
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
        (x t - mu • ∇ Psi (x t)) - x t := by
    intro t ht
    apply (eq_sub_iff_add_eq).mpr
    simpa [add_comm] using (sub_eq_zero.mp (hdynamics t ht))
  have hdx_continuous : ∀ T, 0 < T → ContinuousOn (deriv x) (Set.Icc 0 T) := by
    intro T hT
    have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
    have hcomp : ContinuousOn (fun t =>
        ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
          (x t - mu • ∇ Psi (x t)) - x t) (Set.Icc 0 T) := by
      simpa only [Function.comp_apply] using
        (hfield_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
    exact hcomp.congr fun t ht => hdx_eq t ht.1
  have hdiss_continuous : ∀ z : H, ∀ T, 0 < T → ContinuousOn (fun t =>
      mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (Set.Icc 0 T) := by
    intro z T hT
    have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
    have hgradx_cont : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) := by
      simpa only [Function.comp_apply] using
        (hgrad_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
    exact (continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2)).add
      (continuousOn_const.mul ((hgradx_cont.sub continuousOn_const).norm.pow 2))
  have hfinite : ∀ z ∈ S, ∀ T, 0 < T →
      ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤
        E z 0 := by
    intro z hz T hT
    have hE_cont : ContinuousOn (E z) (Set.Icc 0 T) := by
      intro t ht
      exact (hE_hasDeriv z t ht.1).continuousAt.continuousWithinAt
    have hEderiv_cont : ContinuousOn (fun t => deriv (E z) t) (Set.Icc 0 T) := by
      have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
        simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
      have hgradx_cont : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) := by
        simpa only [Function.comp_apply] using
          (hgrad_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
      have hform : ContinuousOn (fun t =>
          mu⁻¹ * inner ℝ (x t - z) (deriv x t) +
            inner ℝ (deriv x t) (∇ Psi (x t) - ∇ Psi z)) (Set.Icc 0 T) :=
        (continuousOn_const.mul ((hx_cont.sub continuousOn_const).inner
          (hdx_continuous T hT))).add
          ((hdx_continuous T hT).inner (hgradx_cont.sub continuousOn_const))
      exact hform.congr fun t ht => (hE_hasDeriv z t ht.1).deriv
    have hD_int : IntervalIntegrable (fun t =>
        mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) volume 0 T :=
      (hdiss_continuous z T hT).intervalIntegrable_of_Icc (le_of_lt hT)
    have hderiv_int : IntervalIntegrable (fun t => -deriv (E z) t) volume 0 T :=
      (hEderiv_cont.intervalIntegrable_of_Icc (le_of_lt hT)).neg
    have hpoint : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤
          -deriv (E z) t := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      linarith [hlyap z hz t ht.1]
    have hint := intervalIntegral.integral_mono_ae_restrict (le_of_lt hT) hD_int hderiv_int hpoint
    calc
      ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤
          ∫ t in 0..T, -deriv (E z) t := hint
      _ = -(∫ t in 0..T, deriv (E z) t) := by rw [intervalIntegral.integral_neg]
      _ = -(E z T - E z 0) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hT) hE_cont]
        · intro t ht
          simpa only [(hE_hasDeriv z t ht.1.le).deriv] using hE_hasDeriv z t ht.1.le
        · exact hEderiv_cont.intervalIntegrable_of_Icc (le_of_lt hT)
      _ ≤ E z 0 := by linarith [hE_nonneg z T]
  have hdx_sq_integrable : ∀ z ∈ S,
      IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
    intro z hz
    have hscaled : IntegrableOn (fun t => mu⁻¹ * ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
      apply integrableOn_Ici_of_nonneg_interval_bound (C := E z 0)
      · intro T
        by_cases hT : 0 < T
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
            ((continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le)
        · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
          exact integrableOn_empty
      · intro t ht
        exact mul_nonneg (inv_nonneg.mpr hmu.le) (sq_nonneg _)
      · intro T hT
        rcases hT.eq_or_lt with rfl | hT
        · simpa using hE_nonneg z 0
        · have hAint : IntervalIntegrable (fun t => mu⁻¹ * ‖deriv x t‖ ^ 2) volume 0 T :=
            (continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le
          have hDint : IntervalIntegrable (fun t =>
              mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) volume 0 T :=
            (hdiss_continuous z T hT).intervalIntegrable_of_Icc hT.le
          calc
            ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 ≤
                ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 := by
              apply intervalIntegral.integral_mono_on hT.le hAint hDint
              intro t ht
              exact le_add_of_nonneg_right (mul_nonneg hbeta.le (sq_nonneg _))
            _ ≤ E z 0 := hfinite z hz T hT
    change Integrable (fun t => ‖deriv x t‖ ^ 2) (volume.restrict (Set.Ici 0))
    have hres := hscaled.const_mul mu
    change Integrable (fun t => mu * (mu⁻¹ * ‖deriv x t‖ ^ 2))
      (volume.restrict (Set.Ici 0)) at hres
    convert hres using 1
    funext t
    rw [← mul_assoc, mul_inv_cancel₀ hmu.ne', one_mul]
  have hgrad_sq_integrable : ∀ z ∈ S,
      IntegrableOn (fun t => ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (Set.Ici 0) := by
    intro z hz
    have hscaled : IntegrableOn (fun t => beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (Set.Ici 0) := by
      apply integrableOn_Ici_of_nonneg_interval_bound (C := E z 0)
      · intro T
        by_cases hT : 0 < T
        · have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
            simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
          have hgradx_cont : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) := by
            simpa only [Function.comp_apply] using
              (hgrad_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
            ((continuousOn_const.mul ((hgradx_cont.sub continuousOn_const).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le)
        · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
          exact integrableOn_empty
      · intro t ht
        exact mul_nonneg hbeta.le (sq_nonneg _)
      · intro T hT
        rcases hT.eq_or_lt with rfl | hT
        · simpa using hE_nonneg z 0
        · have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
            simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
          have hgradx_cont : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) := by
            simpa only [Function.comp_apply] using
              (hgrad_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
          have hAint : IntervalIntegrable (fun t =>
              beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) volume 0 T :=
            (continuousOn_const.mul ((hgradx_cont.sub continuousOn_const).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le
          have hDint : IntervalIntegrable (fun t =>
              mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) volume 0 T :=
            (hdiss_continuous z T hT).intervalIntegrable_of_Icc hT.le
          calc
            ∫ t in 0..T, beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤
                ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 := by
              apply intervalIntegral.integral_mono_on hT.le hAint hDint
              intro t ht
              exact le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hmu.le) (sq_nonneg _))
            _ ≤ E z 0 := hfinite z hz T hT
    change Integrable (fun t => ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (volume.restrict (Set.Ici 0))
    have hres := hscaled.const_mul beta⁻¹
    change Integrable (fun t => beta⁻¹ * (beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2))
      (volume.restrict (Set.Ici 0)) at hres
    convert hres using 1
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ hbeta.ne', one_mul]
  rcases hS with ⟨z0, hz0⟩
  have hnorm_bound : ∀ t, 0 ≤ t → ‖x t - z0‖ ^ 2 ≤ 2 * mu * E z0 0 := by
    intro t ht
    have hsupport := convex_supporting_baillon_haddad Psi (fun y => ∇ Psi y)
      hPsi_convex hPsi_grad z0 (x t)
    have hrem : 0 ≤ Psi (x t) - inner ℝ (∇ Psi z0) (x t - z0) - Psi z0 := by
      linarith
    have hanti := hE_antitone z0 hz0 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hquad : (2 * mu)⁻¹ * ‖x t - z0‖ ^ 2 ≤ E z0 0 := by
      dsimp [E]
      linarith
    have hcoef : 0 < (2 * mu)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hmu)
    calc
      ‖x t - z0‖ ^ 2 = (2 * mu) * ((2 * mu)⁻¹ * ‖x t - z0‖ ^ 2) := by
        field_simp [hmu.ne']
      _ ≤ (2 * mu) * E z0 0 := by gcongr
  have hE0_nonneg : 0 ≤ E z0 0 := hE_nonneg z0 0
  let R : ℝ := Real.sqrt (2 * mu * E z0 0)
  have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
  have hR_sq : R ^ 2 = 2 * mu * E z0 0 := by
    dsimp [R]
    simpa [pow_two] using Real.mul_self_sqrt (show 0 ≤ 2 * mu * E z0 0 by positivity)
  have hnorm_bound' : ∀ t, 0 ≤ t → ‖x t - z0‖ ≤ R := by
    intro t ht
    nlinarith [hnorm_bound t ht, norm_nonneg (x t - z0)]
  obtain ⟨L, hfield_lip⟩ := proximal_gradient_field_lipschitz Phi hPhi (∇ Psi) mu beta hmu hB
  let V : H → H := fun u =>
    ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ (u - mu • ∇ Psi u) - u
  let K : NNReal := ‖V z0‖₊ + L * R.toNNReal
  have hdx_bound : ∀ t, 0 ≤ t → ‖deriv x t‖ ≤ K := by
    intro t ht
    rw [hdx_eq t ht]
    change ‖V (x t)‖ ≤ K
    calc
      ‖V (x t)‖ = ‖(V (x t) - V z0) + V z0‖ := by congr 1; abel
      _ ≤ ‖V (x t) - V z0‖ + ‖V z0‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖x t - z0‖ + ‖V z0‖ := by
        gcongr
        simpa [V] using hfield_lip.norm_sub_le (x t) z0
      _ ≤ (L : ℝ) * R + ‖V z0‖ := by
        gcongr
        exact hnorm_bound' t ht
      _ = K := by
        simp [K, R, hR_nonneg]
        ring
  have hx_lip : LipschitzOnWith K x (Set.Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (hderiv t ht).differentiableAt
    · intro t ht
      apply NNReal.coe_le_coe.mpr
      exact hdx_bound t ht
  have hgrad_uc : UniformContinuous (∇ Psi) := by
    exact cocoercive_uniformContinuous hB
  have hgradstrong : ∀ z ∈ S, Tendsto (fun t => ∇ Psi (x t)) atTop (nhds (∇ Psi z)) := by
    intro z hz
    have hres_uc : UniformContinuousOn (fun t => ∇ Psi (x t) - ∇ Psi z) (Set.Ici 0) := by
      have htranslate : UniformContinuous (fun u : H => u - ∇ Psi z) :=
        uniformContinuous_id.sub uniformContinuous_const
      simpa only [Function.comp_def] using
        htranslate.comp_uniformContinuousOn
          (hgrad_uc.comp_uniformContinuousOn hx_lip.uniformContinuousOn)
    have hzero := uniformContinuousOn_sq_integrable_tendsto_zero _ hres_uc
      (hgrad_sq_integrable z hz)
    have h := hzero.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => ∇ Psi z) atTop (nhds (∇ Psi z)))
    simpa only [sub_add_cancel, zero_add] using h
  have hVuc : UniformContinuousOn (fun t : ℝ => V (x t)) (Set.Ici 0) := by
    exact (by simpa [V] using hfield_lip : LipschitzWith L V)
      |>.uniformContinuous.comp_uniformContinuousOn hx_lip.uniformContinuousOn
  have hdx_uc : UniformContinuousOn (deriv x) (Set.Ici 0) := by
    apply hVuc.congr
    intro t ht
    exact (hdx_eq t ht).symm
  have hdxzero : Tendsto (deriv x) atTop (nhds 0) :=
    uniformContinuousOn_sq_integrable_tendsto_zero _ hdx_uc (hdx_sq_integrable z0 hz0)
  refine ⟨?_, ?_, hdxzero⟩
  · have hcluster : ∀ z : H, ∀ u : ℕ → ℝ, Tendsto u atTop atTop →
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
          (nhds (toWeakSpace ℝ H z)) → z ∈ S := by
      intro z u hu hweak
      obtain ⟨N, hN⟩ := eventually_atTop.1
        (hu.eventually (eventually_ge_atTop (0 : ℝ)))
      have hweak_shift : Tendsto (fun n ↦ toWeakSpace ℝ H (x (u (n + N)))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        simpa only [Function.comp_def] using hweak.comp (Filter.tendsto_add_atTop_nat N)
      have hgrad_shift : Tendsto (fun n ↦ ∇ Psi (x (u (n + N)))) atTop
          (nhds (∇ Psi z0)) := by
        simpa only [Function.comp_def] using (hgradstrong z0 hz0).comp hu |>.comp
          (Filter.tendsto_add_atTop_nat N)
      have hdx_shift : Tendsto (fun n ↦ deriv x (u (n + N))) atTop (nhds 0) := by
        simpa only [Function.comp_def] using hdxzero.comp hu |>.comp
          (Filter.tendsto_add_atTop_nat N)
      have hy : Tendsto (fun n ↦ toWeakSpace ℝ H
          (x (u (n + N)) + deriv x (u (n + N)))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        refine (weakConvergence_iff_forall_tendsto_inner_right _ z).2 ?_
        intro v
        have hweak_inner :=
          (weakConvergence_iff_forall_tendsto_inner_right _ z).1 hweak_shift v
        have hdx_inner : Tendsto (fun n ↦ inner ℝ (deriv x (u (n + N))) v) atTop
            (nhds (inner ℝ (0 : H) v)) :=
          hdx_shift.inner (tendsto_const_nhds (x := v))
        simpa only [inner_add_left, inner_zero_left, add_zero] using hweak_inner.add hdx_inner
      have hq : Tendsto (fun n ↦
          -∇ Psi (x (u (n + N))) - mu⁻¹ • deriv x (u (n + N))) atTop
          (nhds (-∇ Psi z0)) := by
        have hsmul : Tendsto (fun n ↦ (mu⁻¹ : ℝ) • deriv x (u (n + N))) atTop
            (nhds 0) := by
          simpa using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (mu⁻¹ : ℝ)) atTop
              (nhds mu⁻¹)).smul hdx_shift
        simpa using hgrad_shift.neg.sub hsmul
      have hsub : -∇ Psi z0 ∈ ERealFunction.subdifferential Phi z := by
        apply maximal_monotone_graph_weak_strong_closed (ERealFunction.subdifferential Phi)
          (ERealFunction.subdifferential_isMaximalMonotone_of_mem_gammaZero hPhi)
          (fun n ↦ x (u (n + N)) + deriv x (u (n + N)))
          (fun n ↦ -∇ Psi (x (u (n + N))) - mu⁻¹ • deriv x (u (n + N))) z (-∇ Psi z0)
          hy hq
        intro n
        apply proximal_gradient_classical_subgradient Phi hPhi (∇ Psi) x mu hmu hderiv hdynamics
        exact hN (n + N) (Nat.le_add_left _ _)
      have hgradeq : ∇ Psi z = ∇ Psi z0 :=
        cocoercive_weak_strong_closed hbeta hB (fun n ↦ x (u (n + N))) z (∇ Psi z0)
          hweak_shift hgrad_shift
      exact (hsolution z).mpr (by simpa [hgradeq] using hsub)
    have hunique_time : ∀ z1 z2 : H, ∀ u v : ℕ → ℝ, Tendsto u atTop atTop →
        Tendsto v atTop atTop →
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
          (nhds (toWeakSpace ℝ H z1)) →
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (v n))) atTop
          (nhds (toWeakSpace ℝ H z2)) → z1 = z2 := by
      intro z1 z2 u v hu hv huweak hvweak
      have hz1 : z1 ∈ S := hcluster z1 u hu huweak
      have hz2 : z2 ∈ S := hcluster z2 v hv hvweak
      rcases hE_limit z1 hz1 with ⟨l1, hl1⟩
      rcases hE_limit z2 hz2 with ⟨l2, hl2⟩
      let F : ℝ → ℝ := fun t ↦ mu⁻¹ * inner ℝ (x t) (z2 - z1) +
        inner ℝ (x t) (∇ Psi z2 - ∇ Psi z1)
      let C : ℝ := (2 * mu)⁻¹ * (‖z1‖ ^ 2 - ‖z2‖ ^ 2) +
        inner ℝ (∇ Psi z1) z1 - inner ℝ (∇ Psi z2) z2 - Psi z1 + Psi z2
      have hident (t : ℝ) : E z1 t - E z2 t = F t + C := by
        dsimp [E, F, C]
        rw [← real_inner_self_eq_norm_sq (x t - z1),
          ← real_inner_self_eq_norm_sq (x t - z2),
          ← real_inner_self_eq_norm_sq z1,
          ← real_inner_self_eq_norm_sq z2]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]
        ring
      have hF : Tendsto F atTop (nhds (l1 - l2 - C)) := by
        have h := (hl1.sub hl2).sub (tendsto_const_nhds (x := C))
        convert h using 1
        · ext t
          rw [hident]
          ring
      let q1 : ℝ := mu⁻¹ * inner ℝ z1 (z2 - z1) +
        inner ℝ z1 (∇ Psi z2 - ∇ Psi z1)
      let q2 : ℝ := mu⁻¹ * inner ℝ z2 (z2 - z1) +
        inner ℝ z2 (∇ Psi z2 - ∇ Psi z1)
      have hFu : Tendsto (fun n ↦ F (u n)) atTop (nhds q1) := by
        have hcoord1 := (weakConvergence_iff_forall_tendsto_inner_right _ z1).1 huweak
          (z2 - z1)
        have hcoord2 := (weakConvergence_iff_forall_tendsto_inner_right _ z1).1 huweak
          (∇ Psi z2 - ∇ Psi z1)
        simpa [F, q1] using
          ((tendsto_const_nhds (x := mu⁻¹)).mul hcoord1).add hcoord2
      have hFv : Tendsto (fun n ↦ F (v n)) atTop (nhds q2) := by
        have hcoord1 := (weakConvergence_iff_forall_tendsto_inner_right _ z2).1 hvweak
          (z2 - z1)
        have hcoord2 := (weakConvergence_iff_forall_tendsto_inner_right _ z2).1 hvweak
          (∇ Psi z2 - ∇ Psi z1)
        simpa [F, q2] using
          ((tendsto_const_nhds (x := mu⁻¹)).mul hcoord1).add hcoord2
      have hsame : q1 = q2 := by
        calc
          q1 = l1 - l2 - C := tendsto_nhds_unique hFu (hF.comp hu)
          _ = q2 := (tendsto_nhds_unique hFv (hF.comp hv)).symm
      have hzero : mu⁻¹ * ‖z2 - z1‖ ^ 2 +
          inner ℝ (∇ Psi z2 - ∇ Psi z1) (z2 - z1) = 0 := by
        calc
          mu⁻¹ * ‖z2 - z1‖ ^ 2 +
              inner ℝ (∇ Psi z2 - ∇ Psi z1) (z2 - z1) = q2 - q1 := by
            dsimp [q1, q2]
            rw [← real_inner_self_eq_norm_sq (z2 - z1)]
            simp only [inner_sub_left, inner_sub_right, real_inner_comm]
            ring
          _ = 0 := sub_eq_zero.mpr hsame.symm
      have hmon : 0 ≤ inner ℝ (∇ Psi z2 - ∇ Psi z1) (z2 - z1) := by
        calc
          0 ≤ beta * ‖∇ Psi z2 - ∇ Psi z1‖ ^ 2 :=
            mul_nonneg hbeta.le (sq_nonneg _)
          _ ≤ inner ℝ (∇ Psi z2 - ∇ Psi z1) (z2 - z1) := by
            simpa [real_inner_comm] using
              hB.ineq ⟨z2, Set.mem_univ _⟩ ⟨z1, Set.mem_univ _⟩
      have hsq : ‖z2 - z1‖ ^ 2 = 0 := by
        nlinarith [hzero, hmon, inv_pos.mpr hmu]
      exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))).symm
    have hseq : ∀ u : ℕ → ℝ, Tendsto u atTop atTop → ∃ z : H,
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
      intro u hu
      obtain ⟨N, hN⟩ := eventually_atTop.1
        (hu.eventually (eventually_ge_atTop (0 : ℝ)))
      let y : ℕ → H := fun n ↦ x (u (n + N))
      have hybdd : Bornology.IsBounded (Set.range y) := by
        apply isBounded_iff_forall_norm_le.mpr
        refine ⟨R + ‖z0‖, ?_⟩
        rintro w ⟨n, rfl⟩
        calc
          ‖y n‖ = ‖(y n - z0) + z0‖ := by congr 1; abel
          _ ≤ ‖y n - z0‖ + ‖z0‖ := norm_add_le _ _
          _ ≤ R + ‖z0‖ := by
            gcongr
            exact hnorm_bound' (u (n + N)) (hN (n + N) (Nat.le_add_left _ _))
      have hyunique : ∀ z1 z2 : H,
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (y n)) (toWeakSpace ℝ H z1) →
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (y n)) (toWeakSpace ℝ H z2) → z1 = z2 := by
        intro z1 z2 hz1 hz2
        rcases hz1.exists_subseq_tendsto with ⟨p, hp, hpweak⟩
        rcases hz2.exists_subseq_tendsto with ⟨q, hq, hqweak⟩
        apply hunique_time z1 z2 (fun n ↦ u (p n + N)) (fun n ↦ u (q n + N))
        · exact hu.comp ((Filter.tendsto_add_atTop_nat N).comp hp.tendsto_atTop)
        · exact hu.comp ((Filter.tendsto_add_atTop_nat N).comp hq.tendsto_atTop)
        · simpa [y, Function.comp_def] using hpweak
        · simpa [y, Function.comp_def] using hqweak
      obtain ⟨z, hz⟩ := (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint y).2
        ⟨hybdd, hyunique⟩
      refine ⟨z, ?_⟩
      apply tendsto_of_tendsto_add_nat_local N
      simpa [y] using hz
    have hnat_time : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := by
      simpa using (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    obtain ⟨xinf, hnat⟩ := hseq (fun n : ℕ ↦ (n : ℝ)) hnat_time
    have hxinfS : xinf ∈ S := hcluster xinf (fun n : ℕ ↦ (n : ℝ)) hnat_time hnat
    refine ⟨xinf, hxinfS, ?_⟩
    refine (weakConvergence_iff_forall_tendsto_inner_right x xinf).2 ?_
    intro w
    apply real_tendsto_atTop_of_all_divergent_sequences_local
    intro u hu
    obtain ⟨z, hz⟩ := hseq u hu
    have hzxinf : z = xinf := hunique_time z xinf u (fun n : ℕ ↦ (n : ℝ)) hu hnat_time hz hnat
    simpa [hzxinf] using
      (weakConvergence_iff_forall_tendsto_inner_right (fun n ↦ x (u n)) z).1 hz w
  · intro z hz
    exact ⟨hgradstrong z hz, (integrableOn_Ici_iff_integrableOn_Ioi).mp
      (hgrad_sq_integrable z hz)⟩

end AbbasDynamical2015
