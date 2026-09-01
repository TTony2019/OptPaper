import Mathlib
import Foundation.Convex.Subdifferential
import Foundation.Differentiation.MoreauGradient

namespace AbbasDynamical2015

open MeasureTheory
open ERealFunction

/-- The Yosida residual at a point carrying a subgradient is bounded by that subgradient. -/
theorem norm_scaledProximityResidual_le_of_mem_subdifferential
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ gammaZero H)
    (gamma : PosReal) {y w : H}
    (hw : w ∈ subdifferential Phi y) :
    ‖(gamma : ℝ)⁻¹ • (y - Prox[gamma, Phi, hPhi] y)‖ ≤ ‖w‖ := by
  let A : H := (gamma : ℝ)⁻¹ • (y - Prox[gamma, Phi, hPhi] y)
  change ‖A‖ ≤ ‖w‖
  have hA : A ∈ subdifferential Phi (Prox[gamma, Phi, hPhi] y) := by
    simpa [A] using scaledProximityOperator_residual_mem hPhi gamma y
  have hmono : (subdifferential (fun z : H ↦ (Phi z : EReal))).IsMonotone :=
    isMonotone_subdifferential (fun z : H ↦ (Phi z : EReal))
      (isProper_of_mem_gammaZero hPhi)
  have hinner := hmono (x := Prox[gamma, Phi, hPhi] y) (y := y) A hA w hw
  have hgamma : (-(gamma : ℝ)) * (gamma : ℝ)⁻¹ = -1 := by
    simp [mul_inv_cancel₀ gamma.2.ne']
  have hdisplacement : Prox[gamma, Phi, hPhi] y - y = -(gamma : ℝ) • A := by
    calc
      Prox[gamma, Phi, hPhi] y - y = -(y - Prox[gamma, Phi, hPhi] y) := by abel
      _ = (-1 : ℝ) • (y - Prox[gamma, Phi, hPhi] y) := by simp
      _ = ((-(gamma : ℝ)) * (gamma : ℝ)⁻¹) •
          (y - Prox[gamma, Phi, hPhi] y) := by rw [hgamma]
      _ = -(gamma : ℝ) • ((gamma : ℝ)⁻¹ • (y - Prox[gamma, Phi, hPhi] y)) := by
        rw [smul_smul]
      _ = -(gamma : ℝ) • A := by rfl
  rw [hdisplacement, inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq,
    real_inner_comm] at hinner
  have hcs : inner ℝ A w ≤ ‖A‖ * ‖w‖ :=
    le_trans (le_abs_self _) (abs_real_inner_le_norm A w)
  have hgamma_pos : 0 < (gamma : ℝ) := gamma.2
  have hsq : ‖A‖ ^ 2 ≤ inner ℝ A w := by
    nlinarith
  nlinarith [norm_nonneg A, norm_nonneg w, sq_nonneg (‖A‖ - ‖w‖)]

private theorem tendsto_scaledProximityOperator_of_parameter_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ gammaZero H)
    (gamma : ℕ → PosReal)
    (hgamma : Filter.Tendsto (fun n ↦ (gamma n : ℝ)) Filter.atTop (nhds 0))
    {z w y : H} (hw : w ∈ subdifferential Phi z)
    (hy : y ∈ effectiveDomain Phi) :
    Filter.Tendsto (fun n ↦ Prox[gamma n, Phi, hPhi] y) Filter.atTop (nhds y) := by
  let p : ℕ → H := fun n ↦ Prox[gamma n, Phi, hPhi] y
  let d : ℕ → ℝ := fun n ↦ ‖y - p n‖
  let C : ℝ := (Phi y : EReal).toReal - (Phi z : EReal).toReal + ‖w‖ * ‖y - z‖
  have hpSub (n : ℕ) :
      (gamma n : ℝ)⁻¹ • (y - p n) ∈ subdifferential Phi (p n) := by
    simpa [p] using scaledProximityOperator_residual_mem hPhi (gamma n) y
  have hpDom (n : ℕ) : p n ∈ effectiveDomain Phi :=
    SubdifferentiableAt.mem_effectiveDomain hPhi.2.nonempty
      ⟨_, hpSub n⟩
  have hbasic (n : ℕ) :
      d n ^ 2 / (gamma n : ℝ) ≤ C + ‖w‖ * d n := by
    have hprox := subgradient_ineq_toReal_of_mem_gammaZero
      hPhi (hpSub n) hy
    have hminor := subgradient_ineq_toReal_of_mem_gammaZero
      hPhi hw (hpDom n)
    have hinner_residual :
        inner ℝ ((gamma n : ℝ)⁻¹ • (y - p n)) (y - p n) =
          d n ^ 2 / (gamma n : ℝ) := by
      rw [inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [d]
      simp only [map_inv₀, starRingEnd_apply, star_trivial]
      rw [div_eq_mul_inv]
      ring_nf
    rw [hinner_residual] at hprox
    have hsplit : p n - z = (p n - y) + (y - z) := by abel
    rw [hsplit, inner_add_right] at hminor
    have hwy : -(inner ℝ w (p n - y)) ≤ ‖w‖ * d n := by
      calc
        -(inner ℝ w (p n - y)) = inner ℝ w (y - p n) := by
          rw [show y - p n = -(p n - y) by abel, inner_neg_right]
        _ ≤ |inner ℝ w (y - p n)| := le_abs_self _
        _ ≤ ‖w‖ * ‖y - p n‖ := abs_real_inner_le_norm _ _
        _ = ‖w‖ * d n := by rfl
    have hwz : -(inner ℝ w (y - z)) ≤ ‖w‖ * ‖y - z‖ := by
      calc
        -(inner ℝ w (y - z)) ≤ |inner ℝ w (y - z)| := neg_le_abs _
        _ ≤ ‖w‖ * ‖y - z‖ := abs_real_inner_le_norm _ _
    dsimp [C]
    linarith
  have hsq_bound (n : ℕ) :
      d n ^ 2 ≤ 2 * (gamma n : ℝ) * C + (gamma n : ℝ) ^ 2 * ‖w‖ ^ 2 := by
    have hγ : 0 < (gamma n : ℝ) := (gamma n).2
    have hmul := (div_le_iff₀ hγ).mp (hbasic n)
    have hyoung :
        (gamma n : ℝ) * ‖w‖ * d n ≤
          (d n ^ 2 + (gamma n : ℝ) ^ 2 * ‖w‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (d n - (gamma n : ℝ) * ‖w‖)]
    nlinarith
  have hbound_tendsto : Filter.Tendsto
      (fun n ↦ 2 * (gamma n : ℝ) * C + (gamma n : ℝ) ^ 2 * ‖w‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have ht := ((hgamma.const_mul 2).mul_const C).add
      ((hgamma.pow 2).mul_const (‖w‖ ^ 2))
    convert ht using 1
    norm_num
  rw [Metric.tendsto_atTop] at hbound_tendsto ⊢
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨N, hN⟩ := hbound_tendsto (ε ^ 2) hεsq
  refine ⟨N, fun n hn ↦ ?_⟩
  have hd0 : 0 ≤ d n := norm_nonneg _
  have hlt := hN n hn
  rw [dist_zero_right] at hlt
  have hbound_lt :
      2 * (gamma n : ℝ) * C + (gamma n : ℝ) ^ 2 * ‖w‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt (le_abs_self _) hlt
  change dist (p n) y < ε
  rw [dist_eq_norm, ← norm_neg (p n - y)]
  rw [show -(p n - y) = y - p n by abel]
  change d n < ε
  nlinarith [hsq_bound n]

private theorem moreauEnvelope_toReal_tendsto_of_mem_effectiveDomain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ gammaZero H)
    (gamma : ℕ → PosReal)
    (hgamma : Filter.Tendsto (fun n ↦ (gamma n : ℝ)) Filter.atTop (nhds 0))
    {z w y : H} (hw : w ∈ subdifferential Phi z)
    (hy : y ∈ effectiveDomain Phi) :
    Filter.Tendsto (fun n ↦ (({}^[(gamma n)] Phi) y).toReal) Filter.atTop
      (nhds (Phi y : EReal).toReal) := by
  let p : ℕ → H := fun n ↦ Prox[gamma n, Phi, hPhi] y
  have hp_tendsto : Filter.Tendsto p Filter.atTop (nhds y) := by
    simpa [p] using
      tendsto_scaledProximityOperator_of_parameter_tendsto_zero Phi hPhi gamma hgamma hw hy
  have hpdom : ∀ n, p n ∈ effectiveDomain Phi := by
    intro n
    apply subdifferential_domain_subset_effectiveDomain Phi hPhi.2.nonempty
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨(gamma n : ℝ)⁻¹ • (y - p n), by
      simpa [p] using
        scaledProximityOperator_residual_mem hPhi (gamma n) y⟩
  have hp_top : ∀ n, (Phi (p n) : EReal) ≠ ⊤ := fun n ↦
    ne_of_lt (mem_effectiveDomain_iff.mp (hpdom n))
  have hp_bot : ∀ n, (Phi (p n) : EReal) ≠ ⊥ := fun n ↦
    ne_of_gt (show (⊥ : EReal) < (Phi (p n) : EReal) from (Phi (p n)).2)
  have hy_top : (Phi y : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (Phi y : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (Phi y : EReal) from (Phi y).2)
  have hformula : ∀ n,
      ({}^[(gamma n)] Phi) y =
        (Phi (p n) : EReal) +
          ((((‖y - p n‖ ^ 2) / (2 * (gamma n : ℝ)) : ℝ) : EReal)) := by
    intro n
    simpa [p] using
      moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        (f := Phi) (γ := gamma n) hPhi y
  have henv_bot : ∀ n, ({}^[(gamma n)] Phi) y ≠ ⊥ := by
    intro n
    rw [hformula n]
    exact EReal.add_ne_bot_iff.2 ⟨hp_bot n, EReal.coe_ne_bot _⟩
  have hprox_le_env : ∀ n,
      (Phi (p n) : EReal).toReal ≤ (({}^[(gamma n)] Phi) y).toReal := by
    intro n
    rw [hformula n,
      EReal.toReal_add (hp_top n) (hp_bot n) (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe]
    have hden : 0 < 2 * (gamma n : ℝ) := mul_pos (by norm_num) (gamma n).2
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hden.le)
  have henv_le : ∀ n, (({}^[(gamma n)] Phi) y).toReal ≤ (Phi y : EReal).toReal := by
    intro n
    have hupperE : ({}^[(gamma n)] Phi) y ≤ (Phi y : EReal) := by
      rw [moreauEnvelope_apply]
      have h := iInf_le
        (fun q : H ↦ (Phi q : EReal) +
          ((((1 / (2 * (gamma n : ℝ))) * ‖y - q‖ ^ 2 : ℝ) : EReal))) y
      simpa using h
    exact EReal.toReal_le_toReal hupperE (henv_bot n) hy_top
  rw [Metric.tendsto_atTop]
  intro ε hε
  let ξ : EReal := (((Phi y : EReal).toReal - ε : ℝ) : EReal)
  have hcoe_y : (((Phi y : EReal).toReal : ℝ) : EReal) = (Phi y : EReal) :=
    EReal.coe_toReal hy_top hy_bot
  have hξ_lt : ξ < (Phi y : EReal) := by
    rw [← hcoe_y]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hε)
  have hlsc_y : LowerSemicontinuousAt (fun q : H ↦ (Phi q : EReal)) y :=
    (lowerSemicontinuous_iff_forall_lowerSemicontinuousAt.mp hPhi.1) y
  obtain ⟨V, hV, hVlower⟩ :=
    (lowerSemicontinuousAt_iff_exists_mem_nhds_forall_lt.mp hlsc_y) ξ hξ_lt
  have hp_eventually : ∀ᶠ n in Filter.atTop, p n ∈ V := hp_tendsto hV
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp_eventually
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnV : p n ∈ V := hN n hn
  have hlowerE : ξ < (Phi (p n) : EReal) := hVlower (p n) hnV
  have hcoe_p : (((Phi (p n) : EReal).toReal : ℝ) : EReal) = (Phi (p n) : EReal) :=
    EReal.coe_toReal (hp_top n) (hp_bot n)
  have hlower : (Phi y : EReal).toReal - ε < (Phi (p n) : EReal).toReal := by
    change (((Phi y : EReal).toReal - ε : ℝ) : EReal) < (Phi (p n) : EReal) at hlowerE
    rw [← hcoe_p] at hlowerE
    exact EReal.coe_lt_coe_iff.mp hlowerE
  rw [Real.dist_eq]
  have hlower_env := lt_of_lt_of_le hlower (hprox_le_env n)
  have hupper_env := henv_le n
  rw [abs_lt]
  constructor <;> linarith

private theorem ac_comp_of_lipschitzOn_image_H
    {H : Type*} [PseudoMetricSpace H] {x : ℝ → H} {phi : H → ℝ}
    {a b : ℝ} {K : NNReal}
    (hx : AbsolutelyContinuousOnInterval x a b)
    (hphi : LipschitzOnWith K phi (x '' Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun t ↦ phi (x t)) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  rcases (absolutelyContinuousOnInterval_iff _ _ _).mp hx (ε / (K + 1))
      (by positivity) with ⟨δ, hδ, hδ_bound⟩
  refine ⟨δ, hδ, fun (n, I) hnI₁ hnI₂ ↦ ?_⟩
  calc
    ∑ i ∈ Finset.range n, dist (phi (x (I i).1)) (phi (x (I i).2)) ≤
        ∑ i ∈ Finset.range n, K * dist (x (I i).1) (x (I i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hphi ⟨(I i).1, (hnI₁.left i hi).left, rfl⟩
        ⟨(I i).2, (hnI₁.left i hi).right, rfl⟩
      apply ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by simp) (edist_ne_top _ _)) at h
      rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at h
    _ = K * ∑ i ∈ Finset.range n, dist (x (I i).1) (x (I i).2) := by
      rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by
      gcongr
      simpa using (hδ_bound (n, I) hnI₁ hnI₂).le
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field

private theorem moreauEnvelope_comp_ac_and_increment_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ gammaZero H)
    (gamma : PosReal) (x v : ℝ → H) {b : ℝ}
    (hb : 0 ≤ b) (hx_ac : AbsolutelyContinuousOnInterval x 0 b)
    (hsubgradient : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      v t ∈ subdifferential Phi (x t))
    (hx_deriv : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      HasDerivAt x (deriv x t) t)
    (hM : IntegrableOn (fun r ↦ ‖v r‖ * ‖deriv x r‖) (Set.Icc 0 b)) :
    AbsolutelyContinuousOnInterval
        (fun t ↦ (({}^[gamma] Phi) (x t)).toReal) 0 b ∧
      ∀ {s t}, s ∈ Set.Icc 0 b → t ∈ Set.Icc 0 b → s ≤ t →
        abs ((({}^[gamma] Phi) (x t)).toReal -
          (({}^[gamma] Phi) (x s)).toReal) ≤
          ∫ r in s..t, ‖v r‖ * ‖deriv x r‖ := by
  let phi : H → ℝ := fun y ↦ (({}^[gamma] Phi) y).toReal
  let G : H → H := fun y ↦
    (gamma : ℝ)⁻¹ • (y - Prox[gamma, Phi, hPhi] y)
  have hgrad : ∀ y, HasGradientAt phi (G y) y := by
    intro y
    simpa [phi, G] using
      moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
        Phi gamma hPhi y
  have hG_lip : LipschitzWith (Real.toNNReal ((gamma : ℝ)⁻¹)) G := by
    have h :=
      lipschitzWith_inv_of_gradient_moreauEnvelope_toReal_of_mem_gammaZero
        Phi gamma hPhi
    rw [gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero
      Phi gamma hPhi] at h
    simpa [G] using h
  have hphi_C1 : ContDiff ℝ 1 phi := by
    rw [contDiff_one_iff_hasFDerivAt]
    refine ⟨fun y ↦ InnerProductSpace.toDual ℝ H (G y), ?_, fun y ↦ (hgrad y).hasFDerivAt⟩
    exact (InnerProductSpace.toDual ℝ H).continuous.comp hG_lip.continuous
  have hcompact : IsCompact (x '' Set.uIcc 0 b) :=
    isCompact_uIcc.image_of_continuousOn hx_ac.continuousOn
  have hphi_local : LocallyLipschitzOn (x '' Set.uIcc 0 b) phi := by
    intro y _
    rcases hphi_C1.locallyLipschitz y with ⟨K, u, hu, hKu⟩
    exact ⟨K, u, Filter.Eventually.filter_mono inf_le_left hu, hKu⟩
  obtain ⟨K, hphi_lip⟩ :=
    hphi_local.exists_lipschitzOnWith_of_compact hcompact
  have hF_ac : AbsolutelyContinuousOnInterval (fun t ↦ phi (x t)) 0 b := by
    exact ac_comp_of_lipschitzOn_image_H hx_ac hphi_lip
  have hchain : ∀ᵐ r ∂volume.restrict (Set.Icc 0 b),
      HasDerivAt (fun t ↦ phi (x t))
        (inner ℝ (G (x r)) (deriv x r)) r := by
    filter_upwards [hx_deriv] with r hr
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      (hgrad (x r)).hasFDerivAt.comp_hasDerivAt r hr
  have hderiv_bound : ∀ᵐ r ∂volume.restrict (Set.Icc 0 b),
      ‖deriv (fun t ↦ phi (x t)) r‖ ≤ ‖v r‖ * ‖deriv x r‖ := by
    filter_upwards [hchain, hsubgradient] with r hr hvr
    have hG_norm : ‖G (x r)‖ ≤ ‖v r‖ := by
      simpa [G] using
        norm_scaledProximityResidual_le_of_mem_subdifferential Phi hPhi gamma hvr
    rw [hr.deriv, Real.norm_eq_abs]
    calc
      |inner ℝ (G (x r)) (deriv x r)| ≤ ‖G (x r)‖ * ‖deriv x r‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖v r‖ * ‖deriv x r‖ := by gcongr
  refine ⟨by simpa [phi] using hF_ac, ?_⟩
  intro s t hs ht hst
  have hF_ac_st : AbsolutelyContinuousOnInterval (fun r ↦ phi (x r)) s t :=
    hF_ac.mono (by
      rw [Set.uIcc_of_le hst, Set.uIcc_of_le hb]
      exact Set.Icc_subset_Icc hs.1 ht.2)
  have hM_st : IntervalIntegrable (fun r ↦ ‖v r‖ * ‖deriv x r‖) volume s t := by
    apply IntegrableOn.intervalIntegrable
    apply hM.mono_set
    rw [Set.uIcc_of_le hst]
    exact Set.Icc_subset_Icc hs.1 ht.2
  have hderiv_bound' : ∀ᵐ r ∂volume,
      r ∈ Set.Ioc s t →
        ‖deriv (fun q ↦ phi (x q)) r‖ ≤ ‖v r‖ * ‖deriv x r‖ := by
    have hglobal : ∀ᵐ r ∂volume, r ∈ Set.Icc 0 b →
        ‖deriv (fun q ↦ phi (x q)) r‖ ≤ ‖v r‖ * ‖deriv x r‖ :=
      (ae_restrict_iff' measurableSet_Icc).mp hderiv_bound
    filter_upwards [hglobal] with r hr
    intro hrst
    exact hr ⟨le_trans hs.1 hrst.1.le, le_trans hrst.2 ht.2⟩
  change abs (phi (x t) - phi (x s)) ≤ _
  rw [← hF_ac_st.integral_deriv_eq_sub, ← Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_of_norm_le hst hderiv_bound' hM_st

private theorem
    absolutelyContinuousOnInterval_of_pointwise_limit_of_abs_sub_le_intervalIntegral
    {F : ℝ → ℝ} {Fn : ℕ → ℝ → ℝ} {M : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hM : IntegrableOn M (Set.Icc 0 b))
    (hlim : ∀ t, t ∈ Set.Icc 0 b →
      Filter.Tendsto (fun n ↦ Fn n t) Filter.atTop (nhds (F t)))
    (hinc : ∀ n {s t}, s ∈ Set.Icc 0 b → t ∈ Set.Icc 0 b → s ≤ t →
      abs (Fn n t - Fn n s) ≤ ∫ r in s..t, M r) :
    AbsolutelyContinuousOnInterval F 0 b := by
  have hM_interval : IntervalIntegrable M volume 0 b := by
    apply IntegrableOn.intervalIntegrable
    simpa [Set.uIcc_of_le hb] using hM
  let P : ℝ → ℝ := fun t ↦ ∫ r in 0..t, M r
  have hP : AbsolutelyContinuousOnInterval P 0 b := by
    simpa [P] using
      hM_interval.absolutelyContinuousOnInterval_intervalIntegral (c := 0)
        (by simp [hb])
  have hdom_interval {s t : ℝ} (hs : s ∈ Set.Icc 0 b) (ht : t ∈ Set.Icc 0 b) :
      IntervalIntegrable M volume s t := by
    apply hM_interval.mono_set
    rw [Set.uIcc_of_le hb]
    rcases le_total s t with hst | hts
    · rw [Set.uIcc_of_le hst]
      exact Set.Icc_subset_Icc hs.1 ht.2
    · rw [Set.uIcc_of_ge hts]
      exact Set.Icc_subset_Icc ht.1 hs.2
  have hF_le_P {s t : ℝ} (hs : s ∈ Set.Icc 0 b) (ht : t ∈ Set.Icc 0 b) :
      dist (F s) (F t) ≤ dist (P s) (P t) := by
    have hlim_dist : Filter.Tendsto (fun n ↦ dist (Fn n s) (Fn n t))
        Filter.atTop (nhds (dist (F s) (F t))) :=
      (hlim s hs).dist (hlim t ht)
    apply le_of_tendsto' hlim_dist
    intro n
    rcases le_total s t with hst | hts
    · have hn := hinc n hs ht hst
      rw [Real.dist_eq, abs_sub_comm]
      calc
        |Fn n t - Fn n s| ≤ ∫ r in s..t, M r := hn
        _ = P t - P s := by
          change (∫ r in s..t, M r) =
            (∫ r in 0..t, M r) - ∫ r in 0..s, M r
          symm
          exact intervalIntegral.integral_interval_sub_left
            (hdom_interval ⟨le_rfl, hb⟩ ht)
            (hdom_interval ⟨le_rfl, hb⟩ hs)
        _ ≤ |P s - P t| := by
          rw [abs_sub_comm]
          exact le_abs_self _
    · have hn := hinc n ht hs hts
      rw [Real.dist_eq]
      calc
        |Fn n s - Fn n t| ≤ ∫ r in t..s, M r := hn
        _ = P s - P t := by
          change (∫ r in t..s, M r) =
            (∫ r in 0..s, M r) - ∫ r in 0..t, M r
          symm
          exact intervalIntegral.integral_interval_sub_left
            (hdom_interval ⟨le_rfl, hb⟩ hs)
            (hdom_interval ⟨le_rfl, hb⟩ ht)
        _ ≤ |P s - P t| := le_abs_self _
  rw [absolutelyContinuousOnInterval_iff] at hP ⊢
  intro ε hε
  obtain ⟨δ, hδ, hPδ⟩ := hP ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hEδ
  calc
    ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) ≤
        ∑ i ∈ Finset.range E.1, dist (P (E.2 i).1) (P (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hF_le_P
        (by simpa [Set.uIcc_of_le hb] using (hE.1 i hi).1)
        (by simpa [Set.uIcc_of_le hb] using (hE.1 i hi).2)
    _ < ε := hPδ E hE hEδ

private theorem deriv_energy_eq_inner_of_absolutelyContinuous
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ gammaZero H)
    (x v : ℝ → H) (b : ℝ) (hb : 0 < b)
    (hsubgradient : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      v t ∈ subdifferential Phi (x t))
    (hdom : ∀ t ∈ Set.Icc 0 b, x t ∈ effectiveDomain Phi)
    (hx_deriv : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      HasDerivAt x (deriv x t) t)
    (hF_ac : AbsolutelyContinuousOnInterval
      (fun t ↦ (Phi (x t) : EReal).toReal) 0 b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      deriv (fun s ↦ (Phi (x s) : EReal).toReal) t = inner ℝ (v t) (deriv x t) := by
  let F : ℝ → ℝ := fun t ↦ (Phi (x t) : EReal).toReal
  have hF_diff : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      t ∈ Set.uIcc 0 b → DifferentiableAt ℝ F t :=
    MeasureTheory.ae_restrict_of_ae hF_ac.ae_differentiableAt
  have hleft : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), t ≠ 0 := by
    apply MeasureTheory.ae_restrict_of_ae
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  have hright : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), t ≠ b := by
    apply MeasureTheory.ae_restrict_of_ae
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc, hsubgradient,
    hx_deriv, hF_diff, hleft, hright] with r hr hsubr hxdr hFdr hr0' hrb'
  have hr0 : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0')
  have hrb : r < b := lt_of_le_of_ne hr.2 hrb'
  have hFr : HasDerivAt F (deriv F r) r :=
    (hFdr (by simpa [Set.uIcc_of_le hb.le] using hr)).hasDerivAt
  let G : ℝ → ℝ := fun u ↦ F u - F r - inner ℝ (v r) (x u - x r)
  have hG_min : IsLocalMin G r := by
    change ∀ᶠ u in nhds r, G r ≤ G u
    filter_upwards [Ioo_mem_nhds hr0 hrb] with u hu
    have huIcc : u ∈ Set.Icc 0 b := ⟨hu.1.le, hu.2.le⟩
    have hineq := subgradient_ineq_toReal_of_mem_gammaZero hPhi hsubr
      (hdom u huIcc)
    dsimp [G, F]
    simp only [sub_self, inner_zero_right]
    linarith
  have hxsub : HasDerivAt (fun u ↦ x u - x r) (deriv x r) r := by
    convert hxdr.sub (hasDerivAt_const r (x r)) using 1; simp
  have hinner : HasDerivAt (fun u ↦ inner ℝ (v r) (x u - x r))
      (inner ℝ (v r) (deriv x r)) r := by
    simpa using (hasDerivAt_const r (v r)).inner ℝ hxsub
  have hG_deriv : HasDerivAt G (deriv F r - inner ℝ (v r) (deriv x r)) r := by
    simpa [G] using (hFr.sub (hasDerivAt_const r (F r))).sub hinner
  have hzero := hG_min.hasDerivAt_eq_zero hG_deriv
  dsimp [F] at hzero ⊢
  linarith

/-- Lemma 2.9: the subgradient chain rule on a bounded interval. -/
theorem subgradient_chain_rule {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ gammaZero H)
    (x v : ℝ → H) (b : ℝ) (hb : 0 < b)
    (hx_ac : AbsolutelyContinuousOnInterval x 0 b)
    (hsubgradient : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      v t ∈ subdifferential Phi (x t))
    (hdom : ∀ t ∈ Set.Icc 0 b, x t ∈ effectiveDomain Phi)
    (hx_deriv : ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      HasDerivAt x (deriv x t) t)
    (hvL2 : MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b))) :
    AbsolutelyContinuousOnInterval (fun t ↦ (Phi (x t) : EReal).toReal) 0 b ∧
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 b),
      deriv (fun s ↦ (Phi (x s) : EReal).toReal) t = inner ℝ (v t) (deriv x t) := by
  let F : ℝ → ℝ := fun t ↦ (Phi (x t) : EReal).toReal
  have hF_ac : AbsolutelyContinuousOnInterval F 0 b := by
    let M : ℝ → ℝ := fun r ↦ ‖v r‖ * ‖deriv x r‖
    have hv_sq : IntegrableOn (fun r ↦ ‖v r‖ ^ 2) (Set.Icc 0 b) :=
      (memLp_two_iff_integrable_sq_norm hvL2.aestronglyMeasurable).mp hvL2
    have hdx_sq : IntegrableOn (fun r ↦ ‖deriv x r‖ ^ 2) (Set.Icc 0 b) :=
      (memLp_two_iff_integrable_sq_norm hdxL2.aestronglyMeasurable).mp hdxL2
    have hmajorant : IntegrableOn
        (fun r ↦ (‖v r‖ ^ 2 + ‖deriv x r‖ ^ 2) / 2) (Set.Icc 0 b) := by
      simpa [add_div] using (hv_sq.add hdx_sq).div_const 2
    have hM : IntegrableOn M (Set.Icc 0 b) := by
      apply Integrable.mono' hmajorant
      · exact hvL2.aestronglyMeasurable.norm.mul hdxL2.aestronglyMeasurable.norm
      · filter_upwards with r
        dsimp [M]
        rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        nlinarith [sq_nonneg (‖v r‖ - ‖deriv x r‖)]
    have hvol : volume (Set.Icc 0 b) ≠ 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    obtain ⟨r, hr, hsubr⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hvol hsubgradient
    let gamma : ℕ → PosReal := fun n ↦
      ⟨1 / ((n : ℝ) + 1), by positivity⟩
    have hgamma : Filter.Tendsto (fun n ↦ (gamma n : ℝ)) Filter.atTop (nhds 0) := by
      simpa [gamma] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0))
    let Fn : ℕ → ℝ → ℝ := fun n t ↦ (({}^[(gamma n)] Phi) (x t)).toReal
    have hlim : ∀ t, t ∈ Set.Icc 0 b →
        Filter.Tendsto (fun n ↦ Fn n t) Filter.atTop (nhds (F t)) := by
      intro t ht
      simpa [Fn, F] using
        moreauEnvelope_toReal_tendsto_of_mem_effectiveDomain Phi hPhi gamma hgamma
          (z := x r) (w := v r) hsubr (hdom t ht)
    have hinc : ∀ n {s t}, s ∈ Set.Icc 0 b → t ∈ Set.Icc 0 b → s ≤ t →
        abs (Fn n t - Fn n s) ≤ ∫ q in s..t, M q := by
      intro n s t hs ht hst
      have hsmooth := moreauEnvelope_comp_ac_and_increment_bound
        Phi hPhi (gamma n) x v hb.le hx_ac hsubgradient hx_deriv hM
      simpa [Fn, M] using hsmooth.2 hs ht hst
    exact absolutelyContinuousOnInterval_of_pointwise_limit_of_abs_sub_le_intervalIntegral
      hb.le hM hlim hinc
  constructor
  · exact hF_ac
  · simpa [F] using deriv_energy_eq_inner_of_absolutelyContinuous Phi hPhi x v b hb
      hsubgradient hdom hx_deriv hF_ac

end AbbasDynamical2015
