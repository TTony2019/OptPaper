import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_2
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_7
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_thm_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_2
import Foundation.Analysis.ExtendedRealFunctions
import Mathlib

open scoped InnerProductSpace

open ERealFunction

open Filter Topology

/-- The real-valued `γ`-Moreau envelope of `F`, namely `x ↦ ({}^[γ] F x).toReal`. -/
noncomputable def moreauEnvelopeReal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) : H → ℝ :=
  fun x ↦ (({}^[γ] F) x).toReal

/-- Foundation: the gradient of the real-valued Moreau envelope is the scaled proximal residual. -/
theorem hasFDerivAt_moreauEnvelopeReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {F : H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H))
    (γ : PosReal) (x : H) :
    HasFDerivAt (moreauEnvelopeReal F γ)
      (innerSL ℝ ((γ : ℝ)⁻¹ • (x - ERealFunction.scaledProximityOperator F hF γ x))) x := by
  simpa [moreauEnvelopeReal] using
    (ERealFunction.moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
      (f := F) (γ := γ) hF x).hasFDerivAt

/-- Foundation: the gradient field of the real-valued Moreau envelope is Lipschitz. -/
theorem lipschitzWith_gradient_moreauEnvelopeReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {F : H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H))
    (γ : PosReal) :
    LipschitzWith (Real.toNNReal ((γ : ℝ)⁻¹)) (gradient (moreauEnvelopeReal F γ)) := by
  simpa [moreauEnvelopeReal] using
    ERealFunction.lipschitzWith_inv_of_gradient_moreauEnvelope_toReal_of_mem_gammaZero
      (f := F) (γ := γ) hF

/--
Theorem 4.1:
reduced to the regularity facts for the extended-real Moreau envelope.
-/
theorem IPAHDDNonsmooth_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (F : H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H))
    (phi : H → ℝ) (h gamma beta lam r : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDDNonsmooth F hF phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta lam)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta) (hlam : 0 < lam)
    (hgamma : gamma ≥ (h / 2 + beta) / lam)
    (hbelowLam : ∃ c : ℝ, ∀ x, c ≤ moreauEnvelopeReal F ⟨lam, hlam⟩ x)
    (smooth : IPAHDD (moreauEnvelopeReal F ⟨lam, hlam⟩) phi.toEReal
      hdf.toEReal_mem_gammaZero h gamma beta)
    (hsmooth : smooth.x = alg.x) :
    ∃ xInf pInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        moreauEnvelopeReal F ⟨lam, hlam⟩ (alg.x 1) -
          sInf (Set.range (moreauEnvelopeReal F ⟨lam, hlam⟩)) ∧
      HasFiniteLength alg.x ∧ Tendsto alg.x Filter.atTop (𝓝 xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * (1 / lam) / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦
        ‖alg.x (k.1 + 1) - 2 • alg.x k.1 + alg.x (k.1 - 1)‖ ^ 2) ≤
        2 * h ^ 2 * (E1 + beta * (1 / lam) / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      IsDryFrictionCritical phi (moreauEnvelopeReal F ⟨lam, hlam⟩) xInf ∧
      HasFiniteLength (fun k ↦ ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ (alg.x k)) ∧
      Tendsto (fun k ↦ ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ (alg.x k))
        Filter.atTop (𝓝 pInf) ∧
      pInf = ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ xInf ∧
      ((1 / lam) • (xInf - pInf) ∈ subdifferential F pInf) ∧
      (-gradient (moreauEnvelopeReal F ⟨lam, hlam⟩) xInf ∈ interior (subdifferential phi 0) →
        let q := 1 / Real.sqrt (1 + 2 * h * (gamma * lam - beta) / (lam + beta * h))
        0 < q ∧ q < 1 ∧ ∃ k0, ∀ k ≥ k0,
          ‖alg.x (k + 1) - alg.x k‖ ≤ q ^ (k - k0) * ‖alg.x (k0 + 1) - alg.x k0‖ ∧
          ‖alg.x k - xInf‖ ≤ q ^ (k - k0) / (1 - q) * ‖alg.x (k0 + 1) - alg.x k0‖) ∧
      (‖gradient (moreauEnvelopeReal F ⟨lam, hlam⟩) xInf‖ < r →
        Metric.ball (0 : H) r ⊆ subdifferential phi 0 → IsFinitelyConvergent alg.x) := by
  let P : H → H := ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩
  have hP_firm : FirmlyNonexpansive P := by
    have hfirm := ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
      (f := (⟨lam, hlam⟩ : PosReal) • F)
      (ERealFunction.smul_mem_gammaZero F hF ⟨lam, hlam⟩)
    simpa [P, ERealFunction.scaledProximityOperator] using hfirm
  have hnonexp : ∀ x y, ‖P x - P y‖ ≤ ‖x - y‖ := fun x y => by
    simpa [dist_eq_norm] using (lipschitzWith_one_of_firmlyNonexpansive hP_firm).dist_le_mul x y
  let fLam : H → ℝ := moreauEnvelopeReal F ⟨lam, hlam⟩
  have hderiv : ∀ x, HasFDerivAt fLam (innerSL ℝ ((1 / lam) • (x - P x))) x := by
    intro x
    have h := hasFDerivAt_moreauEnvelopeReal (F := F) hF ⟨lam, hlam⟩ x
    simpa [fLam, P, one_div] using h
  have hlipgrad : LipschitzWith (Real.toNNReal ((⟨lam, hlam⟩ : PosReal) : ℝ)⁻¹)
      (gradient fLam) := by
    have h := lipschitzWith_gradient_moreauEnvelopeReal (F := F) hF ⟨lam, hlam⟩
    simpa [fLam] using h
  have hLip : HasLipschitzGradient (gradient fLam) (1 / lam) := by
    intro x y
    have h := hlipgrad.dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm] at h
    simpa [Real.coe_toNNReal _ (inv_nonneg.mpr hlam.le), one_div] using h
  have hfLam : ContDiff ℝ 1 fLam := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    have hfd_eq : fderiv ℝ fLam = fun x => InnerProductSpace.toDual ℝ H (gradient fLam x) := by
      funext x
      rw [gradient]
      exact (LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual ℝ H)
        (fderiv ℝ fLam x)).symm
    rw [hfd_eq]
    exact (InnerProductSpace.toDual ℝ H).continuous.comp hlipgrad.continuous
  let moreauGrad : H → H := fun x ↦ (1 / lam) • (x - P x)
  have hgrad_eq : gradient fLam = moreauGrad := by
    funext x
    rw [gradient, (hderiv x).fderiv]
    have h1 : InnerProductSpace.toDual ℝ H (moreauGrad x) = innerSL ℝ (moreauGrad x) := by
      ext y
      simp
    rw [← h1, LinearIsometryEquiv.symm_apply_apply]
  have hLnonneg : 0 ≤ (1 / lam : ℝ) := (one_div_pos.mpr hlam).le
  have hgamma' : gamma ≥ (1 / lam : ℝ) * (h / 2 + beta) := by
    calc gamma ≥ (h / 2 + beta) / lam := hgamma
         _ = (1 / lam : ℝ) * (h / 2 + beta) := by ring
  have hfinite := IPAHDD_finiteLength_and_critical fLam phi h gamma beta
    (1 / lam) r hdf smooth hfLam hLip
    hLnonneg hbelowLam hpositive hgamma'
  rcases hfinite with ⟨xInf, E1, hE1, hlength, hlim, hcritical, hlenbound, haccelbound⟩
  have hlengthAlg : HasFiniteLength alg.x := by simpa [hsmooth] using hlength
  have hlimAlg : Tendsto alg.x Filter.atTop (𝓝 xInf) := by simpa [hsmooth] using hlim
  have hproxLength : HasFiniteLength (fun k ↦ P (alg.x k)) := by
    unfold HasFiniteLength at hlengthAlg ⊢
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => hnonexp _ _) hlengthAlg
  have hproxCont : Continuous P := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    calc dist (P y) (P x) = ‖P y - P x‖ := dist_eq_norm _ _
         _ ≤ ‖y - x‖ := hnonexp _ _
         _ = dist y x := (dist_eq_norm _ _).symm
         _ < ε := hy
  have hproxLim : Tendsto (fun k ↦ P (alg.x k)) Filter.atTop
      (𝓝 (P xInf)) := hproxCont.continuousAt.tendsto.comp hlimAlg
  have hsubgrad : moreauGrad xInf ∈ subdifferential F (P xInf) := by
    have h := ERealFunction.scaledProximityOperator_residual_mem hF ⟨lam, hlam⟩ xInf
    simpa [P, moreauGrad, one_div, subdifferential] using h
  have hgeo := IPAHDD_geometric_and_finite fLam phi h gamma beta (1 / lam) r
    hdf smooth xInf hfLam hLip hLnonneg hbelowLam hpositive hgamma' hlim
  have hrate :
      1 / Real.sqrt (1 + 2 * h * (gamma - beta * (1 / lam)) /
        (1 + beta * h * (1 / lam))) =
      1 / Real.sqrt (1 + 2 * h * (gamma * lam - beta) / (lam + beta * h)) := by
    congr 2
    field_simp [hlam.ne']
  refine ⟨xInf, P xInf, E1, ?_, hlengthAlg, hlimAlg, ?_, ?_, ?_, hproxLength,
    hproxLim, rfl, ?_, ?_, ?_⟩
  · simpa [hsmooth] using hE1
  · simpa [hsmooth, moreauGrad] using hlenbound
  · simpa [hsmooth, moreauGrad] using haccelbound
  · simpa [IsDryFrictionCritical] using hcritical
  · simpa [moreauGrad] using hsubgrad
  · intro hinterior
    simpa only [hrate, hsmooth] using
      hgeo.1 (by simpa [fLam, moreauGrad, hgrad_eq] using hinterior)
  · intro hnorm hball
    obtain ⟨kStop, hkStop⟩ := hgeo.2 (by simpa [fLam, moreauGrad, hgrad_eq] using hnorm)
    exact eventually_constant_of_eventual_successor_eq alg.x kStop (by
      simpa only [hsmooth] using hkStop)
