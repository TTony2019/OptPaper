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

/-- Theorem 4.1, reduced to the regularity facts for the extended-real Moreau envelope. -/
theorem IPAHDDNonsmooth_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (F : H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H))
    (phi fLam : H → ℝ) (h gamma beta lam r : ℝ) (hdf : DryFriction phi)
    (alg : IPAHDDNonsmooth F hF phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta lam)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta) (hlam : 0 < lam) (hr : 0 < r)
    (hdf_r : Metric.ball (0 : H) r ⊆ subdifferential phi 0)
    (hgamma : gamma ≥ (h / 2 + beta) / lam)
    (hfLam : ContDiff ℝ 1 fLam)
    (hMoreau : (∀ x, HasFDerivAt fLam
      (innerSL ℝ ((1 / lam) • (x - ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ x))) x) ∧
      HasLipschitzGradient (gradient fLam) (1 / lam) ∧
      Continuous (gradient fLam) ∧
      (∃ c : ℝ, ∀ x, c ≤ fLam x) ∧
      (∀ x y, ‖ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ x -
        ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ y‖ ≤ ‖x - y‖))
    (smooth : IPAHDD fLam phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta)
    (hsmooth : smooth.x = alg.x) :
    ∃ xInf pInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        fLam (alg.x 1) - sInf (Set.range fLam) ∧
      HasFiniteLength alg.x ∧ Tendsto alg.x Filter.atTop (𝓝 xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * (1 / lam) / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦
        ‖alg.x (k.1 + 1) - 2 • alg.x k.1 + alg.x (k.1 - 1)‖ ^ 2) ≤
        2 * h ^ 2 * (E1 + beta * (1 / lam) / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      IsDryFrictionCritical phi fLam xInf ∧
      HasFiniteLength (fun k ↦ ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ (alg.x k)) ∧
      Tendsto (fun k ↦ ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ (alg.x k))
        Filter.atTop (𝓝 pInf) ∧
      pInf = ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ xInf ∧
      ((1 / lam) • (xInf - pInf) ∈ subdifferential F pInf) ∧
      (-gradient fLam xInf ∈ interior (subdifferential phi 0) →
        let q := 1 / Real.sqrt (1 + 2 * h * (gamma * lam - beta) / (lam + beta * h))
        0 < q ∧ q < 1 ∧ ∃ k0, ∀ k ≥ k0,
          ‖alg.x (k + 1) - alg.x k‖ ≤ q ^ (k - k0) * ‖alg.x (k0 + 1) - alg.x k0‖ ∧
          ‖alg.x k - xInf‖ ≤ q ^ (k - k0) / (1 - q) * ‖alg.x (k0 + 1) - alg.x k0‖) ∧
      (‖gradient fLam xInf‖ < r →
        Metric.ball (0 : H) r ⊆ subdifferential phi 0 → IsFinitelyConvergent alg.x) := by
  rcases hMoreau with ⟨hderiv, hLip, hCont, hbelowLam, hnonexp⟩
  let P : H → H := ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩
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
    hLnonneg hbelowLam hpositive hr hdf_r hgamma'
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
    hdf smooth xInf hfLam hLip hLnonneg hbelowLam hpositive hr hdf_r hgamma' hlim
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
    simpa only [hrate, hsmooth] using hgeo.1 (by simpa [moreauGrad, hgrad_eq] using hinterior)
  · intro hnorm hball
    obtain ⟨kStop, hkStop⟩ := hgeo.2 (by simpa [moreauGrad, hgrad_eq] using hnorm)
    exact eventually_constant_of_eventual_successor_eq alg.x kStop (by
      simpa only [hsmooth] using hkStop)
