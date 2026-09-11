import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_6

/-- Coordinatewise IPAHDD update with soft thresholding on velocities. -/
noncomputable def softThresholdVector {n : Type*} (a : ℝ) (ha : 0 ≤ a)
    (x : EuclideanSpace ℝ n) : EuclideanSpace ℝ n :=
  WithLp.toLp 2 fun i ↦ softThreshold a ha (x.ofLp i)

structure IPAHDDSoftThreshold {n : Type*} [Fintype n]
    (f : EuclideanSpace ℝ n → ℝ) (h gamma beta r : ℝ) where
  x : ℕ → EuclideanSpace ℝ n
  initial0 : EuclideanSpace ℝ n
  initial1 : EuclideanSpace ℝ n
  init0 : x 0 = initial0
  init1 : x 1 = initial1
  threshold_nonneg : 0 ≤ h * r / (1 + h * gamma)
  update (k : ℕ) : x (k + 2) = x (k + 1) + h • softThresholdVector (h * r / (1 + h * gamma)) threshold_nonneg
    ((1 / (h * (1 + h * gamma))) • (x (k + 1) - x k) -
      (beta / (1 + h * gamma)) • (gradient f (x (k + 1)) - gradient f (x k)) -
      (h / (1 + h * gamma)) • gradient f (x (k + 1)))
