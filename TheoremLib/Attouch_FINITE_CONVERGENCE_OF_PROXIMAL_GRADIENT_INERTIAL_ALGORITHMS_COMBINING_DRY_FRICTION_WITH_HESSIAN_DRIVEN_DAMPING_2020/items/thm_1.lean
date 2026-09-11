import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_lem_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_4
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_thm_2
import Mathlib

open scoped InnerProductSpace

open ERealFunction

/-- A sequence has finite length when its increments are summable. -/
def HasFiniteLength {H : Type*} [NormedAddCommGroup H] (x : ℕ → H) : Prop :=
  Summable (fun k ↦ ‖x (k + 1) - x k‖)

/-- The stationary inclusion at the limit point. -/
def IsDryFrictionCritical {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (phi f : H → ℝ) (x : H) : Prop := -gradient f x ∈ subdifferential phi 0

/-- An open subgradient ball gives the sharp linear dry-friction bound. -/
theorem subgradient_ball_exact_linear_lower_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) {r : ℝ} (hzero : phi 0 = 0) (hr : 0 < r)
    (hball : Metric.ball (0 : H) r ⊆ subdifferential phi 0) :
    ∀ u : H, r * ‖u‖ ≤ phi u := by
  intro u
  by_cases hu : u = 0
  · simp [hu, hzero]
  by_contra hru
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hquot : phi u / ‖u‖ < r := (div_lt_iff₀ hnorm).mpr (lt_of_not_ge hru)
  obtain ⟨t, htquot, htr⟩ := exists_between hquot
  let p : H := t • ((‖u‖)⁻¹ • u)
  have hphi : 0 ≤ phi u := by
    have hp' := hball (Metric.mem_ball_self hr) u
    change (⟪u - 0, 0⟫_ℝ : EReal) + (phi 0 : EReal) ≤ (phi u : EReal) at hp'
    norm_cast at hp'
    simp [hzero, inner_zero_right] at hp'
    exact hp'
  have ht : 0 < t := lt_of_le_of_lt (div_nonneg hphi (norm_nonneg u)) htquot
  have hp_norm : ‖p‖ < r := by
    dsimp [p]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u)]
    field_simp [ne_of_gt hnorm]
    simpa using htr
  have hp : p ∈ subdifferential phi 0 := hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hp_norm)
  have hinner : inner ℝ p u = t * ‖u‖ := by
    dsimp [p]
    rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [map_inv₀, starRingEnd_apply, star_trivial]
    field_simp [ne_of_gt hnorm]
  have hlower : t * ‖u‖ ≤ phi u := by
    have hp' := hp u
    change (⟪u - 0, p⟫_ℝ : EReal) + (phi 0 : EReal) ≤ (phi u : EReal) at hp'
    norm_cast at hp'
    simp [hzero] at hp'
    rw [real_inner_comm] at hp'
    rw [← hinner]
    exact hp'
  have hupper : phi u < t * ‖u‖ := (div_lt_iff₀ hnorm).mp htquot
  exact (not_lt_of_ge hlower hupper)

private theorem inner_sub_self_energy_identity {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) :
    inner ℝ (u - v) u = (1 / 2 : ℝ) * ‖u‖ ^ 2 - (1 / 2 : ℝ) * ‖v‖ ^ 2 +
      (1 / 2 : ℝ) * ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v u]
  ring

private theorem finite_length_tendsto {H : Type*} [NormedAddCommGroup H] [CompleteSpace H]
    (x : ℕ → H) (hs : Summable (fun k ↦ ‖x (k + 1) - x k‖)) :
    ∃ a, Filter.Tendsto x Filter.atTop (nhds a) := by
  have hdist : Summable (fun k ↦ dist (x k) (x k.succ)) := by
    simpa [dist_eq_norm, Nat.succ_eq_add_one, norm_sub_rev] using hs
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)

/-- Strong limits of subgradients of a continuous convex function remain subgradients. -/
theorem convex_subgradient_limit_at_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (u q : ℕ → H) (q0 : H) (hphi : Continuous phi)
    (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds q0))
    (hmem : ∀ n, q n ∈ subdifferential phi (u n)) :
    q0 ∈ subdifferential phi 0 := by
  rw [subdifferential]
  intro y
  change (⟪y - 0, q0⟫_ℝ : EReal) + (phi 0 : EReal) ≤ (phi y : EReal)
  norm_cast
  rw [real_inner_comm, add_comm]
  have hu' : Filter.Tendsto (fun n => y - u n) Filter.atTop (nhds (y - 0)) :=
    (continuous_const.sub continuous_id : Continuous fun x : H => y - x).tendsto 0 |>.comp hu
  have hinter : Filter.Tendsto (fun n => inner ℝ (q n) (y - u n)) Filter.atTop
      (nhds (inner ℝ q0 (y - 0))) :=
    continuous_inner.tendsto (q0, y - 0) |>.comp (hq.prodMk_nhds hu')
  have hright : Filter.Tendsto (fun n => phi (u n) + inner ℝ (q n) (y - u n))
      Filter.atTop (nhds (phi 0 + inner ℝ q0 (y - 0))) :=
    (hphi.tendsto 0 |>.comp hu).add hinter
  have hev : ∀ᶠ n in Filter.atTop, phi (u n) + inner ℝ (q n) (y - u n) ≤ phi y := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hny := (hmem n) y
    change (⟪y - u n, q n⟫_ℝ : EReal) + (phi (u n) : EReal) ≤ (phi y : EReal) at hny
    norm_cast at hny
    rw [real_inner_comm, add_comm] at hny
    exact hny
  exact le_of_tendsto_of_tendsto hright
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => phi y) Filter.atTop (nhds (phi y)))
    hev

/-- Reindex a series over the positive natural numbers by predecessor. -/
theorem tsum_subtype_succ_reindex {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    (a : ℕ → α) :
    tsum (fun k : {k : ℕ // 1 ≤ k} => a k.1) = tsum (fun n : ℕ => a (n + 1)) := by
  let e : ℕ ≃ {k : ℕ // 1 ≤ k} :=
    { toFun := fun n => ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩
      invFun := fun k => k.1 - 1
      left_inv := by intro n; simp
      right_inv := by intro k; simp [Nat.sub_add_cancel k.2] }
  simpa [e] using (Equiv.tsum_eq e (fun k : {k : ℕ // 1 ≤ k} => a k.1)).symm

private theorem IPAHDD_shifted_recurrence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f phi : H → ℝ) (hphi : phi.toEReal ∈ Γ₀(H))
    (h gamma beta : ℝ) (alg : IPAHDD f phi.toEReal hphi h gamma beta) (hh : 0 < h)
    (hg : 0 < gamma) (k : ℕ) :
    ∃ q, q ∈ subdifferential phi ((1 / h) • (alg.x (k + 2) - alg.x (k + 1))) ∧
      ((1 / h) • (alg.x (k + 2) - alg.x (k + 1)) -
          (1 / h) • (alg.x (k + 1) - alg.x k) +
          gamma • (alg.x (k + 2) - alg.x (k + 1)) + h • q +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) = 0) := by
  let D : ℝ := 1 + h * gamma
  let z : H :=
    (1 / (h * D)) • (alg.x (k + 1) - alg.x k) -
      (beta / D) • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) -
      (h / D) • gradient f (alg.x (k + 1))
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [mul_pos hh hg]
  have hD0 : D ≠ 0 := ne_of_gt hD
  -- The proximal point is Foundation's proximity operator, and its residual is the subgradient
  -- witness `q` (Proposition 16.44).
  have hlam_pos : 0 < h / D := div_pos hh hD
  let P : H → H := ERealFunction.scaledProximityOperator phi.toEReal hphi ⟨h / D, hlam_pos⟩
  have hmem : (h / D)⁻¹ • (z - P z) ∈ subdifferential phi (P z) :=
    ERealFunction.scaledProximityOperator_residual_mem hphi ⟨h / D, hlam_pos⟩ z
  let q : H := (h / D)⁻¹ • (z - P z)
  have hq : q ∈ subdifferential phi (P z) := by
    simpa [q, P] using hmem
  have hqeq : (h / D) • q = z - P z := by
    dsimp [q]
    rw [smul_smul, mul_inv_cancel₀ (div_ne_zero hh.ne' hD0)]
    simp
  have hstep : h • P z = alg.x (k + 2) - alg.x (k + 1) := by
    rw [alg.update k]
    simp [P, z, D]
  have hp : P z = (1 / h) • (alg.x (k + 2) - alg.x (k + 1)) := by
    calc
      P z = (1 / h) • (h • P z) := by
        rw [smul_smul]
        field_simp [hh.ne']
        simp
      _ = (1 / h) • (alg.x (k + 2) - alg.x (k + 1)) := by rw [hstep]
  refine ⟨q, ?_, ?_⟩
  · simpa [hp] using hq
  · have hscaled := congrArg (fun w : H => D • w) hqeq
    rw [hp] at hscaled
    dsimp [z] at hscaled
    simp only [smul_sub, smul_smul] at hscaled
    have h1 : D * (1 / (h * D)) = 1 / h := by field_simp [hh.ne', hD0]
    have h2 : D * (beta / D) = beta := by field_simp [hD0]
    have h3 : D * (h / D) = h := by field_simp [hD0]
    have h4 : D * (1 / h) = 1 / h + gamma := by
      dsimp [D]
      field_simp [hh.ne']
    rw [h1, h2, h3, h4] at hscaled
    simp only [smul_sub, add_smul] at hscaled ⊢
    rw [hscaled]
    abel

private theorem smooth_descent_of_fderiv_lipschitz {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ) (L : ℝ) (hf : ContDiff ℝ 1 f)
    (hL : HasLipschitzGradient (gradient f) L) (x y : H) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 := by
  have hgrad : ∀ z, HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    fun z => hasFDerivAt_gradient f hf z
  apply AttouchPeypouquetRedont2014.descent_lemma f (gradient f) L
  · exact fun z => (hgrad z).differentiableAt
  · intro z u
    rw [(hgrad z).fderiv]
    exact innerSL_apply_apply ℝ (gradient f z) u
  · exact hL

/-- Adding the first term back preserves summability of a natural sequence. -/
private theorem summable_real_of_summable_real_succ (a : ℕ → ℝ)
    (ha : Summable (fun n => a (n + 1))) : Summable a := by
  exact (summable_nat_add_iff (f := a) 1).mp ha

/-- Theorem 2.1: IPAHDD trajectories have finite length and satisfy the limit inclusion. -/
theorem IPAHDD_finiteLength_and_critical {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (f phi : H → ℝ) (h gamma beta L r : ℝ) (hdf : DryFriction phi)
    (alg : IPAHDD f phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta)
    (hf : ContDiff ℝ 1 f) (hL : HasLipschitzGradient (gradient f) L)
    (hL_nonneg : 0 ≤ L)
    (hbelow : ∃ c : ℝ, ∀ x, c ≤ f x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hr : 0 < r) (hdf_r : Metric.ball (0 : H) r ⊆ subdifferential phi 0)
    (hgamma : gamma ≥ L * (h / 2 + beta)) :
    ∃ xInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 + f (alg.x 1) - sInf (Set.range f) ∧
      HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (nhds xInf) ∧
      IsDryFrictionCritical phi f xInf ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦
        ‖alg.x (k.1 + 1) - 2 • alg.x k.1 + alg.x (k.1 - 1)‖ ^ 2) ≤
        2 * h ^ 2 * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
  let d : ℕ → H := fun k ↦ alg.x (k + 1) - alg.x k
  let v : ℕ → H := fun k ↦ (1 / h) • d k
  rcases hpositive with ⟨hh, hg, hb⟩
  have hgrad : ∀ z, HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    fun z => hasFDerivAt_gradient f hf z
  have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  have hden : 0 < 1 + h * gamma := by
    nlinarith [mul_pos hh hg]
  have hden0 : 1 + h * gamma ≠ 0 := ne_of_gt hden
  have hlam : 0 < h / (1 + h * gamma) := div_pos hh hden
  have hc : 0 ≤ beta * L / (2 * h) := by
    exact div_nonneg (mul_nonneg hb.le hL_nonneg) (by positivity)
  have hdry : ∀ u : H, r * ‖u‖ ≤ phi u :=
    subgradient_ball_exact_linear_lower_bound phi hdf.value_at_zero hr hdf_r
  have hshift (k : ℕ) :
      ∃ q, q ∈ subdifferential phi (v (k + 1)) ∧
        (v (k + 1) - v k + gamma • d (k + 1) + h • q +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) = 0) := by
    simpa [v, d, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      IPAHDD_shifted_recurrence f phi hdf.toEReal_mem_gammaZero h gamma beta alg hh hg k
  have hdescent (x y : H) :
      f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 :=
    smooth_descent_of_fderiv_lipschitz f L hf hL x y
  have hdv (k : ℕ) : d k = h • v k := by
    dsimp [d, v]
    rw [smul_smul]
    field_simp [hh.ne']
    simp
  have hraw (k : ℕ) :
      (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
        (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
        gamma * h * ‖v (k + 1)‖ ^ 2 + h * phi (v (k + 1)) +
        beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
        inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) ≤ 0 := by
    obtain ⟨q, hq, hrec⟩ := hshift k
    have hinner := congrArg (fun z : H => inner ℝ z (v (k + 1))) hrec
    have hinert : inner ℝ (v (k + 1) - v k) (v (k + 1)) =
        (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
          (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 :=
      inner_sub_self_energy_identity _ _
    have hdamp : inner ℝ (gamma • d (k + 1)) (v (k + 1)) =
        gamma * h * ‖v (k + 1)‖ ^ 2 := by
      rw [hdv (k + 1), inner_smul_left, inner_smul_left,
        real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      ring
    have hqterm : inner ℝ (h • q) (v (k + 1)) = h * inner ℝ q (v (k + 1)) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
    have hbetaterm :
        inner ℝ (beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) (v (k + 1)) =
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
    have hgradterm : inner ℝ (h • gradient f (alg.x (k + 1))) (v (k + 1)) =
        inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
      dsimp [v]
      rw [inner_smul_left, inner_smul_right]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hh.ne']
    have hscalar :
        (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
          (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
          gamma * h * ‖v (k + 1)‖ ^ 2 + h * inner ℝ q (v (k + 1)) +
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) = 0 := by
      simpa only [inner_add_left, inner_sub_left, inner_zero_left, add_zero,
        hinert, hdamp, hqterm, hbetaterm, hgradterm] using hinner
    have hphi : phi (v (k + 1)) ≤ inner ℝ q (v (k + 1)) := by
      have hq0 := hq 0
      change (⟪0 - v (k + 1), q⟫_ℝ : EReal) + (phi (v (k + 1)) : EReal) ≤
        (phi 0 : EReal) at hq0
      norm_cast at hq0
      simp [hdf.value_at_zero, inner_neg_left] at hq0
      rw [real_inner_comm] at hq0
      linarith
    have hhphi : h * phi (v (k + 1)) ≤ h * inner ℝ q (v (k + 1)) :=
      mul_le_mul_of_nonneg_left hphi hh.le
    linarith
  have hfric (k : ℕ) : r * ‖d (k + 1)‖ ≤ h * phi (v (k + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left (hdry (v (k + 1))) hh.le
    have hnorm : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
      rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    rw [hnorm]
    nlinarith
  have hcross (k : ℕ) :
      beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
        beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2) := by
    have hnormv : ‖v (k + 1)‖ = ‖d (k + 1)‖ / h := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / h)]
      ring
    have hinner :
        inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
          L * ‖d k‖ * (‖d (k + 1)‖ / h) := by
      calc
        inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
            ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖ :=
          real_inner_le_norm _ _
        _ ≤ (L * ‖alg.x (k + 1) - alg.x k‖) * ‖v (k + 1)‖ := by
          exact mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg _)
        _ = L * ‖d k‖ * (‖d (k + 1)‖ / h) := by simp [d, hnormv]
    have hmul := mul_le_mul_of_nonneg_left hinner hb.le
    have hyoung : 2 * (‖d k‖ * ‖d (k + 1)‖) ≤
        ‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖d k‖ - ‖d (k + 1)‖)]
    have hcoef : 0 ≤ beta * L / h := by positivity
    have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
    field_simp [hh.ne'] at hmul hyoung' ⊢
    nlinarith
  have hcross_lower (k : ℕ) :
      -(beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2)) ≤
        beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
    have hnormv : ‖v (k + 1)‖ = ‖d (k + 1)‖ / h := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / h)]
      ring
    have hnormgrad :
        ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ ≤ L * ‖d k‖ := by
      simpa [d] using hL (alg.x (k + 1)) (alg.x k)
    have hprod :
        ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖ ≤
          (L * ‖d k‖) * ‖v (k + 1)‖ :=
      mul_le_mul_of_nonneg_right hnormgrad (norm_nonneg _)
    have hinter :
        -(L * ‖d k‖ * (‖d (k + 1)‖ / h)) ≤
          inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
      calc
        -(L * ‖d k‖ * (‖d (k + 1)‖ / h)) =
            -((L * ‖d k‖) * ‖v (k + 1)‖) := by rw [hnormv]
        _ ≤ -(‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖) :=
            neg_le_neg hprod
        _ ≤ inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) :=
            neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have hmul := mul_le_mul_of_nonneg_left hinter hb.le
    have hyoung : 2 * (‖d k‖ * ‖d (k + 1)‖) ≤
        ‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖d k‖ - ‖d (k + 1)‖)]
    have hcoef : 0 ≤ beta * L / h := by positivity
    have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
    field_simp [hh.ne'] at hmul hyoung' ⊢
    nlinarith
  let c : ℝ := beta * L / (2 * h)
  let E : ℕ → ℝ := fun k =>
    (1 / 2 : ℝ) * ‖v k‖ ^ 2 + f (alg.x (k + 1)) - sInf (Set.range f)
  let M : ℕ → ℝ := fun k => E k + c * ‖d k‖ ^ 2
  have hc' : 0 ≤ c := by simpa [c] using hc
  obtain ⟨a, ha⟩ := hbelow
  have hbounded : BddBelow (Set.range f) := ⟨a, by
    rintro y ⟨z, rfl⟩
    exact ha z⟩
  have hE_nonneg (k : ℕ) : 0 ≤ E k := by
    have hinf : sInf (Set.range f) ≤ f (alg.x (k + 1)) :=
      csInf_le hbounded ⟨alg.x (k + 1), rfl⟩
    dsimp [E]
    have hkin : 0 ≤ (1 / 2 : ℝ) * ‖v k‖ ^ 2 := by positivity
    linarith
  have hM_nonneg (k : ℕ) : 0 ≤ M k := by
    dsimp [M]
    exact add_nonneg (hE_nonneg k) (mul_nonneg hc' (sq_nonneg _))
  have hcoef : c ≤ gamma / h - L / 2 - beta * L / (2 * h) := by
    dsimp [c]
    field_simp [hh.ne']
    nlinarith [hgamma]
  have hacc_vec (k : ℕ) :
      d (k + 1) - d k = alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k := by
    dsimp [d]
    abel
  have hacc_id (k : ℕ) :
      (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 =
        (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
    have hv : v (k + 1) - v k = (1 / h) • (d (k + 1) - d k) := by
      dsimp [v, d]
      simp only [smul_sub]
    rw [hv, hacc_vec, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / h)]
    field_simp [hh.ne']
  have hstep (k : ℕ) :
      M (k + 1) - M k +
          (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
          r * ‖d (k + 1)‖ ≤ 0 := by
    have hdesc := hdescent (alg.x (k + 1)) (alg.x (k + 2))
    have hdesc' :
        f (alg.x (k + 2)) - f (alg.x (k + 1)) -
            (L / 2) * ‖d (k + 1)‖ ^ 2 ≤
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
      dsimp [d]
      norm_num [Nat.add_assoc] at hdesc ⊢
      linarith
    have hdamp : gamma * h * ‖v (k + 1)‖ ^ 2 =
        (gamma / h) * ‖d (k + 1)‖ ^ 2 := by
      have hnorm : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
        rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      rw [hnorm]
      field_simp [hh.ne']
    have hmain :
        E (k + 1) - E k + (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
          (gamma / h - L / 2 - c) * ‖d (k + 1)‖ ^ 2 + r * ‖d (k + 1)‖ ≤
          c * ‖d k‖ ^ 2 := by
      have hraw' := hraw k
      rw [hdamp] at hraw'
      dsimp [E, c]
      linarith [hraw', hfric k, hcross_lower k, hdesc']
    have hcoeftimes : c * ‖d (k + 1)‖ ^ 2 ≤
        (gamma / h - L / 2 - c) * ‖d (k + 1)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · linarith [hcoef]
      · exact sq_nonneg _
    calc
      M (k + 1) - M k +
          (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
          r * ‖d (k + 1)‖ =
          E (k + 1) - E k + (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
            c * ‖d (k + 1)‖ ^ 2 - c * ‖d k‖ ^ 2 + r * ‖d (k + 1)‖ := by
              rw [hacc_id k]
              dsimp [M]
              ring
      _ ≤ 0 := by linarith
  have htel (N : ℕ) :
      M N + ∑ k ∈ Finset.range N,
          ((1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
            r * ‖d (k + 1)‖) ≤ M 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep N]
  have hsum_d (N : ℕ) : ∑ k ∈ Finset.range N, ‖d (k + 1)‖ ≤ M 0 / r := by
    have hacc_nonneg : 0 ≤ ∑ k ∈ Finset.range N,
        (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro k hk
      positivity
    have hlen_nonneg : 0 ≤ ∑ k ∈ Finset.range N, r * ‖d (k + 1)‖ := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg hr.le (norm_nonneg _)
    have hle := htel N
    rw [Finset.sum_add_distrib] at hle
    have hlen_factor :
        (∑ k ∈ Finset.range N, r * ‖d (k + 1)‖) =
          r * (∑ k ∈ Finset.range N, ‖d (k + 1)‖) := by
      rw [Finset.mul_sum]
    rw [hlen_factor] at hle
    have hright : r * (∑ k ∈ Finset.range N, ‖d (k + 1)‖) ≤ M 0 := by
      linarith [hM_nonneg N]
    have hright' : (∑ k ∈ Finset.range N, ‖d (k + 1)‖) * r ≤ M 0 := by
      simpa [mul_comm] using hright
    exact (le_div_iff₀ hr).mpr hright'
  have hsum_acc (N : ℕ) : ∑ k ∈ Finset.range N,
      ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 ≤ 2 * h ^ 2 * M 0 := by
    have hacc_nonneg : 0 ≤ ∑ k ∈ Finset.range N,
        (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro k hk
      positivity
    have hlen_nonneg : 0 ≤ ∑ k ∈ Finset.range N, r * ‖d (k + 1)‖ := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg hr.le (norm_nonneg _)
    have hle := htel N
    rw [Finset.sum_add_distrib] at hle
    have hscaled : (1 / (2 * h ^ 2)) *
        (∑ k ∈ Finset.range N,
          ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2) ≤ M 0 := by
      rw [Finset.mul_sum]
      linarith [hM_nonneg N]
    have hpos : 0 < 2 * h ^ 2 := by positivity
    have hmult := mul_le_mul_of_nonneg_left hscaled hpos.le
    have hcancel : (2 * h ^ 2) * ((1 / (2 * h ^ 2)) *
        (∑ k ∈ Finset.range N,
          ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2)) =
        ∑ k ∈ Finset.range N,
          ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
      field_simp [hh.ne']
    rw [hcancel] at hmult
    simpa [mul_assoc] using hmult
  have hs_d : Summable (fun k => ‖d (k + 1)‖) :=
    summable_of_sum_range_le (fun k => norm_nonneg _) hsum_d
  have hs_acc : Summable (fun k =>
      ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2) :=
    summable_of_sum_range_le (fun k => sq_nonneg _) hsum_acc
  have hs : Summable (fun k : ℕ => ‖d k‖) :=
    summable_real_of_summable_real_succ (fun k : ℕ => ‖d k‖) hs_d
  have hfinite : HasFiniteLength alg.x := by
    unfold HasFiniteLength
    simpa [d] using hs
  obtain ⟨xInf, hxInf⟩ := finite_length_tendsto alg.x hfinite
  let E1 : ℝ := (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
    f (alg.x 1) - sInf (Set.range f)
  have hE1 : E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
      f (alg.x 1) - sInf (Set.range f) := rfl
  have hM0 : M 0 = E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2 := by
    dsimp [M, E, c, v, d, E1]
  have hlength0 : tsum (fun k => ‖d (k + 1)‖) ≤ M 0 / r :=
    Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) hsum_d
  have hlength : tsum (fun k : {k : ℕ // 1 ≤ k} =>
      ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
      (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
    change tsum (fun k : {k : ℕ // 1 ≤ k} =>
      (fun n : ℕ => ‖d n‖) k.1) ≤ _
    calc
      tsum (fun k : {k : ℕ // 1 ≤ k} => (fun n : ℕ => ‖d n‖) k.1) =
          tsum (fun n : ℕ => ‖d (n + 1)‖) :=
        tsum_subtype_succ_reindex (fun n : ℕ => ‖d n‖)
      _ ≤ M 0 / r := hlength0
      _ = (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
        rw [hM0]
        field_simp [hr.ne']
  have hacc0 : tsum (fun k =>
      ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2) ≤ 2 * h ^ 2 * M 0 :=
    Real.tsum_le_of_sum_range_le (fun k => sq_nonneg _) hsum_acc
  have hacc : tsum (fun k : {k : ℕ // 1 ≤ k} =>
      ‖alg.x (k.1 + 1) - 2 • alg.x k.1 + alg.x (k.1 - 1)‖ ^ 2) ≤
      2 * h ^ 2 * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
    change tsum (fun k : {k : ℕ // 1 ≤ k} =>
      (fun n : ℕ => ‖alg.x (n + 1) - 2 • alg.x n + alg.x (n - 1)‖ ^ 2) k.1) ≤ _
    calc
      tsum (fun k : {k : ℕ // 1 ≤ k} =>
          (fun n : ℕ => ‖alg.x (n + 1) - 2 • alg.x n + alg.x (n - 1)‖ ^ 2) k.1) =
          tsum (fun n : ℕ =>
            ‖alg.x ((n + 1) + 1) - 2 • alg.x (n + 1) + alg.x ((n + 1) - 1)‖ ^ 2) :=
        tsum_subtype_succ_reindex
          (fun n : ℕ => ‖alg.x (n + 1) - 2 • alg.x n + alg.x (n - 1)‖ ^ 2)
      _ ≤ 2 * h ^ 2 * M 0 := by simpa [Nat.add_assoc, Nat.add_sub_cancel] using hacc0
      _ = 2 * h ^ 2 * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by rw [hM0]
  have hd_norm : Filter.Tendsto (fun k => ‖d k‖) Filter.atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  have hd : Filter.Tendsto d Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hd_norm
  have hd_succ : Filter.Tendsto (fun k => d (k + 1)) Filter.atTop (nhds 0) := by
    simpa using hd.comp (Filter.tendsto_add_atTop_nat 1)
  have hv : Filter.Tendsto v Filter.atTop (nhds 0) := by
    simpa [v] using hd.const_smul (1 / h)
  have hv_succ : Filter.Tendsto (fun k => v (k + 1)) Filter.atTop (nhds 0) := by
    simpa using hv.comp (Filter.tendsto_add_atTop_nat 1)
  have hv_diff : Filter.Tendsto (fun k => v (k + 1) - v k) Filter.atTop (nhds 0) :=
    by simpa using hv_succ.sub hv
  have hxInf_succ : Filter.Tendsto (fun k => alg.x (k + 1)) Filter.atTop (nhds xInf) := by
    simpa using hxInf.comp (Filter.tendsto_add_atTop_nat 1)
  have hgrad : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hxInf
  have hgrad_succ : Filter.Tendsto (fun k => gradient f (alg.x (k + 1)))
      Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hxInf_succ
  have hgrad_diff : Filter.Tendsto
      (fun k => gradient f (alg.x (k + 1)) - gradient f (alg.x k)) Filter.atTop (nhds 0) :=
    by simpa using hgrad_succ.sub hgrad
  let q : ℕ → H := fun k => Classical.choose (hshift k)
  have hqmem (k : ℕ) : q k ∈ subdifferential phi (v (k + 1)) :=
    (Classical.choose_spec (hshift k)).1
  have hqrec (k : ℕ) :
      v (k + 1) - v k + gamma • d (k + 1) + h • q k +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) = 0 :=
    (Classical.choose_spec (hshift k)).2
  have hqsolve (k : ℕ) :
      h • q k = -(v (k + 1) - v k + gamma • d (k + 1) +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1))) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      h • q k + (v (k + 1) - v k + gamma • d (k + 1) +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1))) =
          v (k + 1) - v k + gamma • d (k + 1) + h • q k +
            beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
            h • gradient f (alg.x (k + 1)) := by ac_rfl
      _ = 0 := hqrec k
  have hdamp : Filter.Tendsto (fun k => gamma • d (k + 1)) Filter.atTop (nhds 0) :=
    by simpa using hd_succ.const_smul gamma
  have hbeta : Filter.Tendsto
      (fun k => beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)))
      Filter.atTop (nhds 0) := by simpa using hgrad_diff.const_smul beta
  have hgrad_term : Filter.Tendsto (fun k => h • gradient f (alg.x (k + 1)))
      Filter.atTop (nhds (h • gradient f xInf)) := hgrad_succ.const_smul h
  have hright : Filter.Tendsto (fun k =>
      -(v (k + 1) - v k + gamma • d (k + 1) +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)))) Filter.atTop (nhds (-(h • gradient f xInf))) := by
    simpa using (((hv_diff.add hdamp).add hbeta).add hgrad_term).neg
  have hq_scaled : Filter.Tendsto (fun k => h • q k) Filter.atTop
      (nhds (h • (-gradient f xInf))) := by
    convert hright using 1
    · ext k
      rw [hqsolve]
    · simp
  have hscalar : (1 / h : ℝ) * h = 1 := by field_simp [hh.ne']
  have hq : Filter.Tendsto q Filter.atTop (nhds (-gradient f xInf)) := by
    have hq' := hq_scaled.const_smul (1 / h)
    have hqfun : (fun k => (1 / h) • (h • q k)) = q := by
      funext k
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    have hqlim : (1 / h) • (h • (-gradient f xInf)) = -gradient f xInf := by
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    rw [hqfun, hqlim] at hq'
    exact hq'
  have hcritical : IsDryFrictionCritical phi f xInf := by
    unfold IsDryFrictionCritical
    exact convex_subgradient_limit_at_zero phi (fun k => v (k + 1)) q
      (-gradient f xInf) hdf.continuous hv_succ hq hqmem
  exact ⟨xInf, E1, hE1, hfinite, hxInf, hcritical, hlength, hacc⟩
