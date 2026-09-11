import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_5
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_1

open scoped InnerProductSpace

open ERealFunction

private theorem IPAHDDN_shifted_recurrence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f phi : H → ℝ) (hphi : phi.toEReal ∈ Γ₀(H))
    (h gamma beta : ℝ) (alg : IPAHDDN f phi.toEReal hphi h gamma beta) (hh : 0 < h)
    (hg : 0 < gamma) (k : ℕ) :
    ∃ q, q ∈ subdifferential phi ((1 / h) • (alg.x (k + 2) - alg.x (k + 1))) ∧
      ((1 / h) • (alg.x (k + 2) - alg.x (k + 1)) -
          (1 / h) • (alg.x (k + 1) - alg.x k) + gamma •
            (alg.x (k + 2) - alg.x (k + 1)) + h • q +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.y k) = 0) := by
  let D : ℝ := 1 + h * gamma
  let z : H :=
    (1 / h) • (alg.y k - alg.x (k + 1)) -
      (beta / D) • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) -
      (h / D) • gradient f (alg.y k)
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [mul_pos hh hg]
  have hD0 : D ≠ 0 := ne_of_gt hD
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
  refine ⟨q, by simpa [hp] using hq, ?_⟩
  have hy : (1 / h) • (alg.y k - alg.x (k + 1)) =
      (1 / (h * D)) • (alg.x (k + 1) - alg.x k) := by
    rw [show alg.y k = alg.x (k + 1) + (1 / D) •
        (alg.x (k + 1) - alg.x k) by simpa [D] using alg.extrapolate k]
    rw [add_sub_cancel_left, smul_smul]
    congr 1
    field_simp [hh.ne', hD0]
  have hz : z = (1 / (h * D)) • (alg.x (k + 1) - alg.x k) -
      (beta / D) • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) -
      (h / D) • gradient f (alg.y k) := by
    dsimp [z]
    rw [hy]
  have hscaled := congrArg (fun w : H => D • w) hqeq
  rw [hp] at hscaled
  rw [hz] at hscaled
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

private theorem IPAHDDN_finite_length_tendsto {H : Type*} [NormedAddCommGroup H]
    [CompleteSpace H] (x : ℕ → H)
    (hs : Summable (fun k ↦ ‖x (k + 1) - x k‖)) :
    ∃ a, Filter.Tendsto x Filter.atTop (nhds a) := by
  have hdist : Summable (fun k ↦ dist (x k) (x k.succ)) := by
    simpa [dist_eq_norm, Nat.succ_eq_add_one, norm_sub_rev] using hs
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)

private theorem IPAHDDN_inner_sub_self_energy_identity {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) :
    inner ℝ (u - v) u = (1 / 2 : ℝ) * ‖u‖ ^ 2 - (1 / 2 : ℝ) * ‖v‖ ^ 2 +
      (1 / 2 : ℝ) * ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v u]
  ring

private theorem IPAHDDN_smooth_descent_of_fderiv_lipschitz {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (L : ℝ) (hf : ContDiff ℝ 1 f)
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

private theorem IPAHDDN_summable_of_summable_succ (a : ℕ → ℝ)
    (ha : Summable (fun n => a (n + 1))) : Summable a :=
  (summable_nat_add_iff (f := a) 1).mp ha

private theorem IPAHDDN_parameter_quadratic_nonneg
    (h gamma beta L a b : ℝ) (hh : 0 < h) (hbpos : 0 < beta) (hL : 0 ≤ L)
    (hgamma : gamma ≥ (3 * L / 2) * (h + beta))
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ ((1 + h * gamma - L * h ^ 2 / 2 - 3 * beta * h * L / 2) / 2 +
        beta * h * L / 4) * (a ^ 2 + b ^ 2) -
      (1 + L * h ^ 2 / (1 + h * gamma)) * a * b := by
  have hD : 0 < 1 + h * gamma := by
    have : 0 ≤ gamma := le_trans (mul_nonneg (by positivity) (by positivity)) hgamma
    nlinarith [mul_nonneg hh.le this]
  have hgmult : (3 * L / 2) * (h + beta) * h ≤ gamma * h :=
    mul_le_mul_of_nonneg_right hgamma hh.le
  have hqbase : 1 + L * h ^ 2 ≤
      1 + h * gamma - L * h ^ 2 / 2 - 3 * beta * h * L / 2 := by
    nlinarith [mul_nonneg hL (mul_nonneg hh.le hbpos.le)]
  have hfrac : L * h ^ 2 / (1 + h * gamma) ≤ L * h ^ 2 := by
    apply (div_le_iff₀ hD).mpr
    have hgamma0 : 0 ≤ gamma := le_trans (mul_nonneg (by positivity) (by positivity)) hgamma
    have hD1 : 1 ≤ 1 + h * gamma := by nlinarith [mul_nonneg hh.le hgamma0]
    nlinarith [mul_nonneg hL (sq_nonneg h)]
  have hQ : 1 + L * h ^ 2 / (1 + h * gamma) ≤
      1 + h * gamma - L * h ^ 2 / 2 - 3 * beta * h * L / 2 := by
    linarith
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hmul := mul_le_mul_of_nonneg_right hQ hab
  have hcoef : 0 ≤ beta * h * L / 4 := by positivity
  have hqnon : 0 ≤ 1 + h * gamma - L * h ^ 2 / 2 - 3 * beta * h * L / 2 := by
    nlinarith [mul_nonneg hL (sq_nonneg h)]
  have hsum : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith
  have hquad := mul_le_mul_of_nonneg_left hsum (by linarith :
    0 ≤ (1 + h * gamma - L * h ^ 2 / 2 - 3 * beta * h * L / 2) / 2)
  nlinarith

/--
Theorem 3.1:
IPAHDD-N has finite length under its Lyapunov parameter conditions.
-/
theorem IPAHDDN_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f phi : H → ℝ) (h gamma beta L r : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDDN f phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta)
    (hf : ContDiff ℝ 1 f)
    (hL : HasLipschitzGradient (gradient f) L) (hL_nonneg : 0 ≤ L)
    (hbelow : ∃ c : ℝ, ∀ x, c ≤ f x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hgamma : gamma ≥ (3 * L / 2) * (h + beta)) (hh : L * h ^ 2 ≤ 1) :
    ∃ xInf, HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (nhds xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * ((1 / (2 * h ^ 2)) * (1 + h * gamma - L * h ^ 2 / 2) *
          ‖alg.x 1 - alg.x 0‖ ^ 2 + f (alg.x 1) - sInf (Set.range f)) ∧
      IsDryFrictionCritical phi f xInf ∧ Filter.Tendsto alg.y Filter.atTop (nhds xInf) := by
  let d : ℕ → H := fun k ↦ alg.x (k + 1) - alg.x k
  let v : ℕ → H := fun k ↦ (1 / h) • d k
  rcases hpositive with ⟨hh, hg, hb⟩
  have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  have hgrad : ∀ z, HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    fun z => hasFDerivAt_gradient f hf z
  have hD : 0 < 1 + h * gamma := by nlinarith [mul_pos hh hg]
  have hD0 : 1 + h * gamma ≠ 0 := ne_of_gt hD
  have hshift (k : ℕ) :
      ∃ q, q ∈ subdifferential phi (v (k + 1)) ∧
        (v (k + 1) - v k + gamma • d (k + 1) + h • q +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.y k) = 0) := by
    simpa [v, d, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      IPAHDDN_shifted_recurrence f phi hdf.toEReal_mem_gammaZero h gamma beta alg hh hg k
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
        inner ℝ (gradient f (alg.y k)) (d (k + 1)) ≤ 0 := by
    obtain ⟨q, hq, hrec⟩ := hshift k
    have hinner := congrArg (fun z : H => inner ℝ z (v (k + 1))) hrec
    have hinert := IPAHDDN_inner_sub_self_energy_identity (v (k + 1)) (v k)
    have hdamp : inner ℝ (gamma • d (k + 1)) (v (k + 1)) =
        gamma * h * ‖v (k + 1)‖ ^ 2 := by
      rw [hdv (k + 1), inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      ring
    have hqterm : inner ℝ (h • q) (v (k + 1)) = h * inner ℝ q (v (k + 1)) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
    have hbetaterm : inner ℝ (beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)))
        (v (k + 1)) = beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k))
          (v (k + 1)) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
    have hgradterm : inner ℝ (h • gradient f (alg.y k)) (v (k + 1)) =
        inner ℝ (gradient f (alg.y k)) (d (k + 1)) := by
      dsimp [v]
      rw [inner_smul_left, inner_smul_right]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hh.ne']
    have hscalar :
        (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
          (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
          gamma * h * ‖v (k + 1)‖ ^ 2 + h * inner ℝ q (v (k + 1)) +
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
          inner ℝ (gradient f (alg.y k)) (d (k + 1)) = 0 := by
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
    have hhphi := mul_le_mul_of_nonneg_left hphi hh.le
    linarith
  have hfric (k : ℕ) : r * ‖d (k + 1)‖ ≤ h * phi (v (k + 1)) := by
    have hdry := subgradient_ball_exact_linear_lower_bound phi hdf.value_at_zero
      hdf.radius_pos hdf.ball_subset (v (k + 1))
    have hmul := mul_le_mul_of_nonneg_left hdry hh.le
    have hnorm : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
      rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    rw [hnorm]
    nlinarith
  have hdescent (x y : H) :
      f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 :=
    IPAHDDN_smooth_descent_of_fderiv_lipschitz f L hf hL x y
  have hcross (k : ℕ) :
      beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
        (beta * h * L / 2) * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2) := by
    have hnormgrad : ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ ≤ L * ‖d k‖ := by
      simpa [d] using hL (alg.x (k + 1)) (alg.x k)
    have hinter : inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
        (L * ‖d k‖) * ‖v (k + 1)‖ :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hnormgrad (norm_nonneg _))
    have hmul := mul_le_mul_of_nonneg_left hinter hb.le
    have hnorm0 : ‖d k‖ = h * ‖v k‖ := by
      rw [hdv k, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    rw [hnorm0] at hmul
    have hyoung : 2 * (‖v k‖ * ‖v (k + 1)‖) ≤ ‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v k‖ - ‖v (k + 1)‖)]
    have hcoef : 0 ≤ beta * h * L / 2 := by positivity
    have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
    nlinarith
  have hsmooth (k : ℕ) :
      f (alg.x (k + 2)) - f (alg.x (k + 1)) - (L / 2) * ‖d (k + 1)‖ ^ 2 -
          (L / (1 + h * gamma)) * ‖d k‖ * ‖d (k + 1)‖ ≤
        inner ℝ (gradient f (alg.y k)) (d (k + 1)) := by
    have hextrap : alg.y k - alg.x (k + 1) =
        (1 / (1 + h * gamma)) • d k := by
      rw [alg.extrapolate k]
      dsimp [d]
      abel
    have hnormxy : ‖alg.x (k + 1) - alg.y k‖ =
        ‖d k‖ / (1 + h * gamma) := by
      rw [show alg.x (k + 1) - alg.y k = -(alg.y k - alg.x (k + 1)) by abel,
        norm_neg, hextrap, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 1 / (1 + h * gamma))]
      ring
    have hlip : ‖gradient f (alg.x (k + 1)) - gradient f (alg.y k)‖ ≤
        L * (‖d k‖ / (1 + h * gamma)) := by
      rw [← hnormxy]
      exact hL _ _
    have hinter : inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.y k)) (d (k + 1)) ≤
        (L * (‖d k‖ / (1 + h * gamma))) * ‖d (k + 1)‖ :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hlip (norm_nonneg _))
    have hdesc := hdescent (alg.x (k + 1)) (alg.x (k + 2))
    have hdiff : alg.x (k + 2) - alg.x (k + 1) = d (k + 1) := by
      rfl
    rw [hdiff] at hdesc
    have hsplit : inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) =
        inner ℝ (gradient f (alg.y k)) (d (k + 1)) +
          inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.y k)) (d (k + 1)) := by
      rw [inner_sub_left]
      ring
    rw [hsplit] at hdesc
    have hcoef : L * (‖d k‖ / (1 + h * gamma)) * ‖d (k + 1)‖ =
        (L / (1 + h * gamma)) * ‖d k‖ * ‖d (k + 1)‖ := by ring
    rw [hcoef] at hinter
    nlinarith
  have hcross_neg (k : ℕ) :
      -(beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1))) ≤
        (beta * h * L / 2) * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2) := by
    have hnormgrad : ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ ≤ L * ‖d k‖ := by
      simpa [d] using hL (alg.x (k + 1)) (alg.x k)
    have hinter : -inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
        (L * ‖d k‖) * ‖v (k + 1)‖ :=
      (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hnormgrad (norm_nonneg _)))
    have hmul := mul_le_mul_of_nonneg_left hinter hb.le
    have hnorm0 : ‖d k‖ = h * ‖v k‖ := by
      rw [hdv k, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    rw [hnorm0] at hmul
    have hyoung : 2 * (‖v k‖ * ‖v (k + 1)‖) ≤ ‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v k‖ - ‖v (k + 1)‖)]
    have hcoef : 0 ≤ beta * h * L / 2 := by positivity
    have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
    nlinarith
  let E : ℕ → ℝ := fun k ↦
    ((1 + h * gamma - L * h ^ 2 / 2) / 2) * ‖v k‖ ^ 2 +
      f (alg.x (k + 1)) - sInf (Set.range f)
  have hstep (k : ℕ) : E (k + 1) - E k + r * ‖d (k + 1)‖ ≤ 0 := by
    have hcombined := hraw k
    have htri : ‖v (k + 1)‖ ≤ ‖v k‖ + ‖v (k + 1) - v k‖ := by
      calc
        ‖v (k + 1)‖ = ‖v k + (v (k + 1) - v k)‖ := by
          apply congrArg norm
          abel
        _ ≤ ‖v k‖ + ‖v (k + 1) - v k‖ := norm_add_le _ _
    have htri' : ‖v k‖ ≤ ‖v (k + 1)‖ + ‖v (k + 1) - v k‖ := by
      calc
        ‖v k‖ = ‖v (k + 1) - (v (k + 1) - v k)‖ := by
          apply congrArg norm
          abel
        _ ≤ ‖v (k + 1)‖ + ‖v (k + 1) - v k‖ := norm_sub_le _ _
    have habs : |‖v (k + 1)‖ - ‖v k‖| ≤ ‖v (k + 1) - v k‖ := by
      rw [abs_le]
      constructor <;> linarith
    have hdiffsq : ‖v (k + 1)‖ ^ 2 + ‖v k‖ ^ 2 -
        2 * ‖v (k + 1)‖ * ‖v k‖ ≤ ‖v (k + 1) - v k‖ ^ 2 := by
      have hsquare := mul_self_le_mul_self (abs_nonneg (‖v (k + 1)‖ - ‖v k‖)) habs
      calc
        ‖v (k + 1)‖ ^ 2 + ‖v k‖ ^ 2 - 2 * ‖v (k + 1)‖ * ‖v k‖ =
            (‖v (k + 1)‖ - ‖v k‖) ^ 2 := by ring
        _ = |‖v (k + 1)‖ - ‖v k‖| ^ 2 := by rw [sq_abs]
        _ ≤ ‖v (k + 1) - v k‖ ^ 2 := by simpa [pow_two] using hsquare
    have hquad := IPAHDDN_parameter_quadratic_nonneg h gamma beta L
      ‖v (k + 1)‖ ‖v k‖ hh hb hL_nonneg hgamma (norm_nonneg _) (norm_nonneg _)
    have hnormk : ‖d k‖ = h * ‖v k‖ := by
      rw [hdv k, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hnormkp : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
      rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hsm := hsmooth k
    rw [hnormk, hnormkp] at hsm
    have hfri := hfric k
    rw [hnormkp] at hfri
    have hcrossn := hcross_neg k
    dsimp [E]
    rw [hnormkp]
    simp only [Nat.add_assoc]
    ring_nf at hcombined hsm hfri hquad hdiffsq hcrossn ⊢
    nlinarith [hcombined, hfri, hsm, hcrossn]
  have hE_nonneg (k : ℕ) : 0 ≤ E k := by
    obtain ⟨c, hc⟩ := hbelow
    have hbdd : BddBelow (Set.range f) := ⟨c, by
      rintro _ ⟨z, rfl⟩
      exact hc z⟩
    have hfinf : sInf (Set.range f) ≤ f (alg.x (k + 1)) :=
      csInf_le hbdd ⟨alg.x (k + 1), rfl⟩
    have hcoef : 0 ≤ (1 + h * gamma - L * h ^ 2 / 2) / 2 := by
      have hgmult : (3 * L / 2) * (h + beta) * h ≤ gamma * h :=
        mul_le_mul_of_nonneg_right hgamma hh.le
      nlinarith [mul_nonneg hL_nonneg (sq_nonneg h),
        mul_nonneg hL_nonneg (mul_nonneg hh.le hb.le)]
    dsimp [E]
    have hvel : 0 ≤ ((1 + h * gamma - L * h ^ 2 / 2) / 2) * ‖v k‖ ^ 2 :=
      mul_nonneg hcoef (sq_nonneg _)
    nlinarith
  have htel (N : ℕ) :
      E N + ∑ k ∈ Finset.range N, r * ‖d (k + 1)‖ ≤ E 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep N]
  have hsum_d (N : ℕ) : ∑ k ∈ Finset.range N, ‖d (k + 1)‖ ≤ E 0 / r := by
    have hlen_nonneg : 0 ≤ ∑ k ∈ Finset.range N, r * ‖d (k + 1)‖ := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg hdf.radius_pos.le (norm_nonneg _)
    have hle := htel N
    have hfactor : (∑ k ∈ Finset.range N, r * ‖d (k + 1)‖) =
        r * (∑ k ∈ Finset.range N, ‖d (k + 1)‖) := by
      rw [Finset.mul_sum]
    rw [hfactor] at hle
    have hright : r * (∑ k ∈ Finset.range N, ‖d (k + 1)‖) ≤ E 0 := by
      linarith [hE_nonneg N]
    exact (le_div_iff₀ hdf.radius_pos).mpr (by simpa [mul_comm] using hright)
  have hs_d : Summable (fun k => ‖d (k + 1)‖) :=
    summable_of_sum_range_le (fun k => norm_nonneg _) hsum_d
  have hs : Summable (fun k : ℕ => ‖d k‖) :=
    IPAHDDN_summable_of_summable_succ _ hs_d
  have hfinite : HasFiniteLength alg.x := by
    unfold HasFiniteLength
    simpa [d] using hs
  obtain ⟨xInf, hxInf⟩ := IPAHDDN_finite_length_tendsto alg.x hs
  have hlength0 : tsum (fun k => ‖d (k + 1)‖) ≤ E 0 / r :=
    Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) hsum_d
  have hlength : tsum (fun k : {k : ℕ // 1 ≤ k} ↦
      ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * ((1 / (2 * h ^ 2)) * (1 + h * gamma - L * h ^ 2 / 2) *
          ‖alg.x 1 - alg.x 0‖ ^ 2 + f (alg.x 1) - sInf (Set.range f)) := by
    change tsum (fun k : {k : ℕ // 1 ≤ k} => (fun n : ℕ => ‖d n‖) k.1) ≤ _
    calc
      tsum (fun k : {k : ℕ // 1 ≤ k} => (fun n : ℕ => ‖d n‖) k.1) =
          tsum (fun n : ℕ => ‖d (n + 1)‖) :=
        tsum_subtype_succ_reindex (fun n : ℕ => ‖d n‖)
      _ ≤ E 0 / r := hlength0
      _ = (1 / r) * ((1 / (2 * h ^ 2)) * (1 + h * gamma - L * h ^ 2 / 2) *
          ‖alg.x 1 - alg.x 0‖ ^ 2 + f (alg.x 1) - sInf (Set.range f)) := by
        dsimp [E, v, d]
        have hinv_h : 0 < (1 / h : ℝ) := one_div_pos.mpr hh
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv_h]
        field_simp [hdf.radius_pos.ne', hh.ne']
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
  have hy_minus_x : Filter.Tendsto (fun k => alg.y k - alg.x (k + 1))
      Filter.atTop (nhds 0) := by
    have hid : (fun k => alg.y k - alg.x (k + 1)) =
        fun k => (1 / (1 + h * gamma)) • d k := by
      funext k
      rw [alg.extrapolate k]
      dsimp [d]
      abel
    rw [hid]
    simpa using hd.const_smul (1 / (1 + h * gamma))
  have hy : Filter.Tendsto alg.y Filter.atTop (nhds xInf) := by
    have hsum := hxInf_succ.add hy_minus_x
    convert hsum using 1
    · ext k
      abel
    · simp
  have hgrad : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hxInf
  have hgrad_succ : Filter.Tendsto (fun k => gradient f (alg.x (k + 1)))
      Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hxInf_succ
  have hgrad_diff : Filter.Tendsto
      (fun k => gradient f (alg.x (k + 1)) - gradient f (alg.x k)) Filter.atTop (nhds 0) :=
    by simpa using hgrad_succ.sub hgrad
  have hgrad_y : Filter.Tendsto (fun k => gradient f (alg.y k)) Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hy
  let q : ℕ → H := fun k => Classical.choose (hshift k)
  have hqmem (k : ℕ) : q k ∈ subdifferential phi (v (k + 1)) :=
    (Classical.choose_spec (hshift k)).1
  have hqrec (k : ℕ) :
      v (k + 1) - v k + gamma • d (k + 1) + h • q k +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.y k) = 0 :=
    (Classical.choose_spec (hshift k)).2
  have hqsolve (k : ℕ) :
      h • q k = -(v (k + 1) - v k + gamma • d (k + 1) +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.y k)) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      h • q k + (v (k + 1) - v k + gamma • d (k + 1) +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.y k)) =
          v (k + 1) - v k + gamma • d (k + 1) + h • q k +
            beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.y k) := by ac_rfl
      _ = 0 := hqrec k
  have hdamp : Filter.Tendsto (fun k => gamma • d (k + 1)) Filter.atTop (nhds 0) :=
    by simpa using hd_succ.const_smul gamma
  have hbeta : Filter.Tendsto
      (fun k => beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) Filter.atTop (nhds 0) :=
    by simpa using hgrad_diff.const_smul beta
  have hgrad_term : Filter.Tendsto (fun k => h • gradient f (alg.y k))
      Filter.atTop (nhds (h • gradient f xInf)) := hgrad_y.const_smul h
  have hright : Filter.Tendsto (fun k =>
      -(v (k + 1) - v k + gamma • d (k + 1) +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.y k)))
      Filter.atTop (nhds (-(h • gradient f xInf))) := by
    simpa using (((hv_diff.add hdamp).add hbeta).add hgrad_term).neg
  have hq_scaled : Filter.Tendsto (fun k => h • q k) Filter.atTop
      (nhds (h • (-gradient f xInf))) := by
    convert hright using 1
    · ext k
      rw [hqsolve]
    · simp
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
  exact ⟨xInf, hfinite, hxInf, hlength, hcritical, hy⟩
