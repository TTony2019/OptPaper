import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_1

open scoped InnerProductSpace

open ERealFunction

private theorem IPAHDDVar_shifted_recurrence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f phi : H → ℝ) (hphi : phi.toEReal ∈ Γ₀(H))
    (h gamma beta : ℝ) (alg : IPAHDDVar f phi.toEReal hphi h gamma beta) (hh : 0 < h) (k : ℕ) :
    ∃ q, q ∈ subdifferential phi ((1 / h) • (alg.x (k + 2) - alg.x (k + 1))) ∧
      ((1 / h) • (alg.x (k + 2) - alg.x (k + 1)) -
          (1 / h) • (alg.x (k + 1) - alg.x k) + (h * gamma) •
            ((1 / h) • (alg.x (k + 1) - alg.x k)) +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) + h • q = 0) := by
  let z : H := ((1 - h * gamma) / h) • (alg.x (k + 1) - alg.x k) -
    beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) - h • gradient f (alg.x (k + 1))
  let P : H → H := ERealFunction.scaledProximityOperator phi.toEReal hphi ⟨h, hh⟩
  have hmem : h⁻¹ • (z - P z) ∈ subdifferential phi (P z) :=
    ERealFunction.scaledProximityOperator_residual_mem hphi ⟨h, hh⟩ z
  let q : H := h⁻¹ • (z - P z)
  have hq : q ∈ subdifferential phi (P z) := by
    simpa [q, P] using hmem
  have hqeq : h • q = z - P z := by
    dsimp [q]
    rw [smul_smul, mul_inv_cancel₀ hh.ne']
    simp
  have hstep : h • P z = alg.x (k + 2) - alg.x (k + 1) := by
    rw [alg.update k]
    simp [P, z]
  have hp : P z = (1 / h) • (alg.x (k + 2) - alg.x (k + 1)) := by
    calc
      P z = (1 / h) • (h • P z) := by
        rw [smul_smul]
        field_simp [hh.ne']
        simp
      _ = (1 / h) • (alg.x (k + 2) - alg.x (k + 1)) := by rw [hstep]
  refine ⟨q, by simpa [hp] using hq, ?_⟩
  rw [← hp]
  dsimp [z] at hqeq ⊢
  rw [hqeq]
  have hcoef : (1 - h * gamma) / h = 1 / h - gamma := by
    field_simp [hh.ne']
  have hmul : (h * gamma) * (1 / h) = gamma := by
    field_simp [hh.ne']
  rw [hcoef]
  simp only [smul_sub, smul_smul]
  rw [hmul]
  module

/-- Polarization identity adapted to the old-velocity damping in IPAHDD-Var. -/
private theorem IPAHDDVar_inner_old_damping_identity {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) (h gamma : ℝ) :
    inner ℝ (u - v) u + h * gamma * inner ℝ v u =
      (1 / 2 : ℝ) * ‖u‖ ^ 2 - (1 / 2 : ℝ) * (1 - h * gamma) ^ 2 * ‖v‖ ^ 2 +
        (1 / 2 : ℝ) * ‖u - (1 - h * gamma) • v‖ ^ 2 := by
  have hnorm : ‖(1 - h * gamma) • v‖ ^ 2 =
      (1 - h * gamma) ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [norm_sub_sq_real, inner_sub_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hnorm]
  rw [real_inner_comm v u]
  ring

/-- The remaining old-velocity quadratic form is dissipative under the
variable-friction parameter condition. -/
private theorem IPAHDDVar_quadratic_dissipation {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h gamma beta L : ℝ) (hh : 0 < h) (hL : 0 ≤ L) (hbeta : 0 ≤ beta)
    (hgamma : L * (beta + h / 2) + gamma ^ 2 * h / 2 ≤ gamma) (u w : H) :
    h * L * (beta + h / 2) * ‖u‖ ^ 2 -
        h * (gamma - gamma ^ 2 * h / 2) * ‖w‖ ^ 2 -
          (1 / 2 : ℝ) * ‖u - (1 - h * gamma) • w‖ ^ 2 ≤ 0 := by
  let A : ℝ := L * (beta + h / 2)
  let B : ℝ := gamma - gamma ^ 2 * h / 2
  let a : ℝ := 1 - h * gamma
  let C : ℝ := 1 - 2 * h * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAB : A ≤ B := by dsimp [A, B]; nlinarith
  have hB : B ≤ 1 / (2 * h) := by
    have hs : 0 ≤ (h * gamma - 1) ^ 2 := sq_nonneg _
    apply (le_div_iff₀ (show 0 < 2 * h by positivity)).mpr
    dsimp [B]
    nlinarith
  have hC : 0 ≤ C := by
    dsimp [C]
    have hle : 2 * h * A ≤ 1 := by
      calc
        2 * h * A ≤ 2 * h * B := mul_le_mul_of_nonneg_left hAB (by positivity)
        _ ≤ 1 := by
          simpa [mul_comm] using (le_div_iff₀ (show 0 < 2 * h by positivity)).mp hB
    linarith
  have ha : a ^ 2 = 1 - 2 * h * B := by
    dsimp [a, B]
    ring
  by_cases hC0 : C = 0
  · have hAeq : A = 1 / (2 * h) := by
      dsimp [C] at hC0
      field_simp [hh.ne'] at hC0 ⊢
      linarith
    have hBeq : B = 1 / (2 * h) := by linarith
    have ha0 : a = 0 := by
      have : a ^ 2 = 0 := by
        rw [ha, hBeq]
        field_simp [hh.ne']
        norm_num
      exact sq_eq_zero_iff.mp this
    have hmain : h * A * ‖u‖ ^ 2 - h * B * ‖w‖ ^ 2 -
        (1 / 2 : ℝ) * ‖u - a • w‖ ^ 2 ≤ 0 := by
      rw [ha0]
      simp only [zero_smul, sub_zero]
      rw [hAeq, hBeq]
      field_simp [hh.ne']
      nlinarith [norm_nonneg w]
    convert hmain using 1
    all_goals dsimp [A, B, a]
    all_goals ring
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hCid :
        h * A * ‖u‖ ^ 2 - h * B * ‖w‖ ^ 2 -
            (1 / 2 : ℝ) * ‖u - a • w‖ ^ 2 =
          -(C / 2) * ‖u - (a / C) • w‖ ^ 2 -
            (h * (B - A) / C) * ‖w‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right,
        inner_smul_right]
      have hnorma : ‖a • w‖ ^ 2 = a ^ 2 * ‖w‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have hnormac : ‖(a / C) • w‖ ^ 2 = (a / C) ^ 2 * ‖w‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hnorma, hnormac]
      have hCdef : C = 1 - 2 * h * A := rfl
      field_simp [hC0]
      rw [ha, hCdef]
      ring
    have hmain : h * A * ‖u‖ ^ 2 - h * B * ‖w‖ ^ 2 -
        (1 / 2 : ℝ) * ‖u - a • w‖ ^ 2 ≤ 0 := by
      rw [hCid]
      apply add_nonpos
      · simpa [neg_mul] using neg_nonpos.mpr
          (mul_nonneg (div_nonneg hC (show (0 : ℝ) ≤ 2 by norm_num))
            (sq_nonneg ‖u - (a / C) • w‖))
      · exact neg_nonpos.mpr (mul_nonneg
          (div_nonneg (mul_nonneg hh.le (sub_nonneg.mpr hAB)) hCpos.le) (sq_nonneg ‖w‖))
    convert hmain using 1
    all_goals dsimp [A, B, a]
    all_goals ring

/-- The standard descent estimate, kept local because the version in `thm_1` is private. -/
private theorem IPAHDDVar_smooth_descent {H : Type*} [NormedAddCommGroup H]
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

/-- Finite length implies convergence in a complete normed additive group. -/
private theorem IPAHDDVar_finite_length_tendsto {H : Type*} [NormedAddCommGroup H]
    [CompleteSpace H] (x : ℕ → H)
    (hs : Summable (fun k ↦ ‖x (k + 1) - x k‖)) :
    ∃ a, Filter.Tendsto x Filter.atTop (nhds a) := by
  have hdist : Summable (fun k ↦ dist (x k) (x k.succ)) := by
    simpa [dist_eq_norm, Nat.succ_eq_add_one, norm_sub_rev] using hs
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)

private theorem IPAHDDVar_summable_real_of_summable_real_succ (a : ℕ → ℝ)
    (ha : Summable (fun n => a (n + 1))) : Summable a := by
  exact (summable_nat_add_iff (f := a) 1).mp ha

private theorem IPAHDDVar_subgradient_interior_forces_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {phi : H → ℝ} {p u : H}
    (hzero : phi 0 = 0) (hp : p ∈ subdifferential phi u)
    (hinterior : p ∈ interior (subdifferential phi 0)) : u = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hinterior)
  by_contra hu
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let z : H := p + (ε / (2 * ‖u‖)) • u
  have hzdist : dist z p < ε := by
    rw [dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < ε / (2 * ‖u‖))]
    field_simp [hnu.ne']
    linarith
  have hz : z ∈ subdifferential phi 0 := hball hzdist
  have hp0 := hp 0
  have hzu := hz u
  have hp0' : phi u ≤ inner ℝ p u := by
    change (⟪0 - u, p⟫_ℝ : EReal) + (phi u : EReal) ≤ (phi 0 : EReal) at hp0
    norm_cast at hp0
    simp only [zero_sub, inner_neg_left, hzero, neg_add_le_iff_le_add, add_zero,
      real_inner_comm] at hp0
    linarith
  have hzu' : inner ℝ z u ≤ phi u := by
    change (⟪u - 0, z⟫_ℝ : EReal) + (phi 0 : EReal) ≤ (phi u : EReal) at hzu
    norm_cast at hzu
    simp only [sub_zero, hzero, add_zero] at hzu
    rw [real_inner_comm] at hzu
    exact hzu
  have hle : inner ℝ z u ≤ inner ℝ p u := hzu'.trans hp0'
  have hinner : inner ℝ z u = inner ℝ p u + (ε / (2 * ‖u‖)) * ‖u‖ ^ 2 := by
    dsimp [z]
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [starRingEnd_apply, star_trivial]
  rw [hinner] at hle
  have hpos : 0 < (ε / (2 * ‖u‖)) * ‖u‖ ^ 2 := by positivity
  linarith

/--
Theorem 2.6: (Human checked)
the variable-friction IPAHDD scheme has finite-length trajectories.
-/
theorem IPAHDDVar_finiteLength {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f phi : H → ℝ) (h gamma beta L r : ℝ)
    (hdf : DF_r phi r)
    (alg : IPAHDDVar f phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta)
    (hf : ContDiff ℝ 1 f)
    (hL : HasLipschitzGradient (gradient f) L)
    (hbelow : ∃ c : ℝ, ∀ x, c ≤ f x)
    (hpositive : 0 < h ∧ 0 < gamma) (hL_nonneg : 0 ≤ L) (hbeta_nonneg : 0 ≤ beta)
    (hgamma : gamma ≥ L * (beta + h / 2) + gamma ^ 2 * h / 2) :
    ∃ xInf E1, E1 = (1 / 2) * (1 + beta * h * L) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        f (alg.x 1) - sInf (Set.range f) ∧
      HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (nhds xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤ E1 / r ∧
      IsDryFrictionCritical phi f xInf ∧
      (gamma > L * (beta + h / 2) + gamma ^ 2 * h / 2 →
        (-gradient f xInf ∈ interior (subdifferential phi 0) →
          ∃ q C : ℝ, 0 < q ∧ q < 1 ∧ 0 ≤ C ∧ ∀ k : ℕ,
            ‖alg.x k - xInf‖ ≤ C * q ^ k) ∧
        (‖gradient f xInf‖ < r →
          ∃ N, ∀ k ≥ N, alg.x k = alg.x N)) := by
  let d : ℕ → H := fun k ↦ alg.x (k + 1) - alg.x k
  let v : ℕ → H := fun k ↦ (1 / h) • d k
  rcases hpositive with ⟨hh, hg⟩
  have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  have hgrad : ∀ z, HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    fun z => hasFDerivAt_gradient f hf z
  have hshift (k : ℕ) :
      ∃ q, q ∈ subdifferential phi (v (k + 1)) ∧
        (v (k + 1) - v k + (h * gamma) • v k +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) + h • q = 0) := by
    simpa [v, d, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      IPAHDDVar_shifted_recurrence f phi hdf.toEReal_mem_gammaZero h gamma beta alg hh k
  have hdv (k : ℕ) : d k = h • v k := by
    dsimp [d, v]
    rw [smul_smul]
    field_simp [hh.ne']
    simp
  have hraw (k : ℕ) :
      inner ℝ (v (k + 1) - v k) (v (k + 1)) +
          h * gamma * inner ℝ (v k) (v (k + 1)) + h * phi (v (k + 1)) +
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) ≤ 0 := by
    obtain ⟨q, hq, hrec⟩ := hshift k
    have hinner := congrArg (fun z : H => inner ℝ z (v (k + 1))) hrec
    have hqterm : inner ℝ (h • q) (v (k + 1)) =
        h * inner ℝ q (v (k + 1)) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
    have hbetaterm : inner ℝ
        (beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) (v (k + 1)) =
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
        inner ℝ (v (k + 1) - v k) (v (k + 1)) +
            h * gamma * inner ℝ (v k) (v (k + 1)) +
            beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
            h * inner ℝ q (v (k + 1)) +
            inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) = 0 := by
      simp only [inner_add_left, inner_sub_left, inner_zero_left,
        inner_smul_left, starRingEnd_apply, star_trivial, hqterm, hbetaterm,
        hgradterm] at hinner
      rw [inner_sub_left, inner_sub_left]
      convert hinner using 1
      all_goals ring
    have hphi : phi (v (k + 1)) ≤ inner ℝ q (v (k + 1)) := by
      have hq0 := hq 0
      change (⟪0 - v (k + 1), q⟫_ℝ : EReal) + (phi (v (k + 1)) : EReal) ≤
        (phi 0 : EReal) at hq0
      norm_cast at hq0
      simp only [zero_sub, inner_neg_left, hdf.value_at_zero, neg_add_le_iff_le_add,
        add_zero, real_inner_comm] at hq0
      linarith
    have hhphi : h * phi (v (k + 1)) ≤ h * inner ℝ q (v (k + 1)) :=
      mul_le_mul_of_nonneg_left hphi hh.le
    linarith
  have hdry : ∀ u : H, r * ‖u‖ ≤ phi u :=
    subgradient_ball_exact_linear_lower_bound phi hdf.value_at_zero hdf.radius_pos hdf.ball_subset
  have hdescent (x y : H) :
      f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 :=
    IPAHDDVar_smooth_descent f L hf hL x y
  have hfric (k : ℕ) : r * ‖d (k + 1)‖ ≤ h * phi (v (k + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left (hdry (v (k + 1))) hh.le
    have hnorm : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
      rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    rw [hnorm]
    nlinarith
  have hcross_lower (k : ℕ) :
      -(h * L * beta / 2) * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2) ≤
        beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
    have hnormgrad : ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ ≤ L * ‖d k‖ := by
      simpa [d] using hL (alg.x (k + 1)) (alg.x k)
    have hinter : -(L * ‖d k‖ * ‖v (k + 1)‖) ≤
        inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
      have habs := abs_real_inner_le_norm (gradient f (alg.x (k + 1)) - gradient f (alg.x k))
        (v (k + 1))
      have hprod : ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖ ≤
          (L * ‖d k‖) * ‖v (k + 1)‖ :=
        mul_le_mul_of_nonneg_right hnormgrad (norm_nonneg _)
      have := le_trans habs hprod
      exact neg_le_of_abs_le this
    have hmul := mul_le_mul_of_nonneg_left hinter hbeta_nonneg
    have hnorm : ‖d k‖ = h * ‖v k‖ := by
      rw [hdv k, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    rw [hnorm] at hmul
    have hyoung : 2 * (‖v k‖ * ‖v (k + 1)‖) ≤ ‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v k‖ - ‖v (k + 1)‖)]
    have hcoef : 0 ≤ h * L * beta / 2 := by positivity
    have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
    nlinarith
  have hdesc' (k : ℕ) :
      f (alg.x (k + 2)) - f (alg.x (k + 1)) - (h ^ 2 * L / 2) * ‖v (k + 1)‖ ^ 2 ≤
        inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
    have hd := hdescent (alg.x (k + 1)) (alg.x (k + 2))
    have hxy : alg.x (k + 2) - alg.x (k + 1) = d (k + 1) := by simp [d]
    rw [hxy, hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh] at hd
    rw [← hdv (k + 1)] at hd
    nlinarith
  let E : ℕ → ℝ := fun k =>
    (1 / 2) * (1 + beta * h * L) * ‖v k‖ ^ 2 + f (alg.x (k + 1)) - sInf (Set.range f)
  have hE_nonneg (k : ℕ) : 0 ≤ E k := by
    obtain ⟨c, hc⟩ := hbelow
    have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨x, rfl⟩; exact hc x⟩
    have hinf : sInf (Set.range f) ≤ f (alg.x (k + 1)) :=
      csInf_le hbdd ⟨alg.x (k + 1), rfl⟩
    have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 + beta * h * L) := by positivity
    dsimp [E]
    nlinarith [sq_nonneg ‖v k‖]
  have hstep (k : ℕ) : E (k + 1) - E k + r * ‖d (k + 1)‖ ≤ 0 := by
    have hid := IPAHDDVar_inner_old_damping_identity (v (k + 1)) (v k) h gamma
    have hquad := IPAHDDVar_quadratic_dissipation h gamma beta L hh hL_nonneg
      hbeta_nonneg hgamma (v (k + 1)) (v k)
    dsimp [E]
    rw [show alg.x (k + 1 + 1) = alg.x (k + 2) by congr 1]
    have hraw' := hraw k
    rw [hid] at hraw'
    nlinarith [hraw', hfric k, hcross_lower k, hdesc' k, hquad]
  have htel (N : ℕ) :
      E N - E 0 + ∑ k ∈ Finset.range N, r * ‖d (k + 1)‖ ≤ 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep N]
  have hsum_d (N : ℕ) : ∑ k ∈ Finset.range N, ‖d (k + 1)‖ ≤ E 0 / r := by
    have htel' := htel N
    have hfactor : (∑ k ∈ Finset.range N, r * ‖d (k + 1)‖) =
        r * ∑ k ∈ Finset.range N, ‖d (k + 1)‖ := by rw [Finset.mul_sum]
    rw [hfactor] at htel'
    apply (le_div_iff₀ hdf.radius_pos).mpr
    linarith [hE_nonneg N]
  have hs_d : Summable (fun k => ‖d (k + 1)‖) :=
    summable_of_sum_range_le (fun k => norm_nonneg _) hsum_d
  have hs : Summable (fun k : ℕ => ‖d k‖) :=
    IPAHDDVar_summable_real_of_summable_real_succ (fun k => ‖d k‖) hs_d
  have hfinite : HasFiniteLength alg.x := by
    unfold HasFiniteLength
    simpa [d] using hs
  obtain ⟨xInf, hxInf⟩ := IPAHDDVar_finite_length_tendsto alg.x hfinite
  let E1 : ℝ := (1 / 2) * (1 + beta * h * L) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
    f (alg.x 1) - sInf (Set.range f)
  have hE1 : E1 = (1 / 2) * (1 + beta * h * L) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
      f (alg.x 1) - sInf (Set.range f) := rfl
  have hE0 : E 0 = E1 := by simp [E, E1, v, d]
  have hlength0 : tsum (fun k => ‖d (k + 1)‖) ≤ E 0 / r :=
    Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) hsum_d
  have hlength : tsum (fun k : {k : ℕ // 1 ≤ k} => ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤ E1 / r := by
    change tsum (fun k : {k : ℕ // 1 ≤ k} => (fun n : ℕ => ‖d n‖) k.1) ≤ _
    calc
      tsum (fun k : {k : ℕ // 1 ≤ k} => (fun n : ℕ => ‖d n‖) k.1) =
          tsum (fun n : ℕ => ‖d (n + 1)‖) := tsum_subtype_succ_reindex (fun n : ℕ => ‖d n‖)
      _ ≤ E 0 / r := hlength0
      _ = E1 / r := by rw [hE0]
  have hd_norm : Filter.Tendsto (fun k => ‖d k‖) Filter.atTop (nhds 0) := hs.tendsto_atTop_zero
  have hd : Filter.Tendsto d Filter.atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hd_norm
  have hv : Filter.Tendsto v Filter.atTop (nhds 0) := by simpa [v] using hd.const_smul (1 / h)
  have hv_succ : Filter.Tendsto (fun k => v (k + 1)) Filter.atTop (nhds 0) := by
    simpa using hv.comp (Filter.tendsto_add_atTop_nat 1)
  have hv_diff : Filter.Tendsto (fun k => v (k + 1) - v k) Filter.atTop (nhds 0) := by
    simpa using hv_succ.sub hv
  have hxInf_succ : Filter.Tendsto (fun k => alg.x (k + 1)) Filter.atTop (nhds xInf) := by
    simpa using hxInf.comp (Filter.tendsto_add_atTop_nat 1)
  have hgradlim : Filter.Tendsto (fun k => gradient f (alg.x k))
    Filter.atTop (nhds (gradient f xInf)) := (hC1.tendsto xInf).comp hxInf
  have hgrad_succ : Filter.Tendsto (fun k => gradient f (alg.x (k + 1)))
    Filter.atTop (nhds (gradient f xInf)) := (hC1.tendsto xInf).comp hxInf_succ
  have hgrad_diff : Filter.Tendsto (fun k => gradient f (alg.x (k + 1)) - gradient f (alg.x k))
    Filter.atTop (nhds 0) := by simpa using hgrad_succ.sub hgradlim
  let q : ℕ → H := fun k => Classical.choose (hshift k)
  have hqmem (k : ℕ) : q k ∈ subdifferential phi (v (k + 1)) :=
    (Classical.choose_spec (hshift k)).1
  have hqrec (k : ℕ) : v (k + 1) - v k + (h * gamma) • v k +
      beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.x (k + 1))
      + h • q k = 0 := (Classical.choose_spec (hshift k)).2
  have hqsolve (k : ℕ) : h • q k = -(v (k + 1) - v k + (h * gamma) • v k +
      beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.x (k + 1)))
      := by
    apply eq_neg_of_add_eq_zero_left
    calc h • q k + (v (k + 1) - v k + (h * gamma) • v k +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.x (k + 1)))
        = v (k + 1) - v k + (h * gamma) • v k + beta •
          (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) + h • gradient f (alg.x (k + 1)) + h • q k := by ac_rfl
      _ = 0 := hqrec k
  have hdamp : Filter.Tendsto (fun k => (h * gamma) • v k) Filter.atTop (nhds 0) := by
    simpa using hv.const_smul (h * gamma)
  have hbeta : Filter.Tendsto (fun k => beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) Filter.atTop (nhds 0) := by
    simpa using hgrad_diff.const_smul beta
  have hgradterm : Filter.Tendsto (fun k => h • gradient f (alg.x (k + 1))) Filter.atTop (nhds (h • gradient f xInf)) :=
    hgrad_succ.const_smul h
  have hqscaled : Filter.Tendsto (fun k => h • q k) Filter.atTop (nhds (h • (-gradient f xInf))) := by
    have ht := (((hv_diff.add hdamp).add hbeta).add hgradterm).neg
    simpa [hqsolve] using ht
  have hq : Filter.Tendsto q Filter.atTop (nhds (-gradient f xInf)) := by
    have ht := hqscaled.const_smul (1 / h)
    convert ht using 1 <;> ext k <;> rw [smul_smul] <;> field_simp [hh.ne'] <;> simp
  have hcritical : IsDryFrictionCritical phi f xInf := by
    unfold IsDryFrictionCritical
    exact convex_subgradient_limit_at_zero phi (fun k => v (k + 1)) q (-gradient f xInf)
      hdf.continuous hv_succ hq hqmem
  refine ⟨xInf, E1, hE1, hfinite, hxInf, hlength, hcritical, ?_⟩
  intro hstrict
  have hconstant_of (he : ∀ᶠ k : ℕ in Filter.atTop,
      q k ∈ interior (subdifferential phi 0)) :
      ∃ N, ∀ k ≥ N, alg.x k = alg.x N := by
    rcases Filter.eventually_atTop.1 he with ⟨N, hN⟩
    refine ⟨N + 1, ?_⟩
    intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction n with
    | zero => simp
    | succ n ih =>
      have hvzero : v (N + n + 1) = 0 :=
        IPAHDDVar_subgradient_interior_forces_zero hdf.value_at_zero
          (hqmem (N + n)) (hN (N + n) (by omega))
      have hdzero : d (N + n + 1) = 0 := by rw [hdv, hvzero, smul_zero]
      have hstepx : alg.x (N + n + 1 + 1) = alg.x (N + n + 1) := by
        dsimp [d] at hdzero
        exact sub_eq_zero.mp hdzero
      have ih' := ih (by omega)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hstepx.trans (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih')
  constructor
  · intro hinterior
    have he : ∀ᶠ k : ℕ in Filter.atTop, q k ∈ interior (subdifferential phi 0) :=
      hq.eventually (IsOpen.mem_nhds isOpen_interior hinterior)
    obtain ⟨N, hN⟩ := hconstant_of he
    have htail : ∀ k ≥ N, alg.x k = xInf := by
      have heq : alg.x =ᶠ[Filter.atTop] fun _ : ℕ => alg.x N :=
        Filter.eventually_atTop.2 ⟨N, hN⟩
      have hNlim : Filter.Tendsto alg.x Filter.atTop (nhds (alg.x N)) := heq.tendsto
      have hxeq : xInf = alg.x N := tendsto_nhds_unique hxInf hNlim
      intro k hk
      rw [hN k hk, ← hxeq]
    let rho : ℝ := 1 / 2
    let C : ℝ := ∑ i ∈ Finset.range N, ‖alg.x i - xInf‖ / rho ^ i
    have hrhonon : 0 ≤ rho := by norm_num [rho]
    have hCnon : 0 ≤ C := by
      dsimp [C]
      apply Finset.sum_nonneg
      intro i hi
      positivity
    refine ⟨rho, C, by norm_num [rho], by norm_num [rho], ?_, ?_⟩
    · exact hCnon
    · intro k
      by_cases hk : N ≤ k
      · rw [htail k hk]
        simpa using (mul_nonneg hCnon (pow_nonneg hrhonon k))
      · have hkmem : k ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hk)
        have hterm : ‖alg.x k - xInf‖ / rho ^ k ≤ C := by
          dsimp [C]
          apply Finset.single_le_sum (s := Finset.range N)
            (f := fun i => ‖alg.x i - xInf‖ / rho ^ i)
          · intro i hi
            positivity
          · exact hkmem
        have hrhopos : 0 < rho ^ k := pow_pos (by norm_num [rho]) _
        apply (div_le_iff₀ hrhopos).mp
        simpa [mul_comm] using hterm
  · intro hmargin
    have hmargin' : ‖-gradient f xInf‖ < r := by simpa using hmargin
    have hqn : ∀ᶠ k : ℕ in Filter.atTop, ‖q k‖ < r :=
      hq.norm.eventually (eventually_lt_nhds hmargin')
    apply hconstant_of
    filter_upwards [hqn] with k hk
    apply mem_interior_iff_mem_nhds.mpr
    apply Metric.mem_nhds_iff.mpr
    refine ⟨r - ‖q k‖, sub_pos.mpr hk, ?_⟩
    intro y hy
    apply hdf.ball_subset
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    have hy' : ‖y‖ < r := calc
      ‖y‖ = ‖(y - q k) + q k‖ := by congr 1; abel
      _ ≤ ‖y - q k‖ + ‖q k‖ := norm_add_le _ _
      _ < r := by linarith
    simpa using hy'
