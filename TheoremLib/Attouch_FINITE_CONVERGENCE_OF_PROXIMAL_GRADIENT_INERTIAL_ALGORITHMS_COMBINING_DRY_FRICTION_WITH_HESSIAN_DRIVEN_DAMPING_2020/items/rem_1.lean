import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_1

open scoped InnerProductSpace

open ERealFunction

/-- The IPAHDD update written as a subgradient recurrence for the next velocity. -/
theorem rem_1_shifted_recurrence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f phi : H → ℝ) (prox : ℝ → H → H)
    (h gamma beta : ℝ) (alg : IPAHDD f phi prox h gamma beta) (hh : 0 < h)
    (hg : 0 < gamma) (hprox : ∀ lam x, IsProximalPoint phi lam x (prox lam x)) (k : ℕ) :
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
  rcases hprox (h / D) z with ⟨_hlam_pos, hmem⟩
  let q : H := (h / D)⁻¹ • (z - prox (h / D) z)
  have hq : q ∈ subdifferential phi (prox (h / D) z) := by
    simpa [q, subdifferential] using hmem
  have hqeq : (h / D) • q = z - prox (h / D) z := by
    dsimp [q]
    rw [smul_smul, mul_inv_cancel₀ (div_ne_zero hh.ne' hD0)]
    simp
  have hstep : h • prox (h / D) z = alg.x (k + 2) - alg.x (k + 1) := by
    rw [alg.update k]
    simp [z, D]
  have hp : prox (h / D) z = (1 / h) • (alg.x (k + 2) - alg.x (k + 1)) := by
    calc
      prox (h / D) z = (1 / h) • (h • prox (h / D) z) := by
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
    abel_nf

/-- Remark 2.3: in finite dimension, an interior limiting force also yields finite stopping. -/
theorem finiteDimensional_finiteStopping_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (f phi : H → ℝ)
    (prox : ℝ → H → H) (h gamma beta L r : ℝ) (alg : IPAHDD f phi prox h gamma beta)
    (xInf : H) (hlimit : Filter.Tendsto alg.x Filter.atTop (nhds xInf))
    (hfinite : HasFiniteLength alg.x)
    (_hcritical : IsDryFrictionCritical phi f xInf)
    (_hL : HasLipschitzGradient (gradient f) L) (hC1 : Continuous (gradient f))
    (_hbelow : ∃ c : ℝ, ∀ x, c ≤ f x) (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (_hgamma : gamma ≥ L * (h / 2 + beta))
    (_hdf : DryFriction phi) (_hr : 0 < r)
    (_hdf_r : Metric.ball (0 : H) r ⊆ subdifferential phi 0)
    (hprox : ∀ lam x, IsProximalPoint phi lam x (prox lam x))
    (hinterior : -gradient f xInf ∈ interior (subdifferential phi 0)) :
    ∃ N, ∀ k ≥ N, alg.x (k + 1) = alg.x k := by
  let d : ℕ → H := fun k ↦ alg.x (k + 1) - alg.x k
  let v : ℕ → H := fun k ↦ (1 / h) • d k
  rcases hpositive with ⟨hh, hg, hb⟩
  have hshift (k : ℕ) :
      ∃ q, q ∈ subdifferential phi (v (k + 1)) ∧
        (v (k + 1) - v k + gamma • d (k + 1) + h • q +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) = 0) := by
    simpa [v, d, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      rem_1_shifted_recurrence f phi prox h gamma beta alg hh hg hprox k
  have hd_norm : Filter.Tendsto (fun k => ‖d k‖) Filter.atTop (nhds 0) :=
    hfinite.tendsto_atTop_zero
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
  have hx_succ : Filter.Tendsto (fun k => alg.x (k + 1)) Filter.atTop (nhds xInf) := by
    simpa using hlimit.comp (Filter.tendsto_add_atTop_nat 1)
  have hgrad : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hlimit
  have hgrad_succ : Filter.Tendsto (fun k => gradient f (alg.x (k + 1)))
      Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hx_succ
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
      (fun k => beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) Filter.atTop (nhds 0) :=
    by simpa using hgrad_diff.const_smul beta
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
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hinterior) with ⟨ε, hε, hball⟩
  have hε2 : 0 < ε / 2 := by linarith
  have hq_tail : ∀ᶠ k in Filter.atTop, ‖q k - (-gradient f xInf)‖ < ε / 2 := by
    have := hq.eventually (Metric.ball_mem_nhds _ hε2)
    filter_upwards [this] with k hk
    simpa [Metric.mem_ball, dist_eq_norm] using hk
  rcases Filter.eventually_atTop.1 hq_tail with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro k hk
  have hkN : N ≤ k - 1 := Nat.le_sub_of_add_le hk
  have hkpos : 1 ≤ k := by omega
  have hkidx : (k - 1) + 1 = k := Nat.sub_add_cancel hkpos
  have hvzero : v ((k - 1) + 1) = 0 := by
    by_contra hvne
    let u : H := (‖v ((k - 1) + 1)‖)⁻¹ • v ((k - 1) + 1)
    let p : H := q (k - 1) + (ε / 2) • u
    have hvpos : 0 < ‖v ((k - 1) + 1)‖ := norm_pos_iff.mpr hvne
    have hunit : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvpos]
      field_simp [hvpos.ne']
    have hpball : p ∈ Metric.ball (-gradient f xInf) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc
        ‖p - (-gradient f xInf)‖ = ‖(q (k - 1) - (-gradient f xInf)) + (ε / 2) • u‖ := by
          dsimp [p]
          abel_nf
        _ ≤ ‖q (k - 1) - (-gradient f xInf)‖ + ‖(ε / 2) • u‖ := norm_add_le _ _
        _ = ‖q (k - 1) - (-gradient f xInf)‖ + (ε / 2) * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε2]
        _ < ε := by rw [hunit]; linarith [hN (k - 1) hkN]
    have hp : p ∈ subdifferential phi 0 := hball hpball
    have hqineq := hqmem (k - 1) 0
    have hpineq := hp (v ((k - 1) + 1))
    have hmono : 0 ≤ inner ℝ (q (k - 1) - p) (v ((k - 1) + 1)) := by
      change (⟪v ((k - 1) + 1) - 0, p⟫_ℝ : EReal) + (phi 0 : EReal) ≤
        (phi (v ((k - 1) + 1)) : EReal) at hpineq
      change (⟪0 - v ((k - 1) + 1), q (k - 1)⟫_ℝ : EReal) +
          (phi (v ((k - 1) + 1)) : EReal) ≤ (phi 0 : EReal) at hqineq
      norm_cast at hpineq hqineq
      rw [sub_zero, real_inner_comm] at hpineq
      rw [zero_sub, inner_neg_left, real_inner_comm] at hqineq
      rw [inner_sub_left]
      linarith
    have hinner : inner ℝ (q (k - 1) - p) (v ((k - 1) + 1)) =
        -((ε / 2) * ‖v ((k - 1) + 1)‖) := by
      dsimp [p, u]
      have hsub : q (k - 1) -
          (q (k - 1) + (ε / 2) • (‖v ((k - 1) + 1)‖)⁻¹ • v ((k - 1) + 1)) =
          -((ε / 2) • (‖v ((k - 1) + 1)‖)⁻¹ • v ((k - 1) + 1)) := by
        abel
      rw [hsub, inner_neg_left, inner_smul_left, inner_smul_left,
        real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hvpos.ne']
    rw [hinner] at hmono
    nlinarith
  have hvzero' : (1 / h) • (alg.x (k + 1) - alg.x k) = 0 := by
    simpa [v, d, hkidx] using hvzero
  have hdzero : alg.x (k + 1) - alg.x k = 0 :=
    (smul_eq_zero.mp hvzero').resolve_left (one_div_ne_zero hh.ne')
  exact sub_eq_zero.mp hdzero
