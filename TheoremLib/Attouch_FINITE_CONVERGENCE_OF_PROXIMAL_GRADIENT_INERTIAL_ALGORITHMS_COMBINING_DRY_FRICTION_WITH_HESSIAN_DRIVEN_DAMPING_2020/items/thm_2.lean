import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.lem_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_1

open scoped InnerProductSpace

open ERealFunction

/-- A sequence is finitely convergent when it is eventually constant. -/
def IsFinitelyConvergent {H : Type*} (x : ℕ → H) : Prop := ∃ N, ∀ k ≥ N, x k = x N

/-- A sequence with eventually equal successive terms is eventually constant. -/
theorem eventually_constant_of_eventual_successor_eq {H : Type*} (x : ℕ → H) (N : ℕ)
    (h : ∀ k ≥ N, x (k + 1) = x k) : IsFinitelyConvergent x := by
  refine ⟨N, ?_⟩
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show N + (m + 1) = (N + m) + 1 by omega,
        h (N + m) (Nat.le_add_right N m), ih (Nat.le_add_right N m)]

/-- Positivity of the contraction factor occurring in Theorem 2.2. -/
theorem ipahdd_rate_mem_Ioo (h gamma beta L : ℝ) (hh : 0 < h) (hg : 0 < gamma)
    (hb : 0 < beta) (hL : 0 ≤ L) (hgamma : gamma ≥ L * (h / 2 + beta)) :
    0 < 1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L)) ∧
      1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L)) < 1 := by
  have hgap : 0 < gamma - beta * L := by
    rcases hL.eq_or_lt with rfl | hLpos
    · simpa using hg
    · have hstrict : beta * L < L * (h / 2 + beta) := by
        nlinarith [mul_pos hLpos hh]
      nlinarith [hgamma, hstrict]
  have hA : 0 < 1 + beta * h * L := by positivity
  have hB : 0 < 2 * h * (gamma - beta * L) / (1 + beta * h * L) := by positivity
  have ht : 0 < 1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L) := by positivity
  have hsqrt : 0 < Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L)) :=
    Real.sqrt_pos.2 ht
  constructor
  · exact one_div_pos.mpr hsqrt
  · rw [div_lt_iff₀ hsqrt]
    have hsqrt_one : 1 < Real.sqrt
        (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L)) :=
      (Real.lt_sqrt (by norm_num)).mpr (by nlinarith [hB])
    nlinarith

/-- Scalar form of the IPAHDD contraction-factor identity. -/
private theorem ipahdd_q_sq_mul_A_eq_B_local (h gamma beta L : ℝ) (hh : 0 < h)
    (hB : 0 < 1 + beta * h * L) (hgap : 0 < gamma - beta * L) :
    let B : ℝ := 1 + beta * h * L
    let A : ℝ := B + 2 * h * (gamma - beta * L)
    let q : ℝ := 1 / Real.sqrt (A / B)
    q ^ 2 * A = B := by
  dsimp
  let B : ℝ := 1 + beta * h * L
  let A : ℝ := B + 2 * h * (gamma - beta * L)
  have hA : 0 < A := by
    dsimp [A, B]
    nlinarith [mul_pos hh hgap]
  have hAB : 0 < A / B := div_pos hA hB
  have hsqrt : (Real.sqrt (A / B)) ^ 2 = A / B := Real.sq_sqrt hAB.le
  rw [div_pow, one_pow, hsqrt]
  field_simp [hA.ne', hB.ne']
  ring

/-- A finite geometric tail is bounded by the corresponding infinite tail. -/
private theorem geometric_range_sum_le_local (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n p : ℕ) :
    (∑ i ∈ Finset.range p, q ^ (n + i)) ≤ q ^ n / (1 - q) := by
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hsmall : (∑ i ∈ Finset.range p, q ^ i) ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ hden).mpr
    calc
      (∑ i ∈ Finset.range p, q ^ i) * (1 - q) = 1 - q ^ p := geom_sum_mul_neg q p
      _ ≤ 1 := sub_le_self 1 (pow_nonneg hq0 p)
  calc
    (∑ i ∈ Finset.range p, q ^ (n + i)) =
        q ^ n * (∑ i ∈ Finset.range p, q ^ i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_add]
    _ ≤ q ^ n * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left hsmall (pow_nonneg hq0 _)
    _ = q ^ n / (1 - q) := by ring

/-- The IPAHDD update rewritten as the subgradient recurrence used in the
geometric tail estimate.  This is local because the analogous result in
`thm_1` is an implementation detail of that proof. -/
private theorem ipahdd_shifted_recurrence_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f phi : H → ℝ) (prox : ℝ → H → H)
    (h gamma beta : ℝ) (alg : IPAHDD f phi prox h gamma beta) (hh : 0 < h)
    (hg : 0 < gamma) (hprox : ∀ lam x, IsProximalPoint phi lam x (prox lam x)) (k : ℕ) :
    ∃ s, s ∈ subdifferential phi ((1 / h) • (alg.x (k + 2) - alg.x (k + 1))) ∧
      ((1 / h) • (alg.x (k + 2) - alg.x (k + 1)) -
          (1 / h) • (alg.x (k + 1) - alg.x k) +
          gamma • (alg.x (k + 2) - alg.x (k + 1)) + h • s +
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
  -- `IsProximalPoint` is the subgradient-form
  -- `0 < lam ∧ (lam⁻¹ • (z - p)) ∈ subdifferential phi p`; the residual is the witness `s`.
  rcases hprox (h / D) z with ⟨_hlam_pos, hmem⟩
  let s : H := (h / D)⁻¹ • (z - prox (h / D) z)
  have hs : s ∈ subdifferential phi (prox (h / D) z) := by
    simpa [s, subdifferential] using hmem
  have hseq : (h / D) • s = z - prox (h / D) z := by
    dsimp [s]
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
  refine ⟨s, ?_, ?_⟩
  · simpa [hp] using hs
  · have hscaled := congrArg (fun w : H => D • w) hseq
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

/-- Two positive-parameter proximal inclusions have the same point. -/
private theorem proximal_point_eq_zero_of_subgradient_ball {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (lam : ℝ) (hlam : 0 < lam) (z p : H)
    (hp : IsProximalPoint phi lam z p) (hz : IsProximalPoint phi lam z 0) : p = 0 := by
  rcases hp with ⟨_ha_pos, ha_mem⟩
  rcases hz with ⟨_hb_pos, hb_mem⟩
  let a : H := lam⁻¹ • (z - p)
  let b : H := lam⁻¹ • (z - 0)
  have ha : a ∈ subdifferential phi p := by simpa [a, subdifferential] using ha_mem
  have hb : b ∈ subdifferential phi 0 := by simpa [b, subdifferential] using hb_mem
  have hpa : lam • a = z - p := by
    dsimp [a]
    rw [smul_smul, mul_inv_cancel₀ hlam.ne']
    simp
  have hzb : lam • b = z - 0 := by
    dsimp [b]
    rw [smul_smul, mul_inv_cancel₀ hlam.ne']
    simp
  have hmon : 0 ≤ inner ℝ (a - b) (p - 0) := by
    have h1 := ha 0
    have h2 := hb p
    change (⟪0 - p, a⟫_ℝ : EReal) + (phi p : EReal) ≤ (phi 0 : EReal) at h1
    change (⟪p - 0, b⟫_ℝ : EReal) + (phi 0 : EReal) ≤ (phi p : EReal) at h2
    norm_cast at h1 h2
    simp only [sub_zero, zero_sub, inner_neg_left, real_inner_comm, inner_sub_left] at h1 h2 ⊢
    linarith
  have hab : a - b = -(lam⁻¹) • p := by
    change lam • a = z - p at hpa
    change lam • b = z - 0 at hzb
    calc
      a - b = (lam⁻¹ * lam) • (a - b) := by
        rw [inv_mul_cancel₀ hlam.ne']
        simp
      _ = lam⁻¹ • (lam • (a - b)) := by rw [smul_smul]
      _ = lam⁻¹ • ((z - p) - (z - 0)) := by rw [smul_sub, hpa, hzb]
      _ = lam⁻¹ • (-p) := by
        congr 1
        abel
      _ = -(lam⁻¹) • p := by
        rw [smul_neg]
        exact (neg_smul lam⁻¹ p).symm
  rw [sub_zero, hab, inner_smul_left, real_inner_self_eq_norm_sq] at hmon
  simp only [starRingEnd_apply, star_trivial] at hmon
  have : ‖p‖ ^ 2 ≤ 0 := by nlinarith [inv_pos.mpr hlam]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _)))

/-- The elementary polarization identity used by the local IPAHDD energy estimate. -/
private theorem inner_sub_self_energy_identity_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) :
    inner ℝ (u - v) u = (1 / 2 : ℝ) * ‖u‖ ^ 2 - (1 / 2 : ℝ) * ‖v‖ ^ 2 +
      (1 / 2 : ℝ) * ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v u]
  ring

set_option maxHeartbeats 800000
/-- Theorem 2.2: strict interior dry friction gives geometric decay and finite stopping. -/
theorem IPAHDD_geometric_and_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (f phi : H → ℝ) (prox : ℝ → H → H) (h gamma beta L r : ℝ)
    (alg : IPAHDD f phi prox h gamma beta) (xInf : H)
    (hf : ContDiff ℝ 1 f)
    (hL : HasLipschitzGradient (gradient f) L) (hL_nonneg : 0 ≤ L)
    (hC1 : Continuous (gradient f))
    (_hbelow : ∃ c : ℝ, ∀ x, c ≤ f x) (hdf : DryFriction phi)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta) (_hr : 0 < r)
    (hdf_r : Metric.ball (0 : H) r ⊆ subdifferential phi 0)
    (hprox : ∀ lam x, IsProximalPoint phi lam x (prox lam x))
    (hgamma : gamma ≥ L * (h / 2 + beta))
    (hlimit : Filter.Tendsto alg.x Filter.atTop (nhds xInf)) :
    let q := 1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))
    (-gradient f xInf ∈ interior (subdifferential phi 0) →
      0 < q ∧ q < 1 ∧ ∃ k0, ∀ k ≥ k0,
        ‖alg.x (k + 1) - alg.x k‖ ≤ q ^ (k - k0) * ‖alg.x (k0 + 1) - alg.x k0‖ ∧
        ‖alg.x k - xInf‖ ≤ q ^ (k - k0) / (1 - q) * ‖alg.x (k0 + 1) - alg.x k0‖) ∧
    (‖gradient f xInf‖ < r → ∃ kStop, ∀ k ≥ kStop, alg.x (k + 1) = alg.x k) := by
  dsimp
  rcases hpositive with ⟨hh, hg, hb⟩
  have hq := ipahdd_rate_mem_Ioo h gamma beta L hh hg hb hL_nonneg hgamma
  constructor
  · intro hinterior
    refine ⟨hq.1, hq.2, ?_⟩
    let d : ℕ → H := fun k => alg.x (k + 1) - alg.x k
    let v : ℕ → H := fun k => (1 / h) • d k
    have hdv (k : ℕ) : d k = h • v k := by
      dsimp [d, v]
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    have hshift (k : ℕ) :
        ∃ s, s ∈ subdifferential phi (v (k + 1)) ∧
          (v (k + 1) - v k + gamma • d (k + 1) + h • s +
            beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
            h • gradient f (alg.x (k + 1)) = 0) := by
      simpa [d, v, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ipahdd_shifted_recurrence_local f phi prox h gamma beta alg hh hg hprox k
    have hraw (k : ℕ) :
        (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
          (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
          gamma * h * ‖v (k + 1)‖ ^ 2 + h * phi (v (k + 1)) +
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) ≤ 0 := by
      obtain ⟨s, hs, hrec⟩ := hshift k
      have hinner := congrArg (fun z : H => inner ℝ z (v (k + 1))) hrec
      have hinert := inner_sub_self_energy_identity_local (v (k + 1)) (v k)
      have hdamp : inner ℝ (gamma • d (k + 1)) (v (k + 1)) =
          gamma * h * ‖v (k + 1)‖ ^ 2 := by
        rw [hdv (k + 1), inner_smul_left, inner_smul_left,
          real_inner_self_eq_norm_sq]
        simp only [starRingEnd_apply, star_trivial]
        ring
      have hsterm : inner ℝ (h • s) (v (k + 1)) = h * inner ℝ s (v (k + 1)) := by
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
            gamma * h * ‖v (k + 1)‖ ^ 2 + h * inner ℝ s (v (k + 1)) +
            beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
            inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) = 0 := by
        simpa only [inner_add_left, inner_sub_left, inner_zero_left, add_zero,
          hinert, hdamp, hsterm, hbetaterm, hgradterm] using hinner
      have hphi : phi (v (k + 1)) ≤ inner ℝ s (v (k + 1)) := by
        have hs0 := hs 0
        change (⟪0 - v (k + 1), s⟫_ℝ : EReal) + (phi (v (k + 1)) : EReal) ≤
          (phi 0 : EReal) at hs0
        norm_cast at hs0
        simp [hdf.value_at_zero, inner_neg_left] at hs0
        rw [real_inner_comm] at hs0
        linarith
      have hhphi := mul_le_mul_of_nonneg_left hphi hh.le
      linarith
    obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp hinterior)
    let eps : ℝ := rho / 2
    have heps : 0 < eps := by dsimp [eps]; positivity
    have hgradlim : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop
        (nhds (gradient f xInf)) := hC1.tendsto xInf |>.comp hlimit
    have hgradtail : ∀ᶠ k : ℕ in Filter.atTop,
        ‖gradient f (alg.x k) - gradient f xInf‖ < eps := by
      have hzero : Filter.Tendsto (fun k => gradient f (alg.x k) - gradient f xInf)
          Filter.atTop (nhds 0) := by
        simpa using hgradlim.sub (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => gradient f xInf) Filter.atTop (nhds (gradient f xInf)))
      simpa using hzero.norm.eventually
        (eventually_lt_nhds (show ‖(0 : H)‖ < eps by simpa using heps))
    obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hgradtail
    have htranslated (k : ℕ) (hk : k0 ≤ k) (u : H) (hu : ‖u‖ ≤ 1) :
        -gradient f (alg.x (k + 1)) + eps • u ∈ subdifferential phi 0 := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hrewrite :
          (-gradient f (alg.x (k + 1)) + eps • u) - -gradient f xInf =
            -(gradient f (alg.x (k + 1)) - gradient f xInf) + eps • u := by
        abel
      rw [hrewrite]
      calc
        ‖-(gradient f (alg.x (k + 1)) - gradient f xInf) + eps • u‖ ≤
            ‖gradient f (alg.x (k + 1)) - gradient f xInf‖ + ‖eps • u‖ := by
              calc
                _ ≤ ‖-(gradient f (alg.x (k + 1)) - gradient f xInf)‖ + ‖eps • u‖ := norm_add_le _ _
                _ = _ := by rw [norm_neg]
        _ = ‖gradient f (alg.x (k + 1)) - gradient f xInf‖ + eps * ‖u‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos heps]
        _ < eps + eps * ‖u‖ := by
              gcongr
              exact hk0 (k + 1) (by omega)
        _ ≤ eps + eps := by
              gcongr
              simpa using mul_le_mul_of_nonneg_left hu heps.le
        _ = rho := by dsimp [eps]; ring
    have hfricInterior (k : ℕ) (hk : k0 ≤ k) :
        eps * ‖v (k + 1)‖ ≤
          phi (v (k + 1)) + inner ℝ (gradient f (alg.x (k + 1))) (v (k + 1)) := by
      by_cases hv0 : v (k + 1) = 0
      · simp [hv0, hdf.value_at_zero]
      · let u : H := (‖v (k + 1)‖)⁻¹ • v (k + 1)
        have hvpos : 0 < ‖v (k + 1)‖ := norm_pos_iff.mpr hv0
        have hu : ‖u‖ ≤ 1 := by
          dsimp [u]
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
          field_simp [hvpos.ne']
          norm_num
        have hs := htranslated k hk u hu
        have hsub := hs (v (k + 1))
        have hinner : inner ℝ u (v (k + 1)) = ‖v (k + 1)‖ := by
          dsimp [u]
          rw [inner_smul_left, real_inner_self_eq_norm_sq]
          simp only [map_inv₀, starRingEnd_apply, star_trivial]
          field_simp [hvpos.ne']
        change (⟪v (k + 1) - 0, -gradient f (alg.x (k + 1)) + eps • u⟫_ℝ : EReal) +
            (phi 0 : EReal) ≤ (phi (v (k + 1)) : EReal) at hsub
        norm_cast at hsub
        simp only [sub_zero] at hsub
        rw [hdf.value_at_zero, inner_add_right, inner_neg_right, inner_smul_right] at hsub
        rw [real_inner_comm (gradient f (alg.x (k + 1))) (v (k + 1)),
          real_inner_comm u (v (k + 1)), hinner] at hsub
        linarith
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
      have hprod := mul_le_mul_of_nonneg_right hnormgrad (norm_nonneg (v (k + 1)))
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
    have hsq_contract (k : ℕ) (hk : k0 ≤ k) :
        (1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖d (k + 1)‖ ^ 2 ≤
          (1 + beta * h * L) * ‖d k‖ ^ 2 := by
      have hnorm (j : ℕ) : ‖d j‖ = h * ‖v j‖ := by
        rw [hdv j, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      have hraw' := hraw k
      have hfric := hfricInterior k hk
      have hcross := hcross_lower k
      have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 := by positivity
      have hrawtwo := mul_le_mul_of_nonneg_left hraw' (show (0 : ℝ) ≤ 2 by norm_num)
      have hfric' := mul_le_mul_of_nonneg_left hfric hh.le
      have hgradscale :
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) =
            h * inner ℝ (gradient f (alg.x (k + 1))) (v (k + 1)) := by
        rw [hdv (k + 1), inner_smul_right]
      have hfricscale : h * eps * ‖v (k + 1)‖ ≤
          h * phi (v (k + 1)) + inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
        rw [hgradscale]
        nlinarith [hfric']
      have hcrossv :
          -(beta * L * h * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2)) ≤
            2 * beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
        calc
          -(beta * L * h * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2)) =
              2 * (-(beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2))) := by
                rw [hnorm k, hnorm (k + 1)]
                field_simp [hh.ne']
          _ ≤ 2 * (beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k))
              (v (k + 1))) := mul_le_mul_of_nonneg_left hcross (by norm_num)
          _ = _ := by ring
      have hvcontract :
          (1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖v (k + 1)‖ ^ 2 ≤
            (1 + beta * h * L) * ‖v k‖ ^ 2 := by
        have hepsnorm : 0 ≤ h * eps * ‖v (k + 1)‖ := by positivity
        nlinarith [hrawtwo, hcrossv, hfricscale]
      rw [hnorm k, hnorm (k + 1)]
      calc
        (1 + beta * h * L + 2 * h * (gamma - beta * L)) * (h * ‖v (k + 1)‖) ^ 2 =
            h ^ 2 * ((1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖v (k + 1)‖ ^ 2) := by ring
        _ ≤ h ^ 2 * ((1 + beta * h * L) * ‖v k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hvcontract (sq_nonneg h)
        _ = (1 + beta * h * L) * (h * ‖v k‖) ^ 2 := by ring
    have hgap : 0 < gamma - beta * L := by
      rcases hL_nonneg.eq_or_lt with rfl | hLpos
      · simpa using hg
      · have hstrict : beta * L < L * (h / 2 + beta) := by
          nlinarith [mul_pos hLpos hh]
        nlinarith [hgamma, hstrict]
    have hB : 0 < 1 + beta * h * L := by positivity
    have hA : 0 < 1 + beta * h * L + 2 * h * (gamma - beta * L) := by
      nlinarith [mul_pos hh hgap]
    have hq_sq :
        (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ 2 *
            (1 + beta * h * L + 2 * h * (gamma - beta * L)) =
          1 + beta * h * L := by
      have hratio :
          (1 + beta * h * L + 2 * h * (gamma - beta * L)) / (1 + beta * h * L) =
            1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L) := by
        field_simp [hB.ne']
      have hhelper := ipahdd_q_sq_mul_A_eq_B_local h gamma beta L hh hB hgap
      dsimp only at hhelper
      rw [hratio] at hhelper
      exact hhelper
    have hcontract (k : ℕ) (hk : k0 ≤ k) :
        ‖d (k + 1)‖ ≤
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) * ‖d k‖ := by
      have hsquare : ‖d (k + 1)‖ ^ 2 ≤
          ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) * ‖d k‖) ^ 2 := by
        have hmain := hsq_contract k hk
        have hrewrite : 1 + beta * h * L =
            (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))) ^ 2 *
              (1 + beta * h * L + 2 * h * (gamma - beta * L)) := hq_sq.symm
        rw [hrewrite] at hmain
        have hmul := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hA.le)
        field_simp [hA.ne'] at hmul
        nlinarith
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq.1.le (norm_nonneg _))).mp hsquare
    have hgeom (n : ℕ) : ‖d (k0 + n)‖ ≤
        (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n * ‖d k0‖ := by
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            ‖d (k0 + (n + 1))‖ = ‖d ((k0 + n) + 1)‖ := by congr 2
            _ ≤ (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
                (1 + beta * h * L))) * ‖d (k0 + n)‖ :=
              hcontract (k0 + n) (Nat.le_add_right k0 n)
            _ ≤ (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
                (1 + beta * h * L))) *
                ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
                  (1 + beta * h * L))) ^ n * ‖d k0‖) :=
              mul_le_mul_of_nonneg_left ih hq.1.le
            _ = (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
                (1 + beta * h * L))) ^ (n + 1) * ‖d k0‖ := by
              rw [pow_succ]
              ring
    have hsum (n p : ℕ) :
        (∑ i ∈ Finset.range p,
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) ^ (n + i)) ≤
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) ^ n /
            (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L)))) := by
      exact geometric_range_sum_le_local _ hq.1.le hq.2 n p
    have htel (n p : ℕ) :
        alg.x (k0 + n + p) - alg.x (k0 + n) =
          ∑ i ∈ Finset.range p, d (k0 + n + i) := by
      induction p with
      | zero => simp
      | succ p ih =>
          rw [Finset.sum_range_succ, ← ih]
          dsimp [d]
          convert (show alg.x (k0 + n + p + 1) - alg.x (k0 + n) =
              (alg.x (k0 + n + p) - alg.x (k0 + n)) +
                (alg.x (k0 + n + p + 1) - alg.x (k0 + n + p)) by abel) using 1
    have htail (n p : ℕ) :
        ‖alg.x (k0 + n) - alg.x (k0 + n + p)‖ ≤
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n /
            (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L)))) * ‖d k0‖ := by
      calc
        ‖alg.x (k0 + n) - alg.x (k0 + n + p)‖ =
            ‖-(alg.x (k0 + n) - alg.x (k0 + n + p))‖ := (norm_neg _).symm
        _ = ‖alg.x (k0 + n + p) - alg.x (k0 + n)‖ := by
            congr 1
            abel
        _ = ‖∑ i ∈ Finset.range p, d (k0 + n + i)‖ := by rw [htel]
        _ ≤ ∑ i ∈ Finset.range p, ‖d (k0 + n + i)‖ :=
          norm_sum_le (Finset.range p) (fun i => d (k0 + n + i))
        _ ≤ ∑ i ∈ Finset.range p,
            (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))) ^ (n + i) * ‖d k0‖ := by
              apply Finset.sum_le_sum
              intro i hi
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hgeom (n + i)
        _ = (∑ i ∈ Finset.range p,
            (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))) ^ (n + i)) * ‖d k0‖ := by
              rw [Finset.sum_mul]
        _ ≤ ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) ^ n /
            (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))))) * ‖d k0‖ :=
              mul_le_mul_of_nonneg_right (hsum n p) (norm_nonneg _)
    refine ⟨k0, ?_⟩
    intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hdist : ‖alg.x (k0 + n) - xInf‖ ≤
        (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n /
          (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L)))) * ‖d k0‖ := by
      apply le_of_tendsto
        ((tendsto_const_nhds.sub
          (hlimit.comp (Filter.tendsto_add_atTop_nat (k0 + n)))).norm)
      filter_upwards with p
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail n p
    constructor
    · simpa [d] using hgeom n
    · simpa [d] using hdist
  · intro hmargin
    let D : ℝ := 1 + h * gamma
    let lam : ℝ := h / D
    let z : ℕ → H := fun k =>
      (1 / (h * D)) • (alg.x (k + 1) - alg.x k) -
        (beta / D) • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) -
        lam • gradient f (alg.x (k + 1))
    have hD : 0 < D := by
      dsimp [D]
      nlinarith [mul_pos hh hg]
    have hlam : 0 < lam := by
      dsimp [lam]
      exact div_pos hh hD
    have hxshift : Filter.Tendsto (fun k => alg.x (k + 1)) Filter.atTop (nhds xInf) := by
      simpa using hlimit.comp (Filter.tendsto_add_atTop_nat 1)
    have hinc : Filter.Tendsto (fun k => alg.x (k + 1) - alg.x k)
        Filter.atTop (nhds 0) := by
      simpa using hxshift.sub hlimit
    have hgradlim : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop
        (nhds (gradient f xInf)) := hC1.tendsto xInf |>.comp hlimit
    have hgradshift : Filter.Tendsto (fun k => gradient f (alg.x (k + 1))) Filter.atTop
        (nhds (gradient f xInf)) := by
      simpa using hgradlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hgraddiff : Filter.Tendsto
        (fun k => gradient f (alg.x (k + 1)) - gradient f (alg.x k)) Filter.atTop (nhds 0) := by
      simpa using hgradshift.sub hgradlim
    have hzlim : Filter.Tendsto z Filter.atTop (nhds (lam • (-gradient f xInf))) := by
      dsimp [z]
      simpa using ((hinc.const_smul (1 / (h * D))).sub
        (hgraddiff.const_smul (beta / D))).sub (hgradshift.const_smul lam)
    have hscaled : Filter.Tendsto (fun k => lam⁻¹ • z k) Filter.atTop
        (nhds (-gradient f xInf)) := by
      have := hzlim.const_smul lam⁻¹
      simpa only [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul] using this
    have hsmall : ∀ᶠ k : ℕ in Filter.atTop, ‖lam⁻¹ • z k‖ < r := by
      exact hscaled.norm.eventually (eventually_lt_nhds (by simpa using hmargin))
    rcases Filter.eventually_atTop.1 hsmall with ⟨kStop, hkStop⟩
    have hnext : ∀ j ≥ kStop, alg.x (j + 2) = alg.x (j + 1) := by
      intro j hj
      have hmem : lam⁻¹ • z j ∈ subdifferential phi 0 := hdf_r (by
        simpa [Metric.mem_ball, dist_eq_norm] using hkStop j hj)
      have hzero : IsProximalPoint phi lam (z j) 0 := by
        refine ⟨hlam, ?_⟩
        simpa [sub_zero] using hmem
      have hp := hprox lam (z j)
      have hpzero : prox lam (z j) = 0 :=
        proximal_point_eq_zero_of_subgradient_ball phi lam hlam (z j) (prox lam (z j)) hp hzero
      have hupdate := alg.update j
      rw [show h / (1 + h * gamma) = lam by rfl] at hupdate
      have hz :
          (1 / (h * (1 + h * gamma))) • (alg.x (j + 1) - alg.x j) -
              (beta / (1 + h * gamma)) • (gradient f (alg.x (j + 1)) - gradient f (alg.x j)) -
              (h / (1 + h * gamma)) • gradient f (alg.x (j + 1)) = z j := by
        rfl
      rw [hz, hpzero] at hupdate
      simpa using hupdate
    refine ⟨kStop + 1, ?_⟩
    intro k hk
    have hkstop : k - 1 ≥ kStop := by omega
    have hsucc := hnext (k - 1) hkstop
    have hindex : k - 1 + 2 = k + 1 := by omega
    have hindex' : k - 1 + 1 = k := by omega
    rw [hindex] at hsucc
    rw [hindex'] at hsucc
    exact hsucc
