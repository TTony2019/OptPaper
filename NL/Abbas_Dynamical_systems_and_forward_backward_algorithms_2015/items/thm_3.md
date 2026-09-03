## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/thm_3.lean`

## Lean statement
```lean
theorem bf_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (mu h beta delta : ℝ)
    (alg : BackwardForwardDiscretization Phi
      hPhi B mu h)
    (hmu : 0 < mu ∧ mu < 2 * beta) (hh : 0 < h ∧ h < delta)
    (hdelta : delta = 1 / 2 + min 1 (beta / mu))
    (hS : S.Nonempty)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    ∃ ybar xbar,
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩ ybar = xbar ∧
      xbar ∈ S ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (alg.y k)) atTop
        (nhds (toWeakSpace ℝ H ybar)) ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (alg.x k)) atTop
        (nhds (toWeakSpace ℝ H xbar)) ∧
      Tendsto (fun k ↦ B (alg.x k)) atTop (nhds (B xbar)) ∧
      Summable (fun k ↦ ‖alg.x (k + 1) - alg.x k‖ ^ 2) ∧
      Summable (fun k ↦ ‖alg.y (k + 1) - alg.y k‖ ^ 2) ∧
      Tendsto (fun k ↦ alg.y k - alg.x k) atTop (nhds (ybar - xbar))
```

## Statement explanation
Statement. The theorem `bf_convergence` is set in a real Hilbert space context. Precisely:

- `H : Type*` is an unspecified type equipped with a normed additive commutative group structure, a real inner product structure, and completeness, so it is a real Hilbert space.
- `Phi : H → Set.Ioi (⊥ : EReal)` is a function assigning to each point an extended real number lying strictly above the bottom element `⊥` of `EReal`. This is an extended-real-valued objective function that is never equal to `-∞` in the extended-real order.
- `hPhi : Phi ∈ ERealFunction.gammaZero H` states that `Phi` belongs to the gamma-zero class of extended-real-valued functions used in the theory of convex analysis in Mathlib.
- `S : Set H` is a proposed solution set.
- `B : H → H` is an operator.
- `mu`, `h`, `beta`, `delta` are real numbers.
- `alg : BackwardForwardDiscretization Phi hPhi B mu h` is an algorithmic object supplying the discrete sequences `alg.x k` and `alg.y k` produced by a backward-forward discretization associated with `Phi`, `B`, and step parameters `mu` and `h`.
- `hmu` asserts `0 < mu` and `mu < 2 * beta`.
- `hh` asserts `0 < h` and `h < delta`.
- `hdelta` asserts that `delta = 1 / 2 + min 1 (beta / mu)`.
- `hS` asserts that the solution set `S` is nonempty.
- `hB` asserts that `B` is `beta`-cocoercive on the whole space, expressed via the restricted operator `fun w : Set.univ ↦ B w`.
- `hsolution

## Lean proof
```lean
by
  let P : H → H := ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
  let F : H → H := fun x ↦ x - mu • B x
  let T : H → H := fun y ↦ P y - mu • B (P y)
  have hbeta : 0 < beta := by nlinarith [hmu.1, hmu.2]
  have hPfirm : FirmlyNonexpansive P := by
    have hscaled := ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, hmu.1⟩
    simpa [P, ERealFunction.scaledProximityOperator] using
      ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero hscaled
  have hPavg : AveragedWith (1 / 2 : ℝ) (fun x : Set.univ ↦ P x) :=
    firmlyNonexpansiveOn_iff_averagedWith_half _ |>.mp
      (firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ.mp hPfirm)
  have halphaF : 0 < mu / (2 * beta) ∧ mu / (2 * beta) < 1 := by
    have hden : 0 < 2 * beta := by positivity
    exact ⟨div_pos hmu.1 hden, (div_lt_one hden).mpr hmu.2⟩
  have hFavg : AveragedWith (mu / (2 * beta)) (fun x : Set.univ ↦ F x) := by
    simpa [F] using
      (cocoerciveOn_iff_averagedWith_id_sub_smul hbeta ⟨hmu.1, hmu.2⟩
        (fun w : Set.univ ↦ B w)).mp hB
  have hTavgRaw : AveragedWith
      (1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / (mu / (2 * beta))) (1 / (1 / 2))))
      (fun x : Set.univ ↦ T x) := by
    have hFop : IsAveragedOperator F (mu / (2 * beta)) halphaF :=
      (isAveragedOperator_iff_averagedWith F (mu / (2 * beta)) halphaF).mpr hFavg
    have hPop : IsAveragedOperator P (1 / 2 : ℝ) (by norm_num) :=
      (isAveragedOperator_iff_averagedWith P (1 / 2 : ℝ) (by norm_num)).mpr hPavg
    simpa [T, F, Function.comp_def] using
      (averaged_composition_constant F P (mu / (2 * beta)) (1 / 2 : ℝ)
        halphaF (by norm_num) hFop hPop)
  have hyupdate : ∀ k, alg.y (k + 1) = (1 - h) • alg.y k + h • T (alg.y k) := by
    intro k
    rw [alg.equation_step k, alg.prox_step k]
  have hTfixed : (Function.fixedPoints T).Nonempty := by
    rcases hS with ⟨z, hz⟩
    refine ⟨z - mu • B z, ?_⟩
    simpa [T, P] using
      (bf_solution_produces_fixed_point Phi hPhi B mu hmu.1 S hsolution hz)
  have hparam :
      1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / (mu / (2 * beta))) (1 / (1 / 2))) =
        1 / delta := by
    have hmu0 : mu ≠ 0 := ne_of_gt hmu.1
    have hbeta0 : beta ≠ 0 := ne_of_gt hbeta
    have hr : 1 / (mu / (2 * beta)) = 2 * (beta / mu) := by
      field_simp [hmu0, hbeta0]
    rw [hr, show 1 / (1 / 2 : ℝ) = 2 by norm_num, hdelta]
    rcases le_total (beta / mu) 1 with hle | hge
    · have hm : 2 * (beta / mu) ≤ 2 := by nlinarith
      rw [min_eq_left hm, min_eq_right hle]
      field_simp [hmu0, hbeta0]
    · have hm : 2 ≤ 2 * (beta / mu) := by nlinarith
      rw [min_eq_right hm, min_eq_left hge]
      field_simp [hmu0, hbeta0]
  have hTavg : AveragedWith (1 / delta) (fun x : Set.univ ↦ T x) := by
    rw [← hparam]
    exact hTavgRaw
  have hdelta_pos : 0 < delta := by
    rw [hdelta]
    have hratio : 0 < beta / mu := div_pos hbeta hmu.1
    exact add_pos_of_pos_of_nonneg (by norm_num)
      (le_min (by norm_num) hratio.le)
  have halpha : (1 / delta) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact one_div_pos.mpr hdelta_pos
    · apply (div_lt_one hdelta_pos).mpr
      rw [hdelta]
      have hratio : 0 < beta / mu := div_pos hbeta hmu.1
      have hratio_half : (1 / 2 : ℝ) < beta / mu := by
        apply (lt_div_iff₀ hmu.1).mpr
        nlinarith [hmu.2]
      have hmin : (1 / 2 : ℝ) < min (1 : ℝ) (beta / mu) :=
        lt_min (by norm_num) hratio_half
      nlinarith
  have hhalpha : h ∈ Set.Ioo (0 : ℝ) (1 / (1 / delta)) := by
    rw [one_div_div]
    simpa [hdelta] using hh
  obtain ⟨ybar, hybarfix, hyweak, hysum⟩ :=
    bf_relaxed_averaged_orbit T (1 / delta) h alg.y hTavg halpha hhalpha hTfixed hyupdate
  let xbar := P ybar
  have hxbarS : xbar ∈ S := by
    apply bf_fixed_point_prox_mem_solution Phi hPhi B mu hmu.1 S hsolution
    simpa [T, P, xbar] using hybarfix
  have htail :
      Tendsto (fun k ↦ toWeakSpace ℝ H (alg.x k)) atTop
          (nhds (toWeakSpace ℝ H xbar)) ∧
      Tendsto (fun k ↦ B (alg.x k)) atTop (nhds (B xbar)) ∧
      Summable (fun k ↦ ‖alg.x (k + 1) - alg.x k‖ ^ 2) ∧
      Tendsto (fun k ↦ alg.y k - alg.x k) atTop (nhds (ybar - xbar)) := by
    rcases hS with ⟨z0, hz0⟩
    let v : ℕ → H := fun n ↦ (mu : ℝ)⁻¹ • (alg.y n - alg.x n)
    let g : ℕ → ℝ := fun n ↦ (Phi z0 : EReal).toReal -
      (Phi (alg.x n) : EReal).toReal - inner ℝ (z0 - alg.x n) (v n)
    let A : ℕ → ℝ := fun n ↦ (1 / (2 * mu)) * ‖alg.x n - z0‖ ^ 2 + g n
    have h51k : ∀ k, A (k + 1) - A k + (1 / (2 * mu)) *
        ‖alg.x (k + 1) - alg.x k‖ ^ 2 +
        h * inner ℝ (B (alg.x k) - B z0) (alg.x k - z0) +
        h * inner ℝ (alg.x k - z0) (v k + B z0) ≤
        (1 / mu) * inner ℝ (alg.x (k + 1) - alg.x k)
          (alg.y (k + 1) - alg.y k) := by
      intro k
      simpa [v, g, A] using
        (bf_discrete_source51 Phi hPhi S B mu h alg hsolution hz0 k)
    have hcoco : ∀ k, beta * ‖B (alg.x k) - B z0‖ ^ 2 ≤
        inner ℝ (B (alg.x k) - B z0) (alg.x k - z0) := by
      intro k
      have hc := hB.ineq (⟨alg.x k, Set.mem_univ _⟩ : Set.univ)
        (⟨z0, Set.mem_univ _⟩ : Set.univ)
      simpa [real_inner_comm] using hc
    have hmono : ∀ k, 0 ≤ inner ℝ (alg.x k - z0) (v k + B z0) := by
      intro k
      have hv : v k ∈ ERealFunction.subdifferential Phi (alg.x k) := by
        simpa [v, alg.prox_step k] using
          (ERealFunction.scaledProximityOperator_residual_mem hPhi
            ⟨mu, alg.mu_pos⟩ (alg.y k))
      have hzsub : -B z0 ∈ ERealFunction.subdifferential Phi z0 :=
        (hsolution z0).1 hz0
      have hm := ERealFunction.isMonotone_subdifferential
        (fun x : H => (Phi x : EReal))
        (ERealFunction.isProper_of_mem_gammaZero hPhi) (v k) hv (-B z0) hzsub
      rw [show v k - (-B z0) = v k + B z0 by abel] at hm
      simpa [real_inner_comm] using hm
    have hAnonneg : ∀ k, 0 ≤ A k := by
      intro k
      dsimp [A]
      have hg := bf_prox_gap_nonneg Phi hPhi S B mu hmu.1 alg hsolution hz0 k
      have hcoef : 0 ≤ (1 / (2 * mu) : ℝ) :=
        one_div_nonneg.mpr (mul_nonneg (by norm_num) alg.mu_pos.le)
      exact add_nonneg (mul_nonneg hcoef (sq_nonneg _))
        (by simpa [v, g, real_inner_comm] using hg)
    have hsource55 : ∀ k,
        A (k + 1) - A k + (1 / (4 * mu)) *
          ‖alg.x (k + 1) - alg.x k‖ ^ 2 +
          h * beta * ‖B (alg.x k) - B z0‖ ^ 2 ≤
          (1 / mu) * ‖alg.y (k + 1) - alg.y k‖ ^ 2 := by
      intro k
      apply bf_discrete_source55_half mu h beta alg.mu_pos alg.h_pos
        (A k) (A (k + 1))
        (alg.x (k + 1) - alg.x k) (alg.y (k + 1) - alg.y k)
        (B (alg.x k)) (B z0) (alg.x k - z0) (v k + B z0)
      · exact h51k k
      · exact hcoco k
      · exact hmono k
    have hsum_err : Summable (fun k => (1 / mu) *
        ‖alg.y (k + 1) - alg.y k‖ ^ 2) := by
      simpa using hysum.mul_left (1 / mu)
    have hsum_dx : Summable (fun k => (1 / (4 * mu)) *
        ‖alg.x (k + 1) - alg.x k‖ ^ 2) := by
      apply summable_of_nonneg_le_diff_add_summable
        (fun k => (1 / (4 * mu)) * ‖alg.x (k + 1) - alg.x k‖ ^ 2)
        A (fun k => (1 / mu) * ‖alg.y (k + 1) - alg.y k‖ ^ 2)
      · intro k
        exact mul_nonneg
          (one_div_nonneg.mpr (mul_nonneg (by norm_num) alg.mu_pos.le))
          (sq_nonneg _)
      · exact hAnonneg
      · exact hsum_err
      · intro k
        have hbnon : 0 ≤ h * beta * ‖B (alg.x k) - B z0‖ ^ 2 :=
          mul_nonneg (mul_nonneg hh.1.le hbeta.le) (sq_nonneg _)
        linarith [hsource55 k, hbnon]
    have hsum_B : Summable (fun k => h * beta *
        ‖B (alg.x k) - B z0‖ ^ 2) := by
      apply summable_of_nonneg_le_diff_add_summable
        (fun k => h * beta * ‖B (alg.x k) - B z0‖ ^ 2)
        A (fun k => (1 / mu) * ‖alg.y (k + 1) - alg.y k‖ ^ 2)
      · intro k
        exact mul_nonneg
          (mul_nonneg hh.1.le hbeta.le) (sq_nonneg _)
      · exact hAnonneg
      · exact hsum_err
      · intro k
        have hdxnon : 0 ≤ (1 / (4 * mu)) *
            ‖alg.x (k + 1) - alg.x k‖ ^ 2 :=
          mul_nonneg (one_div_nonneg.mpr
            (mul_nonneg (by norm_num) alg.mu_pos.le)) (sq_nonneg _)
        linarith [hsource55 k, hdxnon]
    have hsum_Bsq : Summable (fun k => ‖B (alg.x k) - B z0‖ ^ 2) := by
      have hm := hsum_B.mul_left (h * beta)⁻¹
      convert hm using 1
      funext k
      field_simp [hh.1.ne', hbeta.ne']
    have hBnorm0 : Tendsto (fun k => ‖B (alg.x k) - B z0‖) atTop (nhds 0) := by
      exact ext_cor_1_sq_tendsto_implies_norm_tendsto_zero
        (fun k => ‖B (alg.x k) - B z0‖) (fun k => norm_nonneg _)
        hsum_Bsq.tendsto_atTop_zero
    have hBdiff : Tendsto (fun k => B (alg.x k) - B z0) atTop (nhds 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).2 hBnorm0
    have hBconst : B z0 = B xbar :=
      bf_operator_constant_on_solution_set Phi hPhi B beta S hbeta hB
        hsolution z0 hz0 xbar hxbarS
    have hBstrong : Tendsto (fun k => B (alg.x k)) atTop (nhds (B xbar)) := by
      have hadd := hBdiff.add (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => B z0) atTop (nhds (B z0)))
      simpa [hBconst] using hadd
    have hsum_dx_unscaled : Summable (fun k =>
        ‖alg.x (k + 1) - alg.x k‖ ^ 2) := by
      have hm := hsum_dx.mul_left (4 * mu)
      convert hm using 1
      funext k
      field_simp [alg.mu_pos.ne']
    have hdy_norm0 : Tendsto (fun k => ‖alg.y (k + 1) - alg.y k‖)
        atTop (nhds 0) := by
      exact ext_cor_1_sq_tendsto_implies_norm_tendsto_zero
        (fun k => ‖alg.y (k + 1) - alg.y k‖) (fun k => norm_nonneg _)
        hysum.tendsto_atTop_zero
    have hdy0 : Tendsto (fun k => alg.y (k + 1) - alg.y k) atTop (nhds 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).2 hdy_norm0
    have hresidual_identity : ∀ k, alg.y k - alg.x k =
        -mu • B (alg.x k) - h⁻¹ • (alg.y (k + 1) - alg.y k) := by
      intro k
      have hstep : alg.y (k + 1) - alg.y k = h •
          (alg.x k - alg.y k - mu • B (alg.x k)) := by
        rw [alg.equation_step k]
        module
      rw [hstep, smul_smul, inv_mul_cancel₀ alg.h_pos.ne', one_smul]
      module
    have hreslim : Tendsto (fun k => alg.y k - alg.x k) atTop
        (nhds (ybar - xbar)) := by
      have hfirst : Tendsto (fun k => -mu • B (alg.x k)) atTop
          (nhds (-mu • B xbar)) := by
        simpa using hBstrong.const_smul (-mu)
      have hsecond : Tendsto (fun k => h⁻¹ • (alg.y (k + 1) - alg.y k)) atTop
          (nhds 0) := by
        simpa using hdy0.const_smul h⁻¹
      have hsumlim := hfirst.sub hsecond
      have hyrel : ybar - xbar = -mu • B xbar := by
        have hfix : P ybar - mu • B (P ybar) = ybar := by
          simpa [T] using hybarfix
        calc
          ybar - xbar = ybar - P ybar := rfl
          _ = (P ybar - mu • B (P ybar)) - P ybar := by rw [hfix]
          _ = -mu • B (P ybar) := by module
          _ = -mu • B xbar := rfl
      simpa [hresidual_identity, hyrel] using hsumlim
    have hxweak : Tendsto (fun k => toWeakSpace ℝ H (alg.x k)) atTop
        (nhds (toWeakSpace ℝ H xbar)) := by
      apply (weakConvergence_iff_forall_tendsto_inner_right
        (fun k => alg.x k) xbar).2
      intro w
      have hyw := (weakConvergence_iff_forall_tendsto_inner_right
        (fun k => alg.y k) ybar).1 hyweak w
      have hresw : Tendsto (fun k => inner ℝ (alg.y k - alg.x k) w) atTop
          (nhds (inner ℝ (ybar - xbar) w)) := by
        have hcomp := (innerSL ℝ w).continuous.tendsto (ybar - xbar)
        simpa only [innerSL_apply_apply, real_inner_comm] using hcomp.comp hreslim
      have hsub := hyw.sub hresw
      have hpoint : ∀ k, inner ℝ (alg.x k) w =
          inner ℝ (alg.y k) w - inner ℝ (alg.y k - alg.x k) w := by
        intro k
        calc
          inner ℝ (alg.x k) w =
              inner ℝ (alg.y k - (alg.y k - alg.x k)) w := by
                congr 1
                module
          _ = inner ℝ (alg.y k) w - inner ℝ (alg.y k - alg.x k) w := by
            rw [inner_sub_left]
      convert hsub using 1
      · simp only [hpoint, inner_sub_right, real_inner_comm]
      · simp only [inner_sub_right, real_inner_comm]
        ring_nf
    exact ⟨hxweak, hBstrong, hsum_dx_unscaled, hreslim⟩
  exact ⟨ybar, xbar, rfl, hxbarS, hyweak, htail.1, htail.2.1,
    htail.2.2.1, hysum, htail.2.2.2⟩
```

## Proof explanation
No proof explanation was returned by the model.

