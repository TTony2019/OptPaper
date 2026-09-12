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
The theorem `bf_convergence` is a convergence statement for a backward-forward discretization in a real Hilbert space $H$. The space $H$ is assumed to be a complete real inner product space. The function $\Phi:H\to \mathrm{EReal}$ takes values strictly above the bottom element $\bot=-\infty$, and the hypothesis $\Phi\in\Gamma_0(H)$ says that $\Phi$ is a proper, convex, lower semicontinuous extended-real-valued function. The set $S\subseteq H$ is the solution set, characterized by the equivalence

$$
z\in S \quad\Longleftrightarrow\quad -Bz\in \partial\Phi(z)
$$

for every $z\in H$. Thus $S$ is the zero-inclusion solution set for the problem $0\in Bz+\partial\Phi(z)$. The map $B:H\to H$ is single-valued, and the hypothesis $hB$ says that $B$ is $\beta$-cocoercive on all of $H$, meaning that for all $u,v\in H$,

$$
\beta\,\|Bu-Bv\|^2 \le \langle Bu-Bv,u-v\rangle .
$$

The real parameters are $\mu,h,\beta,\delta$. The assumptions on them are

$$
0<\mu<2\beta,\qquad 0<h<\delta,\qquad
\delta=\frac12+\min\left(1,\frac{\beta}{\mu}\right).
$$

The object `alg` is a `BackwardForwardDiscretization` with parameter $\mu$, step $h$, operator $B$, and function $\Phi$; its proof fields supply the two sequences $x_k,y_k$, positivity of $\mu$ and $h$, and the proximal and update equations used later. The set $S$ is assumed nonempty.

The conclusion is that there exist $ybar,xbar\in H$ such that

$$
xbar=\mathrm{Prox}_{\mu\Phi}(ybar),
$$

where the scaled proximity operator is formed using $hPhi$ and the positivity of $\mu$, and such that

$$
xbar\in S,
$$

the sequence $y_k$ converges weakly to $ybar$,

$$
y_k\rightharpoonup ybar,
$$

the sequence $x_k$ converges weakly to $xbar$,

$$
x_k\rightharpoonup xbar,
$$

the images $B(x_k)$ converge strongly to $B(xbar)$,

$$
B(x_k)\to B(xbar),
$$

the squared successive differences are summable,

$$
\sum_{k}\|x_{k+1}-x_k\|^2<\infty,
\qquad
\sum_{k}\|y_{k+1}-y_k\|^2<\infty,
$$

and the residual converges strongly:

$$
y_k-x_k\to ybar-xbar.
$$

In ordinary mathematical language, under a cocoercivity condition on $B$, a step-size restriction $h<\delta$, and the assumption that the solution set is nonempty, the relaxed backward-forward orbit converges weakly to a pair $(ybar,xbar)$ where $xbar$ is the proximal image of $ybar$ and lies in the solution set. The operator values along $x_k$ converge strongly, the successive increments are square-summable, and the gap $y_k-x_k$ tends to the limiting gap.

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
The proof begins by introducing three auxiliary operators. Let

$$
P(y)=\mathrm{Prox}_{\mu\Phi}(y),
\qquad
F(x)=x-\mu Bx,
\qquad
T(y)=P(y)-\mu B(P(y)).
$$

Thus $T=F\circ P$. The goal is to show that the $y$-sequence is a relaxed averaged iteration for $T$, then transfer the resulting weak convergence from $y_k$ to $x_k=P(y_k)$, and finally establish the strong convergence and summability claims.

First, the proof notes that $\beta>0$. This follows from $0<\mu$ and $\mu<2\beta$ by `nlinarith`. Next it shows that $P$ is firmly nonexpansive. Since $\Phi\in\Gamma_0(H)$ and $\mu>0$, the cited result `smul_mem_gammaZero` says that the positive scalar multiple $\mu\Phi$ again belongs to $\Gamma_0(H)$. The cited theorem `proximityOperator_firmlyNonexpansive_of_mem_gammaZero` then says that the proximity operator of a $\Gamma_0$-function is firmly nonexpansive. Because $P$ is by definition the scaled proximity operator of $\Phi$ with parameter $\mu$, this gives that $P$ is firmly nonexpansive. The proof then converts this into averagedness: the theorem `firmlyNonexpansiveOn_iff_averagedWith_half` says that firm nonexpansiveness on a set is equivalent to averagedness with parameter $1/2$, and `firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ` identifies the whole-space firm nonexpansiveness with the version on `Set.univ`. Hence $P$ is $(1/2)$-averaged.

Second, the proof obtains averagedness of $F$. From $0<\mu<2\beta$, it proves

$$
0<\frac{\mu}{2\beta}<1.
$$

The cited theorem `cocoerciveOn_iff_averagedWith_id_sub_smul` says that if $\beta>0$ and $\gamma\in(0,2\beta)$, then $\beta$-cocoercivity of an operator $B$ on a set $D$ is equivalent to averagedness of the map

$$
x\mapsto x-\gamma Bx
$$

with parameter $\gamma/(2\beta)$. Applying this with $\gamma=\mu$ and $D=\mathrm{Set.univ}$, the hypothesis $hB$ gives that

$$
F(x)=x-\mu Bx
$$

is $(\mu/(2\beta))$-averaged.

Third, the proof shows that $T=F\circ P$ is averaged. It converts the averagedness of $F$ and $P$ into the `IsAveragedOperator` form, then invokes `averaged_composition_constant`. In this instance that result gives that the composition $F\circ P$ is averaged with parameter

$$
\frac{1}{\frac12+\frac12\min\left(\frac{1}{\mu/(2\beta)},\frac{1}{1/2}\right)}.
$$

Since $T=F\circ P$, this is an averagedness statement for $T$. The proof then simplifies this parameter. It uses

$$
\frac{1}{\mu/(2\beta)}=\frac{2\beta}{\mu},
\qquad
\frac{1}{1/2}=2,
$$

and splits into the two cases $\beta/\mu\le 1$ and $1\le \beta/\mu$. In both cases the displayed parameter becomes

$$
\frac{1}{\delta},
$$

because

$$
\delta=\frac12+\min\left(1,\frac{\beta}{\mu}\right).
$$

Thus $T$ is $(1/\delta)$-averaged.

The proof next verifies that the relaxed averaged-orbit theorem applies. It proves $0<\delta$ and $(1/\delta)\in(0,1)$. Indeed, $\delta>0$ is immediate from its definition. Also $\mu<2\beta$ gives $\beta/\mu>1/2$, hence $\min(1,\beta/\mu)>1/2$, so $\delta>1$, which implies $1/\delta<1$. Since $h<\delta$, and $1/(1/\delta)=\delta$, the hypothesis $hh$ gives

$$
h\in\left(0,\frac{1}{1/\delta}\right).
$$

Thus all hypotheses on the averaging parameter and step size are satisfied.

The proof also needs a fixed point of $T$. Since $S$ is nonempty, choose $z\in S$. The cited result `bf_solution_produces_fixed_point` is used in the following form: if $z\in S$, then $z-\mu Bz$ is a fixed point of $T$. Therefore `Function.fixedPoints T` is nonempty. Next, from the discretization fields, the proof obtains the update formula

$$
y_{k+1}=(1-h)y_k+hT(y_k).
$$

Indeed, `alg.prox_step` identifies $x_k=P(y_k)$, while `alg.equation_step` gives the backward-forward update; after rewriting, this is exactly the relaxed averaged-iteration form.

Now the cited theorem `bf_relaxed_averaged_orbit` is applied to $T$, the averaging parameter $1/\delta$, the step $h$, and the sequence $u_k=y_k$. Its conclusions give a point $ybar$ such that $T(ybar)=ybar$, such that

$$
y_k\rightharpoonup ybar
$$

weakly, and such that

$$
\sum_k\|y_{k+1}-y_k\|^2<\infty.
$$

The proof sets

$$
xbar=P(ybar).
$$

Since $T(ybar)=ybar$, we have

$$
P(ybar)-\mu B(P(ybar))=ybar.
$$

The cited result `bf_fixed_point_prox_mem_solution` states that if

$$
P(y)-\mu B(P(y))=y,
$$

then $P(y)\in S$. Applying this to $y=ybar$ gives $xbar=P(ybar)\in S$.

The remaining part of the proof establishes the strong convergence, summability, and weak convergence of $x_k$. It again chooses a point $z_0\in S$, using the nonemptiness of $S$. It defines

$$
v_k=\mu^{-1}(y_k-x_k),
$$

$$
g_k=(\Phi z_0)_{\mathbb R}-(\Phi x_k)_{\mathbb R}
-\langle z_0-x_k,v_k\rangle,
$$

and

$$
A_k=\frac{1}{2\mu}\|x_k-z_0\|^2+g_k.
$$

Here $(\Phi z)_{\mathbb R}$ denotes the real reading of the extended-real value $\Phi(z)$ supplied by `EReal.toReal`.

The cited result `bf_discrete_source51` is used to produce the discrete energy inequality

$$
\begin{aligned}
A_{k+1}-A_k+\frac{1}{2\mu}\|x_{k+1}-x_k\|^2
&+h\langle Bx_k-Bz_0,x_k-z_0\rangle\\
&+h\langle x_k-z_0,v_k+Bz_0\rangle
\le \frac{1}{\mu}\langle x_{k+1}-x_k,y_{k+1}-y_k\rangle.
\end{aligned}
$$

This is the source estimate from which the summability conclusions will be extracted. The proof also derives the cocoercivity inequality

$$
\beta\|Bx_k-Bz_0\|^2\le \langle Bx_k-Bz_0,x_k-z_0\rangle,
$$

directly from the hypothesis $hB$ applied to $x_k$ and $z_0$, using symmetry of the real inner product.

Next, the proof proves the monotonicity inequality

$$
0\le \langle x_k-z_0,v_k+Bz_0\rangle.
$$

For this, it first notes that

$$
v_k\in\partial\Phi(x_k).
$$

This follows from the cited theorem `scaledProximityOperator_residual_mem`, which says that for a $\Gamma_0$-function $f$, a positive parameter $\gamma$, and a point $y$,

$$
\gamma^{-1}\bigl(y-\mathrm{Prox}_{\gamma f}(y)\bigr)
\in \partial f\bigl(\mathrm{Prox}_{\gamma f}(y)\bigr).
$$

Since $x_k$ is the proximal image of $y_k$, this gives $v_k=\mu^{-1}(y_k-x_k)\in\partial\Phi(x_k)$. Also, from the solution characterization,

$$
-Bz_0\in\partial\Phi(z_0).
$$

The cited theorem `isMonotone_subdifferential` says that the subdifferential of a proper convex function is a monotone set-valued operator. The properness hypothesis is supplied by `isProper_of_mem_gammaZero`, which states that a $\Gamma_0$-function is proper when regarded as an extended-real-valued function. Monotonicity therefore gives

$$
0\le \langle x_k-z_0,v_k-(-Bz_0)\rangle,
$$

which is exactly

$$
0\le \langle x_k-z_0,v_k+Bz_0\rangle.
$$

The proof then shows that $A_k\ge 0$. It uses the cited theorem `bf_prox_gap_nonneg`, which gives

$$
0\le (\Phi z_0)_{\mathbb R}-(\Phi x_k)_{\mathbb R}
-\left\langle \mu^{-1}(y_k-x_k),z_0-x_k\right\rangle.
$$

After identifying $\mu^{-1}(y_k-x_k)$ with $v_k$ and using symmetry of the inner product, this is precisely $g_k\ge 0$. Since

$$
\frac{1}{2\mu}\|x_k-z_0\|^2\ge 0,
$$

it follows that $A_k\ge 0$.

With these three ingredients, the proof applies the algebraic lemma `bf_discrete_source55_half`. Its statement is: if

$$
A_1-A_0+\frac{1}{2\mu}\|dx\|^2+h\langle bx-bz,xz\rangle+h\langle xz,q\rangle
\le \frac{1}{\mu}\langle dx,dy\rangle,
$$

if

$$
\beta\|bx-bz\|^2\le \langle bx-bz,xz\rangle,
$$

and if

$$
0\le \langle xz,q\rangle,
$$

then

$$
A_1-A_0+\frac{1}{4\mu}\|dx\|^2+h\beta\|bx-bz\|^2
\le \frac{1}{\mu}\|dy\|^2.
$$

Instantiating this with $A_0=A_k$, $A_1=A_{k+1}$, $dx=x_{k+1}-x_k$, $dy=y_{k+1}-y_k$, $bx=Bx_k$, $bz=Bz_0$, $xz=x_k-z_0$, and $q=v_k+Bz_0$ yields

$$
A_{k+1}-A_k+\frac{1}{4\mu}\|x_{k+1}-x_k\|^2
+h\beta\|Bx_k-Bz_0\|^2
\le \frac{1}{\mu}\|y_{k+1}-y_k\|^2.
$$

The summability of the $y$-increments gives that the sequence

$$
c_k=\frac{1}{\mu}\|y_{k+1}-y_k\|^2
$$

is summable. The proof then applies the lemma `summable_of_nonneg_le_diff_add_summable`, which states that if $a_k\ge 0$, $d_k\ge 0$, $c$ is summable, and

$$
a_k\le d_k-d_{k+1}+c_k
$$

for every $k$, then $a$ is summable. Taking

$$
a_k=\frac{1}{4\mu}\|x_{k+1}-x_k\|^2,
\qquad
d_k=A_k,
\qquad
c_k=\frac{1}{\mu}\|y_{k+1}-y_k\|^2
$$

gives summability of the scaled $x$-increment squares. Taking instead

$$
a_k=h\beta\|Bx_k-Bz_0\|^2
$$

with the same $d_k$ and $c_k$ gives summability of $h\beta\|Bx_k-Bz_0\|^2$. After multiplying by the positive constants $(4\mu)$ and $(h\beta)^{-1}$, respectively, the proof obtains

$$
\sum_k\|x_{k+1}-x_k\|^2<\infty
$$

and

$$
\sum_k\|Bx_k-Bz_0\|^2<\infty.
$$

From the latter summability, the terms $\|Bx_k-Bz_0\|^2$ tend to $0$. The cited theorem `ext_cor_1_sq_tendsto_implies_norm_tendsto_zero` says that if $r_k\ge 0$ and $r_k^2\to 0$, then $r_k\to 0$. Applying it with $r_k=\|Bx_k-Bz_0\|$ gives

$$
\|Bx_k-Bz_0\|\to 0.
$$

Using `tendsto_zero_iff_norm_tendsto_zero`, this converts to

$$
Bx_k-Bz_0\to 0,
$$

hence $Bx_k\to Bz_0$. The proof then invokes `bf_operator_constant_on_solution_set`, which says that if $B$ is $\beta$-cocoercive with $\beta>0$ and $S$ is the solution set defined by the subdifferential inclusion, then $B$ is constant on $S$. Since $z_0\in S$ and $xbar\in S$, it follows that $Bz_0=Bxbar$. Therefore

$$
Bx_k\to Bxbar.
$$

Similarly, from the summability of the $y$-increments, the terms $\|y_{k+1}-y_k\|^2$ tend to $0$, and again `ext_cor_1_sq_tendsto_implies_norm_tendsto_zero` and `tendsto_zero_iff_norm_tendsto_zero` give

$$
y_{k+1}-y_k\to 0.
$$

The proof also derives the residual identity

$$
y_k-x_k=-\mu Bx_k-h^{-1}(y_{k+1}-y_k)
$$

from the update equation. Since $Bx_k\to Bxbar$ and $y_{k+1}-y_k\to 0$, the right-hand side tends to $-\mu Bxbar$. But from the fixed-point equation $T(ybar)=ybar$, we have

$$
ybar=P(ybar)-\mu B(P(ybar))=xbar-\mu Bxbar,
$$

so

$$
-\mu Bxbar=ybar-xbar.
$$

Therefore

$$
y_k-x_k\to ybar-xbar.
$$

Finally, the proof obtains weak convergence of $x_k$. The cited theorem `weakConvergence_iff_forall_tendsto_inner_right` states that in a complete Hilbert space, weak convergence $\xi_k\rightharpoonup x$ is equivalent to convergence of all inner products:

$$
\langle \xi_k,u\rangle\to \langle x,u\rangle
$$

for every $u$. Since $y_k\rightharpoonup ybar$, for every $w$,

$$
\langle y_k,w\rangle\to \langle ybar,w\rangle.
$$

Since $y_k-x_k\to ybar-xbar$ strongly, continuity of the linear functional $z\mapsto \langle z,w\rangle$ gives

$$
\langle y_k-x_k,w\rangle\to \langle ybar-xbar,w\rangle.
$$

Subtracting these limits yields

$$
\langle x_k,w\rangle
=\langle y_k,w\rangle-\langle y_k-x_k,w\rangle
\to
\langle ybar,w\rangle-\langle ybar-xbar,w\rangle
=\langle xbar,w\rangle.
$$

Applying the weak-convergence criterion again, this time to the sequence $x_k$, gives

$$
x_k\rightharpoonup xbar.
$$

The proof then assembles all conclusions: the chosen $ybar$ and $xbar=P(ybar)$ satisfy the proximal relation by definition, $xbar\in S$ has been shown, the weak convergences of $y_k$ and $x_k$ have been proved, the strong convergence $Bx_k\to Bxbar$ has been proved, both squared-increment series are summable, and the residual convergence $y_k-x_k\to ybar-xbar$ has been established. This is exactly the existential conclusion of `bf_convergence`.

