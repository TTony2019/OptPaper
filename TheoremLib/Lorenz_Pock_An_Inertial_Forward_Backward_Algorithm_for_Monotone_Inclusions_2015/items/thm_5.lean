import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_2
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_2
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_3
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_4
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_3
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_thm_1

open Filter

open ERealFunction

open scoped Pointwise

namespace LorenzPock

set_option maxHeartbeats 1600000

/-! ## Scalar estimates behind condition (22)

Condition (22) says `τ⁻¹ - L_Q/2 > 0`, `σ⁻¹ - L_P/2 > 0` and
`‖K‖² < (τ⁻¹ - L_Q/2) (σ⁻¹ - L_P/2)`.  Reading this as the discriminant condition of the
two-variable form `a p² - 2 t p q + b q²` shows that

`S = M - ½L = [[(τ⁻¹ - L_Q/2) Id, -K*], [-K, (σ⁻¹ - L_P/2) Id]]`

is positive definite, which is hypothesis (i) of Theorem 1; the same estimate with `L = 0`
gives the coercivity of `M` needed by the Lyapunov argument. -/

private theorem coerciveQuad {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ^ 2 < a * b) :
    ∃ c : ℝ, 0 < c ∧ ∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
      c * (p ^ 2 + q ^ 2) ≤ a * p ^ 2 - 2 * t * p * q + b * q ^ 2 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hnum : 0 < a * b - t ^ 2 := sub_pos.mpr ht
  set ε : ℝ := (1 + t ^ 2 / (a * b)) / 2 with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have e1 : (1 - ε) * a = a * (a * b - t ^ 2) / (2 * (a * b)) := by
    rw [hεdef]; field_simp; ring
  have e2 : b - t ^ 2 / (ε * a) = b * (a * b - t ^ 2) / (a * b + t ^ 2) := by
    rw [hεdef]; field_simp; ring
  have e3 : a - t ^ 2 / (ε * b) = a * (a * b - t ^ 2) / (a * b + t ^ 2) := by
    rw [hεdef]; field_simp; ring
  have e4 : (1 - ε) * b = b * (a * b - t ^ 2) / (2 * (a * b)) := by
    rw [hεdef]; field_simp; ring
  have hX : 0 < (1 - ε) * a := by rw [e1]; positivity
  have hY : 0 < b - t ^ 2 / (ε * a) := by rw [e2]; positivity
  have hZ : 0 < a - t ^ 2 / (ε * b) := by rw [e3]; positivity
  have hW : 0 < (1 - ε) * b := by rw [e4]; positivity
  have amgm1 : ∀ p q : ℝ, 2 * t * p * q ≤ ε * a * p ^ 2 + (t ^ 2 / (ε * a)) * q ^ 2 := by
    intro p q
    have h := mul_nonneg (mul_nonneg hε0.le ha.le) (sq_nonneg (p - t * q / (ε * a)))
    have hexp : ε * a * (p - t * q / (ε * a)) ^ 2 =
        ε * a * p ^ 2 - 2 * t * p * q + (t ^ 2 / (ε * a)) * q ^ 2 := by
      field_simp
      ring
    linarith [hexp.ge, h]
  let c : ℝ := min (min ((1 - ε) * a) (b - t ^ 2 / (ε * a)))
    (min (a - t ^ 2 / (ε * b)) ((1 - ε) * b))
  refine ⟨c, lt_min (lt_min hX hY) (lt_min hZ hW), fun p q hp hq => ?_⟩
  have hle1 : c ≤ (1 - ε) * a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hle2 : c ≤ b - t ^ 2 / (ε * a) := le_trans (min_le_left _ _) (min_le_right _ _)
  have h1 := mul_le_mul_of_nonneg_right hle1 (sq_nonneg p)
  have h2 := mul_le_mul_of_nonneg_right hle2 (sq_nonneg q)
  have ham := amgm1 p q
  have hsplit : a * p ^ 2 - 2 * t * p * q + b * q ^ 2 =
      ((1 - ε) * a * p ^ 2 + (b - t ^ 2 / (ε * a)) * q ^ 2) +
        (ε * a * p ^ 2 - 2 * t * p * q + (t ^ 2 / (ε * a)) * q ^ 2) := by
    ring
  linarith [h1, h2, ham, hsplit.le, hsplit.ge]

/-- The quadratic form of `S = M - ½L` for the preconditioner (20) and the metric
`L = diag(L_Q, L_P)`. -/
theorem primal_dual_sub_block_inner {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (K : X →L[ℝ] Y) (τ σ LQ LP : ℝ) (u : WithLp 2 (X × Y)) :
    inner ℝ ((primalDualPreconditioner K τ σ -
        (1 / 2 : ℝ) • diagonalPreconditioner (LQ • ContinuousLinearMap.id ℝ X)
          (LP • ContinuousLinearMap.id ℝ Y)) u) u
      = (τ⁻¹ - LQ / 2) * ‖u.ofLp.1‖ ^ 2 - 2 * inner ℝ (K u.ofLp.1) u.ofLp.2
        + (σ⁻¹ - LP / 2) * ‖u.ofLp.2‖ ^ 2 := by
  rw [ContinuousLinearMap.sub_apply, inner_sub_left, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, primalDualPreconditioner, blockOperator_inner,
    diagonalPreconditioner_apply, WithLp.prod_inner_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- The quadratic form `A p² - 2 c x + B q²` is nonnegative as soon as `c²t² ≤ A B` and
`|x| ≤ t p q`.  This is the algebraic content of condition (24): the Schur-type product
condition on the two diagonal entries dominates the (scaled) off-diagonal term. -/
private theorem quadratic_nonneg_of_schur {A B t c x p q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : c ^ 2 * t ^ 2 ≤ A * B) (hx : |x| ≤ t * p * q) :
    0 ≤ A * p ^ 2 - 2 * c * x + B * q ^ 2 := by
  have hsum : 0 ≤ A * p ^ 2 + B * q ^ 2 :=
    add_nonneg (mul_nonneg hA (sq_nonneg p)) (mul_nonneg hB (sq_nonneg q))
  have hle_abs : 2 * (|c| * t) * (p * q) ≤ A * p ^ 2 + B * q ^ 2 := by
    have habs' : |c| ^ 2 * t ^ 2 ≤ A * B := by rw [sq_abs]; exact hAB
    have hpq : 0 ≤ (p * q) ^ 2 := sq_nonneg _
    have hkey : (2 * (|c| * t) * (p * q)) ^ 2 ≤ (A * p ^ 2 + B * q ^ 2) ^ 2 := by
      have h1 : 4 * (|c| ^ 2 * t ^ 2) * (p * q) ^ 2 ≤ 4 * (A * B) * (p * q) ^ 2 := by
        nlinarith [habs', hpq]
      have h2 : 4 * (A * B) * (p * q) ^ 2 ≤ (A * p ^ 2 + B * q ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (A * p ^ 2 - B * q ^ 2)]
      nlinarith [h1, h2]
    have h := sq_le_sq.mp hkey
    rw [abs_of_nonneg hsum] at h
    exact le_trans (le_abs_self _) h
  have hcx : c * x ≤ |c| * t * p * q := by
    calc c * x ≤ |c * x| := le_abs_self _
      _ = |c| * |x| := abs_mul c x
      _ ≤ |c| * (t * p * q) := mul_le_mul_of_nonneg_left hx (abs_nonneg c)
      _ = |c| * t * p * q := by ring
  nlinarith [hle_abs, hcx]

/-- The quadratic form of `M` itself, for the Lyapunov step. -/
theorem primal_dual_block_inner {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (K : X →L[ℝ] Y) (τ σ : ℝ) (u : WithLp 2 (X × Y)) :
    inner ℝ (primalDualPreconditioner K τ σ u) u
      = τ⁻¹ * ‖u.ofLp.1‖ ^ 2 - 2 * inner ℝ (K u.ofLp.1) u.ofLp.2
        + σ⁻¹ * ‖u.ofLp.2‖ ^ 2 := by
  rw [primalDualPreconditioner, blockOperator_inner]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- Theorem 5: the iterates of the inertial primal--dual method (21) converge weakly to a
saddle point of (19) as soon as (22) and (23) hold.

## Matching the paper's hypotheses

The numbered conditions of the paper appear verbatim:

* (22) is `hτ`, `hσ`, `hschur`;
* `α_k ∈ [0, α]` with `α < 1` is `hα`, `hαbound`;
* (23) is `hsummable`, stated with the `M`-squared norm of `def_4`;
* `∇Q`, `∇P^*` co-coercive with respect to `L_Q⁻¹`, `L_P⁻¹` are
  `hgradQ_cocoercive`, `hgradPStar_cocoercive` — the paper obtains them from the
  Lipschitz gradients of (19) via Baillon--Haddad.

Everything the paper *derives* is derived here, so this theorem verifies "(22) ⟹
convergence" rather than assuming its consequences:

* `S = M - ½L` is positive definite (hypothesis (i) of Theorem 1) — this is the paper's
  "`S = M - ½L` is positive definite if (22) is fulfilled";
* the coercivity constants of `M` and `S` needed to pass between the `S_k`-norm and the
  ambient norm (see the docstring of `thm_1` for why they are needed);
* the co-coercivity of `B = (∇Q, ∇P^*)` with respect to `L⁻¹ = diag(L_Q⁻¹, L_P⁻¹)`;
* that (21) is an instance of (10) with `λ_k ≡ 1`, by constructing the product-space
  `InertialForwardBackwardIteration`.

## Structural hypotheses

Two hypotheses are not derivable from the paper's numbered conditions with the
convex-analytic machinery available here, and are recorded explicitly:

* `hmaxA`, `hmaxB` : the §3 remark "this setup fits into our general framework of Sect. 2",
  i.e. maximal monotonicity of `A = [[∂G, K*], [-K, ∂F*]]` and of `B = diag(∇Q, ∇P^*)`.
  The paper's hypotheses make these true (`G, F^* ∈ Γ₀` gives maximal monotone
  subdifferentials, and the skew block is a bounded linear monotone perturbation), but
  `def_2` only assumes convexity of the epigraphs, and Foundation's
  `subdifferential_isMaximalMonotone_of_mem_gammaZero` additionally needs properness.
* `hS_nonempty`, `hS_saddle` : the paper's proof opens with "Denote by `x^*` a zero of
  `A + B`", and the saddle points of (19) are exactly the zeros of `A + B`; the latter is
  the paper's own identification of the optimality system. -/
theorem primal_dual_parameter_convergence {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (p : SaddlePointProblem X Y) (τ σ αbound : ℝ) (α : ℕ → ℝ)
    (it : InertialPrimalDualIteration X Y p.gradQ p.gradPStar p.K
      (subdifferential p.G) (subdifferential p.FStar) α τ σ)
    (hτ : 0 < τ ∧ τ < 2 / p.LQ) (hσ : 0 < σ ∧ σ < 2 / p.LP)
    (hschur : ‖p.K‖ ^ 2 < (τ⁻¹ - p.LQ / 2) * (σ⁻¹ - p.LP / 2))
    (hα : ∀ k, 0 ≤ α k ∧ α k ≤ αbound) (hαbound : αbound < 1)
    (hgradQ_cocoercive : ∀ x x', inner ℝ (p.gradQ x - p.gradQ x') (x - x') ≥
      (1 / p.LQ) * ‖p.gradQ x - p.gradQ x'‖ ^ 2)
    (hgradPStar_cocoercive : ∀ y y', inner ℝ (p.gradPStar y - p.gradPStar y') (y - y') ≥
      (1 / p.LP) * ‖p.gradPStar y - p.gradPStar y'‖ ^ 2)
    (hmaxA : SetValuedOperator.IsMaximalMonotone (primalDualSetOperator p.G p.FStar p.K))
    (hmaxB : SetValuedOperator.IsMaximalMonotone
      (primalDualGradientOperator p.gradQ p.gradPStar).toSetValuedOperator)
    (S : Set (WithLp 2 (X × Y)))
    (hsolution : S = {z | ∃ a ∈ primalDualSetOperator p.G p.FStar p.K z,
      a + primalDualGradientOperator p.gradQ p.gradPStar z = 0})
    (hS_nonempty : S.Nonempty)
    (hS_saddle : ∀ z, z ∈ S →
      IsPrimalDualSolution p.G p.FStar p.gradQ p.gradPStar p.K z)
    (hsummable : Summable (fun k ↦ α k * primalDualMnormSq p.K τ σ
      ((it.x k, it.dual k) - (it.x (k - 1), it.dual (k - 1))))) :
    ∃ z : WithLp 2 (X × Y),
      IsPrimalDualSolution p.G p.FStar p.gradQ p.gradPStar p.K z ∧
      Tendsto (fun k ↦ toWeakSpace ℝ (WithLp 2 (X × Y))
        (WithLp.toLp 2 (it.x k, it.dual k))) Filter.atTop
        (nhds (toWeakSpace ℝ (WithLp 2 (X × Y)) z)) ∧
      -- the "Furthermore" clause: (24) with a nondecreasing `α` also gives convergence.
      -- The paper words this as "condition (23) is fulfilled", and then quotes (17) for
      -- algorithm (21); we implement the same chain of implications (24) ⟹ (17) ⟹
      -- Theorem 2, which delivers the convergence directly.
      ((Monotone α ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ k,
        (1 - 3 * α k - ε) / τ ≥ (1 - α k) ^ 2 * p.LQ / 2 ∧
        (1 - 3 * α k - ε) / σ ≥ (1 - α k) ^ 2 * p.LP / 2 ∧
        ((1 - 3 * α k - ε) / τ - (1 - α k) ^ 2 * p.LQ / 2) *
          ((1 - 3 * α k - ε) / σ - (1 - α k) ^ 2 * p.LP / 2) ≥
            (1 - 3 * α k - ε) ^ 2 * ‖p.K‖ ^ 2) →
        ∃ z' : WithLp 2 (X × Y),
          IsPrimalDualSolution p.G p.FStar p.gradQ p.gradPStar p.K z' ∧
          Tendsto (fun k ↦ toWeakSpace ℝ (WithLp 2 (X × Y))
            (WithLp.toLp 2 (it.x k, it.dual k))) Filter.atTop
            (nhds (toWeakSpace ℝ (WithLp 2 (X × Y)) z'))) := by
  have hτpos : 0 < τ := hτ.1
  have hτne : τ ≠ 0 := ne_of_gt hτpos
  have hσpos : 0 < σ := hσ.1
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  have hLQpos : 0 < p.LQ := by
    have h : 0 < 2 / p.LQ := lt_trans hτ.1 hτ.2
    rcases (div_pos_iff.mp h) with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · norm_num at h1
  have hLPpos : 0 < p.LP := by
    have h : 0 < 2 / p.LP := lt_trans hσ.1 hσ.2
    rcases (div_pos_iff.mp h) with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · norm_num at h1
  -- the two coefficients of (22)
  have ha_pos : 0 < τ⁻¹ - p.LQ / 2 := by
    have h2 : τ * p.LQ < 2 := (lt_div_iff₀ hLQpos).mp hτ.2
    have h4 : p.LQ / 2 < τ⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hτpos]
      linarith
    linarith
  have hb_pos : 0 < σ⁻¹ - p.LP / 2 := by
    have h2 : σ * p.LP < 2 := (lt_div_iff₀ hLPpos).mp hσ.2
    have h4 : p.LP / 2 < σ⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hσpos]
      linarith
    linarith
  -- the product-space data of §3
  let Mpd : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) := primalDualPreconditioner p.K τ σ
  have hMpd_def : Mpd = primalDualPreconditioner p.K τ σ := rfl
  let Lpd : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) :=
    diagonalPreconditioner (p.LQ • ContinuousLinearMap.id ℝ X)
      (p.LP • ContinuousLinearMap.id ℝ Y)
  have hLpd_def : Lpd = diagonalPreconditioner (p.LQ • ContinuousLinearMap.id ℝ X)
      (p.LP • ContinuousLinearMap.id ℝ Y) := rfl
  let Linvpd : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) :=
    diagonalPreconditioner ((p.LQ)⁻¹ • ContinuousLinearMap.id ℝ X)
      ((p.LP)⁻¹ • ContinuousLinearMap.id ℝ Y)
  have hLinvpd_def : Linvpd = diagonalPreconditioner ((p.LQ)⁻¹ • ContinuousLinearMap.id ℝ X)
      ((p.LP)⁻¹ • ContinuousLinearMap.id ℝ Y) := rfl
  let Bpd : WithLp 2 (X × Y) → WithLp 2 (X × Y) :=
    primalDualGradientOperator p.gradQ p.gradPStar
  have hBpd_def : Bpd = primalDualGradientOperator p.gradQ p.gradPStar := rfl
  let Apd : SetValuedOperator (WithLp 2 (X × Y)) (WithLp 2 (X × Y)) :=
    primalDualSetOperator p.G p.FStar p.K
  have hApd_def : Apd = primalDualSetOperator p.G p.FStar p.K := rfl
  -- the quadratic form of `S = M - ½L`
  have hS_inner : ∀ u : WithLp 2 (X × Y),
      inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u
        = (τ⁻¹ - p.LQ / 2) * ‖u.ofLp.1‖ ^ 2 - 2 * inner ℝ (p.K u.ofLp.1) u.ofLp.2
          + (σ⁻¹ - p.LP / 2) * ‖u.ofLp.2‖ ^ 2 := by
    intro u
    rw [hMpd_def, hLpd_def]
    exact primal_dual_sub_block_inner p.K τ σ p.LQ p.LP u
  obtain ⟨cS, hcS_pos, hcS⟩ := coerciveQuad ha_pos hb_pos hschur
  -- positive definiteness and coercivity of `S` from (22)
  have hS_coercive : ∃ c : ℝ, 0 < c ∧ ∀ u : WithLp 2 (X × Y),
      c * ‖u‖ ^ 2 ≤ inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u := by
    refine ⟨cS, hcS_pos, fun u => ?_⟩
    rw [hS_inner u]
    have hcs : inner ℝ (p.K u.ofLp.1) u.ofLp.2 ≤ ‖p.K‖ * ‖u.ofLp.1‖ * ‖u.ofLp.2‖ := by
      have h1 := real_inner_le_norm (p.K u.ofLp.1) u.ofLp.2
      have h2 := p.K.le_opNorm u.ofLp.1
      nlinarith [norm_nonneg u.ofLp.2, norm_nonneg u.ofLp.1]
    have hnorm : ‖u‖ ^ 2 = ‖u.ofLp.1‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by
      simpa using WithLp.prod_norm_sq_eq_of_L2 u
    have hb := hcS ‖u.ofLp.1‖ ‖u.ofLp.2‖ (norm_nonneg _) (norm_nonneg _)
    rw [hnorm]
    nlinarith [hcs, hb]
  -- `L = diag(L_Q, L_P)` and its inverse
  have hL_selfadjoint : ∀ u v : WithLp 2 (X × Y),
      inner ℝ (Lpd u) v = inner ℝ u (Lpd v) := by
    have hf : ∀ x y : X, inner ℝ ((p.LQ • ContinuousLinearMap.id ℝ X) x) y =
        inner ℝ x ((p.LQ • ContinuousLinearMap.id ℝ X) y) := by
      intro x y
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        real_inner_smul_left, real_inner_smul_right]
    have hg : ∀ a b : Y, inner ℝ ((p.LP • ContinuousLinearMap.id ℝ Y) a) b =
        inner ℝ a ((p.LP • ContinuousLinearMap.id ℝ Y) b) := by
      intro a b
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        real_inner_smul_left, real_inner_smul_right]
    intro u v
    rw [hLpd_def]
    exact blockOperator_inner_comm _ _ 0 hf hg u v
  have hL_positive_definite : ∀ u : WithLp 2 (X × Y), u ≠ 0 →
      0 < inner ℝ (Lpd u) u := by
    intro u hu
    rw [hLpd_def, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    have h3 : ‖u‖ ^ 2 = ‖u.ofLp.1‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by
      simpa using WithLp.prod_norm_sq_eq_of_L2 u
    have h2 : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hmin : 0 < min p.LQ p.LP := lt_min hLQpos hLPpos
    have hle : min p.LQ p.LP * (‖u.ofLp.1‖ ^ 2 + ‖u.ofLp.2‖ ^ 2) ≤
        p.LQ * ‖u.ofLp.1‖ ^ 2 + p.LP * ‖u.ofLp.2‖ ^ 2 := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
    have hpos : 0 < ‖u.ofLp.1‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by rw [← h3]; exact h2
    nlinarith [mul_pos hmin hpos]
  have hLcomp : Lpd.comp Linvpd = ContinuousLinearMap.id ℝ (WithLp 2 (X × Y)) := by
    ext u
    rw [hLpd_def, hLinvpd_def, ContinuousLinearMap.comp_apply, diagonalPreconditioner_apply,
      diagonalPreconditioner_apply, ContinuousLinearMap.id_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      WithLp.ofLp_toLp]
    rw [← mul_smul, ← mul_smul, mul_inv_cancel₀ (ne_of_gt hLQpos),
      mul_inv_cancel₀ (ne_of_gt hLPpos), one_smul, one_smul, WithLp.toLp_ofLp]
  have hLinv : Linvpd.comp Lpd = ContinuousLinearMap.id ℝ (WithLp 2 (X × Y)) := by
    ext u
    rw [hLpd_def, hLinvpd_def, ContinuousLinearMap.comp_apply, diagonalPreconditioner_apply,
      diagonalPreconditioner_apply, ContinuousLinearMap.id_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      WithLp.ofLp_toLp]
    rw [← mul_smul, ← mul_smul, inv_mul_cancel₀ (ne_of_gt hLQpos),
      inv_mul_cancel₀ (ne_of_gt hLPpos), one_smul, one_smul, WithLp.toLp_ofLp]
  have hLnonneg : ∀ u : WithLp 2 (X × Y), 0 ≤ inner ℝ (Lpd u) u := by
    intro u
    rw [hLpd_def, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    positivity
  have hdecomp : ∀ u : WithLp 2 (X × Y), inner ℝ (Mpd u) u =
      inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u + (1 / 2 : ℝ) * inner ℝ (Lpd u) u := by
    intro u
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, ContinuousLinearMap.smul_apply,
      real_inner_smul_left]
    ring
  -- the metric `M` is coercive (used for the Lyapunov function)
  have hM_coercive : ∃ cM : ℝ, 0 < cM ∧ ∀ u : WithLp 2 (X × Y),
      cM * ‖u‖ ^ 2 ≤ inner ℝ (Mpd u) u := by
    obtain ⟨c, hc, hcS'⟩ := hS_coercive
    exact ⟨c, hc, fun u => by rw [hdecomp u]; linarith [hcS' u, hLnonneg u]⟩
  -- condition (i) of Theorem 1
  have hmetric : ∀ u : WithLp 2 (X × Y), u ≠ 0 →
      0 < inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u := by
    intro u hu
    obtain ⟨c, hc, hcS'⟩ := hS_coercive
    have h1 : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    nlinarith [hcS' u]
  have hM_selfadjoint : ∀ u v : WithLp 2 (X × Y),
      inner ℝ (Mpd u) v = inner ℝ u (Mpd v) := by
    have hf : ∀ x y : X, inner ℝ ((τ⁻¹ • ContinuousLinearMap.id ℝ X) x) y =
        inner ℝ x ((τ⁻¹ • ContinuousLinearMap.id ℝ X) y) := by
      intro x y
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        real_inner_smul_left, real_inner_smul_right]
    have hg : ∀ a b : Y, inner ℝ ((σ⁻¹ • ContinuousLinearMap.id ℝ Y) a) b =
        inner ℝ a ((σ⁻¹ • ContinuousLinearMap.id ℝ Y) b) := by
      intro a b
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        real_inner_smul_left, real_inner_smul_right]
    intro u v
    rw [hMpd_def]
    exact blockOperator_inner_comm _ _ p.K hf hg u v
  -- `M` is positive definite
  have hM_posdef : ∀ u : WithLp 2 (X × Y), u ≠ 0 → 0 < inner ℝ (Mpd u) u := by
    intro u hu
    obtain ⟨c, hc, hcS'⟩ := hS_coercive
    have h1 : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    rw [hdecomp u]
    nlinarith [hcS' u, hLnonneg u]
  -- co-coercivity of `(∇Q, ∇P^*)` with respect to `L⁻¹ = diag(L_Q⁻¹, L_P⁻¹)`
  have hBpd_sub : ∀ u v : WithLp 2 (X × Y),
      Bpd u - Bpd v = WithLp.toLp 2 (p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1,
        p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2) := by
    intro u v
    rw [hBpd_def]
    apply WithLp.ofLp_injective
    simp
  have hLinvpd_inner : ∀ w : WithLp 2 (X × Y),
      inner ℝ (Linvpd w) w = (p.LQ)⁻¹ * ‖w.ofLp.1‖ ^ 2 + (p.LP)⁻¹ * ‖w.ofLp.2‖ ^ 2 := by
    intro w
    rw [hLinvpd_def, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_self_eq_norm_sq, WithLp.ofLp_toLp]
  have hcocoercive : IsCocoerciveWithInverseMetric Bpd Linvpd S := by
    intro u v _
    rw [hBpd_sub u v]
    rw [hLinvpd_inner]
    rw [WithLp.prod_inner_apply]
    simp only [WithLp.ofLp_toLp, WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub]
    have h1 := hgradQ_cocoercive u.ofLp.1 v.ofLp.1
    have h2 := hgradPStar_cocoercive u.ofLp.2 v.ofLp.2
    have h3 : (1 / p.LQ) = (p.LQ)⁻¹ := one_div _
    have h4 : (1 / p.LP) = (p.LP)⁻¹ := one_div _
    rw [h3] at h1
    rw [h4] at h2
    linarith
  -- Lipschitz bound for `(∇Q, ∇P^*)`, from the Lipschitz gradients of (19)
  have hB_lipschitz : ∃ cB : ℝ, 0 < cB ∧ ∀ u v : WithLp 2 (X × Y),
      ‖Bpd u - Bpd v‖ ≤ cB * ‖u - v‖ := by
    refine ⟨max p.LQ p.LP, lt_max_of_lt_left hLQpos, fun u v => ?_⟩
    rw [hBpd_sub u v]
    have hnorm : ‖WithLp.toLp 2 (p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1,
        p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2)‖ ^ 2 =
        ‖p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1‖ ^ 2 +
          ‖p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp
    have hsub : ‖u - v‖ ^ 2 = ‖u.ofLp.1 - v.ofLp.1‖ ^ 2 + ‖u.ofLp.2 - v.ofLp.2‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2 (u - v)]
      simp
    have h1 := p.gradQ_lipschitz u.ofLp.1 v.ofLp.1
    have h2 := p.gradPStar_lipschitz u.ofLp.2 v.ofLp.2
    have hsq : ‖WithLp.toLp 2 (p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1,
        p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2)‖ ^ 2 ≤
        (max p.LQ p.LP * ‖u - v‖) ^ 2 := by
      rw [hnorm, mul_pow, hsub]
      have hq : ‖p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1‖ ^ 2 ≤
          max p.LQ p.LP ^ 2 * ‖u.ofLp.1 - v.ofLp.1‖ ^ 2 := by
        have hstep : ‖p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1‖ ^ 2 ≤
            (p.LQ * ‖u.ofLp.1 - v.ofLp.1‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        have hmono : (p.LQ * ‖u.ofLp.1 - v.ofLp.1‖) ^ 2 ≤
            (max p.LQ p.LP * ‖u.ofLp.1 - v.ofLp.1‖) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hLQpos.le (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) 2
        calc ‖p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1‖ ^ 2
            ≤ (p.LQ * ‖u.ofLp.1 - v.ofLp.1‖) ^ 2 := hstep
          _ ≤ (max p.LQ p.LP * ‖u.ofLp.1 - v.ofLp.1‖) ^ 2 := hmono
          _ = max p.LQ p.LP ^ 2 * ‖u.ofLp.1 - v.ofLp.1‖ ^ 2 := by ring
      have hp : ‖p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2‖ ^ 2 ≤
          max p.LQ p.LP ^ 2 * ‖u.ofLp.2 - v.ofLp.2‖ ^ 2 := by
        have hstep : ‖p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2‖ ^ 2 ≤
            (p.LP * ‖u.ofLp.2 - v.ofLp.2‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
        have hmono : (p.LP * ‖u.ofLp.2 - v.ofLp.2‖) ^ 2 ≤
            (max p.LQ p.LP * ‖u.ofLp.2 - v.ofLp.2‖) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hLPpos.le (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) 2
        calc ‖p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2‖ ^ 2
            ≤ (p.LP * ‖u.ofLp.2 - v.ofLp.2‖) ^ 2 := hstep
          _ ≤ (max p.LQ p.LP * ‖u.ofLp.2 - v.ofLp.2‖) ^ 2 := hmono
          _ = max p.LQ p.LP ^ 2 * ‖u.ofLp.2 - v.ofLp.2‖ ^ 2 := by ring
      linarith
    have hc_nonneg : 0 ≤ max p.LQ p.LP * ‖u - v‖ :=
      mul_nonneg (le_of_lt (lt_max_of_lt_left hLQpos)) (norm_nonneg _)
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hc_nonneg] at this
  -- (21) is an instance of the general scheme (10) with `λ_k ≡ 1`
  have hitFB_apart : ∀ k, WithLp.toLp 2 (it.ξ k, it.dualExtrapolated k) =
      WithLp.toLp 2 (it.x k, it.dual k) + α k •
        (WithLp.toLp 2 (it.x k, it.dual k) -
          WithLp.toLp 2 (it.x (k - 1), it.dual (k - 1))) := by
    intro k
    rw [it.ξ_eq k, it.ζ_eq k]
    apply WithLp.ofLp_injective
    ext <;> simp [smul_sub]
  have hitFB_sub : ∀ k, WithLp.toLp 2 (it.ξ k, it.dualExtrapolated k) -
      WithLp.toLp 2 (it.x (k + 1), it.dual (k + 1)) =
      WithLp.toLp 2 (it.ξ k - it.x (k + 1),
        it.dualExtrapolated k - it.dual (k + 1)) := by
    intro k
    apply WithLp.ofLp_injective
    simp
  let itFB : InertialForwardBackwardIteration (WithLp 2 (X × Y)) Apd Bpd Mpd α (fun _ ↦ 1) :=
    { x := fun k ↦ WithLp.toLp 2 (it.x k, it.dual k)
      y := fun k ↦ WithLp.toLp 2 (it.ξ k, it.dualExtrapolated k)
      inertia_range := fun k ↦ ⟨(hα k).1, lt_of_le_of_lt (hα k).2 hαbound⟩
      metric_self_adjoint := hM_selfadjoint
      metric_positive_definite := hM_posdef
      inertial := hitFB_apart
      forward_backward := fun k ↦ by
        obtain ⟨g, hg, hg_eq⟩ := it.primal_step k
        obtain ⟨f, hf, hf_eq⟩ := it.dual_step k
        -- rescale the two steps of (21) by `τ⁻¹` and `σ⁻¹`
        have hgτ : τ⁻¹ • (it.ξ k - it.x (k + 1)) - p.gradQ (it.ξ k) -
            p.K.adjoint (it.dualExtrapolated k) = g := by
          have h := congrArg (fun w : X ↦ τ⁻¹ • w) hg_eq
          dsimp only at h
          rw [smul_sub, smul_sub] at h
          have hcancel : ∀ w : X, τ⁻¹ • (τ • w) = w := fun w => by
            rw [← mul_smul, inv_mul_cancel₀ hτne, one_smul]
          simp only [hcancel] at h
          rw [← h, smul_sub]
          module
        have hfσ : σ⁻¹ • (it.dualExtrapolated k - it.dual (k + 1)) -
            p.gradPStar (it.dualExtrapolated k) +
            p.K (2 • it.x (k + 1) - it.ξ k) = f := by
          have h := congrArg (fun w : Y ↦ σ⁻¹ • w) hf_eq
          dsimp only at h
          rw [smul_sub, smul_sub] at h
          have hcancel : ∀ w : Y, σ⁻¹ • (σ • w) = w := fun w => by
            rw [← mul_smul, inv_mul_cancel₀ hσne, one_smul]
          simp only [hcancel] at h
          rw [← h, smul_sub]
          module
        refine ⟨WithLp.toLp 2 (g + p.K.adjoint (it.dual (k + 1)),
          f - p.K (it.x (k + 1))), ?_, ?_⟩
        · rw [mem_primalDualSetOperator]
          constructor
          · simpa using hg
          · simpa using hf
        · apply WithLp.ofLp_injective
          ext
          · have hval : (Mpd (WithLp.toLp 2 (it.ξ k, it.dualExtrapolated k) -
                WithLp.toLp 2 (it.x (k + 1), it.dual (k + 1))) -
                (1 : ℝ) • Bpd (WithLp.toLp 2 (it.ξ k, it.dualExtrapolated k))).ofLp.1
                = τ⁻¹ • (it.ξ k - it.x (k + 1)) -
                    p.K.adjoint (it.dualExtrapolated k - it.dual (k + 1)) -
                      p.gradQ (it.ξ k) := by
              rw [hitFB_sub k, hMpd_def, hBpd_def]
              simp [primalDualPreconditioner_apply, primalDualGradientOperator,
                WithLp.ofLp_sub, WithLp.ofLp_smul, one_smul]
            rw [hval]
            have hsplit : τ⁻¹ • (it.ξ k - it.x (k + 1)) -
                p.K.adjoint (it.dualExtrapolated k - it.dual (k + 1)) -
                  p.gradQ (it.ξ k) =
                (τ⁻¹ • (it.ξ k - it.x (k + 1)) - p.gradQ (it.ξ k) -
                  p.K.adjoint (it.dualExtrapolated k)) + p.K.adjoint (it.dual (k + 1)) := by
              rw [map_sub]
              module
            rw [hsplit, hgτ]
            simp
          · have hval : (Mpd (WithLp.toLp 2 (it.ξ k, it.dualExtrapolated k) -
                WithLp.toLp 2 (it.x (k + 1), it.dual (k + 1))) -
                (1 : ℝ) • Bpd (WithLp.toLp 2 (it.ξ k, it.dualExtrapolated k))).ofLp.2
                = -p.K (it.ξ k - it.x (k + 1)) +
                    σ⁻¹ • (it.dualExtrapolated k - it.dual (k + 1)) -
                      p.gradPStar (it.dualExtrapolated k) := by
              rw [hitFB_sub k, hMpd_def, hBpd_def]
              simp [primalDualPreconditioner_apply, primalDualGradientOperator,
                WithLp.ofLp_sub, WithLp.ofLp_smul, one_smul]
            rw [hval]
            have hK₁ : p.K (it.ξ k - it.x (k + 1)) =
                p.K (it.ξ k) - p.K (it.x (k + 1)) := map_sub _ _ _
            have hK₂ : p.K (2 • it.x (k + 1) - it.ξ k) =
                (2 : ℝ) • p.K (it.x (k + 1)) - p.K (it.ξ k) := by
              have hsmul : (2 : ℕ) • it.x (k + 1) = (2 : ℝ) • it.x (k + 1) := by
                rw [two_nsmul, two_smul]
              rw [hsmul, map_sub, ContinuousLinearMap.map_smul]
            have hsplit : -p.K (it.ξ k - it.x (k + 1)) +
                σ⁻¹ • (it.dualExtrapolated k - it.dual (k + 1)) -
                  p.gradPStar (it.dualExtrapolated k) =
                (σ⁻¹ • (it.dualExtrapolated k - it.dual (k + 1)) -
                    p.gradPStar (it.dualExtrapolated k) +
                      p.K (2 • it.x (k + 1) - it.ξ k)) - p.K (it.x (k + 1)) := by
              rw [hK₁, hK₂]
              module
            rw [hsplit, hfσ]
            simp }
  have hitFB_x : ∀ k, itFB.x k = WithLp.toLp 2 (it.x k, it.dual k) := fun k => rfl
  have hitFB_y : ∀ k, itFB.y k = WithLp.toLp 2 (it.ξ k, it.dualExtrapolated k) :=
    fun k => rfl
  -- condition (23) in the `M`-norm of the product space
  have hsumFB : Summable (fun k ↦ α k *
      inner ℝ (Mpd (itFB.x k - itFB.x (k - 1))) (itFB.x k - itFB.x (k - 1))) := by
    refine hsummable.congr (fun k ↦ ?_)
    have hsub : itFB.x k - itFB.x (k - 1) = WithLp.toLp 2
        ((it.x k, it.dual k) - (it.x (k - 1), it.dual (k - 1))) := by
      rw [hitFB_x k, hitFB_x (k - 1)]
      apply WithLp.ofLp_injective
      simp
    rw [primalDualMnormSq_eq_inner, hsub]
  -- maximal monotonicity of the sum `A + B` (Bauschke--Combettes Lemma 2.4)
  have hsummax : SetValuedOperator.IsMaximalMonotone (Apd + Bpd.toSetValuedOperator) := by
    have hBmono : SetValuedOperator.IsMonotone Bpd.toSetValuedOperator := by
      have h' : SetValuedOperator.IsMonotone
          (primalDualGradientOperator p.gradQ p.gradPStar).toSetValuedOperator := hmaxB.1
      rwa [hBpd_def]
    have hBdom : Bpd.toSetValuedOperator.dom = Set.univ := by
      ext z
      simp [SetValuedOperator.mem_dom_iff]
    have hBLip : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y u v, u ∈ Bpd.toSetValuedOperator x →
        v ∈ Bpd.toSetValuedOperator y → ‖u - v‖ ≤ L * ‖x - y‖ := by
      obtain ⟨cB, hcB, hLip⟩ := hB_lipschitz
      refine ⟨cB, hcB.le, fun x y u v hu hv => ?_⟩
      simp only [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu hv
      rw [hu, hv]
      exact hLip x y
    have h := SetValuedOperator.maximal_monotone_add_of_monotone_lipschitz Apd
      Bpd.toSetValuedOperator hmaxA hBmono hBdom hBLip
    rw [hApd_def, hBpd_def] at h
    exact h
  have hconv := inertial_forward_backward_weakly_converges Apd Bpd Mpd Lpd Linvpd α
    (fun _ ↦ 1) itFB S hmaxA hmaxB (by rw [hApd_def, hBpd_def]; exact hsolution)
    hS_nonempty hLinv hLcomp hB_lipschitz
    hL_selfadjoint hL_positive_definite hcocoercive
    (by intro k; norm_num) ⟨αbound, hαbound, hα⟩
    (by intro k u hu; rw [hMpd_def, hLpd_def]; exact hmetric u hu)
    hM_coercive
    (by
      rcases hS_coercive with ⟨c, hc, hc'⟩
      exact ⟨c, hc, fun _ u => hc' u⟩)
    hsummax ⟨1, by norm_num, fun _ => le_rfl⟩ hsumFB
  rcases hconv with ⟨z, hzS, hlim⟩
  refine ⟨z, hS_saddle z hzS, by simpa only [hitFB_x] using hlim, ?_⟩
  -- the "Furthermore" clause of Theorem 5: (24) implies (17), and Theorem 2 applies
  rintro ⟨hα_mono, ⟨ε, hε_pos, h24⟩⟩
  let A : ℕ → ℝ := fun k ↦ (1 - 3 * α k - ε) * τ⁻¹ - (1 - α k) ^ 2 * p.LQ / 2
  let B : ℕ → ℝ := fun k ↦ (1 - 3 * α k - ε) * σ⁻¹ - (1 - α k) ^ 2 * p.LP / 2
  let c : ℕ → ℝ := fun k ↦ 1 - 3 * α k - ε
  have hA_def : A = fun k ↦ (1 - 3 * α k - ε) * τ⁻¹ - (1 - α k) ^ 2 * p.LQ / 2 := rfl
  have hB_def : B = fun k ↦ (1 - 3 * α k - ε) * σ⁻¹ - (1 - α k) ^ 2 * p.LP / 2 := rfl
  have hc_def : c = fun k ↦ 1 - 3 * α k - ε := rfl
  have hA : ∀ k, 0 ≤ A k := by
    intro k
    have h := (h24 k).1
    simpa [A, c, div_eq_mul_inv] using h
  have hB : ∀ k, 0 ≤ B k := by
    intro k
    have h := (h24 k).2.1
    simpa [B, c, div_eq_mul_inv] using h
  have hAB : ∀ k, c k ^ 2 * ‖p.K‖ ^ 2 ≤ A k * B k := by
    intro k
    have h := (h24 k).2.2
    simpa [A, B, c, div_eq_mul_inv] using h
  -- the quadratic form of `R_k - ε M`
  have hR_form : ∀ k (u : WithLp 2 (X × Y)),
      inner ℝ ((((1 - 3 * α k) • Mpd) - (((1 - α k) ^ 2 * (1 : ℝ) / 2) • Lpd) -
          ε • Mpd) u) u
        = A k * ‖u.ofLp.1‖ ^ 2 - 2 * c k * inner ℝ (p.K u.ofLp.1) u.ofLp.2
          + B k * ‖u.ofLp.2‖ ^ 2 := by
    intro k u
    have h1 : inner ℝ (Mpd u) u = τ⁻¹ * ‖u.ofLp.1‖ ^ 2 -
        2 * inner ℝ (p.K u.ofLp.1) u.ofLp.2 + σ⁻¹ * ‖u.ofLp.2‖ ^ 2 := by
      rw [hMpd_def]
      exact primal_dual_block_inner p.K τ σ u
    have h2 : inner ℝ (Lpd u) u = p.LQ * ‖u.ofLp.1‖ ^ 2 + p.LP * ‖u.ofLp.2‖ ^ 2 := by
      rw [hLpd_def, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        real_inner_smul_left, real_inner_self_eq_norm_sq, WithLp.ofLp_toLp]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, inner_sub_left, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, h1, h2]
    rw [hA_def, hB_def, hc_def]
    ring
  have hR : ∃ ε' : ℝ, 0 < ε' ∧ ∀ k (u : WithLp 2 (X × Y)), 0 ≤ inner ℝ
      ((((1 - 3 * α k) • Mpd) - (((1 - α k) ^ 2 * (1 : ℝ) / 2) • Lpd) - ε' • Mpd) u) u := by
    refine ⟨ε, hε_pos, fun k u => ?_⟩
    rw [hR_form k u]
    have hx : |inner ℝ (p.K u.ofLp.1) u.ofLp.2| ≤
        ‖p.K‖ * ‖u.ofLp.1‖ * ‖u.ofLp.2‖ := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h := real_inner_le_norm (-(p.K u.ofLp.1)) u.ofLp.2
        rw [inner_neg_left, norm_neg] at h
        have h2 := p.K.le_opNorm u.ofLp.1
        nlinarith [norm_nonneg u.ofLp.2, norm_nonneg u.ofLp.1]
      · have h1 := real_inner_le_norm (p.K u.ofLp.1) u.ofLp.2
        have h2 := p.K.le_opNorm u.ofLp.1
        nlinarith [norm_nonneg u.ofLp.2, norm_nonneg u.ofLp.1]
    exact quadratic_nonneg_of_schur (hA k) (hB k) (hAB k) hx
  have hconv2 := inertial_lyapunov_condition_implies_weak_convergence Apd Bpd Mpd Lpd
    Linvpd α (fun _ ↦ 1) itFB S hmaxA hmaxB
    (by rw [hApd_def, hBpd_def]; exact hsolution)
    hS_nonempty hLinv hLcomp hB_lipschitz
    hL_selfadjoint hL_positive_definite hcocoercive
    (by intro k; norm_num) ⟨αbound, hαbound, hα⟩
    (by intro k u hu; rw [hMpd_def, hLpd_def]; exact hmetric u hu)
    hM_coercive
    (by
      rcases hS_coercive with ⟨c', hc, hc'⟩
      exact ⟨c', hc, fun _ u => hc' u⟩)
    hsummax ⟨1, by norm_num, fun _ => le_rfl⟩ hα_mono (fun _ _ _ => le_rfl) hR
  rcases hconv2 with ⟨z', hz'S, hlim'⟩
  exact ⟨z', hS_saddle z' hz'S, by simpa only [hitFB_x] using hlim'⟩

end LorenzPock
