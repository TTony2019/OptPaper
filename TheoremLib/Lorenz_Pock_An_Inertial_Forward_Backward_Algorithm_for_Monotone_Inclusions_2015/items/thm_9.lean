import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_5
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_2
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_3
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_5
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_4
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.lem_2
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1

open Filter

open ERealFunction

open scoped Pointwise

namespace LorenzPock

set_option maxHeartbeats 1600000

/-- If `(c x)² ≤ P Q` then `0 ≤ P - 2 c x + Q`: this is the Schur-complement estimate behind
(34), in the form in which the shifted block forms `P`, `Q` appear. -/
private theorem schur_nonneg {P Q c x : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : (c * x) ^ 2 ≤ P * Q) : 0 ≤ P - 2 * c * x + Q := by
  have hsum : 0 ≤ P + Q := by linarith
  have h1 : (2 * (c * x)) ^ 2 ≤ (P + Q) ^ 2 := by nlinarith [sq_nonneg (P - Q)]
  have h2 := sq_le_sq.mp h1
  rw [abs_of_nonneg hsum] at h2
  nlinarith [le_abs_self (2 * (c * x)), abs_nonneg (2 * (c * x))]

/-- Condition (34) of Theorem 9, for a single index `k`: the two shifted blocks
`(1 - 3α_k - ε) T⁻¹ - ((1 - α_k)²/2) D` and `(1 - 3α_k - ε) Σ⁻¹ - ((1 - α_k)²/2) E` are
positive definite, and the off-diagonal block scaled by their inverse square roots is
contractive:

`‖ ((1-3α_k-ε)Σ⁻¹ - ((1-α_k)²/2)E)^{-1/2} K ((1-3α_k-ε)T⁻¹ - ((1-α_k)²/2)D)^{-1/2} ‖
  ≤ 1/(1-3α_k-ε)`.

As for (33), the square roots appearing in the paper's formula are supplied as witness
operators and pinned down by algebraic identities, so the condition is not satisfiable by
zero operators.  `0 < 1 - 3α_k - ε` is recorded separately because the stated bound is
meaningless otherwise (with `1 - 3α_k - ε ≤ 0` no operator can satisfy it). -/
def AlphaCondition34 {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (K : X →L[ℝ] Y) (Tinv : X →L[ℝ] X) (Sigmainv : Y →L[ℝ] Y) (D : X →L[ℝ] X)
    (E : Y →L[ℝ] Y) (α : ℕ → ℝ) (ε : ℝ) (k : ℕ) : Prop :=
  0 < 1 - 3 * α k - ε ∧
  (∀ x, x ≠ 0 → 0 < inner ℝ (((1 - 3 * α k - ε) • Tinv - ((1 - α k) ^ 2 / 2) • D) x) x) ∧
  (∀ y, y ≠ 0 → 0 < inner ℝ (((1 - 3 * α k - ε) • Sigmainv - ((1 - α k) ^ 2 / 2) • E) y) y) ∧
  ∃ (A₁ksqrt A₁kinvsqrt : X →L[ℝ] X) (A₂ksqrt A₂kinvsqrt : Y →L[ℝ] Y),
    (∀ x y, inner ℝ (A₁ksqrt x) y = inner ℝ x (A₁ksqrt y)) ∧
    (∀ x y, inner ℝ (A₂ksqrt x) y = inner ℝ x (A₂ksqrt y)) ∧
    (∀ x y, inner ℝ (A₂kinvsqrt x) y = inner ℝ x (A₂kinvsqrt y)) ∧
    A₁ksqrt.comp A₁ksqrt = (1 - 3 * α k - ε) • Tinv - ((1 - α k) ^ 2 / 2) • D ∧
    A₂ksqrt.comp A₂ksqrt = (1 - 3 * α k - ε) • Sigmainv - ((1 - α k) ^ 2 / 2) • E ∧
    A₁kinvsqrt.comp A₁ksqrt = ContinuousLinearMap.id ℝ X ∧
    A₂kinvsqrt.comp A₂ksqrt = ContinuousLinearMap.id ℝ Y ∧
    ‖A₂kinvsqrt.comp (K.comp A₁kinvsqrt)‖ ≤ 1 / (1 - 3 * α k - ε)

/-- Theorem 9: the operator-preconditioned scheme (30) converges weakly to a saddle point of
(19) under the block-metric conditions (31)--(33).

## Matching the paper's hypotheses

The paper's conditions appear verbatim:

* (31), (32) are `h31`, `h32`;
* (33) is `h33`, with the `(Σ⁻¹ - ½E)^{-1/2}`, `(T⁻¹ - ½D)^{-1/2}` of the formula supplied as
  explicit witness operators and *pinned down* by the algebraic identities
  `A₁sqrt ∘ A₁sqrt = T⁻¹ - ½D` etc. — the paper's notation presupposes these square roots,
  and with the identities imposed the condition is no longer satisfiable by zero operators;
* "∇Q and ∇P^* co-coercive with respect to `D^{-1}` and `E^{-1}`" are
  `hgradQ_cocoercive`, `hgradPStar_cocoercive`;
* `α_k ∈ [0, α]` with `α < 1` is `hα`, `hαbound`;
* the summability of `Σ α_k ‖(x^k,y^k) - (x^{k-1},y^{k-1})‖²_M` is `hsummable`, with `M`
  the operator preconditioner of `def_5`.

What the paper derives is derived here:

* `S = M - ½C` is positive definite — the paper's "Now we use Lemma 8 to see that (31),
  (32) and (33) imply that `S` is positive definite".  This is where `lem_2` enters the
  proof chain; the quantitative form of the same estimate also supplies the coercivity
  constant required by `thm_1` (see the docstring of `thm_1`), which is why the paper's
  Lemma 8 is invoked through `block_operator_coercive_of_coercive_blocks`;
* co-coercivity of `B = (∇Q, ∇P^*)` with respect to `C⁻¹ = diag(D⁻¹, E⁻¹)`;
* that (30) is an instance of (10) with `λ_k ≡ 1` — here `Tinv.comp T = id` and
  `Sigmainv.comp Sigma = id` (the paper's `T⁻¹`, `Σ⁻¹`) are exactly what is needed, so
  `hT_inverse` and `hSigma_inverse` are consumed by the proof;
* maximal monotonicity of `A + B` from that of `A`, of `B`, and the Lipschitz bound on
  `(∇Q, ∇P^*)` that `def_2` records.

## Structural and strengthening hypotheses

* `hmaxA`, `hmaxB`, `hS_nonempty`, `hS_saddle` : as in `thm_5` (see its docstring).
* `h31`, `h32` are conditions (31), (32), stated with an explicit positive constant, i.e.
  as *uniform* lower bounds for the two Schur blocks `Σ⁻¹ - ½E`, `T⁻¹ - ½D`.  The paper
  states them as pointwise positivity; as explained in the docstring of `thm_1`, the proof
  of Theorem 1 needs a uniform constant in order to pass between the `S`-norm and the
  ambient norm, and in the paper's setting (`T, Σ, D, E` bounded positive definite with
  bounded inverses) the uniform bound does hold, but extracting it needs the spectral
  theory of self-adjoint operators on real Hilbert spaces.
* `hD_*`, `hE_*` : the paper's "the two bound, linear, symmetric and positive linear maps
  `D⁻¹` and `E⁻¹`", together with the two-sided inverse identities relating them to `D`
  and `E`. -/
theorem preconditioned_primal_dual_convergence {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (p : SaddlePointProblem X Y) (αbound : ℝ) (α : ℕ → ℝ)
    (T : X →L[ℝ] X) (Sigma : Y →L[ℝ] Y) (Tinv : X →L[ℝ] X) (Sigmainv : Y →L[ℝ] Y)
    (D Dinv : X →L[ℝ] X) (E Einv : Y →L[ℝ] Y)
    (it : PreconditionedInertialPrimalDualIteration X Y p.G p.FStar p.K T Sigma
      p.gradQ p.gradPStar α)
    (hT_inverse : Tinv.comp T = ContinuousLinearMap.id ℝ X)
    (hSigma_inverse : Sigmainv.comp Sigma = ContinuousLinearMap.id ℝ Y)
    (hD_inverse : Dinv.comp D = ContinuousLinearMap.id ℝ X)
    (hD_inverse' : D.comp Dinv = ContinuousLinearMap.id ℝ X)
    (hE_inverse : Einv.comp E = ContinuousLinearMap.id ℝ Y)
    (hE_inverse' : E.comp Einv = ContinuousLinearMap.id ℝ Y)
    (hD_selfadjoint : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y))
    (hE_selfadjoint : ∀ a b, inner ℝ (E a) b = inner ℝ a (E b))
    (hTinv_selfadjoint : ∀ x y, inner ℝ (Tinv x) y = inner ℝ x (Tinv y))
    (hSigmainv_selfadjoint : ∀ a b, inner ℝ (Sigmainv a) b = inner ℝ a (Sigmainv b))
    (hD_pos : ∀ x, x ≠ 0 → 0 < inner ℝ (D x) x)
    (hE_pos : ∀ a, a ≠ 0 → 0 < inner ℝ (E a) a)
    (h31 : ∃ b : ℝ, 0 < b ∧ ∀ y,
      b * ‖y‖ ^ 2 ≤ inner ℝ ((Sigmainv - (1 / 2 : ℝ) • E) y) y)
    (h32 : ∃ a : ℝ, 0 < a ∧ ∀ x,
      a * ‖x‖ ^ 2 ≤ inner ℝ ((Tinv - (1 / 2 : ℝ) • D) x) x)
    (h33 : ∃ (A₁sqrt A₁invsqrt : X →L[ℝ] X) (A₂sqrt A₂invsqrt : Y →L[ℝ] Y),
      A₁sqrt.comp A₁sqrt = Tinv - (1 / 2 : ℝ) • D ∧
      A₂sqrt.comp A₂sqrt = Sigmainv - (1 / 2 : ℝ) • E ∧
      A₁invsqrt.comp A₁sqrt = ContinuousLinearMap.id ℝ X ∧
      A₂invsqrt.comp A₂sqrt = ContinuousLinearMap.id ℝ Y ∧
      (∀ x y, inner ℝ (A₁sqrt x) y = inner ℝ x (A₁sqrt y)) ∧
      (∀ x y, inner ℝ (A₂sqrt x) y = inner ℝ x (A₂sqrt y)) ∧
      (∀ x y, inner ℝ (A₂invsqrt x) y = inner ℝ x (A₂invsqrt y)) ∧
      ‖A₂invsqrt.comp ((-p.K).comp A₁invsqrt)‖ < 1)
    (hgradQ_cocoercive : ∀ x x', inner ℝ (p.gradQ x - p.gradQ x') (x - x') ≥
      inner ℝ (Dinv (p.gradQ x - p.gradQ x')) (p.gradQ x - p.gradQ x'))
    (hgradPStar_cocoercive : ∀ y y', inner ℝ (p.gradPStar y - p.gradPStar y') (y - y') ≥
      inner ℝ (Einv (p.gradPStar y - p.gradPStar y')) (p.gradPStar y - p.gradPStar y'))
    (hα : ∀ k, 0 ≤ α k ∧ α k ≤ αbound) (hαbound : αbound < 1)
    (hmaxA : SetValuedOperator.IsMaximalMonotone (primalDualSetOperator p.G p.FStar p.K))
    (hmaxB : SetValuedOperator.IsMaximalMonotone
      (primalDualGradientOperator p.gradQ p.gradPStar).toSetValuedOperator)
    (S : Set (WithLp 2 (X × Y)))
    (hsolution : S = {z | ∃ a ∈ primalDualSetOperator p.G p.FStar p.K z,
      a + primalDualGradientOperator p.gradQ p.gradPStar z = 0})
    (hS_nonempty : S.Nonempty)
    (hS_saddle : ∀ z, z ∈ S →
      IsPrimalDualSolution p.G p.FStar p.gradQ p.gradPStar p.K z)
    (hsummable : Summable (fun k ↦ α k * inner ℝ
      (operatorPreconditioner Tinv Sigmainv p.K (WithLp.toLp 2
        ((it.x k, it.y k) - (it.x (k - 1), it.y (k - 1)))))
      (WithLp.toLp 2 ((it.x k, it.y k) - (it.x (k - 1), it.y (k - 1)))))) :
    ∃ z : WithLp 2 (X × Y),
      IsPrimalDualSolution p.G p.FStar p.gradQ p.gradPStar p.K z ∧
      Tendsto (fun k ↦ toWeakSpace ℝ (WithLp 2 (X × Y))
        (WithLp.toLp 2 (it.x k, it.y k))) Filter.atTop
        (nhds (toWeakSpace ℝ (WithLp 2 (X × Y)) z)) ∧
      -- the "Furthermore" clause: (34) with a nondecreasing `α` also gives convergence
      ((Monotone α ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ k,
        AlphaCondition34 p.K Tinv Sigmainv D E α ε k) →
        ∃ z' : WithLp 2 (X × Y),
          IsPrimalDualSolution p.G p.FStar p.gradQ p.gradPStar p.K z' ∧
          Tendsto (fun k ↦ toWeakSpace ℝ (WithLp 2 (X × Y))
            (WithLp.toLp 2 (it.x k, it.y k))) Filter.atTop
            (nhds (toWeakSpace ℝ (WithLp 2 (X × Y)) z'))) := by
  -- the product-space data of §3.2
  let Mpd : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) :=
    operatorPreconditioner Tinv Sigmainv p.K
  have hMpd_def : Mpd = operatorPreconditioner Tinv Sigmainv p.K := rfl
  let Lpd : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) := diagonalPreconditioner D E
  have hLpd_def : Lpd = diagonalPreconditioner D E := rfl
  let Linvpd : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) := diagonalPreconditioner Dinv Einv
  have hLinvpd_def : Linvpd = diagonalPreconditioner Dinv Einv := rfl
  let Bpd : WithLp 2 (X × Y) → WithLp 2 (X × Y) :=
    primalDualGradientOperator p.gradQ p.gradPStar
  have hBpd_def : Bpd = primalDualGradientOperator p.gradQ p.gradPStar := rfl
  let Apd : SetValuedOperator (WithLp 2 (X × Y)) (WithLp 2 (X × Y)) :=
    primalDualSetOperator p.G p.FStar p.K
  have hApd_def : Apd = primalDualSetOperator p.G p.FStar p.K := rfl
  -- the quadratic form of `S = M - ½C`
  have hS_inner : ∀ u : WithLp 2 (X × Y),
      inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u
        = inner ℝ ((Tinv - (1 / 2 : ℝ) • D) u.ofLp.1) u.ofLp.1
          - 2 * inner ℝ (p.K u.ofLp.1) u.ofLp.2
          + inner ℝ ((Sigmainv - (1 / 2 : ℝ) • E) u.ofLp.2) u.ofLp.2 := by
    intro u
    rw [hMpd_def, hLpd_def, ContinuousLinearMap.sub_apply, inner_sub_left,
      ContinuousLinearMap.smul_apply, real_inner_smul_left, operatorPreconditioner,
      blockOperator_inner, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
    ring
  -- (31) + (32) + (33) give positivity and coercivity of `S` (Lemma 8 in quantitative form)
  obtain ⟨A₁sqrt, A₁invsqrt, A₂sqrt, A₂invsqrt, hA₁sqrt, hA₂sqrt, hA₁invsqrt, hA₂invsqrt,
    hA₁sqrt_sa, hA₂sqrt_sa, hA₂invsqrt_sa, hbound⟩ := h33
  have hS_block : ∀ u : WithLp 2 (X × Y),
      inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u
        = inner ℝ ((Tinv - (1 / 2 : ℝ) • D) u.ofLp.1 + (-p.K).adjoint u.ofLp.2) u.ofLp.1
          + inner ℝ ((-p.K) u.ofLp.1 + (Sigmainv - (1 / 2 : ℝ) • E) u.ofLp.2) u.ofLp.2 := by
    intro u
    rw [hS_inner u]
    simp only [ContinuousLinearMap.neg_apply, inner_sub_left, inner_add_left,
      inner_neg_left, inner_neg_right, ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm]
    ring
  have hS_coercive : ∃ c : ℝ, 0 < c ∧ ∀ u : WithLp 2 (X × Y),
      c * ‖u‖ ^ 2 ≤ inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u := by
    obtain ⟨c, hc, hc'⟩ := block_operator_coercive_of_coercive_blocks
      (Tinv - (1 / 2 : ℝ) • D) (Sigmainv - (1 / 2 : ℝ) • E) (-p.K)
      A₁sqrt A₁invsqrt A₂sqrt A₂invsqrt hA₁sqrt hA₂sqrt hA₁invsqrt hA₂invsqrt
      hA₁sqrt_sa hA₂sqrt_sa hA₂invsqrt_sa h32 h31 hbound
    refine ⟨c, hc, fun u => ?_⟩
    rw [hS_block u]
    have hnorm : ‖u‖ ^ 2 = ‖u.ofLp.1‖ ^ 2 + ‖u.ofLp.2‖ ^ 2 := by
      simpa using WithLp.prod_norm_sq_eq_of_L2 u
    rw [hnorm]
    exact hc' u.ofLp
  have hL_positive_definite : ∀ u : WithLp 2 (X × Y), u ≠ 0 →
      0 < inner ℝ (Lpd u) u := by
    intro u hu
    rw [hLpd_def, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
    simp only [WithLp.ofLp_toLp]
    have h1 : 0 < inner ℝ (D u.ofLp.1) u.ofLp.1 + inner ℝ (E u.ofLp.2) u.ofLp.2 := by
      rcases eq_or_ne u.ofLp.1 0 with hx | hx
      · have hy : u.ofLp.2 ≠ 0 := by
          intro hy
          exact hu (by
            have hz : u.ofLp = 0 :=
              Prod.ext (by simpa using hx) (by simpa using hy)
            calc u = WithLp.toLp 2 u.ofLp := (WithLp.toLp_ofLp 2 u).symm
              _ = WithLp.toLp 2 (0 : X × Y) := by rw [hz]
              _ = 0 := WithLp.toLp_zero 2)
        rw [hx]
        simp only [map_zero, inner_zero_left, zero_add]
        exact hE_pos _ hy
      · have := hD_pos _ hx
        have hEnonneg : 0 ≤ inner ℝ (E u.ofLp.2) u.ofLp.2 := by
          rcases eq_or_ne u.ofLp.2 0 with hy | hy
          · rw [hy]; simp
          · exact (hE_pos _ hy).le
        linarith
    simpa using h1
  have hL_selfadjoint : ∀ u v : WithLp 2 (X × Y),
      inner ℝ (Lpd u) v = inner ℝ u (Lpd v) := by
    intro u v
    rw [hLpd_def]
    exact blockOperator_inner_comm D E 0 hD_selfadjoint hE_selfadjoint u v
  have hLcomp : Lpd.comp Linvpd = ContinuousLinearMap.id ℝ (WithLp 2 (X × Y)) := by
    ext u
    rw [hLpd_def, hLinvpd_def, ContinuousLinearMap.comp_apply, diagonalPreconditioner_apply,
      diagonalPreconditioner_apply, ContinuousLinearMap.id_apply]
    have h1 : D (Dinv u.ofLp.1) = u.ofLp.1 := by
      have h := congrArg (fun L : X →L[ℝ] X => L u.ofLp.1) hD_inverse'
      simpa [ContinuousLinearMap.comp_apply] using h
    have h2 : E (Einv u.ofLp.2) = u.ofLp.2 := by
      have h := congrArg (fun L : Y →L[ℝ] Y => L u.ofLp.2) hE_inverse'
      simpa [ContinuousLinearMap.comp_apply] using h
    rw [h1, h2, WithLp.toLp_ofLp]
  have hLinv : Linvpd.comp Lpd = ContinuousLinearMap.id ℝ (WithLp 2 (X × Y)) := by
    ext u
    rw [hLpd_def, hLinvpd_def, ContinuousLinearMap.comp_apply, diagonalPreconditioner_apply,
      diagonalPreconditioner_apply, ContinuousLinearMap.id_apply]
    have h1 : Dinv (D u.ofLp.1) = u.ofLp.1 := by
      have h := congrArg (fun L : X →L[ℝ] X => L u.ofLp.1) hD_inverse
      simpa [ContinuousLinearMap.comp_apply] using h
    have h2 : Einv (E u.ofLp.2) = u.ofLp.2 := by
      have h := congrArg (fun L : Y →L[ℝ] Y => L u.ofLp.2) hE_inverse
      simpa [ContinuousLinearMap.comp_apply] using h
    rw [h1, h2, WithLp.toLp_ofLp]
  have hLnonneg : ∀ u : WithLp 2 (X × Y), 0 ≤ inner ℝ (Lpd u) u := by
    intro u
    rw [hLpd_def, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
    simp only [WithLp.ofLp_toLp]
    have h1 : 0 ≤ inner ℝ (D u.ofLp.1) u.ofLp.1 := by
      rcases eq_or_ne u.ofLp.1 0 with hx | hx
      · rw [hx]; simp
      · exact (hD_pos _ hx).le
    have h2 : 0 ≤ inner ℝ (E u.ofLp.2) u.ofLp.2 := by
      rcases eq_or_ne u.ofLp.2 0 with hy | hy
      · rw [hy]; simp
      · exact (hE_pos _ hy).le
    linarith
  have hM_selfadjoint : ∀ u v : WithLp 2 (X × Y),
      inner ℝ (Mpd u) v = inner ℝ u (Mpd v) := by
    intro u v
    rw [hMpd_def]
    exact blockOperator_inner_comm Tinv Sigmainv p.K hTinv_selfadjoint hSigmainv_selfadjoint u v
  have hM_coercive : ∃ cM : ℝ, 0 < cM ∧ ∀ u : WithLp 2 (X × Y),
      cM * ‖u‖ ^ 2 ≤ inner ℝ (Mpd u) u := by
    obtain ⟨c, hc, hcS'⟩ := hS_coercive
    refine ⟨c, hc, fun u => ?_⟩
    have hdecomp : inner ℝ (Mpd u) u =
        inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u + (1 / 2 : ℝ) * inner ℝ (Lpd u) u := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left, ContinuousLinearMap.smul_apply,
        real_inner_smul_left]
      ring
    rw [hdecomp]
    linarith [hcS' u, hLnonneg u]
  have hmetric : ∀ u : WithLp 2 (X × Y), u ≠ 0 →
      0 < inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u := by
    intro u hu
    obtain ⟨c, hc, hcS'⟩ := hS_coercive
    have h1 : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    nlinarith [hcS' u]
  have hM_posdef : ∀ u : WithLp 2 (X × Y), u ≠ 0 → 0 < inner ℝ (Mpd u) u := by
    intro u hu
    obtain ⟨c, hc, hcS'⟩ := hS_coercive
    have h1 : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hdecomp : inner ℝ (Mpd u) u =
        inner ℝ ((Mpd - (1 / 2 : ℝ) • Lpd) u) u + (1 / 2 : ℝ) * inner ℝ (Lpd u) u := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left, ContinuousLinearMap.smul_apply,
        real_inner_smul_left]
      ring
    rw [hdecomp]
    nlinarith [hcS' u, hLnonneg u]
  -- co-coercivity of `(∇Q, ∇P^*)` with respect to `C⁻¹ = diag(D⁻¹, E⁻¹)`
  have hBpd_sub : ∀ u v : WithLp 2 (X × Y),
      Bpd u - Bpd v = WithLp.toLp 2 (p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1,
        p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2) := by
    intro u v
    rw [hBpd_def]
    apply WithLp.ofLp_injective
    simp
  have hLinvpd_inner : ∀ w : WithLp 2 (X × Y),
      inner ℝ (Linvpd w) w = inner ℝ (Dinv w.ofLp.1) w.ofLp.1
        + inner ℝ (Einv w.ofLp.2) w.ofLp.2 := by
    intro w
    rw [hLinvpd_def, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
  have hcocoercive : IsCocoerciveWithInverseMetric Bpd Linvpd S := by
    intro u v _
    rw [hBpd_sub u v, hLinvpd_inner, WithLp.prod_inner_apply]
    simp only [WithLp.ofLp_toLp, WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub]
    have h1 := hgradQ_cocoercive u.ofLp.1 v.ofLp.1
    have h2 := hgradPStar_cocoercive u.ofLp.2 v.ofLp.2
    linarith
  -- Lipschitz bound for `(∇Q, ∇P^*)`, from the Lipschitz gradients recorded in `def_2`
  have hB_lipschitz : ∃ cB : ℝ, 0 < cB ∧ ∀ u v : WithLp 2 (X × Y),
      ‖Bpd u - Bpd v‖ ≤ cB * ‖u - v‖ := by
    -- the Lipschitz constants recorded in `def_2` are nonnegative in content: a negative
    -- constant forces the gradient to be constant, for which any positive constant works
    have hgrad (c : ℝ) (hc : ∀ x y : X, ‖p.gradQ x - p.gradQ y‖ ≤ c * ‖x - y‖) :
        ∀ x y : X, ‖p.gradQ x - p.gradQ y‖ ≤ (max c 0 + 1) * ‖x - y‖ := by
      intro x y
      rcases le_or_gt c 0 with h | h
      · have hzero : ‖p.gradQ x - p.gradQ y‖ ≤ 0 :=
          le_trans (hc x y) (mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg _))
        nlinarith [norm_nonneg (x - y), le_max_right c 0]
      · exact le_trans (hc x y)
          (mul_le_mul_of_nonneg_right (by linarith [le_max_left c 0]) (norm_nonneg _))
    have hgradP (c : ℝ) (hc : ∀ y z : Y, ‖p.gradPStar y - p.gradPStar z‖ ≤ c * ‖y - z‖) :
        ∀ y z : Y, ‖p.gradPStar y - p.gradPStar z‖ ≤ (max c 0 + 1) * ‖y - z‖ := by
      intro y z
      rcases le_or_gt c 0 with h | h
      · have hzero : ‖p.gradPStar y - p.gradPStar z‖ ≤ 0 :=
          le_trans (hc y z) (mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg _))
        nlinarith [norm_nonneg (y - z), le_max_right c 0]
      · exact le_trans (hc y z)
          (mul_le_mul_of_nonneg_right (by linarith [le_max_left c 0]) (norm_nonneg _))
    set cB : ℝ := max (max p.LQ 0 + 1) (max p.LP 0 + 1) with hcB
    have hcB_pos : 0 < cB := by
      rw [hcB]
      have h0 : (0 : ℝ) < max p.LQ 0 + 1 := by
        have : (0 : ℝ) ≤ max p.LQ 0 := le_max_right _ _
        linarith
      exact lt_of_lt_of_le h0 (le_max_left _ _)
    refine ⟨cB, hcB_pos, fun u v => ?_⟩
    rw [hBpd_sub u v]
    have hq := hgrad p.LQ p.gradQ_lipschitz u.ofLp.1 v.ofLp.1
    have hp := hgradP p.LP p.gradPStar_lipschitz u.ofLp.2 v.ofLp.2
    have h1 : ‖p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1‖ ≤ cB * ‖u.ofLp.1 - v.ofLp.1‖ :=
      le_trans hq (mul_le_mul_of_nonneg_right (by rw [hcB]; linarith [le_max_left (max p.LQ 0 + 1) (max p.LP 0 + 1)])
        (norm_nonneg _))
    have h2 : ‖p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2‖ ≤ cB * ‖u.ofLp.2 - v.ofLp.2‖ :=
      le_trans hp (mul_le_mul_of_nonneg_right (by rw [hcB]; linarith [le_max_right (max p.LQ 0 + 1) (max p.LP 0 + 1)])
        (norm_nonneg _))
    have hnorm : ‖WithLp.toLp 2 (p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1,
        p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2)‖ ^ 2 =
        ‖p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1‖ ^ 2 +
          ‖p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp
    have hsub : ‖u - v‖ ^ 2 = ‖u.ofLp.1 - v.ofLp.1‖ ^ 2 + ‖u.ofLp.2 - v.ofLp.2‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2 (u - v)]
      simp
    have hsq : ‖WithLp.toLp 2 (p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1,
        p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2)‖ ^ 2 ≤ (cB * ‖u - v‖) ^ 2 := by
      rw [hnorm, mul_pow, hsub]
      have hq' : ‖p.gradQ u.ofLp.1 - p.gradQ v.ofLp.1‖ ^ 2 ≤
          cB ^ 2 * ‖u.ofLp.1 - v.ofLp.1‖ ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      have hp' : ‖p.gradPStar u.ofLp.2 - p.gradPStar v.ofLp.2‖ ^ 2 ≤
          cB ^ 2 * ‖u.ofLp.2 - v.ofLp.2‖ ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) h2 2
      nlinarith [hq', hp']
    have hc_nonneg : 0 ≤ cB * ‖u - v‖ := mul_nonneg hcB_pos.le (norm_nonneg _)
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hc_nonneg] at this
  -- (30) is an instance of the general scheme (10) with `λ_k ≡ 1`
  have hitFB_apart : ∀ k, WithLp.toLp 2 (it.ξ k, it.ζ k) =
      WithLp.toLp 2 (it.x k, it.y k) + α k •
        (WithLp.toLp 2 (it.x k, it.y k) -
          WithLp.toLp 2 (it.x (k - 1), it.y (k - 1))) := by
    intro k
    rw [it.extrapolate_primal k, it.extrapolate_dual k]
    apply WithLp.ofLp_injective
    ext <;> simp [smul_sub]
  have hitFB_sub : ∀ k, WithLp.toLp 2 (it.ξ k, it.ζ k) -
      WithLp.toLp 2 (it.x (k + 1), it.y (k + 1)) =
      WithLp.toLp 2 (it.ξ k - it.x (k + 1), it.ζ k - it.y (k + 1)) := by
    intro k
    apply WithLp.ofLp_injective
    simp
  let itFB : InertialForwardBackwardIteration (WithLp 2 (X × Y)) Apd Bpd Mpd α (fun _ ↦ 1) :=
    { x := fun k ↦ WithLp.toLp 2 (it.x k, it.y k)
      y := fun k ↦ WithLp.toLp 2 (it.ξ k, it.ζ k)
      inertia_range := fun k ↦ ⟨(hα k).1, lt_of_le_of_lt (hα k).2 hαbound⟩
      metric_self_adjoint := hM_selfadjoint
      metric_positive_definite := hM_posdef
      inertial := hitFB_apart
      forward_backward := fun k ↦ by
        obtain ⟨g, hg, hg_eq⟩ := it.primal_update k
        obtain ⟨f, hf, hf_eq⟩ := it.dual_update k
        have hbar : it.barξ (k + 1) = 2 • it.x (k + 1) - it.ξ k := it.reflected_primal k
        -- rescale the two steps of (30) by `T⁻¹` and `Σ⁻¹`
        have hgT : Tinv (it.ξ k - it.x (k + 1)) - p.gradQ (it.ξ k) -
            p.K.adjoint (it.ζ k) = g := by
          have h1 : it.ξ k - T (p.gradQ (it.ξ k) + p.K.adjoint (it.ζ k)) -
              it.x (k + 1) = T g := by
            rw [hg_eq]
            abel
          have hTw : ∀ w : X, Tinv (T w) = w := fun w => by
            have h := congrArg (fun L : X →L[ℝ] X => L w) hT_inverse
            simpa [ContinuousLinearMap.comp_apply] using h
          have h2 := congrArg (fun w : X ↦ Tinv w) h1
          dsimp only at h2
          rw [map_sub, map_sub] at h2
          simp only [hTw] at h2
          rw [← h2, map_sub]
          abel
        have hfS : Sigmainv (it.ζ k - it.y (k + 1)) - p.gradPStar (it.ζ k) +
            p.K (2 • it.x (k + 1) - it.ξ k) = f := by
          have h1 : it.ζ k - Sigma (p.gradPStar (it.ζ k) - p.K (it.barξ (k + 1))) -
              it.y (k + 1) = Sigma f := by
            rw [hf_eq]
            abel
          have hSw : ∀ w : Y, Sigmainv (Sigma w) = w := fun w => by
            have h := congrArg (fun L : Y →L[ℝ] Y => L w) hSigma_inverse
            simpa [ContinuousLinearMap.comp_apply] using h
          have h2 := congrArg (fun w : Y ↦ Sigmainv w) h1
          dsimp only at h2
          rw [map_sub, map_sub] at h2
          simp only [hSw] at h2
          rw [hbar] at h2
          rw [← h2, map_sub]
          abel
        refine ⟨WithLp.toLp 2 (g + p.K.adjoint (it.y (k + 1)),
          f - p.K (it.x (k + 1))), ?_, ?_⟩
        · rw [mem_primalDualSetOperator]
          constructor
          · simpa using hg
          · simpa using hf
        · apply WithLp.ofLp_injective
          ext
          · have hval : (Mpd (WithLp.toLp 2 (it.ξ k, it.ζ k) -
                WithLp.toLp 2 (it.x (k + 1), it.y (k + 1))) -
                (1 : ℝ) • Bpd (WithLp.toLp 2 (it.ξ k, it.ζ k))).ofLp.1
                = Tinv (it.ξ k - it.x (k + 1)) -
                    p.K.adjoint (it.ζ k - it.y (k + 1)) - p.gradQ (it.ξ k) := by
              rw [hitFB_sub k, hMpd_def, hBpd_def]
              simp [operatorPreconditioner_apply, primalDualGradientOperator,
                WithLp.ofLp_sub, WithLp.ofLp_smul, one_smul]
            rw [hval]
            have hsplit : Tinv (it.ξ k - it.x (k + 1)) -
                p.K.adjoint (it.ζ k - it.y (k + 1)) - p.gradQ (it.ξ k) =
                (Tinv (it.ξ k - it.x (k + 1)) - p.gradQ (it.ξ k) -
                  p.K.adjoint (it.ζ k)) + p.K.adjoint (it.y (k + 1)) := by
              rw [map_sub (f := p.K.adjoint) (it.ζ k) (it.y (k + 1))]
              abel
            rw [hsplit, hgT]
            simp
          · have hval : (Mpd (WithLp.toLp 2 (it.ξ k, it.ζ k) -
                WithLp.toLp 2 (it.x (k + 1), it.y (k + 1))) -
                (1 : ℝ) • Bpd (WithLp.toLp 2 (it.ξ k, it.ζ k))).ofLp.2
                = -p.K (it.ξ k - it.x (k + 1)) +
                    Sigmainv (it.ζ k - it.y (k + 1)) - p.gradPStar (it.ζ k) := by
              rw [hitFB_sub k, hMpd_def, hBpd_def]
              simp [operatorPreconditioner_apply, primalDualGradientOperator,
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
                Sigmainv (it.ζ k - it.y (k + 1)) - p.gradPStar (it.ζ k) =
                (Sigmainv (it.ζ k - it.y (k + 1)) - p.gradPStar (it.ζ k) +
                    p.K (2 • it.x (k + 1) - it.ξ k)) - p.K (it.x (k + 1)) := by
              rw [hK₁, hK₂]
              module
            rw [hsplit, hfS]
            simp }
  have hitFB_x : ∀ k, itFB.x k = WithLp.toLp 2 (it.x k, it.y k) := fun k => rfl
  have hitFB_y : ∀ k, itFB.y k = WithLp.toLp 2 (it.ξ k, it.ζ k) := fun k => rfl
  have hsumFB : Summable (fun k ↦ α k *
      inner ℝ (Mpd (itFB.x k - itFB.x (k - 1))) (itFB.x k - itFB.x (k - 1))) := by
    refine hsummable.congr (fun k ↦ ?_)
    have hsub : itFB.x k - itFB.x (k - 1) = WithLp.toLp 2
        ((it.x k, it.y k) - (it.x (k - 1), it.y (k - 1))) := by
      rw [hitFB_x k, hitFB_x (k - 1)]
      apply WithLp.ofLp_injective
      simp
    simp only [hMpd_def, hsub]
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
  -- the "Furthermore" clause of Theorem 9: (34) implies (17), and Theorem 2 applies
  rintro ⟨hα_mono, ⟨ε, hε_pos, h34⟩⟩
  have hR : ∃ ε' : ℝ, 0 < ε' ∧ ∀ k (u : WithLp 2 (X × Y)), 0 ≤ inner ℝ
      ((((1 - 3 * α k) • Mpd) - (((1 - α k) ^ 2 * (1 : ℝ) / 2) • Lpd) - ε' • Mpd) u) u := by
    refine ⟨ε, hε_pos, fun k u => ?_⟩
    obtain ⟨hc_pos, -, -, A₁ksqrt, A₁kinvsqrt, A₂ksqrt, A₂kinvsqrt, hA₁ksa, hA₂ksa,
      hA₂kinvsa, hA₁ksq, hA₂ksq, hA₁kinv, hA₂kinv, hbound⟩ := h34 k
    -- the quadratic form of `R_k - ε M`, in terms of the shifted blocks
    have hform : inner ℝ ((((1 - 3 * α k) • Mpd) -
        (((1 - α k) ^ 2 * (1 : ℝ) / 2) • Lpd) - ε • Mpd) u) u
        = inner ℝ (((1 - 3 * α k - ε) • Tinv - ((1 - α k) ^ 2 / 2) • D) u.ofLp.1) u.ofLp.1
          - 2 * (1 - 3 * α k - ε) * inner ℝ (p.K u.ofLp.1) u.ofLp.2
          + inner ℝ (((1 - 3 * α k - ε) • Sigmainv - ((1 - α k) ^ 2 / 2) • E) u.ofLp.2)
              u.ofLp.2 := by
      have h1 : inner ℝ (Mpd u) u = inner ℝ (Tinv u.ofLp.1) u.ofLp.1
          - 2 * inner ℝ (p.K u.ofLp.1) u.ofLp.2
          + inner ℝ (Sigmainv u.ofLp.2) u.ofLp.2 := by
        rw [hMpd_def, operatorPreconditioner, blockOperator_inner]
      have h2 : inner ℝ (Lpd u) u = inner ℝ (D u.ofLp.1) u.ofLp.1
          + inner ℝ (E u.ofLp.2) u.ofLp.2 := by
        rw [hLpd_def, diagonalPreconditioner_apply, WithLp.prod_inner_apply]
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, inner_sub_left, inner_sub_left,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, h1, h2]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    rw [hform]
    -- the cross term, through the square-root factorisation
    have hcross := block_operator_cross_term p.K A₁ksqrt A₁kinvsqrt A₂ksqrt A₂kinvsqrt
      hA₁kinv hA₂kinv hA₂kinvsa u.ofLp.1 u.ofLp.2
    have hP : inner ℝ (((1 - 3 * α k - ε) • Tinv - ((1 - α k) ^ 2 / 2) • D) u.ofLp.1)
        u.ofLp.1 = ‖A₁ksqrt u.ofLp.1‖ ^ 2 := by
      rw [← hA₁ksq]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hA₁ksa]
      exact real_inner_self_eq_norm_sq _
    have hQ : inner ℝ (((1 - 3 * α k - ε) • Sigmainv - ((1 - α k) ^ 2 / 2) • E) u.ofLp.2)
        u.ofLp.2 = ‖A₂ksqrt u.ofLp.2‖ ^ 2 := by
      rw [← hA₂ksq]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hA₂ksa]
      exact real_inner_self_eq_norm_sq _
    -- the scaled cross term is bounded by the product of the two block forms
    have hscaled : ((1 - 3 * α k - ε) * inner ℝ (p.K u.ofLp.1) u.ofLp.2) ^ 2 ≤
        ‖A₁ksqrt u.ofLp.1‖ ^ 2 * ‖A₂ksqrt u.ofLp.2‖ ^ 2 := by
      have hT : ‖A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)‖ * (1 - 3 * α k - ε) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right hbound hc_pos.le
        rwa [div_mul_cancel₀ _ (ne_of_gt hc_pos)] at h
      have hx : (1 - 3 * α k - ε) * inner ℝ (p.K u.ofLp.1) u.ofLp.2
          = inner ℝ ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)) (A₁ksqrt u.ofLp.1))
              (A₂ksqrt u.ofLp.2) * (1 - 3 * α k - ε) := by
        rw [hcross]
        ring
      have h3 : |inner ℝ ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)) (A₁ksqrt u.ofLp.1))
            (A₂ksqrt u.ofLp.2) * (1 - 3 * α k - ε)| ≤
          ‖A₁ksqrt u.ofLp.1‖ * ‖A₂ksqrt u.ofLp.2‖ := by
        have h1 : |inner ℝ ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)) (A₁ksqrt u.ofLp.1))
            (A₂ksqrt u.ofLp.2)| ≤
            ‖A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)‖ * ‖A₁ksqrt u.ofLp.1‖ *
              ‖A₂ksqrt u.ofLp.2‖ := by
          have hb := (A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)).le_opNorm (A₁ksqrt u.ofLp.1)
          have hupper : inner ℝ ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)) (A₁ksqrt u.ofLp.1))
              (A₂ksqrt u.ofLp.2) ≤
              ‖A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)‖ * ‖A₁ksqrt u.ofLp.1‖ *
                ‖A₂ksqrt u.ofLp.2‖ := by
            have ha := real_inner_le_norm ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt))
              (A₁ksqrt u.ofLp.1)) (A₂ksqrt u.ofLp.2)
            nlinarith [norm_nonneg (A₁ksqrt u.ofLp.1), norm_nonneg (A₂ksqrt u.ofLp.2)]
          have hlower : -(‖A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)‖ * ‖A₁ksqrt u.ofLp.1‖ *
                ‖A₂ksqrt u.ofLp.2‖) ≤
              inner ℝ ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)) (A₁ksqrt u.ofLp.1))
                (A₂ksqrt u.ofLp.2) := by
            have ha := real_inner_le_norm (-((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt))
              (A₁ksqrt u.ofLp.1))) (A₂ksqrt u.ofLp.2)
            rw [inner_neg_left, norm_neg] at ha
            nlinarith [norm_nonneg (A₁ksqrt u.ofLp.1), norm_nonneg (A₂ksqrt u.ofLp.2)]
          rw [abs_le]
          exact ⟨hlower, hupper⟩
        rw [abs_mul, abs_of_nonneg hc_pos.le]
        calc |inner ℝ ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)) (A₁ksqrt u.ofLp.1))
              (A₂ksqrt u.ofLp.2)| * (1 - 3 * α k - ε)
            ≤ (‖A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)‖ * ‖A₁ksqrt u.ofLp.1‖ *
                ‖A₂ksqrt u.ofLp.2‖) * (1 - 3 * α k - ε) :=
              mul_le_mul_of_nonneg_right h1 hc_pos.le
          _ = (‖A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)‖ * (1 - 3 * α k - ε)) *
                (‖A₁ksqrt u.ofLp.1‖ * ‖A₂ksqrt u.ofLp.2‖) := by ring
          _ ≤ 1 * (‖A₁ksqrt u.ofLp.1‖ * ‖A₂ksqrt u.ofLp.2‖) :=
              mul_le_mul_of_nonneg_right hT (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = ‖A₁ksqrt u.ofLp.1‖ * ‖A₂ksqrt u.ofLp.2‖ := by ring
      rw [hx, mul_pow]
      calc (inner ℝ ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)) (A₁ksqrt u.ofLp.1))
              (A₂ksqrt u.ofLp.2)) ^ 2 * (1 - 3 * α k - ε) ^ 2
          = (inner ℝ ((A₂kinvsqrt.comp (p.K.comp A₁kinvsqrt)) (A₁ksqrt u.ofLp.1))
              (A₂ksqrt u.ofLp.2) * (1 - 3 * α k - ε)) ^ 2 := by ring
        _ ≤ (‖A₁ksqrt u.ofLp.1‖ * ‖A₂ksqrt u.ofLp.2‖) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = ‖A₁ksqrt u.ofLp.1‖ ^ 2 * ‖A₂ksqrt u.ofLp.2‖ ^ 2 := by ring
    rw [hP, hQ] at *
    exact schur_nonneg (sq_nonneg _) (sq_nonneg _) hscaled
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
