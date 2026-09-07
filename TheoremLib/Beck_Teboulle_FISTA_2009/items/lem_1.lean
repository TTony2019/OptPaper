import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_3

open Set
open scoped RealInnerProductSpace

/-- Lemma 2.1 (Descent Lemma): Quadratic upper bound for `C^{1,1}` functions.

Let `f : ℝⁿ → ℝ` be continuously differentiable with Lipschitz continuous gradient
and Lipschitz constant `L(f)`. Then for any `L ≥ L(f)`,
`f(x) ≤ f(y) + ⟨∇f(y), x - y⟩ + (L/2)‖x - y‖²` for every `x, y ∈ ℝⁿ`.

This is a well-known and fundamental property for smooth functions in the class `C^{1,1}`;
see, e.g., Ortega & Rheinboldt (2000), Bertsekas (1999). -/
theorem quadratic_upper_bound_C11 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hf : IsC11 f Lf) {L : ℝ} (hL : Lf ≤ L)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x ≤ f y + ⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2 := by
  have hLf_pos : 0 < Lf := hf.hL_pos
  -- Line segment and auxiliary functions
  let φ := fun (t : ℝ) => y + t • (x - y)
  let h := fun (t : ℝ) => f (φ t)
  let g := fun (t : ℝ) => h t - h 0 - t * ⟪gradient f y, x - y⟫ - (Lf / 2) * (t ^ 2) * ‖x - y‖ ^ 2
  have hg0 : g 0 = 0 := by dsimp [g, h, φ]; simp
  -- Derivative of h at any t₀ via HasLineDerivAt + HasDerivAt.comp_add_const
  have h_deriv (t₀ : ℝ) : HasDerivAt h (⟪gradient f (φ t₀), x - y⟫) t₀ := by
    have h_diff_f : Differentiable ℝ f := by
      apply hf.contDiff.differentiable; decide
    have h_diffAt : DifferentiableAt ℝ f (φ t₀) := h_diff_f.differentiableAt
    -- HasLineDerivAt gives derivative at 0 of s ↦ f(φ(t₀) + s•(x-y)) = f(φ(t₀+s))
    have h_line_raw : HasLineDerivAt ℝ f
        (lineDeriv ℝ f (φ t₀) (x - y)) (φ t₀) (x - y) :=
      h_diffAt.lineDifferentiableAt.hasLineDerivAt
    have h_line_val : lineDeriv ℝ f (φ t₀) (x - y) = ⟪gradient f (φ t₀), x - y⟫ := by
      rw [h_diffAt.lineDeriv_eq_fderiv, inner_gradient_left h_diffAt]
    dsimp [HasLineDerivAt] at h_line_raw
    rw [h_line_val] at h_line_raw
    -- h_line_raw : HasDerivAt (λ s => f(φ t₀ + s•(x-y))) ⟨...⟩ 0
    -- Note: φ(t₀) + s•(x-y) = y + t₀•(x-y) + s•(x-y) = φ(t₀+s)
    have h_shift_eq : (fun (s : ℝ) => f (φ t₀ + s • (x - y))) =
        (fun (s : ℝ) => h (t₀ + s)) := by
      ext s; dsimp [h, φ]; simp [add_smul, add_assoc]
    rw [h_shift_eq] at h_line_raw
    -- h_line_raw : HasDerivAt (λ s => h(t₀ + s)) f' 0
    -- Shift: HasDerivAt.comp_add_const t₀ (-t₀) h_line_raw
    --   : HasDerivAt (λ s => h(t₀ + (s + (-t₀)))) f' t₀ = HasDerivAt h f' t₀
    have h_shift_back := HasDerivAt.comp_add_const t₀ (-t₀)
      (by simpa [add_neg_cancel] using h_line_raw)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h_shift_back
  -- Derivative of g: g'(t) = h'(t) - 0 - ⟨∇f(y), x-y⟩ - Lf·t·‖x-y‖²
  have hg_deriv (t : ℝ) : HasDerivAt g
      (⟪gradient f (φ t) - gradient f y, x - y⟫ - Lf * t * ‖x - y‖ ^ 2) t := by
    have h1 : HasDerivAt h (⟪gradient f (φ t), x - y⟫) t := h_deriv t
    have h2 : HasDerivAt (fun (_ : ℝ) => h 0) 0 t := hasDerivAt_const _ _
    have h3 : HasDerivAt (fun (s : ℝ) => s * ⟪gradient f y, x - y⟫)
        (⟪gradient f y, x - y⟫) t :=
      hasDerivAt_mul_const (⟪gradient f y, x - y⟫)
    have h4 : HasDerivAt (fun (s : ℝ) => (Lf / 2) * (s ^ 2) * ‖x - y‖ ^ 2)
        (Lf * t * ‖x - y‖ ^ 2) t := by
      have h_sq : HasDerivAt (fun (s : ℝ) => s ^ 2) (2 * t) t := by
        have := hasDerivAt_pow 2 t
        simpa [Nat.cast_ofNat] using this
      set C := (Lf / 2) * ‖x - y‖ ^ 2 with hC
      have h_mul : HasDerivAt (fun (s : ℝ) => C * (s ^ 2)) (C * (2 * t)) t :=
        HasDerivAt.const_mul C h_sq
      have h_simp_deriv : C * (2 * t) = Lf * t * ‖x - y‖ ^ 2 := by
        dsimp [C]; ring
      have h_simp_fun : (fun (s : ℝ) => C * (s ^ 2)) = (fun (s : ℝ) => (Lf / 2) * (s ^ 2) * ‖x - y‖ ^ 2) := by
        ext s; dsimp [C]; ring
      simpa [h_simp_deriv, h_simp_fun] using h_mul
    have h_combined : HasDerivAt (fun (s : ℝ) =>
        h s - h 0 - s * ⟪gradient f y, x - y⟫ - (Lf / 2) * (s ^ 2) * ‖x - y‖ ^ 2)
        (⟪gradient f (φ t), x - y⟫ - 0 - ⟪gradient f y, x - y⟫ - Lf * t * ‖x - y‖ ^ 2) t :=
      ((h1.sub h2).sub h3).sub h4
    simpa [g, sub_sub, inner_sub_left] using h_combined
  -- g is differentiable everywhere → continuous + differentiable on intervals
  have hg_diff (t : ℝ) : DifferentiableAt ℝ g t := (hg_deriv t).differentiableAt
  have hg_cont : Continuous g :=
    continuous_iff_continuousAt.mpr (λ t => (hg_diff t).continuousAt)
  have hg_contOn : ContinuousOn g (Icc (0 : ℝ) 1) := hg_cont.continuousOn
  have hg_diffOn : DifferentiableOn ℝ g (Ioo (0 : ℝ) 1) :=
    fun x hx => (hg_diff x).differentiableWithinAt
  -- g'(t) ≤ 0 for t > 0 (Cauchy-Schwarz + Lipschitz gradient)
  have h_deriv_nonpos {t : ℝ} (ht : 0 < t) :
      ⟪gradient f (φ t) - gradient f y, x - y⟫ - Lf * t * ‖x - y‖ ^ 2 ≤ 0 := by
    have h_cauchy : ⟪gradient f (φ t) - gradient f y, x - y⟫ ≤
        ‖gradient f (φ t) - gradient f y‖ * ‖x - y‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradient f (φ t) - gradient f y‖ ≤ Lf * ‖φ t - y‖ := by
      have hlip := hf.grad_lipschitz.norm_sub_le (φ t) y
      have hLf_nn : (Real.toNNReal Lf : ℝ) = Lf := Real.coe_toNNReal Lf (by linarith)
      simpa [hLf_nn] using hlip
    have h_norm_φ : ‖φ t - y‖ = t * ‖x - y‖ := by
      dsimp [φ]; simp [norm_smul, abs_of_pos ht]
    have h_inner_bound : ⟪gradient f (φ t) - gradient f y, x - y⟫ ≤ Lf * t * ‖x - y‖ ^ 2 := by
      calc
        ⟪gradient f (φ t) - gradient f y, x - y⟫ ≤
            ‖gradient f (φ t) - gradient f y‖ * ‖x - y‖ := h_cauchy
        _ ≤ (Lf * ‖φ t - y‖) * ‖x - y‖ := by
          nlinarith [h_lip, norm_nonneg (x - y)]
        _ = (Lf * (t * ‖x - y‖)) * ‖x - y‖ := by rw [h_norm_φ]
        _ = Lf * t * ‖x - y‖ ^ 2 := by ring
    linarith
  -- Mean Value Theorem on [0,1]:
  -- ∃ c ∈ (0,1) : deriv g c = (g(1) - g(0))/(1-0) = g(1) - g(0)
  have h_mvt : ∃ c ∈ Ioo (0 : ℝ) 1, deriv g c = (g 1 - g 0) / (1 - 0) :=
    exists_deriv_eq_slope g (by norm_num : (0 : ℝ) < 1) hg_contOn hg_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have hc_pos : 0 < c := hc.1
  -- deriv g c equals the HasDerivAt formula (g is differentiable at c)
  have h_deriv_c : deriv g c = ⟪gradient f (φ c) - gradient f y, x - y⟫ - Lf * c * ‖x - y‖ ^ 2 :=
    (hg_deriv c).deriv
  -- Since c > 0, g'(c) ≤ 0
  have h_deriv_c_nonpos : deriv g c ≤ 0 := by
    rw [h_deriv_c]; exact h_deriv_nonpos hc_pos
  -- From MVT: deriv g c = (g(1) - g(0))/(1-0) = g(1) - g(0), with g(0) = 0
  have h_denom : (1 : ℝ) - 0 = 1 := by norm_num
  rw [h_denom, div_one, hg0, sub_zero] at hc_eq
  -- hc_eq : deriv g c = g(1), and deriv g c ≤ 0, so g(1) ≤ 0
  have hg1_nonpos : g 1 ≤ 0 := by linarith
  -- Expand g(1) ≤ 0 to get the descent inequality
  dsimp [g, h, φ] at hg1_nonpos
  have h_simp1 : (1 : ℝ) • (x - y) = x - y := by simp
  rw [h_simp1] at hg1_nonpos
  have h_simp2 : y + (x - y) = x := by abel
  rw [h_simp2] at hg1_nonpos
  have h_simp3 : f (y + (0 : ℝ) • (x - y)) = f y := by simp
  rw [h_simp3] at hg1_nonpos
  -- hg1_nonpos : f x - f y - ⟪∇f y, x - y⟫ - (Lf/2)*‖x-y‖² ≤ 0
  -- → f x ≤ f y + ⟪∇f y, x - y⟫ + (Lf/2)*‖x-y‖²
  have h_bound_lf : f x ≤ f y + ⟪gradient f y, x - y⟫ + (Lf / 2) * ‖x - y‖ ^ 2 := by
    linarith
  -- Upgrade from Lf to L (‖x-y‖² ≥ 0 and Lf ≤ L)
  have h_L : Lf / 2 * ‖x - y‖ ^ 2 ≤ L / 2 * ‖x - y‖ ^ 2 := by
    have h_sq_nonneg : 0 ≤ ‖x - y‖ ^ 2 := pow_two_nonneg _
    nlinarith
  linarith