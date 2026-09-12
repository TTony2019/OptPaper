import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.algo_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_lem_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_thm_1

namespace BotCsetnek2015

noncomputable def M1Value (sigma Lh lambdaUpper alpha lambdaLower nu mu : Real) : Real :=
  sigma / (2 * lambdaUpper) - Lh - nu - (alpha / lambdaLower) * mu

noncomputable def M2Value (Lh Lu lambdaUpper alpha lambdaLower nu mu : Real) : Real :=
  lambdaUpper ^ 2 * Lh ^ 2 *
      (Lh ^ 2 / (2 * nu) + nu + Lh + Lu / (2 * lambdaLower)) +
    alpha / lambdaLower *
      (mu * lambdaUpper ^ 2 * Lh ^ 2 +
        (1 + lambdaUpper * Lh) ^ 2 / (2 * mu))

noncomputable def objectiveWithQuadratic {m : Nat} (P : ProblemData m) (M : Real)
    (x y : EuclideanSpace m) : EReal :=
  erealAddReal (P.objective x) (M * ‖x - y‖ ^ 2)

noncomputable def AlgorithmData.M1 {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) : Real :=
  M1Value A.sigma P.Lgrad_h A.lambdaUpper A.alpha A.lambdaLower nu mu

noncomputable def AlgorithmData.M2 {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) : Real :=
  M2Value P.Lgrad_h A.Lgrad_u A.lambdaUpper A.alpha A.lambdaLower nu mu

theorem argminSet_le {m : Nat} {G : EuclideanSpace m -> EReal}
    {p y : EuclideanSpace m} (hp : p ∈ argminSet G) : G p <= G y := by
  rw [mem_argminSet_iff] at hp
  rw [hp]
  exact sInf_le ⟨y, rfl⟩

private theorem erealAddReal_le_of_le {a : EReal} {r s : Real}
    (hrs : r <= s) : erealAddReal a r <= erealAddReal a s := by
  cases a using EReal.rec with
  | bot =>
      change (⊥ : EReal) <= (⊥ : EReal)
      rfl
  | coe a =>
      change ((a + r : Real) : EReal) <= ((a + s : Real) : EReal)
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  | top =>
      change (⊤ : EReal) <= (⊤ : EReal)
      rfl

theorem erealAddReal_add (a : EReal) (r s : Real) :
    erealAddReal (erealAddReal a r) s = erealAddReal a (r + s) := by
  cases a using EReal.rec with
  | bot =>
      change (⊥ : EReal) = (⊥ : EReal)
      rfl
  | coe a =>
      change (((a + r) + s : Real) : EReal) = ((a + (r + s) : Real) : EReal)
      ring_nf
  | top =>
      change (⊤ : EReal) = (⊤ : EReal)
      rfl

theorem erealAddReal_mono {a b : EReal} {r s : Real}
    (hab : a <= b) (hrs : r <= s) : erealAddReal a r <= erealAddReal b s := by
  cases a using EReal.rec with
  | bot =>
      cases b using EReal.rec <;> change (⊥ : EReal) <= _ <;> simp
  | coe a =>
      cases b using EReal.rec with
      | bot =>
          change ((a : EReal) <= (⊥ : EReal)) at hab
          simp at hab
      | coe b =>
          change ((a + r : Real) : EReal) <= ((b + s : Real) : EReal)
          exact EReal.coe_le_coe_iff.mpr (by
            have hab_real : a <= b := EReal.coe_le_coe_iff.mp hab
            linarith)
      | top =>
          change ((a + r : Real) : EReal) <= (⊤ : EReal)
          exact le_top
  | top =>
      cases b using EReal.rec with
      | bot =>
          change ((⊤ : EReal) <= (⊥ : EReal)) at hab
          simp at hab
      | coe b =>
          change ((⊤ : EReal) <= (b : EReal)) at hab
          simp at hab
      | top =>
          change (⊤ : EReal) <= (⊤ : EReal)
          rfl

theorem erealAddReal_le_cancel_common {a b : EReal} {r s t : Real}
    (h : erealAddReal a (r + t) <= erealAddReal b (s + t)) :
    erealAddReal a r <= erealAddReal b s := by
  cases a using EReal.rec with
  | bot =>
      cases b using EReal.rec <;> change (⊥ : EReal) <= _ <;> simp
  | coe a =>
      cases b using EReal.rec with
      | bot =>
          change ((a + (r + t) : Real) : EReal) <= (⊥ : EReal) at h
          simp at h
      | coe b =>
          change ((a + r : Real) : EReal) <= ((b + s : Real) : EReal)
          apply EReal.coe_le_coe_iff.mpr
          have hreal : a + (r + t) <= b + (s + t) := EReal.coe_le_coe_iff.mp h
          linarith
      | top =>
          change ((a + r : Real) : EReal) <= (⊤ : EReal)
          exact le_top
  | top =>
      cases b using EReal.rec with
      | bot =>
          change (⊤ : EReal) <= (⊥ : EReal) at h
          simp at h
      | coe b =>
          change (⊤ : EReal) <= ((b + (s + t) : Real) : EReal) at h
          have htop : ((b + (s + t) : Real) : EReal) = ⊤ := top_le_iff.mp h
          exact False.elim (EReal.coe_ne_top _ htop)
      | top =>
          change (⊤ : EReal) <= (⊤ : EReal)
          rfl

theorem objectiveWithQuadratic_mono_coeff {m : Nat} (P : ProblemData m)
    {M M' : Real} (hMM : M <= M') (x y : EuclideanSpace m) :
    objectiveWithQuadratic P M x y <= objectiveWithQuadratic P M' x y := by
  unfold objectiveWithQuadratic
  apply erealAddReal_le_of_le
  exact mul_le_mul_of_nonneg_right hMM (sq_nonneg _)

theorem young_mul {a b eps : Real} (heps : 0 < eps) :
    a * b <= (eps / 2) * b ^ 2 + (1 / (2 * eps)) * a ^ 2 := by
  have hne : eps ≠ 0 := ne_of_gt heps
  have hsq : 0 <= (eps * b - a) ^ 2 := sq_nonneg (eps * b - a)
  have hscaled :
      2 * eps * (a * b) <=
        2 * eps * ((eps / 2) * b ^ 2 + (1 / (2 * eps)) * a ^ 2) := by
    field_simp [hne]
    nlinarith [hsq]
  nlinarith [hscaled, heps]

theorem inner_young {m : Nat} {a b : EuclideanSpace m} {eps : Real}
    (heps : 0 < eps) :
    inner Real a b <= (eps / 2) * ‖a‖ ^ 2 + (1 / (2 * eps)) * ‖b‖ ^ 2 := by
  calc
    inner Real a b <= ‖a‖ * ‖b‖ := real_inner_le_norm a b
    _ <= (eps / 2) * ‖a‖ ^ 2 + (1 / (2 * eps)) * ‖b‖ ^ 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (young_mul (a := ‖b‖) (b := ‖a‖) heps)

theorem norm_sq_sub_le_two {m : Nat} (a b c : EuclideanSpace m) :
    ‖a - b‖ ^ 2 <= 2 * (‖a - c‖ ^ 2 + ‖c - b‖ ^ 2) := by
  have htri : ‖a - b‖ <= ‖a - c‖ + ‖c - b‖ := by
    calc
      ‖a - b‖ = ‖(a - c) + (c - b)‖ := by
        congr 1
        abel
      _ <= ‖a - c‖ + ‖c - b‖ := norm_add_le _ _
  have hsquare :
      ‖a - b‖ ^ 2 <= (‖a - c‖ + ‖c - b‖) ^ 2 :=
    sq_le_sq' (by
      have hsum_nonneg : 0 <= ‖a - c‖ + ‖c - b‖ := by positivity
      have hnorm_nonneg : 0 <= ‖a - b‖ := norm_nonneg _
      linarith) htri
  have hquad :
      (‖a - c‖ + ‖c - b‖) ^ 2 <= 2 * (‖a - c‖ ^ 2 + ‖c - b‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a - c‖ - ‖c - b‖)]
  exact le_trans hsquare hquad

theorem m1_index_lower_bound {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) {nu mu : Real} (hmu : 0 < mu) {n : Nat} (hn : 1 <= n) :
    A.M1 nu mu <=
      A.sigma / (2 * A.lambda n) - P.Lgrad_h - nu -
        (A.alphaSeq n / A.lambda n) * mu := by
  have hlam := A.lambda_bounds n hn
  have halpha := A.alpha_bounds n hn
  have hlam_pos : 0 < A.lambda n := lt_of_lt_of_le A.lambdaLower_pos hlam.1
  have hsigma_nonneg : 0 <= A.sigma := le_of_lt A.u_strongly_convex.1
  have hsigma_div :
      A.sigma / (2 * A.lambdaUpper) <= A.sigma / (2 * A.lambda n) := by
    exact div_le_div_of_nonneg_left hsigma_nonneg (by positivity) (by nlinarith [hlam.2])
  have halpha_div :
      A.alphaSeq n / A.lambda n <= A.alpha / A.lambdaLower :=
    div_le_div₀ A.alpha_nonneg halpha.2 A.lambdaLower_pos hlam.1
  have halpha_mul :
      (A.alphaSeq n / A.lambda n) * mu <= (A.alpha / A.lambdaLower) * mu :=
    mul_le_mul_of_nonneg_right halpha_div (le_of_lt hmu)
  unfold AlgorithmData.M1 M1Value
  nlinarith [hsigma_div, halpha_mul]

theorem m2_index_upper_bound {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) {nu mu : Real} (hnu : 0 < nu) (hmu : 0 < mu)
    {n : Nat} (hn1 : 1 <= n) (hnpred : 1 <= n - 1) :
    A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
        (P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
          A.Lgrad_u / (2 * A.lambda n)) +
      (A.alphaSeq n / A.lambda n) *
        (mu * A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 +
          (1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu)) <=
      A.M2 nu mu := by
  have hlam := A.lambda_bounds n hn1
  have hlamp := A.lambda_bounds (n - 1) hnpred
  have halpha := A.alpha_bounds n hn1
  have hLh_nonneg : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
  have hLu_nonneg : 0 <= A.Lgrad_u := le_of_lt A.u_Lgrad_pos
  have hlam_pos : 0 < A.lambda n := lt_of_lt_of_le A.lambdaLower_pos hlam.1
  have hlamp_pos : 0 < A.lambda (n - 1) := lt_of_lt_of_le A.lambdaLower_pos hlamp.1
  have hBpart :
      A.Lgrad_u / (2 * A.lambda n) <= A.Lgrad_u / (2 * A.lambdaLower) := by
    exact div_le_div_of_nonneg_left hLu_nonneg (by nlinarith [A.lambdaLower_pos])
      (by nlinarith [hlam.1])
  have hB :
      P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h + A.Lgrad_u / (2 * A.lambda n) <=
        P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
          A.Lgrad_u / (2 * A.lambdaLower) := by
    linarith
  have hBn_nonneg :
      0 <= P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
        A.Lgrad_u / (2 * A.lambda n) := by
    positivity
  have hlamsq : A.lambda (n - 1) ^ 2 <= A.lambdaUpper ^ 2 := by
    exact sq_le_sq' (by nlinarith [hlamp_pos, A.lambdaUpper_pos]) hlamp.2
  have hcoef :
      A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 <=
        A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 := by
    exact mul_le_mul_of_nonneg_right hlamsq (sq_nonneg P.Lgrad_h)
  have hfirst :
      A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
          (P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
            A.Lgrad_u / (2 * A.lambda n)) <=
        A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 *
          (P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
            A.Lgrad_u / (2 * A.lambdaLower)) := by
    calc
      A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
          (P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
            A.Lgrad_u / (2 * A.lambda n))
          <= A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 *
            (P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
              A.Lgrad_u / (2 * A.lambda n)) := by
              exact mul_le_mul_of_nonneg_right hcoef hBn_nonneg
      _ <= A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 *
            (P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
              A.Lgrad_u / (2 * A.lambdaLower)) := by
              exact mul_le_mul_of_nonneg_left hB
                (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hlampLh :
      A.lambda (n - 1) * P.Lgrad_h <= A.lambdaUpper * P.Lgrad_h :=
    mul_le_mul_of_nonneg_right hlamp.2 hLh_nonneg
  have hbase_nonneg : 0 <= 1 + A.lambda (n - 1) * P.Lgrad_h := by
    nlinarith [mul_nonneg (le_of_lt hlamp_pos) hLh_nonneg]
  have htopbase_nonneg : 0 <= 1 + A.lambdaUpper * P.Lgrad_h := by
    nlinarith [mul_nonneg (le_of_lt A.lambdaUpper_pos) hLh_nonneg]
  have hsq2 :
      (1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 <=
        (1 + A.lambdaUpper * P.Lgrad_h) ^ 2 := by
    exact sq_le_sq' (by nlinarith [hbase_nonneg, htopbase_nonneg]) (by linarith)
  have hsqfrac :
      (1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu) <=
        (1 + A.lambdaUpper * P.Lgrad_h) ^ 2 / (2 * mu) := by
    exact div_le_div_of_nonneg_right hsq2 (by positivity)
  have hmul_lam :
      mu * A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 <=
        mu * A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcoef (le_of_lt hmu)]
  have hC :
      mu * A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 +
          (1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu) <=
        mu * A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 +
          (1 + A.lambdaUpper * P.Lgrad_h) ^ 2 / (2 * mu) := by
    exact add_le_add hmul_lam hsqfrac
  have hCn_nonneg :
      0 <= mu * A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 +
        (1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu) := by
    positivity
  have halpha_div : A.alphaSeq n / A.lambda n <= A.alpha / A.lambdaLower := by
    exact div_le_div₀ A.alpha_nonneg halpha.2 A.lambdaLower_pos hlam.1
  have hsecond :
      (A.alphaSeq n / A.lambda n) *
          (mu * A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 +
            (1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu)) <=
        (A.alpha / A.lambdaLower) *
          (mu * A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 +
            (1 + A.lambdaUpper * P.Lgrad_h) ^ 2 / (2 * mu)) := by
    exact mul_le_mul halpha_div hC hCn_nonneg
      (div_nonneg A.alpha_nonneg (le_of_lt A.lambdaLower_pos))
  unfold AlgorithmData.M2 M2Value
  exact add_le_add hfirst hsecond

theorem algorithm_descent_ineq_12 {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) {n : Nat} (_hn1 : 1 <= n)
    (_hlam_pos : 0 < A.lambda n)
    (hmin :
      algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n (A.p n) <=
        algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n (A.p (n - 1)))
    (hbpn_scaled :
      A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2 <=
        (1 / A.lambda n) * bregmanDistance A.u (A.p n) (A.x n))
    (hbprev_scaled :
      (1 / A.lambda n) * bregmanDistance A.u (A.p (n - 1)) (A.x n) <=
        A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2)
    (hhdesc :
      P.h (A.p n) <=
        P.h (A.p (n - 1)) +
          inner Real (gradient P.h (A.p (n - 1))) (A.p n - A.p (n - 1)) +
          (P.Lgrad_h / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2) :
    erealAddReal (P.objective (A.p n))
        (A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2) <=
      erealAddReal (P.objective (A.p (n - 1)))
        (A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
          P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          inner Real
            (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
            (A.p n - A.p (n - 1)) +
          (A.alphaSeq n / A.lambda n) *
            inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1))) := by
  let pn := A.p n
  let pp := A.p (n - 1)
  let xn := A.x n
  let xp := A.x (n - 1)
  let lam := A.lambda n
  let c := A.alphaSeq n / A.lambda n
  let gxn := gradient P.h (A.x n)
  let gpp := gradient P.h (A.p (n - 1))
  let S : Real :=
    P.h pp + inner Real gpp (pn - pp) +
      (P.Lgrad_h / 2) * ‖pn - pp‖ ^ 2 -
      inner Real pn gxn - c * inner Real pn (xp - xn)
  have hleft_real :
      P.h pn + A.sigma / (2 * A.lambda n) * ‖pn - xn‖ ^ 2 <=
        (1 / A.lambda n) * bregmanDistance A.u pn xn +
          P.h pp + inner Real gpp (pn - pp) +
          (P.Lgrad_h / 2) * ‖pn - pp‖ ^ 2 := by
    nlinarith [hbpn_scaled, hhdesc]
  have hleft :
      erealAddReal (P.objective pn)
          (A.sigma / (2 * A.lambda n) * ‖pn - xn‖ ^ 2) <=
        erealAddReal (P.f pn)
          ((1 / A.lambda n) * bregmanDistance A.u pn xn +
            P.h pp + inner Real gpp (pn - pp) +
            (P.Lgrad_h / 2) * ‖pn - pp‖ ^ 2) := by
    unfold ProblemData.objective objectiveSum
    rw [erealAddReal_add]
    exact erealAddReal_le_of_le hleft_real
  have hmin_shift :
      erealAddReal
          (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n pn) S <=
        erealAddReal
          (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n pp) S := by
    exact erealAddReal_mono (by simpa [pn, pp] using hmin) le_rfl
  have hstep :
      erealAddReal (P.f pn)
          ((1 / A.lambda n) * bregmanDistance A.u pn xn +
            P.h pp + inner Real gpp (pn - pp) +
            (P.Lgrad_h / 2) * ‖pn - pp‖ ^ 2) <=
        erealAddReal (P.f pp)
          (P.h pp + (1 / A.lambda n) * bregmanDistance A.u pp xn +
            (P.Lgrad_h / 2) * ‖pn - pp‖ ^ 2 +
            inner Real (gpp - gxn) (pn - pp) +
            c * inner Real (pn - pp) (xn - xp)) := by
    have hshift' := hmin_shift
    unfold algorithmStepObjective at hshift'
    rw [erealAddReal_add, erealAddReal_add] at hshift'
    convert hshift' using 2 <;>
      simp [S, pn, pp, xn, xp, c, gxn, gpp, inner_sub_left, inner_sub_right,
        real_inner_comm] <;>
      ring_nf
  have hright :
      erealAddReal (P.f pp)
          (P.h pp + (1 / A.lambda n) * bregmanDistance A.u pp xn +
            (P.Lgrad_h / 2) * ‖pn - pp‖ ^ 2 +
            inner Real (gpp - gxn) (pn - pp) +
            c * inner Real (pn - pp) (xn - xp)) <=
        erealAddReal (P.objective pp)
          (A.Lgrad_u / (2 * A.lambda n) * ‖pp - xn‖ ^ 2 +
            P.Lgrad_h / 2 * ‖pn - pp‖ ^ 2 +
            inner Real (gpp - gxn) (pn - pp) +
            c * inner Real (pn - pp) (xn - xp)) := by
    unfold ProblemData.objective objectiveSum
    rw [erealAddReal_add]
    apply erealAddReal_le_of_le
    nlinarith [hbprev_scaled]
  calc
    erealAddReal (P.objective (A.p n))
        (A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2)
        = erealAddReal (P.objective pn)
          (A.sigma / (2 * A.lambda n) * ‖pn - xn‖ ^ 2) := by rfl
    _ <= erealAddReal (P.f pn)
          ((1 / A.lambda n) * bregmanDistance A.u pn xn +
            P.h pp + inner Real gpp (pn - pp) +
            (P.Lgrad_h / 2) * ‖pn - pp‖ ^ 2) := hleft
    _ <= erealAddReal (P.f pp)
          (P.h pp + (1 / A.lambda n) * bregmanDistance A.u pp xn +
            (P.Lgrad_h / 2) * ‖pn - pp‖ ^ 2 +
            inner Real (gpp - gxn) (pn - pp) +
            c * inner Real (pn - pp) (xn - xp)) := hstep
    _ <= erealAddReal (P.objective pp)
          (A.Lgrad_u / (2 * A.lambda n) * ‖pp - xn‖ ^ 2 +
            P.Lgrad_h / 2 * ‖pn - pp‖ ^ 2 +
            inner Real (gpp - gxn) (pn - pp) +
            c * inner Real (pn - pp) (xn - xp)) := hright
    _ = erealAddReal (P.objective (A.p (n - 1)))
        (A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
          P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          inner Real
            (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
            (A.p n - A.p (n - 1)) +
          (A.alphaSeq n / A.lambda n) *
            inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1))) := by
          rfl

set_option maxHeartbeats 1000000 in
/-- Lemma 3.2: one-step Lyapunov descent estimate with constants `M1` and `M2`. -/
theorem lemma_3_2_descent {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) (hnu : 0 < nu) (hmu : 0 < mu) :
    ∀ n, 2 <= n ->
      objectiveWithQuadratic P (A.M1 nu mu) (A.p n) (A.x n) <=
        objectiveWithQuadratic P (A.M2 nu mu) (A.p (n - 1)) (A.x (n - 1)) := by
  intro n hn
  have hn1 : 1 <= n := by omega
  have hnpred : 1 <= n - 1 := by omega
  have hlam := A.lambda_bounds n hn1
  have hlamp := A.lambda_bounds (n - 1) hnpred
  have halpha := A.alpha_bounds n hn1
  have hlam_pos : 0 < A.lambda n := lt_of_lt_of_le A.lambdaLower_pos hlam.1
  have hlamp_pos : 0 < A.lambda (n - 1) := lt_of_lt_of_le A.lambdaLower_pos hlamp.1
  have hLh_nonneg : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
  have hLu_nonneg : 0 <= A.Lgrad_u := le_of_lt A.u_Lgrad_pos
  have hsigma_pos : 0 < A.sigma := A.u_strongly_convex.1
  have hmin :
      algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n (A.p n) <=
        algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n (A.p (n - 1)) :=
    argminSet_le (A.p_argmin n hn1)
  have hx_update :
      A.x n =
        A.p (n - 1) +
          A.lambda (n - 1) •
            (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))) := by
    have hx := A.x_update (n - 1) hnpred
    have hsucc : n - 1 + 1 = n := by omega
    simpa [hsucc] using hx
  have hx_sub :
      A.x n - A.p (n - 1) =
        A.lambda (n - 1) •
          (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))) := by
    rw [hx_update]
    abel
  have h13 :
      ‖A.x n - A.p (n - 1)‖ <=
        A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
    have hLip :=
      P.h_lipschitz_gradient.2.2 (A.x (n - 1)) (A.p (n - 1))
    calc
      ‖A.x n - A.p (n - 1)‖
          = ‖A.lambda (n - 1) •
              (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1)))‖ := by
              rw [hx_sub]
      _ = A.lambda (n - 1) *
            ‖gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))‖ := by
              rw [norm_smul]
              simp [Real.norm_eq_abs, abs_of_pos hlamp_pos]
      _ <= A.lambda (n - 1) *
            (P.Lgrad_h * ‖A.x (n - 1) - A.p (n - 1)‖) := by
              exact mul_le_mul_of_nonneg_left hLip (le_of_lt hlamp_pos)
      _ = A.lambda (n - 1) * P.Lgrad_h *
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
              ring
  have h14 :
      ‖A.x n - A.x (n - 1)‖ <=
        (1 + A.lambda (n - 1) * P.Lgrad_h) *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
    calc
      ‖A.x n - A.x (n - 1)‖
          = ‖(A.x n - A.p (n - 1)) +
              (A.p (n - 1) - A.x (n - 1))‖ := by
              congr 1
              abel
      _ <= ‖A.x n - A.p (n - 1)‖ +
            ‖A.p (n - 1) - A.x (n - 1)‖ := norm_add_le _ _
      _ <= A.lambda (n - 1) * P.Lgrad_h *
              ‖A.x (n - 1) - A.p (n - 1)‖ +
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
              exact add_le_add h13 (by rw [norm_sub_rev])
      _ = (1 + A.lambda (n - 1) * P.Lgrad_h) *
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
              ring
  have h15 :
      ‖A.p n - A.p (n - 1)‖ ^ 2 <=
        2 * (‖A.x n - A.p n‖ ^ 2 +
          A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
    have hbase := norm_sq_sub_le_two (A.p n) (A.p (n - 1)) (A.x n)
    have hrhs_nonneg :
        0 <= A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
      nlinarith [h13, norm_nonneg (A.x n - A.p (n - 1))]
    have h13sq :
        ‖A.x n - A.p (n - 1)‖ ^ 2 <=
          (A.lambda (n - 1) * P.Lgrad_h *
            ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2 := by
      exact sq_le_sq' (by
        have hnorm_nonneg : 0 <= ‖A.x n - A.p (n - 1)‖ := norm_nonneg _
        nlinarith) h13
    calc
      ‖A.p n - A.p (n - 1)‖ ^ 2
          <= 2 * (‖A.p n - A.x n‖ ^ 2 +
            ‖A.x n - A.p (n - 1)‖ ^ 2) := hbase
      _ <= 2 * (‖A.x n - A.p n‖ ^ 2 +
          (A.lambda (n - 1) * P.Lgrad_h *
            ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2) := by
            rw [norm_sub_rev (A.p n) (A.x n)]
            nlinarith [h13sq]
      _ = 2 * (‖A.x n - A.p n‖ ^ 2 +
          A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
            ring
  have h16 :
      inner Real
          (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
          (A.p n - A.p (n - 1)) <=
        (nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          (P.Lgrad_h ^ 2 / (2 * nu)) *
            ‖A.x n - A.p (n - 1)‖ ^ 2 := by
    have hLip := P.h_lipschitz_gradient.2.2 (A.p (n - 1)) (A.x n)
    calc
      inner Real
          (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
          (A.p n - A.p (n - 1))
          <= ‖gradient P.h (A.p (n - 1)) - gradient P.h (A.x n)‖ *
              ‖A.p n - A.p (n - 1)‖ := real_inner_le_norm _ _
      _ <= (P.Lgrad_h * ‖A.p (n - 1) - A.x n‖) *
              ‖A.p n - A.p (n - 1)‖ := by
              exact mul_le_mul_of_nonneg_right hLip (norm_nonneg _)
      _ = (P.Lgrad_h * ‖A.x n - A.p (n - 1)‖) *
              ‖A.p n - A.p (n - 1)‖ := by
              rw [norm_sub_rev (A.p (n - 1)) (A.x n)]
      _ <= (nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (1 / (2 * nu)) *
              (P.Lgrad_h * ‖A.x n - A.p (n - 1)‖) ^ 2 :=
              young_mul (a := P.Lgrad_h * ‖A.x n - A.p (n - 1)‖)
                (b := ‖A.p n - A.p (n - 1)‖) hnu
      _ = (nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (P.Lgrad_h ^ 2 / (2 * nu)) *
              ‖A.x n - A.p (n - 1)‖ ^ 2 := by
              ring
  have h17 :
      inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) <=
        (mu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          (1 / (2 * mu)) * ‖A.x n - A.x (n - 1)‖ ^ 2 :=
    inner_young hmu
  have h13sq :
      ‖A.x n - A.p (n - 1)‖ ^ 2 <=
        (A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2 := by
    have hrhs_nonneg :
        0 <= A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
      nlinarith [h13, norm_nonneg (A.x n - A.p (n - 1))]
    exact sq_le_sq' (by
      have hnorm_nonneg : 0 <= ‖A.x n - A.p (n - 1)‖ := norm_nonneg _
      nlinarith) h13
  have h14sq :
      ‖A.x n - A.x (n - 1)‖ ^ 2 <=
        ((1 + A.lambda (n - 1) * P.Lgrad_h) *
          ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2 := by
    have hlamp_nonneg : 0 <= A.lambda (n - 1) := le_of_lt hlamp_pos
    have hfactor_nonneg : 0 <= 1 + A.lambda (n - 1) * P.Lgrad_h := by
      nlinarith [mul_nonneg hlamp_nonneg hLh_nonneg]
    have hrhs_nonneg :
        0 <= (1 + A.lambda (n - 1) * P.Lgrad_h) *
          ‖A.x (n - 1) - A.p (n - 1)‖ :=
      mul_nonneg hfactor_nonneg (norm_nonneg _)
    exact sq_le_sq' (by
      have hnorm_nonneg : 0 <= ‖A.x n - A.x (n - 1)‖ := norm_nonneg _
      nlinarith) h14
  have hM1 :
      A.M1 nu mu <=
        A.sigma / (2 * A.lambda n) - P.Lgrad_h - nu -
          (A.alphaSeq n / A.lambda n) * mu :=
    m1_index_lower_bound A hmu hn1
  have hbpn :
      (A.sigma / 2) * ‖A.p n - A.x n‖ ^ 2 <=
        bregmanDistance A.u (A.p n) (A.x n) :=
    (algorithm_bregman_bounds A (A.p n) (A.x n)).1
  have hbprev :
      bregmanDistance A.u (A.p (n - 1)) (A.x n) <=
        (A.Lgrad_u / 2) * ‖A.p (n - 1) - A.x n‖ ^ 2 :=
    (algorithm_bregman_bounds A (A.p (n - 1)) (A.x n)).2
  have hbpn_scaled :
      A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2 <=
        (1 / A.lambda n) * bregmanDistance A.u (A.p n) (A.x n) := by
    calc
      A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2
          = (1 / A.lambda n) * ((A.sigma / 2) * ‖A.p n - A.x n‖ ^ 2) := by
              field_simp [ne_of_gt hlam_pos]
      _ <= (1 / A.lambda n) * bregmanDistance A.u (A.p n) (A.x n) := by
              exact mul_le_mul_of_nonneg_left hbpn (by positivity)
  have hbprev_scaled :
      (1 / A.lambda n) * bregmanDistance A.u (A.p (n - 1)) (A.x n) <=
        A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 := by
    calc
      (1 / A.lambda n) * bregmanDistance A.u (A.p (n - 1)) (A.x n)
          <= (1 / A.lambda n) * ((A.Lgrad_u / 2) *
              ‖A.p (n - 1) - A.x n‖ ^ 2) := by
              exact mul_le_mul_of_nonneg_left hbprev (by positivity)
      _ = A.Lgrad_u / (2 * A.lambda n) *
            ‖A.p (n - 1) - A.x n‖ ^ 2 := by
              field_simp [ne_of_gt hlam_pos]
  have hhdesc :
      P.h (A.p n) <=
        P.h (A.p (n - 1)) +
          inner Real (gradient P.h (A.p (n - 1))) (A.p n - A.p (n - 1)) +
          (P.Lgrad_h / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 :=
    lemma_3_1_descent P.h P.Lgrad_h P.h_lipschitz_gradient
      (A.p (n - 1)) (A.p n)
  let M1n : Real :=
    A.sigma / (2 * A.lambda n) - P.Lgrad_h - nu -
      (A.alphaSeq n / A.lambda n) * mu
  let M2n : Real :=
    A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
        (P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
          A.Lgrad_u / (2 * A.lambda n)) +
      (A.alphaSeq n / A.lambda n) *
        (mu * A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 +
          (1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu))
  let K : Real := P.Lgrad_h + nu + (A.alphaSeq n / A.lambda n) * mu
  have hc_nonneg : 0 <= A.alphaSeq n / A.lambda n :=
    div_nonneg halpha.1 (le_of_lt hlam_pos)
  have h12 :=
    algorithm_descent_ineq_12 A hn1 hlam_pos hmin hbpn_scaled hbprev_scaled hhdesc
  have h17_scaled :
      (A.alphaSeq n / A.lambda n) *
          inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) <=
        (A.alphaSeq n / A.lambda n) *
          ((mu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (1 / (2 * mu)) * ‖A.x n - A.x (n - 1)‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left h17 hc_nonneg
  have hdp_coeff_nonneg :
      0 <= P.Lgrad_h / 2 + nu / 2 + (A.alphaSeq n / A.lambda n) * (mu / 2) := by
    positivity
  have hdp_bound :
      (P.Lgrad_h / 2 + nu / 2 + (A.alphaSeq n / A.lambda n) * (mu / 2)) *
          ‖A.p n - A.p (n - 1)‖ ^ 2 <=
        K * ‖A.x n - A.p n‖ ^ 2 +
          K * (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
    calc
      (P.Lgrad_h / 2 + nu / 2 + (A.alphaSeq n / A.lambda n) * (mu / 2)) *
          ‖A.p n - A.p (n - 1)‖ ^ 2
          <= (P.Lgrad_h / 2 + nu / 2 + (A.alphaSeq n / A.lambda n) * (mu / 2)) *
            (2 * (‖A.x n - A.p n‖ ^ 2 +
              A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2)) := by
              exact mul_le_mul_of_nonneg_left h15 hdp_coeff_nonneg
      _ = K * ‖A.x n - A.p n‖ ^ 2 +
          K * (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
              simp [K]
              ring
  have ha_coeff_nonneg :
      0 <= A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu) := by
    positivity
  have h13sq_rev :
      ‖A.p (n - 1) - A.x n‖ ^ 2 <=
        (A.lambda (n - 1) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2 := by
    simpa [norm_sub_rev] using h13sq
  have ha_bound :
      (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
          ‖A.p (n - 1) - A.x n‖ ^ 2 <=
        (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
          (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
    calc
      (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
          ‖A.p (n - 1) - A.x n‖ ^ 2
          <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
            ((A.lambda (n - 1) * P.Lgrad_h *
              ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2) := by
              exact mul_le_mul_of_nonneg_left h13sq_rev ha_coeff_nonneg
      _ = (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
          (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
              ring
  have hdx_coeff_nonneg :
      0 <= (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) := by
    positivity
  have hdx_bound :
      (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
          ‖A.x n - A.x (n - 1)‖ ^ 2 <=
        (A.alphaSeq n / A.lambda n) *
          ((1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu)) *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
    calc
      (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
          ‖A.x n - A.x (n - 1)‖ ^ 2
          <= (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
            (((1 + A.lambda (n - 1) * P.Lgrad_h) *
              ‖A.x (n - 1) - A.p (n - 1)‖) ^ 2) := by
              exact mul_le_mul_of_nonneg_left h14sq hdx_coeff_nonneg
      _ = (A.alphaSeq n / A.lambda n) *
          ((1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu)) *
            ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
              ring
  have hRbound :
      A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
          P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          inner Real
            (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
            (A.p n - A.p (n - 1)) +
          (A.alphaSeq n / A.lambda n) *
            inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) <=
        K * ‖A.x n - A.p n‖ ^ 2 +
          M2n * ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
    have hyoung :
        A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
            P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            inner Real
              (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
              (A.p n - A.p (n - 1)) +
            (A.alphaSeq n / A.lambda n) *
              inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) <=
          (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              ‖A.p (n - 1) - A.x n‖ ^ 2 +
            (P.Lgrad_h / 2 + nu / 2 +
                (A.alphaSeq n / A.lambda n) * (mu / 2)) *
              ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := by
      calc
        A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
            P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
            inner Real
              (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
              (A.p n - A.p (n - 1)) +
            (A.alphaSeq n / A.lambda n) *
              inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1))
            <= A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
              P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
              ((nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
                (P.Lgrad_h ^ 2 / (2 * nu)) *
                  ‖A.x n - A.p (n - 1)‖ ^ 2) +
              (A.alphaSeq n / A.lambda n) *
                inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1)) := by
                linarith [h16]
        _ <= A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
              P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
              ((nu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
                (P.Lgrad_h ^ 2 / (2 * nu)) *
                  ‖A.x n - A.p (n - 1)‖ ^ 2) +
              (A.alphaSeq n / A.lambda n) *
                ((mu / 2) * ‖A.p n - A.p (n - 1)‖ ^ 2 +
                  (1 / (2 * mu)) * ‖A.x n - A.x (n - 1)‖ ^ 2) := by
                linarith [h17_scaled]
        _ = (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              ‖A.p (n - 1) - A.x n‖ ^ 2 +
            (P.Lgrad_h / 2 + nu / 2 +
                (A.alphaSeq n / A.lambda n) * (mu / 2)) *
              ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := by
                rw [norm_sub_rev (A.x n) (A.p (n - 1))]
                ring
    calc
      A.Lgrad_u / (2 * A.lambda n) * ‖A.p (n - 1) - A.x n‖ ^ 2 +
          P.Lgrad_h / 2 * ‖A.p n - A.p (n - 1)‖ ^ 2 +
          inner Real
            (gradient P.h (A.p (n - 1)) - gradient P.h (A.x n))
            (A.p n - A.p (n - 1)) +
          (A.alphaSeq n / A.lambda n) *
            inner Real (A.p n - A.p (n - 1)) (A.x n - A.x (n - 1))
          <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              ‖A.p (n - 1) - A.x n‖ ^ 2 +
            (P.Lgrad_h / 2 + nu / 2 +
                (A.alphaSeq n / A.lambda n) * (mu / 2)) *
              ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := hyoung
      _ <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) +
            (P.Lgrad_h / 2 + nu / 2 +
                (A.alphaSeq n / A.lambda n) * (mu / 2)) *
              ‖A.p n - A.p (n - 1)‖ ^ 2 +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := by
                linarith [ha_bound]
      _ <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) +
            (K * ‖A.x n - A.p n‖ ^ 2 +
              K * (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2)) +
            (A.alphaSeq n / A.lambda n) * (1 / (2 * mu)) *
              ‖A.x n - A.x (n - 1)‖ ^ 2 := by
                linarith [hdp_bound]
      _ <= (A.Lgrad_u / (2 * A.lambda n) + P.Lgrad_h ^ 2 / (2 * nu)) *
              (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) +
            (K * ‖A.x n - A.p n‖ ^ 2 +
              K * (A.lambda (n - 1) ^ 2 * P.Lgrad_h ^ 2 *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2)) +
            (A.alphaSeq n / A.lambda n) *
              ((1 + A.lambda (n - 1) * P.Lgrad_h) ^ 2 / (2 * mu)) *
                ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
                linarith [hdx_bound]
      _ = K * ‖A.x n - A.p n‖ ^ 2 +
          M2n * ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2 := by
            simp [M2n, K]
            ring
  have hindexed :
      objectiveWithQuadratic P M1n (A.p n) (A.x n) <=
        objectiveWithQuadratic P M2n (A.p (n - 1)) (A.x (n - 1)) := by
    unfold objectiveWithQuadratic
    have h12_bound :
        erealAddReal (P.objective (A.p n))
            (A.sigma / (2 * A.lambda n) * ‖A.p n - A.x n‖ ^ 2) <=
          erealAddReal (P.objective (A.p (n - 1)))
            (K * ‖A.x n - A.p n‖ ^ 2 +
              M2n * ‖A.x (n - 1) - A.p (n - 1)‖ ^ 2) := by
      exact le_trans h12 (erealAddReal_le_of_le hRbound)
    have hcommon :
        erealAddReal (P.objective (A.p n))
            (M1n * ‖A.p n - A.x n‖ ^ 2 +
              K * ‖A.x n - A.p n‖ ^ 2) <=
          erealAddReal (P.objective (A.p (n - 1)))
            (M2n * ‖A.p (n - 1) - A.x (n - 1)‖ ^ 2 +
              K * ‖A.x n - A.p n‖ ^ 2) := by
      convert h12_bound using 2 <;>
        simp [M1n, K, norm_sub_rev] <;> ring
    exact erealAddReal_le_cancel_common (t := K * ‖A.x n - A.p n‖ ^ 2)
      (by simpa [norm_sub_rev, add_comm, add_left_comm, add_assoc] using hcommon)
  have hM2 : M2n <= A.M2 nu mu := by
    simpa [M2n] using m2_index_upper_bound A hnu hmu hn1 hnpred
  calc
    objectiveWithQuadratic P (A.M1 nu mu) (A.p n) (A.x n)
        <= objectiveWithQuadratic P M1n (A.p n) (A.x n) := by
            exact objectiveWithQuadratic_mono_coeff P (by simpa [M1n] using hM1)
              (A.p n) (A.x n)
    _ <= objectiveWithQuadratic P M2n (A.p (n - 1)) (A.x (n - 1)) := hindexed
    _ <= objectiveWithQuadratic P (A.M2 nu mu) (A.p (n - 1)) (A.x (n - 1)) := by
            exact objectiveWithQuadratic_mono_coeff P hM2 (A.p (n - 1)) (A.x (n - 1))

end BotCsetnek2015
