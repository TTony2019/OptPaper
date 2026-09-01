import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_10
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.algo_2
import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Hilbert.WeakTopology
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open Filter
open scoped Set

private theorem bf_solution_produces_fixed_point
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (hmu : 0 < mu) (S : Set H)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    {z : H} (hz : z ∈ S) :
    let P := ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
    let T : H → H := fun y ↦ P y - mu • B (P y)
    T (z - mu • B z) = z - mu • B z := by
  dsimp
  have hprox : ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
      (z - mu • B z) = z := by
    rw [eq_comm]
    apply (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
      (f := (⟨mu, hmu⟩ : ERealFunction.PosReal) • Phi)
      (ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, hmu⟩) (z - mu • B z) z).2
    letI : SMul ℝ (Set H) := Set.smulSet
    rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
    change (z - mu • B z) - z ∈
      ((mu : ℝ) • ERealFunction.subdifferential Phi z)
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hmu.ne']
    have hrewrite : (mu : ℝ)⁻¹ • ((z - mu • B z) - z) = -B z := by
      calc
        (mu : ℝ)⁻¹ • ((z - mu • B z) - z) = (mu : ℝ)⁻¹ • (-(mu • B z)) := by
          congr 1
          module
        _ = -(((mu : ℝ)⁻¹ * mu) • (B z)) := by rw [smul_neg, smul_smul]
        _ = -B z := by rw [mul_smul, inv_smul_smul₀ hmu.ne']
    simpa only [hrewrite] using (hsolution z).1 hz
  rw [hprox]

private theorem bf_fixed_point_prox_mem_solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (hmu : 0 < mu) (S : Set H)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    {y : H}
    (hy : ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y -
      mu • B (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y) = y) :
    ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y ∈ S := by
  let x := ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y
  have hy' : x - mu • B x = y := by simpa [x] using hy
  apply (hsolution x).2
  have hres : (mu : ℝ)⁻¹ • (y - x) ∈ ERealFunction.subdifferential Phi x := by
    simpa [x] using
      (ERealFunction.scaledProximityOperator_residual_mem hPhi ⟨mu, hmu⟩ y)
  have hrewrite : (mu : ℝ)⁻¹ • (y - x) = -B x := by
    rw [← hy']
    calc
      (mu : ℝ)⁻¹ •
          ((x - mu • B x) - x) = (mu : ℝ)⁻¹ • (-(mu • B x)) := by
            congr 1
            module
      _ = -(((mu : ℝ)⁻¹ * mu) • B x) := by rw [smul_neg, smul_smul]
      _ = -B x := by rw [mul_smul, inv_smul_smul₀ hmu.ne']
  rwa [hrewrite] at hres

private theorem bf_demiclosed_nonexpansive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → H) (hT : LipschitzWith 1 T) (u : ℕ → H) (z : H)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop
      (nhds (toWeakSpace ℝ H z)))
    (hres : Tendsto (fun n ↦ u n - T (u n)) atTop (nhds 0))
    (hbounded : ∃ C : ℝ, ∀ n, ‖u n - z‖ ≤ C) : T z = z := by
  rcases hbounded with ⟨C, hC⟩
  have hineq : ∀ n, ‖(u n - T (u n)) - (z - T z)‖ ^ 2 ≤
      2 * inner ℝ (u n - z) ((u n - T (u n)) - (z - T z)) := by
    intro n
    have hnonexp : ‖T (u n) - T z‖ ≤ ‖u n - z‖ := by
      simpa [dist_eq_norm] using hT.dist_le_mul (u n) z
    have hsq : ‖T (u n) - T z‖ ^ 2 ≤ ‖u n - z‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnonexp
    have hexpand := norm_sub_sq_real (u n - z)
      ((u n - T (u n)) - (z - T z))
    rw [show T (u n) - T z = (u n - z) -
      ((u n - T (u n)) - (z - T z)) by abel, hexpand] at hsq
    nlinarith
  have hleft : Tendsto (fun n ↦ ‖(u n - T (u n)) - (z - T z)‖ ^ 2) atTop
      (nhds (‖z - T z‖ ^ 2)) := by
    simpa only [zero_sub, norm_neg] using (hres.sub tendsto_const_nhds).norm.pow 2
  have hfixed : Tendsto (fun n ↦ inner ℝ (u n - z) (-(z - T z))) atTop (nhds 0) := by
    have hinner := (weakConvergence_iff_forall_tendsto_inner_right u z).1 hweak
      (-(z - T z))
    have hsub := hinner.sub (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ inner ℝ z (-(z - T z))) atTop (nhds (inner ℝ z (-(z - T z)))))
    simpa [inner_sub_left] using hsub
  have hsecond_abs : Tendsto (fun n ↦
      |inner ℝ (u n - z) (u n - T (u n))|) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n ↦ |inner ℝ (u n - z) (u n - T (u n))|)
      (g := fun n ↦ C * ‖u n - T (u n)‖)
      (Filter.Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards with n
      exact le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    · simpa using hres.norm.const_mul C
  have hsecond : Tendsto (fun n ↦ inner ℝ (u n - z) (u n - T (u n))) atTop
      (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa using hsecond_abs
  have hright : Tendsto (fun n ↦
      2 * inner ℝ (u n - z) ((u n - T (u n)) - (z - T z))) atTop (nhds 0) := by
    have hsplit : (fun n ↦ inner ℝ (u n - z) ((u n - T (u n)) - (z - T z))) =
        fun n ↦ inner ℝ (u n - z) (-(z - T z)) +
          inner ℝ (u n - z) (u n - T (u n)) := by
      funext n
      rw [show ((u n - T (u n)) - (z - T z)) =
        (-(z - T z)) + (u n - T (u n)) by abel, inner_add_right]
    have hinner : Tendsto
        (fun n ↦ inner ℝ (u n - z) ((u n - T (u n)) - (z - T z))) atTop (nhds 0) := by
      simpa [hsplit] using hfixed.add hsecond
    simpa using hinner.const_mul 2
  have hnonpos : ‖z - T z‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hineq)
  have hzero : z - T z = 0 :=
    norm_eq_zero.mp (eq_zero_of_pow_eq_zero (le_antisymm hnonpos (sq_nonneg _)))
  exact (sub_eq_zero.mp hzero).symm

private theorem bf_relaxed_averaged_orbit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → H) (alpha h : ℝ) (u : ℕ → H)
    (hT : AveragedWith alpha (fun x : Set.univ ↦ T x))
    (ha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hh : h ∈ Set.Ioo (0 : ℝ) (1 / alpha))
    (hfix : (Function.fixedPoints T).Nonempty)
    (hupdate : ∀ k, u (k+1) = (1-h) • u k + h • T (u k)) :
    ∃ ybar, T ybar = ybar ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) atTop
        (nhds (toWeakSpace ℝ H ybar)) ∧
      Summable (fun k ↦ ‖u (k+1) - u k‖ ^ 2) := by
  let R : H → H := fun x ↦ (1 - h) • x + h • T x
  let lam : ℝ := h * alpha
  have hlam : lam ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [lam]
    constructor
    · exact mul_pos hh.1 ha.1
    · calc
        h * alpha < (1 / alpha) * alpha := mul_lt_mul_of_pos_right hh.2 ha.1
        _ = 1 := by field_simp [ne_of_gt ha.1]
  have hR : AveragedWith lam (fun x : Set.univ ↦ R x) := by
    have := (averagedWith_iff_averagedWith_relaxedMap ha hh).mp hT
    simpa [R, lam, smul_add, add_smul, add_assoc, add_left_comm, add_comm] using this
  have hRineq := (averagedWith_iff_residual_sqnorm_ineq hlam).mp hR
  obtain ⟨q, hq⟩ := hfix
  have hqR : R q = q := by
    dsimp [R]
    rw [hq]
    module
  let d : ℕ → ℝ := fun k ↦ ‖u k - q‖ ^ 2
  let e : ℕ → ℝ := fun k ↦ ‖u (k+1) - u k‖ ^ 2
  have hdecr : ∀ k, e k * ((1 - lam) / lam) ≤ d k - d (k+1) := by
    intro k
    have hi := hRineq ⟨u k, Set.mem_univ _⟩ ⟨q, Set.mem_univ _⟩
    have huR : u (k+1) = R (u k) := by simpa [R] using hupdate k
    have hres : u k - R (u k) = -(u (k+1) - u k) := by rw [huR, neg_sub]
    have hi' : ‖R (u k) - q‖ ^ 2 ≤ ‖u k - q‖ ^ 2 -
        ((1 - lam) / lam) * ‖u k - R (u k)‖ ^ 2 := by
      simpa [hqR] using hi
    rw [← huR] at hi'
    dsimp [d, e]
    have hn : ‖u k - u (k + 1)‖ = ‖u (k + 1) - u k‖ := norm_sub_rev _ _
    rw [hn] at hi'
    nlinarith
  have hsum_scaled : Summable (fun k ↦ e k * ((1 - lam) / lam)) := by
    apply ext_cor_1_summable_of_nonneg_le_diff _ d
    · intro k
      exact mul_nonneg (sq_nonneg _) (div_nonneg (sub_nonneg.mpr hlam.2.le) hlam.1.le)
    · exact hdecr
    · intro k; exact sq_nonneg _
  have hcoef : 0 < ((1 - lam) / lam) := div_pos (sub_pos.mpr hlam.2) hlam.1
  have hsum : Summable e := by
    have hm := Summable.mul_left (((1 - lam) / lam)⁻¹) hsum_scaled
    convert hm using 1
    funext k
    calc
      e k = e k * 1 := by ring
      _ = e k * ((((1 - lam) / lam)⁻¹) * ((1 - lam) / lam)) := by
        rw [inv_mul_cancel₀ hcoef.ne']
      _ = (((1 - lam) / lam)⁻¹) * (e k * ((1 - lam) / lam)) := by ring
  have hTlip : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa using (lipschitzWith_one_of_averagedWith hT).dist_le_mul
      (⟨x, Set.mem_univ _⟩ : Set.univ) ⟨y, Set.mem_univ _⟩
  have hdist : ∀ z ∈ Function.fixedPoints T, ∃ l : ℝ,
      Tendsto (fun k ↦ ‖u k - z‖) atTop (nhds l) := by
    intro z hz
    let dz : ℕ → ℝ := fun k ↦ ‖u k - z‖ ^ 2
    have hmono : Antitone dz := by
      apply antitone_nat_of_succ_le
      intro k
      have hi := hRineq ⟨u k, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
      have huR : u (k+1) = R (u k) := by simpa [R] using hupdate k
      have hzR : R z = z := by dsimp [R]; rw [hz]; module
      have hi' : ‖R (u k) - z‖ ^ 2 ≤ ‖u k - z‖ ^ 2 -
          ((1 - lam) / lam) * ‖u k - R (u k)‖ ^ 2 := by
        simpa [hzR] using hi
      rw [← huR] at hi'
      dsimp [dz]
      nlinarith [sq_nonneg ‖u (k+1) - u k‖]
    have hbelow : BddBelow (Set.range dz) := ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩
    refine ⟨Real.sqrt (⨅ k, dz k), ?_⟩
    simpa [Function.comp_def, dz, Real.sqrt_sq_eq_abs, abs_of_nonneg] using
      (Real.continuous_sqrt.tendsto (⨅ k, dz k)).comp (tendsto_atTop_ciInf hmono hbelow)
  have hbounded : Bornology.IsBounded (Set.range u) := by
    exact bounded_range_of_convergent_distance_to_point (hdist q hq)
  have hcluster : ∀ z : H,
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k))
        (toWeakSpace ℝ H z) → z ∈ Function.fixedPoints T := by
    intro z hz
    rcases hz with ⟨phi, hphi, hphiweak⟩
    have hres : Tendsto (fun k ↦ u (phi k) - T (u (phi k))) atTop (nhds 0) := by
      have hn : Tendsto (fun k ↦ e (phi k)) atTop (nhds 0) :=
        hsum.tendsto_atTop_zero.comp hphi.tendsto_atTop
      have hn' : Tendsto (fun k ↦ ‖u (phi k + 1) - u (phi k)‖) atTop (nhds 0) := by
        simpa [Function.comp_def, e, Real.sqrt_sq_eq_abs, abs_of_nonneg] using
          (Real.continuous_sqrt.tendsto 0).comp hn
      have hv : Tendsto (fun k ↦ u (phi k + 1) - u (phi k)) atTop (nhds 0) :=
        (tendsto_zero_iff_norm_tendsto_zero).2 hn'
      have hRres : Tendsto (fun k ↦ u (phi k) - R (u (phi k))) atTop (nhds 0) := by
        simpa [hupdate, R, neg_sub] using hv.neg
      have hscaled := hRres.const_smul h⁻¹
      have hrewrite : (fun k ↦ h⁻¹ • (u (phi k) - R (u (phi k)))) =
          (fun k ↦ u (phi k) - T (u (phi k))) := by
        funext k
        dsimp [R]
        rw [smul_sub, smul_add, smul_smul, smul_smul]
        rw [inv_mul_cancel₀ hh.1.ne']
        calc
          h⁻¹ • u (phi k) - ((h⁻¹ * (1 - h)) • u (phi k) + (1 : ℝ) • T (u (phi k))) =
              (h⁻¹ • u (phi k) - (h⁻¹ * (1 - h)) • u (phi k)) - T (u (phi k)) := by
                simp
                module
          _ = (h⁻¹ - h⁻¹ * (1 - h)) • u (phi k) - T (u (phi k)) := by
                rw [← sub_smul]
          _ = u (phi k) - T (u (phi k)) := by
                have hs : h⁻¹ - h⁻¹ * (1 - h) = 1 := by
                  field_simp [hh.1.ne']
                  ring
                rw [hs, one_smul]
      rw [hrewrite] at hscaled
      simpa using hscaled
    rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C, hC⟩
    have hsubbound : ∃ K : ℝ, ∀ k, ‖u (phi k) - z‖ ≤ K := by
      refine ⟨C + ‖z‖, ?_⟩
      intro k
      exact (norm_sub_le _ _).trans (add_le_add (hC _ (Set.mem_range_self _)) le_rfl)
    have hphiweak' : Tendsto (fun k ↦ toWeakSpace ℝ H (u (phi k))) atTop
        (nhds (toWeakSpace ℝ H z)) := by simpa [Function.comp_def] using hphiweak
    exact bf_demiclosed_nonexpansive T hTlip (fun k ↦ u (phi k)) z
      hphiweak' hres hsubbound
  rcases opial_lemma ⟨q, hq⟩ u hdist hcluster with ⟨ybar, hyfix, hyweak⟩
  exact ⟨ybar, hyfix, hyweak, hsum⟩

private theorem bf_operator_constant_on_solution_set
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (beta : ℝ) (S : Set H) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    ∀ z ∈ S, ∀ w ∈ S, B z = B w := by
  intro z hz w hw
  have hmono := ERealFunction.isMonotone_subdifferential
    (fun x : H => (Phi x : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
    (-B z) ((hsolution z).1 hz) (-B w) ((hsolution w).1 hw)
  have hsubmono : inner ℝ (B z - B w) (z - w) ≤ 0 := by
    rw [show (-B z) - (-B w) = -(B z - B w) by abel, inner_neg_left] at hmono
    linarith
  have hc := hB.ineq (⟨z, Set.mem_univ z⟩ : Set.univ) (⟨w, Set.mem_univ w⟩ : Set.univ)
  have hcobound : beta * ‖B z - B w‖ ^ 2 ≤ inner ℝ (B z - B w) (z - w) := by
    simpa [real_inner_comm] using hc
  have hzero : beta * ‖B z - B w‖ ^ 2 = 0 :=
    le_antisymm (hcobound.trans hsubmono) (mul_nonneg hbeta.le (sq_nonneg _))
  have hnorm : ‖B z - B w‖ = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left hbeta.ne')
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

private theorem bf_prox_gap_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (mu : ℝ) (hmu : 0 < mu)
    (alg : BackwardForwardDiscretization Phi hPhi B mu h)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    {z0 : H} (hz0 : z0 ∈ S) (k : ℕ) :
    0 ≤ (Phi z0 : EReal).toReal - (Phi (alg.x k) : EReal).toReal -
      inner ℝ ((mu : ℝ)⁻¹ • (alg.y k - alg.x k)) (z0 - alg.x k) := by
  let v : H := (mu : ℝ)⁻¹ • (alg.y k - alg.x k)
  have hv : v ∈ ERealFunction.subdifferential Phi (alg.x k) := by
    simpa [v, alg.prox_step k] using
      (ERealFunction.scaledProximityOperator_residual_mem hPhi ⟨mu, hmu⟩ (alg.y k))
  have hzdom : z0 ∈ ERealFunction.effectiveDomain Phi :=
    ERealFunction.SubdifferentiableAt.mem_effectiveDomain hPhi.2.nonempty
      ⟨-B z0, (hsolution z0).1 hz0⟩
  have hsub := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi hv hzdom
  dsimp [v] at hsub ⊢
  linarith

private theorem summable_of_nonneg_le_diff_add_summable
    (a d c : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k)
    (hc : Summable c) (hle : ∀ k, a k ≤ d k - d (k + 1) + c k) : Summable a := by
  apply summable_of_sum_range_le (c := d 0 + ∑' k, ‖c k‖) ha
  intro n
  calc
    ∑ k ∈ Finset.range n, a k ≤
        ∑ k ∈ Finset.range n, (d k - d (k + 1) + c k) :=
      Finset.sum_le_sum fun k _ => hle k
    _ = (d 0 - d n) + ∑ k ∈ Finset.range n, c k := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub']
    _ ≤ d 0 + ∑ k ∈ Finset.range n, c k := by
      linarith [hd n]
    _ ≤ d 0 + ∑ k ∈ Finset.range n, ‖c k‖ := by
      simpa only [add_comm] using add_le_add_right
        (Finset.sum_le_sum (s := Finset.range n) (fun k _ => le_abs_self (c k))) (d 0)
    _ ≤ d 0 + ∑' k, ‖c k‖ := by
      gcongr
      exact (hc.norm).sum_le_tsum (Finset.range n)
        (fun k hk => norm_nonneg _)

private theorem bf_gap_inner_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x0 x1 z v0 v1 : H) :
    inner ℝ (z - x0) v0 - inner ℝ (z - x1) v1 =
      inner ℝ (x1 - x0) v0 + inner ℝ (x1 - z) (v1 - v0) := by
  simp only [inner_sub_left, inner_sub_right]
  ring

private theorem bf_gap_increment_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (mu h : ℝ)
    (alg : BackwardForwardDiscretization Phi hPhi B mu h)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    {z0 : H} (hz0 : z0 ∈ S) (k : ℕ) :
    let v := fun n => (mu : ℝ)⁻¹ • (alg.y n - alg.x n)
    let g := fun n => (Phi z0 : EReal).toReal - (Phi (alg.x n) : EReal).toReal -
      inner ℝ (z0 - alg.x n) (v n)
    g (k + 1) - g k ≤ inner ℝ (alg.x (k + 1) - z0) (v (k + 1) - v k) := by
  dsimp
  let v : ℕ → H := fun n => (mu : ℝ)⁻¹ • (alg.y n - alg.x n)
  have hv : v k ∈ ERealFunction.subdifferential Phi (alg.x k) := by
      simpa [v, alg.prox_step k] using
      (ERealFunction.scaledProximityOperator_residual_mem hPhi ⟨mu, alg.mu_pos⟩ (alg.y k))
  have hzdom : z0 ∈ ERealFunction.effectiveDomain Phi :=
    ERealFunction.SubdifferentiableAt.mem_effectiveDomain hPhi.2.nonempty
      ⟨-B z0, (hsolution z0).1 hz0⟩
  have hvnext : v (k + 1) ∈ ERealFunction.subdifferential Phi (alg.x (k + 1)) := by
    simpa [v, alg.prox_step (k + 1)] using
      (ERealFunction.scaledProximityOperator_residual_mem hPhi ⟨mu, alg.mu_pos⟩
        (alg.y (k + 1)))
  have hxnextdom : alg.x (k + 1) ∈ ERealFunction.effectiveDomain Phi :=
    ERealFunction.SubdifferentiableAt.mem_effectiveDomain hPhi.2.nonempty
      ⟨v (k + 1), hvnext⟩
  have hsub := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi hv hxnextdom
  have hinner : (Phi (alg.x k) : EReal).toReal - (Phi (alg.x (k + 1)) : EReal).toReal +
      inner ℝ (alg.x (k + 1) - alg.x k) (v k) ≤ 0 := by
    rw [real_inner_comm] at hsub
    linarith [hsub]
  have hid := bf_gap_inner_identity (alg.x k) (alg.x (k + 1)) z0 (v k) (v (k + 1))
  linarith

private theorem bf_discrete_source55
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (mu h beta : ℝ) (hmu : 0 < mu) (hh : 0 < h) (A0 A1 : ℝ)
    (dx dy bx bz xz q : H)
    (h51 : A1 - A0 + (1 / mu) * ‖dx‖ ^ 2 + h * inner ℝ (bx - bz) xz +
      h * inner ℝ xz q ≤ (1 / mu) * inner ℝ dx dy)
    (hcoco : beta * ‖bx - bz‖ ^ 2 ≤ inner ℝ (bx - bz) xz)
    (hmono : 0 ≤ inner ℝ xz q) :
    A1 - A0 + (1 / (2 * mu)) * ‖dx‖ ^ 2 + h * beta * ‖bx - bz‖ ^ 2 ≤
      (1 / (2 * mu)) * ‖dy‖ ^ 2 := by
  have hinner : inner ℝ dx dy ≤ (‖dx‖ ^ 2 + ‖dy‖ ^ 2) / 2 := by
    have habs : inner ℝ dx dy ≤ ‖dx‖ * ‖dy‖ :=
      (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    nlinarith [sq_nonneg (‖dx‖ - ‖dy‖)]
  have hcoh := mul_le_mul_of_nonneg_left hcoco hh.le
  have hmoh : 0 ≤ h * inner ℝ xz q := mul_nonneg hh.le hmono
  have hinner' := mul_le_mul_of_nonneg_left hinner
    (one_div_pos.mpr hmu).le
  have hcoef : 1 / (2 * mu) = (1 / mu) / 2 := by
    field_simp [hmu.ne']
  rw [hcoef]
  have hmain : A1 - A0 + (1 / mu) * ‖dx‖ ^ 2 +
      h * beta * ‖bx - bz‖ ^ 2 ≤ (1 / mu) * inner ℝ dx dy := by
    linarith [h51, hcoh, hmoh]
  nlinarith [hmain, hinner']

private theorem bf_discrete_source55_half
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (mu h beta : ℝ) (hmu : 0 < mu) (hh : 0 < h) (A0 A1 : ℝ)
    (dx dy bx bz xz q : H)
    (h51 : A1 - A0 + (1 / (2 * mu)) * ‖dx‖ ^ 2 + h * inner ℝ (bx - bz) xz +
      h * inner ℝ xz q ≤ (1 / mu) * inner ℝ dx dy)
    (hcoco : beta * ‖bx - bz‖ ^ 2 ≤ inner ℝ (bx - bz) xz)
    (hmono : 0 ≤ inner ℝ xz q) :
    A1 - A0 + (1 / (4 * mu)) * ‖dx‖ ^ 2 + h * beta * ‖bx - bz‖ ^ 2 ≤
      (1 / mu) * ‖dy‖ ^ 2 := by
  have hinner : inner ℝ dx dy ≤ ‖dx‖ ^ 2 / 4 + ‖dy‖ ^ 2 := by
    have habs : inner ℝ dx dy ≤ ‖dx‖ * ‖dy‖ :=
      (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    nlinarith [sq_nonneg (‖dx‖ - 2 * ‖dy‖)]
  have hcoh := mul_le_mul_of_nonneg_left hcoco hh.le
  have hmoh : 0 ≤ h * inner ℝ xz q := mul_nonneg hh.le hmono
  have hinner' := mul_le_mul_of_nonneg_left hinner
    (one_div_pos.mpr hmu).le
  have hmain : A1 - A0 + (1 / (2 * mu)) * ‖dx‖ ^ 2 +
      h * beta * ‖bx - bz‖ ^ 2 ≤ (1 / mu) * inner ℝ dx dy := by
    linarith [h51, hcoh, hmoh]
  have hcoef : 1 / (4 * mu) = (1 / mu) / 4 := by
    field_simp [hmu.ne']
  have hinner'' : (1 / mu) * inner ℝ dx dy ≤
      (1 / (4 * mu)) * ‖dx‖ ^ 2 + (1 / mu) * ‖dy‖ ^ 2 := by
    rw [hcoef]
    convert hinner' using 1; ring
  have hcoef2 : 1 / (2 * mu) = 2 * (1 / (4 * mu)) := by
    field_simp [hmu.ne']
    norm_num
  rw [hcoef2] at hmain
  linarith [hmain, hinner'']

private theorem bf_discrete_source51
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (mu h : ℝ)
    (alg : BackwardForwardDiscretization Phi hPhi B mu h)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    {z0 : H} (hz0 : z0 ∈ S) (k : ℕ) :
    let v := fun n => (mu : ℝ)⁻¹ • (alg.y n - alg.x n)
    let g := fun n => (Phi z0 : EReal).toReal - (Phi (alg.x n) : EReal).toReal -
      inner ℝ (z0 - alg.x n) (v n)
    let A := fun n => (1 / (2 * mu)) * ‖alg.x n - z0‖ ^ 2 + g n
    A (k + 1) - A k + (1 / (2 * mu)) * ‖alg.x (k + 1) - alg.x k‖ ^ 2 +
      h * inner ℝ (B (alg.x k) - B z0) (alg.x k - z0) +
      h * inner ℝ (alg.x k - z0) (v k + B z0) ≤
      (1 / mu) * inner ℝ (alg.x (k + 1) - alg.x k)
    (alg.y (k + 1) - alg.y k) := by
  dsimp
  let v : ℕ → H := fun n => (mu : ℝ)⁻¹ • (alg.y n - alg.x n)
  let g : ℕ → ℝ := fun n => (Phi z0 : EReal).toReal - (Phi (alg.x n) : EReal).toReal -
      inner ℝ (z0 - alg.x n) (v n)
  let A : ℕ → ℝ := fun n => (1 / (2 * mu)) * ‖alg.x n - z0‖ ^ 2 + g n
  have hgap := bf_gap_increment_le Phi hPhi S B mu h alg hsolution hz0 k
  have hres : alg.y k - alg.x k = mu • v k := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ alg.mu_pos.ne', one_smul]
  have hyinc : alg.y (k + 1) - alg.y k =
      h • ((alg.x k - alg.y k) - mu • B (alg.x k)) := by
    rw [alg.equation_step k]
    module
  have hnorm : ‖alg.x (k + 1) - z0‖ ^ 2 - ‖alg.x k - z0‖ ^ 2 =
      ‖alg.x (k + 1) - alg.x k‖ ^ 2 +
        2 * inner ℝ (alg.x (k + 1) - alg.x k) (alg.x k - z0) := by
    rw [show alg.x (k + 1) - z0 = (alg.x (k + 1) - alg.x k) + (alg.x k - z0) by abel]
    rw [norm_add_sq_real]
    ring
  have hvdiff : v (k + 1) - v k = (mu : ℝ)⁻¹ •
      ((alg.y (k + 1) - alg.y k) - (alg.x (k + 1) - alg.x k)) := by
    dsimp [v]
    rw [smul_sub, smul_sub]
    module
  have hA : A (k + 1) - A k =
      (1 / (2 * mu)) * (‖alg.x (k + 1) - z0‖ ^ 2 - ‖alg.x k - z0‖ ^ 2) +
        (g (k + 1) - g k) := by ring
  dsimp [v, g] at hgap
  have hinner : inner ℝ (alg.x (k + 1) - z0) (v (k + 1) - v k) =
      (1 / mu) * inner ℝ (alg.x (k + 1) - z0)
        ((alg.y (k + 1) - alg.y k) - (alg.x (k + 1) - alg.x k)) := by
    rw [hvdiff]
    simp only [real_inner_smul_right]
    ring
  have hstep : (1 / mu) * inner ℝ (alg.x k - z0)
      (alg.y (k + 1) - alg.y k) =
      - h * inner ℝ (B (alg.x k) - B z0) (alg.x k - z0) -
        h * inner ℝ (alg.x k - z0) (v k + B z0) := by
    rw [hyinc]
    rw [show alg.x k - alg.y k = -(mu • v k) by rw [← hres, neg_sub]]
    simp only [smul_sub, smul_neg, smul_smul, real_inner_smul_right,
      inner_sub_right, inner_add_right, inner_neg_right]
    field_simp [alg.mu_pos.ne']
    simp only [inner_sub_left, real_inner_comm]
    ring
  have hstep' : (1 / mu) * inner ℝ (alg.x k - z0)
      (alg.y (k + 1) - alg.y k) =
      - h * inner ℝ (B (alg.x k) - B z0) (alg.x k - z0) -
        h * inner ℝ (alg.x k - z0)
          ((mu : ℝ)⁻¹ • (alg.y k - alg.x k) + B z0) := by
    simpa [v] using hstep
  have hgap' :
      (g (k + 1) - g k) ≤ (1 / mu) * inner ℝ (alg.x (k + 1) - z0)
        ((alg.y (k + 1) - alg.y k) - (alg.x (k + 1) - alg.x k)) := by
    rw [hvdiff] at hgap
    dsimp [g, v]
    convert hgap using 1;
      simp only [real_inner_smul_right];
      field_simp [alg.mu_pos.ne']
  rw [hA, hnorm]
  have hdecomp :
      (1 / (2 * mu)) *
          (‖alg.x (k + 1) - alg.x k‖ ^ 2 +
            2 * inner ℝ (alg.x (k + 1) - alg.x k) (alg.x k - z0)) +
        (g (k + 1) - g k) + (1 / (2 * mu)) * ‖alg.x (k + 1) - alg.x k‖ ^ 2 +
        h * inner ℝ (B (alg.x k) - B z0) (alg.x k - z0) +
        h * inner ℝ (alg.x k - z0)
          ((mu : ℝ)⁻¹ • (alg.y k - alg.x k) + B z0) -
        (1 / mu) * inner ℝ (alg.x (k + 1) - alg.x k)
          (alg.y (k + 1) - alg.y k) =
      (g (k + 1) - g k) -
        (1 / mu) * inner ℝ (alg.x (k + 1) - z0)
          ((alg.y (k + 1) - alg.y k) -
            (alg.x (k + 1) - alg.x k)) +
        (1 / mu) * inner ℝ (alg.x k - z0)
          (alg.y (k + 1) - alg.y k) +
        h * inner ℝ (B (alg.x k) - B z0) (alg.x k - z0) +
        h * inner ℝ (alg.x k - z0)
          ((mu : ℝ)⁻¹ • (alg.y k - alg.x k) + B z0) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm,
      real_inner_self_eq_norm_sq]
    ring_nf
  have hnonpos :
      (1 / (2 * mu)) * (‖alg.x (k + 1) - alg.x k‖ ^ 2 +
          2 * inner ℝ (alg.x (k + 1) - alg.x k) (alg.x k - z0)) +
        (g (k + 1) - g k) + (1 / (2 * mu)) * ‖alg.x (k + 1) - alg.x k‖ ^ 2 +
        h * inner ℝ (B (alg.x k) - B z0) (alg.x k - z0) +
        h * inner ℝ (alg.x k - z0)
          ((mu : ℝ)⁻¹ • (alg.y k - alg.x k) + B z0) -
        (1 / mu) * inner ℝ (alg.x (k + 1) - alg.x k)
          (alg.y (k + 1) - alg.y k) ≤ 0 := by
    rw [hdecomp]
    linarith [hgap', hstep']
  exact sub_nonpos.mp hnonpos

/-- Theorem 3.1 for a sequence generated by (BF) under Hypothesis H. -/
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
      Tendsto (fun k ↦ alg.y k - alg.x k) atTop (nhds (ybar - xbar)) := by
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

end AbbasDynamical2015
