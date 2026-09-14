import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.algo_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_thm_1
import Foundation.Hilbert.Basic

open ERealFunction

private theorem second_pp_beta_identity_pos_lower {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : H → ℝ} (alg : SecondProximalPointAlgorithm f) :
    (∀ i : ℕ, 1 ≤ i → alg.beta (i + 1) * (alg.beta (i + 1) - 1) = alg.beta i ^ 2) ∧
      (∀ i : ℕ, 1 ≤ i → 0 < alg.beta i) ∧
        (∀ i : ℕ, 1 ≤ i → (i + 1 : ℝ) / 2 ≤ alg.beta i) := by
  have hstep_id : ∀ i : ℕ, 1 ≤ i →
      alg.beta (i + 1) * (alg.beta (i + 1) - 1) = alg.beta i ^ 2 := by
    intro i hi
    rw [alg.beta_step i hi]
    have hrad : 0 ≤ 1 + 4 * alg.beta i ^ 2 := by nlinarith [sq_nonneg (alg.beta i)]
    have hs : Real.sqrt (1 + 4 * alg.beta i ^ 2) ^ 2 = 1 + 4 * alg.beta i ^ 2 :=
      Real.sq_sqrt hrad
    nlinarith [Real.sqrt_nonneg (1 + 4 * alg.beta i ^ 2)]
  have hpos : ∀ i : ℕ, 1 ≤ i → 0 < alg.beta i := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => simp [alg.beta_initial]
    | succ i hi _ =>
      rw [alg.beta_step i hi]
      have : 0 ≤ Real.sqrt (1 + 4 * alg.beta i ^ 2) := Real.sqrt_nonneg _
      nlinarith
  refine ⟨hstep_id, hpos, ?_⟩
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => norm_num [alg.beta_initial]
  | succ i hi ih =>
    rw [alg.beta_step i hi]
    have hs : 0 ≤ Real.sqrt (1 + 4 * alg.beta i ^ 2) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (1 + 4 * alg.beta i ^ 2) ^ 2 = 1 + 4 * alg.beta i ^ 2 :=
      Real.sq_sqrt (by nlinarith [sq_nonneg (alg.beta i)])
    have hinc : alg.beta i + 1 / 2 ≤ (1 + Real.sqrt (1 + 4 * alg.beta i ^ 2)) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt (1 + 4 * alg.beta i ^ 2) - 2 * alg.beta i)]
    push_cast
    linarith

private theorem second_pp_theta_shift {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → ℝ} (alg : SecondProximalPointAlgorithm f) (z : H)
    (hbeta_id : ∀ i : ℕ, 1 ≤ i →
      alg.beta (i + 1) * (alg.beta (i + 1) - 1) = alg.beta i ^ 2)
    (hbeta_pos : ∀ i : ℕ, 1 ≤ i → 0 < alg.beta i) (i : ℕ) (hi : 1 ≤ i) :
    alg.beta (i + 1) • (alg.x i - alg.y (i + 1)) + z - alg.x i =
      alg.beta i • (alg.x (i - 1) + alg.y i - (2 : ℝ) • alg.x i) + z - alg.x (i - 1) := by
  rw [alg.y_step i hi]
  have hne : alg.beta (i + 1) ≠ 0 := ne_of_gt (hbeta_pos (i + 1) (by omega))
  apply (smul_right_injective H hne)
  simp only [smul_sub, smul_add, smul_smul]
  field_simp [hne]
  module

private theorem sq_infDist_le_of_le_sq_dist {H : Type*} [NormedAddCommGroup H] (x : H)
    (S : Set H) (hS : S.Nonempty) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ z, z ∈ S → A ≤ ‖x - z‖ ^ 2) : A ≤ residualDistance x S ^ 2 := by
  rw [residualDistance_defined_for_nonempty (x := x) (S := S) hS]
  have hT : {r | ∃ s ∈ S, r = ‖x - s‖}.Nonempty := by
    rcases hS with ⟨z, hz⟩
    exact ⟨‖x - z‖, z, hz, rfl⟩
  have hsqrt_sq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsqrt : Real.sqrt A ≤ sInf {r | ∃ s ∈ S, r = ‖x - s‖} := by
    apply le_csInf hT
    rintro r ⟨z, hz, rfl⟩
    have hnorm : 0 ≤ ‖x - z‖ := norm_nonneg _
    have hsqrt_nonneg : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
    nlinarith [h z hz]
  have hsqrt_nonneg : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  nlinarith

private theorem second_pp_supporting_inequality {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : H → ℝ} (alg : SecondProximalPointAlgorithm f)
    (hconvex : ConvexOn ℝ Set.univ f) (j : ℕ) (hj : 1 ≤ j) (u : H) :
    f (alg.x j) + inner ℝ ((1 / alg.lam j) • (alg.y j - alg.x j)) (u - alg.x j) ≤ f u := by
  rcases alg.proximal_step j hj with ⟨hlam, hprox⟩
  change IsMinOn (fun z => f z + ‖z - alg.y j‖ ^ 2 / (2 * alg.lam j)) Set.univ (alg.x j) at hprox
  have hsub := proximal_optimality_condition f hlam hconvex hprox
  rw [mem_convexSubdifferential_iff] at hsub
  exact hsub u

private theorem second_pp_polarization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (a b : H) :
    inner ℝ a b = (‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / 4 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

private theorem second_pp_potential_step {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : H → ℝ} (alg : SecondProximalPointAlgorithm f) (z : H)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hbeta_id : ∀ i : ℕ, 1 ≤ i →
      alg.beta (i + 1) * (alg.beta (i + 1) - 1) = alg.beta i ^ 2)
    (hbeta_pos : ∀ i : ℕ, 1 ≤ i → 0 < alg.beta i) (i : ℕ) (hi : 1 ≤ i) :
    let W : ℕ → ℝ := fun n => f (alg.x n) - f z
    let theta : ℕ → H := fun n => alg.beta (n + 1) • (alg.x n - alg.y (n + 1)) + z - alg.x n
    alg.beta (i + 1) ^ 2 * W (i + 1) + ‖theta (i + 1)‖ ^ 2 / (4 * alg.lam (i + 1)) ≤
      alg.beta i ^ 2 * W i + ‖theta i‖ ^ 2 / (4 * alg.lam i) := by
  dsimp
  have hs1 := second_pp_supporting_inequality alg hconvex (i + 1) (by omega) (alg.x i)
  have hs2 := second_pp_supporting_inequality alg hconvex (i + 1) (by omega) z
  have hb : alg.beta (i + 1) ^ 2 = alg.beta i ^ 2 + alg.beta (i + 1) := by
    nlinarith [hbeta_id i hi]
  have hscaled1 := mul_le_mul_of_nonneg_left hs1 (sq_nonneg (alg.beta i))
  have hscaled2 := mul_le_mul_of_nonneg_left hs2 (le_of_lt (hbeta_pos (i + 1) (by omega)))
  have hcore :
      alg.beta i ^ 2 * (f (alg.x i) - f z) - alg.beta (i + 1) ^ 2 * (f (alg.x (i + 1)) - f z) ≥
        (1 / alg.lam (i + 1)) * inner ℝ
          (alg.beta (i + 1) • (alg.y (i + 1) - alg.x (i + 1)))
          (alg.beta (i + 1) • (alg.x i - alg.x (i + 1)) + z - alg.x i) := by
    have htotal :
        alg.beta i ^ 2 * (f (alg.x i) - f (alg.x (i + 1))) +
            alg.beta (i + 1) * (f z - f (alg.x (i + 1))) ≥
          alg.beta i ^ 2 * inner ℝ ((1 / alg.lam (i + 1)) •
            (alg.y (i + 1) - alg.x (i + 1))) (alg.x i - alg.x (i + 1)) +
          alg.beta (i + 1) * inner ℝ ((1 / alg.lam (i + 1)) •
            (alg.y (i + 1) - alg.x (i + 1))) (z - alg.x (i + 1)) := by
      nlinarith [hscaled1, hscaled2]
    calc
      alg.beta i ^ 2 * (f (alg.x i) - f z) - alg.beta (i + 1) ^ 2 *
          (f (alg.x (i + 1)) - f z) =
          alg.beta i ^ 2 * (f (alg.x i) - f (alg.x (i + 1))) +
            alg.beta (i + 1) * (f z - f (alg.x (i + 1))) := by rw [hb]; ring
      _ ≥ alg.beta i ^ 2 * inner ℝ ((1 / alg.lam (i + 1)) •
            (alg.y (i + 1) - alg.x (i + 1))) (alg.x i - alg.x (i + 1)) +
          alg.beta (i + 1) * inner ℝ ((1 / alg.lam (i + 1)) •
            (alg.y (i + 1) - alg.x (i + 1))) (z - alg.x (i + 1)) := htotal
      _ = (1 / alg.lam (i + 1)) * inner ℝ
          (alg.beta (i + 1) • (alg.y (i + 1) - alg.x (i + 1)))
          (alg.beta (i + 1) • (alg.x i - alg.x (i + 1)) + z - alg.x i) := by
          simp only [inner_smul_left, inner_smul_right, inner_add_right, inner_sub_right]
          norm_num
          ring_nf
          have hbn : alg.beta (1 + i) ^ 2 = alg.beta i ^ 2 + alg.beta (1 + i) := by
            simpa [Nat.add_comm] using hb
          rw [hbn]
          ring
  let a : H := alg.beta (i + 1) • (alg.y (i + 1) - alg.x (i + 1))
  let b : H := alg.beta (i + 1) • (alg.x i - alg.x (i + 1)) + z - alg.x i
  have hab_add : a + b =
      alg.beta (i + 1) • (alg.x i + alg.y (i + 1) - (2 : ℝ) • alg.x (i + 1)) + z - alg.x i := by
    dsimp [a, b]
    module
  have hab_sub : a - b =
      -(alg.beta (i + 1) • (alg.x i - alg.y (i + 1)) + z - alg.x i) := by
    dsimp [a, b]
    module
  have hpolar : inner ℝ a b =
      (‖alg.beta (i + 1) • (alg.x i + alg.y (i + 1) - (2 : ℝ) • alg.x (i + 1)) + z - alg.x i‖ ^ 2 -
        ‖alg.beta (i + 1) • (alg.x i - alg.y (i + 1)) + z - alg.x i‖ ^ 2) / 4 := by
    rw [second_pp_polarization, hab_add, hab_sub, norm_neg]
  have hshift := second_pp_theta_shift alg z hbeta_id hbeta_pos (i + 1) (by omega)
  have hlam_i : 0 < alg.lam i := (alg.proximal_step i hi).1
  have hlam_succ : 0 < alg.lam (i + 1) := (alg.proximal_step (i + 1) (by omega)).1
  have hlam_le : alg.lam i ≤ alg.lam (i + 1) := by
    exact alg.lam_monotone i hi
  have hden :
      -‖alg.beta (i + 1) • (alg.x i - alg.y (i + 1)) + z - alg.x i‖ ^ 2 /
          (4 * alg.lam (i + 1)) ≥
        -‖alg.beta (i + 1) • (alg.x i - alg.y (i + 1)) + z - alg.x i‖ ^ 2 /
          (4 * alg.lam i) := by
    have hn : 0 ≤ ‖alg.beta (i + 1) • (alg.x i - alg.y (i + 1)) + z - alg.x i‖ ^ 2 := sq_nonneg _
    field_simp [ne_of_gt hlam_i, ne_of_gt hlam_succ]
    nlinarith
  have hfirst :
      alg.beta (i + 1) • (alg.x i + alg.y (i + 1) - (2 : ℝ) • alg.x (i + 1)) + z - alg.x i =
        alg.beta (i + 1 + 1) • (alg.x (i + 1) - alg.y (i + 1 + 1)) + z - alg.x (i + 1) := by
    simpa [Nat.add_assoc] using hshift.symm
  rw [hfirst] at hpolar
  change _ ≤ _
  have hpolar' :
      inner ℝ (alg.beta (i + 1) • (alg.y (i + 1) - alg.x (i + 1)))
          (alg.beta (i + 1) • (alg.x i - alg.x (i + 1)) + z - alg.x i) =
        (‖alg.beta (i + 1 + 1) • (alg.x (i + 1) - alg.y (i + 1 + 1)) + z - alg.x (i + 1)‖ ^ 2 -
          ‖alg.beta (i + 1) • (alg.x i - alg.y (i + 1)) + z - alg.x i‖ ^ 2) / 4 := by
    simpa [a, b] using hpolar
  rw [hpolar'] at hcore
  field_simp [ne_of_gt hlam_i, ne_of_gt hlam_succ] at hcore hden ⊢
  nlinarith

private theorem second_pp_initial_potential {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : H → ℝ} (alg : SecondProximalPointAlgorithm f) (z : H)
    (lam : ℝ) (hlam : 0 < lam) (hlam_initial : alg.lam 1 = lam)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hbeta_id : ∀ i : ℕ, 1 ≤ i →
      alg.beta (i + 1) * (alg.beta (i + 1) - 1) = alg.beta i ^ 2)
    (hbeta_pos : ∀ i : ℕ, 1 ≤ i → 0 < alg.beta i) :
    let theta : ℕ → H := fun n =>
      alg.beta (n + 1) • (alg.x n - alg.y (n + 1)) + z - alg.x n
    alg.beta 1 ^ 2 * (f (alg.x 1) - f z) + ‖theta 1‖ ^ 2 / (4 * alg.lam 1) ≤
      ‖alg.x 0 - z‖ ^ 2 / (4 * lam) := by
  dsimp
  have hs := second_pp_supporting_inequality alg hconvex 1 (by omega) z
  rw [hlam_initial, alg.y_initial] at hs
  have hs' : -(f (alg.x 1) - f z) ≥
      (1 / lam) * inner ℝ (alg.x 0 - alg.x 1) (z - alg.x 1) := by
    rw [inner_smul_left] at hs
    norm_num at hs
    have h : -(f (alg.x 1) - f z) ≥
        lam⁻¹ * inner ℝ (alg.x 0 - alg.x 1) (z - alg.x 1) := by
      linarith
    simpa [one_div] using h
  have hshift := second_pp_theta_shift alg z hbeta_id hbeta_pos 1 (by omega)
  rw [alg.beta_initial, alg.y_initial] at hshift
  have htheta : alg.beta (1 + 1) • (alg.x 1 - alg.y (1 + 1)) + z - alg.x 1 =
      z + alg.x 0 - (2 : ℝ) • alg.x 1 := by
    calc
      alg.beta (1 + 1) • (alg.x 1 - alg.y (1 + 1)) + z - alg.x 1 =
          (1 : ℝ) • (alg.x (1 - 1) + alg.x 0 - (2 : ℝ) • alg.x 1) + z - alg.x (1 - 1) :=
            hshift
      _ = z + alg.x 0 - (2 : ℝ) • alg.x 1 := by module
  have hpol := second_pp_polarization (alg.x 0 - alg.x 1) (z - alg.x 1)
  have hadd : alg.x 0 - alg.x 1 + (z - alg.x 1) =
      z + alg.x 0 - (2 : ℝ) • alg.x 1 := by module
  have hsub : alg.x 0 - alg.x 1 - (z - alg.x 1) = alg.x 0 - z := by module
  rw [hadd, hsub] at hpol
  rw [alg.beta_initial, hlam_initial, htheta]
  field_simp [ne_of_gt hlam] at hs' ⊢
  nlinarith

private theorem second_pp_pointwise_rate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (alg : SecondProximalPointAlgorithm f) (z : H)
    (lam : ℝ) (k : ℕ) (hk : 1 ≤ k) (hconvex : ConvexOn ℝ Set.univ f)
    (hminz : ∀ u, f z ≤ f u) (hlam : 0 < lam) (hlam_initial : alg.lam 1 = lam) :
    f (alg.x k) - f z ≤ ‖alg.x 0 - z‖ ^ 2 / (lam * (k + 1 : ℝ) ^ 2) := by
  rcases second_pp_beta_identity_pos_lower alg with ⟨hbeta_id, hbeta_pos, hbeta_lower⟩
  let W : ℕ → ℝ := fun n => f (alg.x n) - f z
  let theta : ℕ → H := fun n =>
    alg.beta (n + 1) • (alg.x n - alg.y (n + 1)) + z - alg.x n
  let C : ℝ := ‖alg.x 0 - z‖ ^ 2 / (4 * lam)
  have hpot : ∀ n, 1 ≤ n →
      alg.beta n ^ 2 * W n + ‖theta n‖ ^ 2 / (4 * alg.lam n) ≤ C := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      simpa [W, theta, C] using
        second_pp_initial_potential alg z lam hlam hlam_initial hconvex hbeta_id hbeta_pos
    | succ i hi ih =>
      have hstep := second_pp_potential_step alg z hconvex hbeta_id hbeta_pos i hi
      have hstep' :
          alg.beta (i + 1) ^ 2 * W (i + 1) + ‖theta (i + 1)‖ ^ 2 /
              (4 * alg.lam (i + 1)) ≤
            alg.beta i ^ 2 * W i + ‖theta i‖ ^ 2 / (4 * alg.lam i) := by
        simpa [W, theta, Nat.add_assoc] using hstep
      exact hstep'.trans ih
  have hpotk := hpot k hk
  have hlamk : 0 < alg.lam k := (alg.proximal_step k hk).1
  have htheta_nonneg : 0 ≤ ‖theta k‖ ^ 2 / (4 * alg.lam k) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have hweighted : alg.beta k ^ 2 * W k ≤ C := by nlinarith
  have hW : 0 ≤ W k := sub_nonneg.mpr (hminz _)
  have hbeta_sq : (k + 1 : ℝ) ^ 2 / 4 ≤ alg.beta k ^ 2 := by
    have hbeta := hbeta_lower k hk
    have hbeta_posk := hbeta_pos k hk
    have hleft := mul_le_mul_of_nonneg_left hbeta
      (by positivity : 0 ≤ (k + 1 : ℝ) / 2)
    have hright := mul_le_mul_of_nonneg_right hbeta hbeta_posk.le
    calc
      (k + 1 : ℝ) ^ 2 / 4 = ((k + 1 : ℝ) / 2) * ((k + 1 : ℝ) / 2) := by ring
      _ ≤ ((k + 1 : ℝ) / 2) * alg.beta k := hleft
      _ ≤ alg.beta k * alg.beta k := hright
      _ = alg.beta k ^ 2 := by ring
  have hscale := mul_le_mul_of_nonneg_right hbeta_sq hW
  have hquarter : ((k + 1 : ℝ) ^ 2 / 4) * W k ≤
      ‖alg.x 0 - z‖ ^ 2 / (4 * lam) := hscale.trans hweighted
  have hkplus : 0 < (k + 1 : ℝ) := by exact_mod_cast Nat.succ_pos k
  have hD : 0 < lam * (k + 1 : ℝ) ^ 2 := by positivity
  change W k ≤ _
  field_simp [ne_of_gt hlam, ne_of_gt hD] at hquarter ⊢
  nlinarith

/-- Theorem 6.1: the second proximal point algorithm has the `1/(k+1)^2` rate. -/
theorem second_proximal_point_rate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (alg : SecondProximalPointAlgorithm f) (xstar : H) (lam : ℝ) (k : ℕ)
    (hk : 1 ≤ k)
    (hproper : ERealFunction.IsProper (fun z => (f z : EReal)))
    (hlsc : LowerSemicontinuous f) (hconvex : ConvexOn ℝ Set.univ f)
    (hmin : ∀ z, f xstar ≤ f z) (hlam : 0 < lam) (hlam_initial : alg.lam 1 = lam) :
    f (alg.x k) - f xstar ≤ residualDistance (alg.x 0) {z | f z = f xstar} ^ 2 /
      (lam * (k + 1 : ℝ) ^ 2) := by
  have hW_nonneg : 0 ≤ f (alg.x k) - f xstar := sub_nonneg.mpr (hmin _)
  let S : Set H := {z | f z = f xstar}
  let D : ℝ := lam * (k + 1 : ℝ) ^ 2
  have hS : S.Nonempty := ⟨xstar, rfl⟩
  have hD : 0 < D := by dsimp [D]; positivity
  let A : ℝ := D * (f (alg.x k) - f xstar)
  have hA : 0 ≤ A := mul_nonneg hD.le hW_nonneg
  have hpoint : ∀ z, z ∈ S → A ≤ ‖alg.x 0 - z‖ ^ 2 := by
    intro z hz
    have hz' : f z = f xstar := hz
    have hminz : ∀ u, f z ≤ f u := by
      intro u
      rw [hz']
      exact hmin u
    have hrate := second_pp_pointwise_rate f alg z lam k hk hconvex hminz hlam hlam_initial
    rw [hz'] at hrate
    apply (le_div_iff₀ hD).mp at hrate
    simpa [A, D, mul_comm, mul_left_comm, mul_assoc] using hrate
  have hinf := sq_infDist_le_of_le_sq_dist (alg.x 0) S hS A hA hpoint
  apply (le_div_iff₀ hD).2
  simpa [A, D, S, mul_comm, mul_left_comm, mul_assoc] using hinf
