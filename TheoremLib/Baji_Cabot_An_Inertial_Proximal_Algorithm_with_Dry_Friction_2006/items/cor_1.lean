import Mathlib
import Foundation.SetValued.Basic
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_3
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.lem_1

/-!
# Corollary 2.1
Let $f: H \to \mathbb{R} \cup \{+\infty\}$ be a closed convex function satisfying
$\operatorname{dom} \partial f \neq \emptyset$ and $\inf f > -\infty$.
The operators $A$ and $B$ are supposed to be respectively defined by
$A := \partial |\cdot|^\alpha$ $(\alpha \geqslant 1)$ and $B := \partial f$.
Consider a nondecreasing sequence $(\lambda_n)$ of positive steps. Then,
the sequence $(x_n)$ defined by $(\mathcal{A})$ satisfies
$|(x_{n+2} - x_{n+1}) / \lambda_n| \in \ell^\alpha$.
-/
open SetValuedOperator
open scoped Topology
open scoped Pointwise
open Filter
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- Corollary 2.1: the scaled difference sequence is in ℓ^α. -/
theorem cor_2_1 (f : H → ℝ) (α : ℝ) (hα : α ≥ 1) (A : SetValuedOperator H H)
    (hA : ∀ x, A x = {v | ∀ y, (fun (z : H) => ‖z‖^α) y ≥ (fun (z : H) => ‖z‖^α) x + inner ℝ v (y - x)})
    (B : SetValuedOperator H H) (hB : ∀ x, B x = {v | ∀ y, f y ≥ f x + inner ℝ v (y - x)})
    (hf_conv : ConvexOn ℝ Set.univ f) (hf_lsc : LowerSemicontinuous f)
    (hdom : (SetValuedOperator.dom B).Nonempty)
    (hinf : ∃ m, ∀ x, f x ≥ m) (lam : ℕ → ℝ) (hlam_pos : ∀ n, lam n > 0)
    (hlam_nondec : ∀ n, lam n ≤ lam (n+1)) (x : ℕ → H) (halg : AlgorithmA A B x lam) :
    ∃ (C : ℝ), Tendsto (fun (N : ℕ) => (Finset.range (N+1)).sum (fun n =>
      ‖(lam n)⁻¹ • (x (n+2) - x (n+1))‖^α)) atTop (𝓝 C) := by
  classical
  let vel : ℕ → H := fun n => (lam n)⁻¹ • (x (n+2) - x (n+1))
  let term : ℕ → ℝ := fun n => ‖vel n‖^α
  let weighted : ℕ → ℝ := fun n => lam n * term n
  let energy : ℕ → ℝ := fun n =>
    ((2 * (lam n)^2)⁻¹) * ‖x (n+1) - x n‖^2 + f (x (n+1))
  have hterm_nonneg : ∀ n, 0 ≤ term n := by
    intro n
    exact Real.rpow_nonneg (norm_nonneg _) α
  have henergy_drop : ∀ n, energy (n+1) - energy n ≤ -weighted n := by
    intro n
    let d₁ : H := x (n+1) - x n
    let d₂ : H := x (n+2) - x (n+1)
    let v : H := (lam n)⁻¹ • d₂
    let acc : H := ((lam n)^2)⁻¹ • (x (n+2) - 2 • x (n+1) + x n)
    have hstep : (0 : H) ∈ ({acc} : Set H) + A v + B (x (n+2)) := by
      simpa [AlgorithmA, acc, v, d₂] using halg.step n
    rw [Set.mem_add] at hstep
    rcases hstep with ⟨p, hp, b, hb, hpbeq⟩
    rw [Set.mem_add] at hp
    rcases hp with ⟨a, ha, y, hyA, hp_eq⟩
    rw [Set.mem_singleton_iff] at ha
    subst a
    have hsum_zero : acc + y + b = 0 := by
      simpa [hp_eq] using hpbeq
    have hbsub : ∀ t : H, f t ≥ f (x (n+2)) + inner ℝ b (t - x (n+2)) := by
      have hb' : b ∈ {v | ∀ t : H, f t ≥ f (x (n+2)) + inner ℝ v (t - x (n+2))} := by
        simpa [hB] using hb
      simpa using hb'
    have hf_diff : f (x (n+2)) - f (x (n+1)) ≤ inner ℝ b d₂ := by
      have h := hbsub (x (n+1))
      have hinner : inner ℝ b (x (n+1) - x (n+2)) = - inner ℝ b d₂ := by
        rw [show x (n+1) - x (n+2) = -(x (n+2) - x (n+1)) by abel]
        rw [inner_neg_right]
      linarith
    have hcoeff :
        (2 * (lam (n+1))^2)⁻¹ * ‖d₂‖^2 ≤
          (2 * (lam n)^2)⁻¹ * ‖d₂‖^2 := by
      have hln : 0 < lam n := hlam_pos n
      have hln1 : 0 < lam (n+1) := lt_of_lt_of_le hln (hlam_nondec n)
      have habs : |lam n| ≤ |lam (n+1)| := by
        simpa [abs_of_pos hln, abs_of_pos hln1] using hlam_nondec n
      have hden : 2 * (lam n)^2 ≤ 2 * (lam (n+1))^2 := by
        nlinarith [sq_le_sq.mpr habs]
      have hdenpos : 0 < 2 * (lam n)^2 := by positivity
      have hinv : (2 * (lam (n+1))^2)⁻¹ ≤ (2 * (lam n)^2)⁻¹ := by
        exact inv_anti₀ hdenpos hden
      exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    have henergy_le :
        energy (n+1) - energy n ≤
          (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) + inner ℝ b d₂ := by
      dsimp [energy, d₁, d₂]
      linarith
    have hnorm :
        ‖d₂‖^2 - ‖d₁‖^2 ≤ 2 * inner ℝ (d₂ - d₁) d₂ := by
      have hnon : 0 ≤ ‖d₂ - d₁‖^2 := sq_nonneg _
      rw [norm_sub_sq_real] at hnon
      rw [real_inner_comm d₁ d₂] at hnon
      rw [inner_sub_left]
      rw [real_inner_self_eq_norm_sq]
      nlinarith [hnon]
    have hnorm_scaled :
        (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) ≤
          ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
      have hscale_nonneg : 0 ≤ (2 * (lam n)^2)⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_left hnorm hscale_nonneg
      have hscale_eq :
          (2 * (lam n)^2)⁻¹ * (2 * inner ℝ (d₂ - d₁) d₂) =
            ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
        field_simp [ne_of_gt (hlam_pos n)]
      calc
        (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2)
            ≤ (2 * (lam n)^2)⁻¹ * (2 * inner ℝ (d₂ - d₁) d₂) := hmul
        _ = ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := hscale_eq
    have hacc_eq : acc = ((lam n)^2)⁻¹ • (d₂ - d₁) := by
      dsimp [acc, d₁, d₂]
      congr 1
      abel
    have hacc_inner :
        inner ℝ acc d₂ = ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
      rw [hacc_eq, inner_smul_left]
      rfl
    have henergy_acc :
        energy (n+1) - energy n ≤ inner ℝ (acc + b) d₂ := by
      calc
        energy (n+1) - energy n
            ≤ (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) + inner ℝ b d₂ := henergy_le
        _ ≤ ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ + inner ℝ b d₂ := by
          linarith
        _ = inner ℝ (acc + b) d₂ := by
          rw [← hacc_inner, inner_add_left]
    have haccb : acc + b = -y := by
      calc
        acc + b = (acc + y + b) - y := by abel
        _ = 0 - y := by rw [hsum_zero]
        _ = -y := by simp
    have henergy_y : energy (n+1) - energy n ≤ - inner ℝ y d₂ := by
      calc
        energy (n+1) - energy n ≤ inner ℝ (acc + b) d₂ := henergy_acc
        _ = inner ℝ (-y) d₂ := by rw [haccb]
        _ = - inner ℝ y d₂ := by rw [inner_neg_left]
    have hd₂_eq : d₂ = (lam n) • v := by
      dsimp [v]
      rw [smul_smul]
      field_simp [ne_of_gt (hlam_pos n)]
      simp
    have hinner_d₂ : inner ℝ y d₂ = (lam n) * inner ℝ y v := by
      rw [hd₂_eq, inner_smul_right]
    have hsubA : ∀ t : H, ‖t‖^α ≥ ‖v‖^α + inner ℝ y (t - v) := by
      have hy' : y ∈ {u | ∀ t : H, ‖t‖^α ≥ ‖v‖^α + inner ℝ u (t - v)} := by
        simpa [hA] using hyA
      simpa using hy'
    have hinner_ge : ‖v‖^α ≤ inner ℝ y v := by
      have h := hsubA 0
      have hα_pos : 0 < α := lt_of_lt_of_le zero_lt_one hα
      have hzero : ‖(0 : H)‖^α = 0 := by
        simp [Real.zero_rpow, ne_of_gt hα_pos]
      rw [hzero] at h
      rw [zero_sub, inner_neg_right] at h
      linarith
    have hfinal : -(lam n) * inner ℝ y v ≤ -(lam n) * ‖v‖^α := by
      nlinarith [hlam_pos n, hinner_ge]
    calc
      energy (n+1) - energy n ≤ - inner ℝ y d₂ := henergy_y
      _ = -(lam n) * inner ℝ y v := by
        rw [hinner_d₂]
        ring
      _ ≤ -(lam n) * ‖v‖^α := hfinal
      _ = -weighted n := by
        simp [weighted, term, vel, v, d₂]
  rcases hinf with ⟨m, hm⟩
  have hweighted_le_energy : ∀ n, weighted n ≤ energy n - energy (n+1) := by
    intro n
    have h := henergy_drop n
    linarith
  have henergy_lower : ∀ N, m ≤ energy N := by
    intro N
    have hf_lower : m ≤ f (x (N+1)) := hm (x (N+1))
    have hcoeff_nonneg : 0 ≤ (2 * (lam N)^2)⁻¹ := by positivity
    have hnorm_nonneg : 0 ≤ ‖x (N+1) - x N‖^2 := sq_nonneg _
    have hprod_nonneg : 0 ≤ (2 * (lam N)^2)⁻¹ * ‖x (N+1) - x N‖^2 :=
      mul_nonneg hcoeff_nonneg hnorm_nonneg
    dsimp [energy]
    nlinarith
  have hweighted_sum_bound :
      ∀ N, (Finset.range N).sum weighted ≤ energy 0 - m := by
    intro N
    have hsum_le_energy :
        (Finset.range N).sum weighted ≤
          (Finset.range N).sum (fun n => energy n - energy (n+1)) := by
      exact Finset.sum_le_sum (fun n _ => hweighted_le_energy n)
    have htel :
        (Finset.range N).sum (fun n => energy n - energy (n+1)) =
          energy 0 - energy N := by
      exact Finset.sum_range_sub' energy N
    calc
      (Finset.range N).sum weighted
          ≤ (Finset.range N).sum (fun n => energy n - energy (n+1)) := hsum_le_energy
      _ = energy 0 - energy N := htel
      _ ≤ energy 0 - m := by
        linarith [henergy_lower N]
  have hlam0_le : ∀ n, lam 0 ≤ lam n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact le_trans ih (hlam_nondec n)
  have hterm_le_scaled : ∀ n, term n ≤ (lam 0)⁻¹ * weighted n := by
    intro n
    have h0pos : 0 < lam 0 := hlam_pos 0
    have hscale_nonneg : 0 ≤ (lam 0)⁻¹ := inv_nonneg.mpr (le_of_lt h0pos)
    have hmul := mul_le_mul_of_nonneg_right (hlam0_le n) (hterm_nonneg n)
    calc
      term n = (lam 0)⁻¹ * (lam 0 * term n) := by
        field_simp [ne_of_gt h0pos]
      _ ≤ (lam 0)⁻¹ * (lam n * term n) := by
        exact mul_le_mul_of_nonneg_left hmul hscale_nonneg
      _ = (lam 0)⁻¹ * weighted n := by
        rfl
  have hsum_bound :
      ∀ N, (Finset.range N).sum term ≤ (lam 0)⁻¹ * (energy 0 - m) := by
    intro N
    have hsum_scaled :
        (Finset.range N).sum term ≤
          (Finset.range N).sum (fun n => (lam 0)⁻¹ * weighted n) := by
      exact Finset.sum_le_sum (fun n _ => hterm_le_scaled n)
    have hscale_nonneg : 0 ≤ (lam 0)⁻¹ := inv_nonneg.mpr (le_of_lt (hlam_pos 0))
    calc
      (Finset.range N).sum term
          ≤ (Finset.range N).sum (fun n => (lam 0)⁻¹ * weighted n) := hsum_scaled
      _ = (lam 0)⁻¹ * (Finset.range N).sum weighted := by
        simp [Finset.mul_sum]
      _ ≤ (lam 0)⁻¹ * (energy 0 - m) := by
        exact mul_le_mul_of_nonneg_left (hweighted_sum_bound N) hscale_nonneg
  have hsummable : Summable term := summable_of_sum_range_le hterm_nonneg hsum_bound
  refine ⟨∑' n, term n, ?_⟩
  have ht := hsummable.hasSum.tendsto_sum_nat
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id
  simpa [term, vel] using ht.comp hshift
