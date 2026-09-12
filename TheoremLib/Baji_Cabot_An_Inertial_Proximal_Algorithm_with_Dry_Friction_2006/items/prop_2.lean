import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.SetValued.Basic
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_3
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_4
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_5
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_1

/-!
# Proposition 2.2
Let $A: H \Rightarrow H$ be a maximal monotone operator such that
$\operatorname{dom} A = H$ and $0 \in A(0)$. The operator $B$ is supposed to be
equal to $\partial f$ for a closed convex function
$f: H \to \mathbb{R} \cup \{+\infty\}$ satisfying $\operatorname{dom} \partial f \neq \emptyset$
and $\inf f > -\infty$. The positive sequence $(\lambda_n)$ is assumed to be
nondecreasing. Then, the sequence $(x_n)$ defined by algorithm $(\mathcal{A})$ satisfies:
(i) $E_{n+1} - E_n \leqslant -\lambda_n \Phi_A((x_{n+2} - x_{n+1}) / \lambda_n)$,
where the sequence $(E_n)$ and the function $\Phi_A$ are defined by (2) and (3),
respectively.
(ii) $\sum_{n=0}^{+\infty} \lambda_n \Phi_A((x_{n+2} - x_{n+1}) / \lambda_n) < +\infty$.
-/
open SetValuedOperator
open Filter
open scoped Topology
open scoped Pointwise
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- Proposition 2.2: monotone decrease of the energy sequence and summability. -/
theorem prop_2_2 (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ)
    (hAzero : (0 : H) ∈ A (0 : H)) (f : H → EReal)
    (hf_conv : ∀ x y : H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y)
    (hf_lsc : LowerSemicontinuous f)
    (hB_eq_subderiv : ∀ x, B x = {v | ∀ y, f y ≥ f x + (inner ℝ v (y - x) : EReal)})
    (hdom_subderiv : (SetValuedOperator.dom B).Nonempty) (hinf : ∃ m : ℝ, ∀ x, (m : EReal) ≤ f x)
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, lam n > 0) (hlam_nondec : ∀ n, lam n ≤ lam (n+1))
    (x : ℕ → H) (halg : AlgorithmA A B x lam)
    (hx1_dom : x 1 ∈ ERealFunction.dom f) :
    (∀ n, energySeq x lam f (n+1) - energySeq x lam f n ≤
      (-(lam n) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1))) : EReal)) ∧
    (∃ (S : ℝ), Tendsto (fun (N : ℕ) => (Finset.range (N+1)).sum (fun n => (lam n) *
      PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1))))) atTop (𝓝 S)) := by
  classical
  have hmono : IsMonotone A := hA.1
  rcases hinf with ⟨m, hm⟩
  let energyR : ℕ → ℝ := fun n =>
    ((2 * (lam n)^2)⁻¹) * ‖x (n+1) - x n‖^2 + (f (x (n+1))).toReal
  have hf_iter_ne_bot : ∀ n, f (x n) ≠ ⊥ := by
    intro n hbot
    have hle := hm (x n)
    rw [hbot] at hle
    simp at hle
  have hx1_ne_top : f (x 1) ≠ ⊤ := by
    have hx1_lt : f (x 1) < ⊤ := by
      simpa [ERealFunction.dom] using hx1_dom
    exact ne_of_lt hx1_lt
  have hf_iter_ne_top : ∀ n, f (x (n+1)) ≠ ⊤ := by
    intro n
    cases n with
    | zero =>
        simpa using hx1_ne_top
    | succ k =>
        let d₂ : H := x (k+2) - x (k+1)
        let v : H := (lam k)⁻¹ • d₂
        let acc : H := ((lam k)^2)⁻¹ • (x (k+2) - 2 • x (k+1) + x k)
        have hstep : (0 : H) ∈ ({acc} : Set H) + A v + B (x (k+2)) := by
          simpa [AlgorithmA, acc, v, d₂] using halg.step k
        rw [Set.mem_add] at hstep
        rcases hstep with ⟨p, hp, b, hb, hpbeq⟩
        have hbsub : ∀ t : H, f t ≥ f (x (k+2)) + inner ℝ b (t - x (k+2)) := by
          have hb' :
              b ∈ {v | ∀ t : H, f t ≥ f (x (k+2)) + inner ℝ v (t - x (k+2))} := by
            simpa [hB_eq_subderiv] using hb
          simpa using hb'
        intro hx_top
        have h := hbsub (x 1)
        have htop_le : (⊤ : EReal) ≤ f (x 1) := by
          simpa [hx_top] using h
        exact hx1_ne_top (top_le_iff.mp htop_le)
  have henergySeq_eq : ∀ n, energySeq x lam f n = (energyR n : EReal) := by
    intro n
    dsimp [energySeq, energyR]
    rw [← EReal.coe_toReal (hf_iter_ne_top n) (hf_iter_ne_bot (n+1))]
    simp
  have hPhi_nonneg :
      ∀ z : H, 0 ≤ PhiA A z := by
    intro z
    have hAz : (A z).Nonempty := by
      have hzdom : z ∈ A.dom := by simp [hdomA]
      simpa [SetValuedOperator.mem_dom_iff] using hzdom
    rw [PhiA]
    apply le_sInf
    rintro _ ⟨y, hy, rfl⟩
    have h := hmono y hy (0 : H) hAzero
    have hreal : 0 ≤ inner ℝ y z := by
      simpa using h
    exact (EReal.coe_nonneg).2 hreal
  have hPhi_ne_bot : ∀ z : H, PhiA A z ≠ ⊥ := by
    intro z hbot
    have hnonneg := hPhi_nonneg z
    rw [hbot] at hnonneg
    simp at hnonneg
  have hPhi_ne_top : ∀ z : H, PhiA A z ≠ ⊤ := by
    intro z htop
    have hAz : (A z).Nonempty := by
      have hzdom : z ∈ A.dom := by simp [hdomA]
      simpa [SetValuedOperator.mem_dom_iff] using hzdom
    rcases hAz with ⟨y, hy⟩
    have hle : PhiA A z ≤ (inner ℝ y z : EReal) := by
      rw [PhiA]
      exact sInf_le ⟨y, hy, rfl⟩
    rw [htop] at hle
    exact EReal.coe_ne_top _ (top_le_iff.mp hle)
  let termE : ℕ → EReal := fun n =>
    (lam n : EReal) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1)))
  have hmainR :
      ∀ n, ((energyR (n+1) - energyR n : ℝ) : EReal) ≤ -termE n ∧
        (termE n).toReal ≤ energyR n - energyR (n+1) := by
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
    have hsum_zero : acc + y + b = 0 := by simpa [hp_eq] using hpbeq
    have hbsub : ∀ t : H, f t ≥ f (x (n+2)) + inner ℝ b (t - x (n+2)) := by
      have hb' : b ∈ {v | ∀ t : H, f t ≥ f (x (n+2)) + inner ℝ v (t - x (n+2))} := by
        simpa [hB_eq_subderiv] using hb
      simpa using hb'
    have hf_diff :
        (f (x (n+2))).toReal - (f (x (n+1))).toReal ≤ inner ℝ b d₂ := by
      have h := hbsub (x (n+1))
      have hinner : inner ℝ b (x (n+1) - x (n+2)) = - inner ℝ b d₂ := by
        rw [show x (n+1) - x (n+2) = -(x (n+2) - x (n+1)) by abel]
        rw [inner_neg_right]
      have hx2_top : f (x (n+2)) ≠ ⊤ := hf_iter_ne_top (n+1)
      have hx1_top : f (x (n+1)) ≠ ⊤ := hf_iter_ne_top n
      have hx2_bot : f (x (n+2)) ≠ ⊥ := by
        intro hbot
        have hle := hm (x (n+2))
        rw [hbot] at hle
        simp at hle
      have h_add_bot : f (x (n+2)) + (inner ℝ b (x (n+1) - x (n+2)) : EReal) ≠ ⊥ := by
        rw [← EReal.coe_toReal hx2_top hx2_bot]
        simp
      have hle_real := EReal.toReal_le_toReal h h_add_bot hx1_top
      have hadd_toReal :
          (f (x (n+2)) + (inner ℝ b (x (n+1) - x (n+2)) : EReal)).toReal =
            (f (x (n+2))).toReal + inner ℝ b (x (n+1) - x (n+2)) := by
        exact EReal.toReal_add hx2_top hx2_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      have hle_real' :
          (f (x (n+2))).toReal + inner ℝ b (x (n+1) - x (n+2)) ≤
            (f (x (n+1))).toReal := by
        simpa [hadd_toReal] using hle_real
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
        energyR (n+1) - energyR n ≤
          (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) + inner ℝ b d₂ := by
      dsimp [energyR, d₁, d₂]
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
        energyR (n+1) - energyR n ≤ inner ℝ (acc + b) d₂ := by
      calc
        energyR (n+1) - energyR n
            ≤ (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) + inner ℝ b d₂ := henergy_le
        _ ≤ ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ + inner ℝ b d₂ :=
            by linarith
        _ = inner ℝ (acc + b) d₂ := by
            rw [← hacc_inner, inner_add_left]
    have haccb : acc + b = -y := by
      calc
        acc + b = (acc + y + b) - y := by abel
        _ = 0 - y := by rw [hsum_zero]
        _ = -y := by simp
    have henergy_y :
        energyR (n+1) - energyR n ≤ - inner ℝ y d₂ := by
      calc
        energyR (n+1) - energyR n ≤ inner ℝ (acc + b) d₂ := henergy_acc
        _ = inner ℝ (-y) d₂ := by rw [haccb]
        _ = - inner ℝ y d₂ := by rw [inner_neg_left]
    have hd₂_eq : d₂ = (lam n) • v := by
      dsimp [v]
      rw [smul_smul]
      field_simp [ne_of_gt (hlam_pos n)]
      simp
    have hinner_d₂ : inner ℝ y d₂ = (lam n) * inner ℝ y v := by
      rw [hd₂_eq, inner_smul_right]
    have hPhi_le_y : PhiA A v ≤ (inner ℝ y v : EReal) := by
      rw [PhiA]
      exact sInf_le ⟨y, hyA, rfl⟩
    have hPhi_toReal_le : (PhiA A v).toReal ≤ inner ℝ y v := by
      have h := EReal.toReal_le_toReal hPhi_le_y (hPhi_ne_bot v) (EReal.coe_ne_top _)
      simpa using h
    have hmainRreal :
        energyR (n+1) - energyR n ≤ -(lam n) * (PhiA A v).toReal := by
      calc
        energyR (n+1) - energyR n ≤ - inner ℝ y d₂ := henergy_y
        _ = -(lam n) * inner ℝ y v := by
            rw [hinner_d₂]
            ring
        _ ≤ -(lam n) * (PhiA A v).toReal := by
            have hnonneg : 0 ≤ lam n := le_of_lt (hlam_pos n)
            nlinarith
    have hPhi_coe : (((PhiA A v).toReal : ℝ) : EReal) = PhiA A v :=
      EReal.coe_toReal (hPhi_ne_top v) (hPhi_ne_bot v)
    have hmainE :
        ((energyR (n+1) - energyR n : ℝ) : EReal) ≤
          ((-(lam n) * (PhiA A v).toReal : ℝ) : EReal) :=
      EReal.coe_le_coe hmainRreal
    have hterm_bound : (termE n).toReal ≤ energyR n - energyR (n+1) := by
      have hterm_toReal :
          (termE n).toReal = lam n * (PhiA A v).toReal := by
        simp [termE, v, d₂, EReal.toReal_mul]
      rw [hterm_toReal]
      linarith
    constructor
    · simpa [termE, v, hPhi_coe] using hmainE
    · exact hterm_bound
  have hmain :
      ∀ n, energySeq x lam f (n+1) - energySeq x lam f n ≤
        (-(lam n) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1))) : EReal) := by
    intro n
    rw [henergySeq_eq (n+1), henergySeq_eq n]
    simpa [termE, sub_eq_add_neg] using (hmainR n).1
  refine ⟨hmain, ?_⟩
  let termR : ℕ → ℝ := fun n => (termE n).toReal
  have hterm_nonnegE : ∀ n, 0 ≤ termE n := by
    intro n
    dsimp [termE]
    exact mul_nonneg ((EReal.coe_nonneg).2 (le_of_lt (hlam_pos n))) (hPhi_nonneg _)
  have hterm_ne_bot : ∀ n, termE n ≠ ⊥ := by
    intro n hbot
    have hnonneg := hterm_nonnegE n
    rw [hbot] at hnonneg
    simp at hnonneg
  have hterm_ne_top : ∀ n, termE n ≠ ⊤ := by
    intro n htop
    let v : H := (lam n)⁻¹ • (x (n+2) - x (n+1))
    have hPhi_coe : (((PhiA A v).toReal : ℝ) : EReal) = PhiA A v :=
      EReal.coe_toReal (hPhi_ne_top v) (hPhi_ne_bot v)
    have hterm_coe' :
        termE n = ((lam n * (PhiA A v).toReal : ℝ) : EReal) := by
      simp [termE, v, hPhi_coe]
    rw [hterm_coe'] at htop
    exact EReal.coe_ne_top _ htop
  have hterm_coe : ∀ n, ((termR n : ℝ) : EReal) = termE n := by
    intro n
    exact EReal.coe_toReal (hterm_ne_top n) (hterm_ne_bot n)
  have hterm_nonneg : ∀ n, 0 ≤ termR n := by
    intro n
    have h := EReal.toReal_le_toReal (hterm_nonnegE n) (by simp) (hterm_ne_top n)
    simpa [termR, termE] using h
  have hterm_le_energy :
      ∀ n, termR n ≤ energyR n - energyR (n+1) := by
    intro n
    exact (hmainR n).2
  have henergy_lower : ∀ N, m ≤ energyR N := by
    intro N
    have hf_lower : m ≤ (f (x (N+1))).toReal := by
      have h := EReal.toReal_le_toReal (hm (x (N+1))) (EReal.coe_ne_bot m)
        (hf_iter_ne_top N)
      simpa using h
    have hcoeff_nonneg : 0 ≤ (2 * (lam N)^2)⁻¹ := by positivity
    have hnorm_nonneg : 0 ≤ ‖x (N+1) - x N‖^2 := sq_nonneg _
    have hprod_nonneg : 0 ≤ (2 * (lam N)^2)⁻¹ * ‖x (N+1) - x N‖^2 :=
      mul_nonneg hcoeff_nonneg hnorm_nonneg
    dsimp [energyR]
    nlinarith
  have hsum_bound :
      ∀ N, (Finset.range N).sum termR ≤
        energyR 0 - m := by
    intro N
    have hsum_le_energy :
        (Finset.range N).sum termR ≤
          (Finset.range N).sum (fun n => energyR n - energyR (n+1)) := by
      exact Finset.sum_le_sum (fun n _ => hterm_le_energy n)
    have htel :
        (Finset.range N).sum (fun n => energyR n - energyR (n+1)) =
          energyR 0 - energyR N := by
      exact Finset.sum_range_sub' energyR N
    calc
      (Finset.range N).sum termR
          ≤ (Finset.range N).sum (fun n => energyR n - energyR (n+1)) :=
            hsum_le_energy
      _ = energyR 0 - energyR N := htel
      _ ≤ energyR 0 - m := by
        linarith [henergy_lower N]
  have hsummable : Summable termR := summable_of_sum_range_le hterm_nonneg hsum_bound
  refine ⟨∑' n, termR n, ?_⟩
  have ht := hsummable.hasSum.tendsto_sum_nat
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id
  have htR :
      Tendsto (fun N : ℕ => (Finset.range (N+1)).sum termR) atTop
        (𝓝 (∑' n, termR n)) :=
    ht.comp hshift
  have htE :
      Tendsto (fun N : ℕ => (((Finset.range (N+1)).sum termR : ℝ) : EReal)) atTop
        (𝓝 (((∑' n, termR n : ℝ) : ℝ) : EReal)) :=
    (EReal.tendsto_coe).2 htR
  have hsum_coe :
      ∀ N : ℕ,
        (((Finset.range (N+1)).sum termR : ℝ) : EReal) =
          (Finset.range (N+1)).sum (fun n =>
            (lam n : EReal) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1)))) := by
    intro N
    calc
      (((Finset.range (N+1)).sum termR : ℝ) : EReal)
          = (Finset.range (N+1)).sum (fun n => ((termR n : ℝ) : EReal)) := by
              have hcoe_sum_finset :
                  ∀ s : Finset ℕ,
                    (((s.sum termR : ℝ) : EReal) =
                      s.sum (fun n => ((termR n : ℝ) : EReal))) := by
                intro s
                refine Finset.induction_on s ?_ ?_
                · simp
                · intro a s ha ih
                  simp [Finset.sum_insert, ha, ih]
              exact hcoe_sum_finset (Finset.range (N+1))
      _ = (Finset.range (N+1)).sum (fun n =>
            (lam n : EReal) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1)))) := by
              exact Finset.sum_congr rfl (fun n _ => by
                simpa [termE] using hterm_coe n)
  convert htE using 1
  · ext N
    exact (hsum_coe N).symm
