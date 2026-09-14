import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_6
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.algo_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.algo_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1

open Filter Topology

/- The elementary order fact used in the `f* = -∞` half of Theorem 4.1. -/
private theorem exists_value_le_of_not_bddBelow {H : Type*} {f : H → ℝ}
    (h : ¬ BddBelow (Set.range f)) (B : ℝ) : ∃ z : H, f z ≤ B := by
  by_contra! hB
  apply h
  refine ⟨B, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact le_of_lt (hB z)

/- The exact algorithm's global estimate is enough to compare it with any
   fixed point.  This formulation is deliberately independent of attainment
   of the infimum, which is what Theorem 4.1 needs. -/
private theorem section2_comparison_upper_eventually {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (alg : ProximalPointAlgorithm f)
    (hS : Tendsto (fun k => ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)) atTop atTop)
    (z : H) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k in atTop, f (alg.x k) - f z ≤ η := by
  let S : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)
  let D : ℕ → ℝ := fun k => 1 + (Real.sqrt alg.A / 2) * S k
  let C : ℝ := f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2
  have hc : 0 < Real.sqrt alg.A / 2 :=
    div_pos (Real.sqrt_pos.2 alg.A_pos) (by norm_num)
  have hD : Tendsto D atTop atTop := by
    dsimp [D]
    exact tendsto_const_nhds.add_atTop ((hS.const_mul_atTop' hc))
  have hDsq : Tendsto (fun k => D k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hD
  have hquot : Tendsto (fun k => C / D k ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hDsq
  have hquot_tail : ∀ᶠ k in atTop, C / D k ^ 2 ≤ η :=
    ((tendsto_order.1 hquot).2 η hη).mono fun _ hk => le_of_lt hk
  by_cases hC : 0 ≤ C
  · filter_upwards [eventually_ge_atTop 1, hquot_tail] with k hk hq
    have hglobal := proximal_point_global_rate f alg z k hk (by simp [IsFeasible]) hC
    have hres : 0 ≤ ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) (alg.lam_pos _)))
    calc
      f (alg.x k) - f z ≤
          f (alg.x k) - f z + ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) :=
        le_add_of_nonneg_right hres
      _ ≤ C / D k ^ 2 := by simpa [C, D, S] using hglobal
      _ ≤ η := hq
  · have hCneg : C < 0 := lt_of_not_ge hC
    have hquad : 0 ≤ (alg.A / 2) * ‖z - alg.x 0‖ ^ 2 :=
      mul_nonneg (div_nonneg (le_of_lt alg.A_pos) (by norm_num)) (sq_nonneg _)
    have hz0_lt : f (alg.x 0) - f z < 0 := by
      dsimp [C] at hCneg
      linarith
    filter_upwards [eventually_ge_atTop 1] with k hk
    -- The rate at the starting point has constant `0 ≥ 0`, so it gives the
    -- descent `f (alg.x k) ≤ f (alg.x 0)`; together with `f (alg.x 0) < f z`
    -- (from `C < 0`) this bounds `f (alg.x k) - f z` by a negative constant.
    have hglobal0 : f (alg.x k) - f (alg.x 0) +
        ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) ≤
        (f (alg.x 0) - f (alg.x 0) + (alg.A / 2) * ‖alg.x 0 - alg.x 0‖ ^ 2) /
          (1 + (Real.sqrt alg.A / 2) * S k) ^ 2 :=
      proximal_point_global_rate f alg (alg.x 0) k hk (by simp [IsFeasible]) (by simp)
    have hdescent : f (alg.x k) - f (alg.x 0) ≤ 0 := by
      have hres0 : 0 ≤ ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) :=
        div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) (alg.lam_pos _)))
      have hbound : f (alg.x k) - f (alg.x 0) +
          ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) ≤ 0 := by
        simpa [S] using hglobal0
      linarith
    have hz_le : f (alg.x k) - f z ≤ f (alg.x 0) - f z := by linarith
    exact le_of_lt (lt_of_le_of_lt hz_le (lt_of_lt_of_le hz0_lt hη.le))

/- Coercing a bounded-below real range to extended reals preserves its
   infimum.  Keeping this small order lemma local makes the two limit cases
   below read entirely in terms of real objective values. -/
private theorem ereal_sInf_coe_range_eq {H : Type*} [Nonempty H] (f : H → ℝ)
    (hBdd : BddBelow (Set.range f)) :
    sInf (Set.range fun x => (f x : EReal)) = ((sInf (Set.range f) : ℝ) : EReal) := by
  have hBdd₁ : BddBelow (WithTop.some '' Set.range f) :=
    Monotone.map_bddBelow (fun _ _ h => WithTop.coe_le_coe.2 h) hBdd
  change sInf (Set.range (fun x => WithBot.some (WithTop.some (f x)))) =
    WithBot.some (WithTop.some (sInf (Set.range f)))
  rw [Set.range_comp' (fun x : WithTop ℝ => WithBot.some x)
    (fun x => WithTop.some (f x))]
  rw [Set.range_comp' (fun x : ℝ => WithTop.some x) f]
  symm
  rw [WithTop.coe_sInf' (Set.range_nonempty f) hBdd, WithBot.coe_sInf' hBdd₁]

private theorem ereal_sInf_coe_range_eq_bot_of_not_bddBelow {H : Type*} [Nonempty H]
    (f : H → ℝ) (hUnbdd : ¬ BddBelow (Set.range f)) :
    sInf (Set.range fun x => (f x : EReal)) = ⊥ := by
  apply eq_bot_iff.mpr
  rw [sInf_le_iff]
  intro b hb
  by_cases hbot : b = ⊥
  · exact hbot.le
  obtain ⟨a, rfl⟩ := WithBot.ne_bot_iff_exists.mp hbot
  by_cases htop : a = ⊤
  · obtain ⟨z⟩ := ‹Nonempty H›
    have hz := hb (show (f z : EReal) ∈ Set.range fun x => (f x : EReal) from ⟨z, rfl⟩)
    have hnot : ¬ (⊤ : EReal) ≤ (f z : EReal) := by simp
    exact (hnot (by simpa only [htop] using hz)).elim
  obtain ⟨R, rfl⟩ := WithTop.ne_top_iff_exists.mp htop
  exfalso
  apply hUnbdd
  refine ⟨R, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact EReal.coe_le_coe_iff.mp
    (hb (show (f z : EReal) ∈ Set.range fun x => (f x : EReal) from ⟨z, rfl⟩))

private theorem comparison_tendsto_csInf {H : Type*} [Nonempty H] (f : H → ℝ)
    (u : ℕ → H) (hBdd : BddBelow (Set.range f))
    (hcomp : ∀ (z : H) (η : ℝ), 0 < η → ∀ᶠ k in atTop, f (u k) - f z ≤ η) :
    Tendsto (fun k => f (u k)) atTop (𝓝 (sInf (Set.range f))) := by
  let m : ℝ := sInf (Set.range f)
  have hmle : ∀ z : H, m ≤ f z := fun z => csInf_le hBdd ⟨z, rfl⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  have hmlt : m < m + η / 2 := by linarith
  obtain ⟨v, hv, hvlt⟩ := exists_lt_of_csInf_lt (Set.range_nonempty f)
    (show sInf (Set.range f) < m + η / 2 by simpa [m] using hmlt)
  rcases hv with ⟨z, rfl⟩
  have hgap : f z - m < η / 2 := by linarith
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hcomp z (η / 2) (by linarith)))
  refine ⟨N, fun k hk => ?_⟩
  have hupper : f (u k) - m < η := by
    calc
      f (u k) - m = (f (u k) - f z) + (f z - m) := by ring
      _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt (hN k hk) hgap
      _ = η := by ring
  have hlower : 0 ≤ f (u k) - m := sub_nonneg.mpr (hmle (u k))
  rw [Real.dist_eq, abs_of_nonneg hlower]
  exact hupper

private theorem comparison_tendsto_ereal_bot {H : Type*} [Nonempty H] (f : H → ℝ)
    (u : ℕ → H) (hUnbdd : ¬ BddBelow (Set.range f))
    (hcomp : ∀ (z : H) (η : ℝ), 0 < η → ∀ᶠ k in atTop, f (u k) - f z ≤ η) :
    Tendsto (fun k => (f (u k) : EReal)) atTop (𝓝 ⊥) := by
  apply EReal.tendsto_coe_atBot.comp
  rw [Filter.tendsto_atBot]
  intro R
  obtain ⟨z, hz⟩ := exists_value_le_of_not_bddBelow hUnbdd (R - 1)
  filter_upwards [hcomp z 1 (by norm_num)] with k hk
  calc
    f (u k) = (f (u k) - f z) + f z := by ring
    _ ≤ 1 + f z := by linarith
    _ ≤ 1 + (R - 1) := by linarith
    _ = R := by ring

/-- Theorem 4.1, conditional comparison form.

The paper obtains the two comparison hypotheses from the exact/inexact rate
theorems and the monotonic construction.  They are explicit arguments here so
that the extended-real limit argument is not confused with those separate rate
derivations.  The section-specific hypotheses are retained as paper-side
context; the comparison hypotheses are the assumptions actually consumed by
this limit proof. -/
theorem proximal_algorithms_minimize_infimum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (originalSection2 : ProximalPointAlgorithm f)
    (originalSection3 : InexactProximalPointAlgorithm f ε)
    (monotonic : MonotonicProximalPointAlgorithm f)
    (hsection2 : Tendsto (fun k => ∑ j ∈ Finset.range k, Real.sqrt (originalSection2.lam j)) atTop atTop)
    (hsection3 : ∃ σ : ℝ, 1 / 2 < σ ∧
      (∃ M : ℝ, 0 < M ∧ ∀ i j, i ≤ j → originalSection3.lam i ≤ M * originalSection3.lam j) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ k, 1 ≤ k → |ε k| ≤ c / (k : ℝ) ^ σ))
    (hmonotonic : Tendsto (fun k => ∑ j ∈ Finset.range k, Real.sqrt (monotonic.lam j)) atTop atTop)
    (hsection3Comparison : ∀ (z : H) (η : ℝ), 0 < η →
      ∀ᶠ k in atTop, f (originalSection3.x k) - f z ≤ η)
    (hmonotonicComparison : ∀ (z : H) (η : ℝ), 0 < η →
      ∀ᶠ k in atTop, f (monotonic.x k) - f z ≤ η)
    (δ : ℕ → ℝ) (hδ : δ 0 = 0)
    (hrec : ∀ i, δ (i + 1) = (1 - originalSection3.alpha i) * δ i +
      ε i ^ 2 / (2 * originalSection3.lam i))
    (hinf : ¬ ∃ z, ∀ w, f z ≤ f w) :
    Tendsto (fun k => (f (originalSection2.x k) : EReal)) atTop
        (𝓝 (sInf (Set.range fun x => (f x : EReal)))) ∧
      Tendsto (fun k => (f (originalSection3.x k) : EReal)) atTop
        (𝓝 (sInf (Set.range fun x => (f x : EReal)))) ∧
      Tendsto (fun k => (f (monotonic.x k) : EReal)) atTop
        (𝓝 (sInf (Set.range fun x => (f x : EReal)))) := by
  letI : Nonempty H := ⟨originalSection2.x 0⟩
  by_cases hBdd : BddBelow (Set.range f)
  · have h2 := comparison_tendsto_csInf f originalSection2.x hBdd
      (section2_comparison_upper_eventually f originalSection2 hsection2)
    have h3 := comparison_tendsto_csInf f originalSection3.x hBdd hsection3Comparison
    have hm := comparison_tendsto_csInf f monotonic.x hBdd hmonotonicComparison
    constructor
    · rw [ereal_sInf_coe_range_eq f hBdd]
      exact (EReal.tendsto_coe).2 h2
    constructor
    · rw [ereal_sInf_coe_range_eq f hBdd]
      exact (EReal.tendsto_coe).2 h3
    · rw [ereal_sInf_coe_range_eq f hBdd]
      exact (EReal.tendsto_coe).2 hm
  · have hinf_eq := ereal_sInf_coe_range_eq_bot_of_not_bddBelow f hBdd
    constructor
    · simpa [hinf_eq] using
        (comparison_tendsto_ereal_bot f originalSection2.x hBdd
          (section2_comparison_upper_eventually f originalSection2 hsection2))
    constructor
    · simpa [hinf_eq] using
        (comparison_tendsto_ereal_bot f originalSection3.x hBdd hsection3Comparison)
    · simpa [hinf_eq] using
        (comparison_tendsto_ereal_bot f monotonic.x hBdd hmonotonicComparison)
