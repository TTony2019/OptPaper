import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_5
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_5
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1

open Filter Topology

private theorem betaSequence_nonneg (α : ℕ → ℝ)
    (hα : ∀ i, α i ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    0 ≤ betaSequence α n := by
  rw [betaSequence]
  exact Finset.prod_nonneg fun i hi =>
    sub_nonneg.mpr (le_of_lt (hα i).2)

/-- A technical form of Theorem 3.3.

The paper derives the two eventual rate hypotheses below from Lemma 2.2 and
Lemma 3.3.  They are kept explicit here because the asymptotic `O` notation in
the paper is not a Lean proposition by itself; this theorem then records the
resulting one-sided objective-gap estimate.  The original parameter and error
hypotheses are retained for traceability, while `hbetaRate` and `hdeltaRate`
carry the quantitative content used by this Lean proof. -/
theorem inexact_proximal_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (ε : ℕ → ℝ)
    (alg : InexactProximalPointAlgorithm f ε) (δ : ℕ → ℝ) (z : H) (σ : ℝ)
    (hσ : 1 / 2 < σ) (hfeasible : IsFeasible (fun w => (f w : EReal)) z)
    (hsteps : ∃ M : ℝ, 0 < M ∧ ∀ i j, i ≤ j → alg.lam i ≤ M * alg.lam j)
    (herrors : ∃ c : ℝ, 0 < c ∧ ∀ k, 1 ≤ k → |ε k| ≤ c / (k : ℝ) ^ σ)
    (hδ : δ 0 = 0)
    (hrec : ∀ i, δ (i + 1) = (1 - alg.alpha i) * δ i + ε i ^ 2 / (2 * alg.lam i))
    (C0 B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hglobal : ∀ k, f (alg.x k) - f z ≤ betaSequence alg.alpha k * C0 + δ k)
    (hbetaRate : ∀ᶠ k in atTop,
      betaSequence alg.alpha k ≤ B * (1 / (k : ℝ) ^ 2))
    (hdeltaRate : ∀ᶠ k in atTop,
      |δ k| ≤ D * (1 / (k : ℝ) ^ (2 * σ - 1))) :
    ∀ᶠ k in atTop, f (alg.x k) - f z ≤
      (B * |C0|) * (1 / (k : ℝ) ^ 2) +
        D * (1 / (k : ℝ) ^ (2 * σ - 1)) := by
  filter_upwards [hbetaRate, hdeltaRate] with k hkbeta hkdelta
  have hbeta_nonneg : 0 ≤ betaSequence alg.alpha k :=
    betaSequence_nonneg alg.alpha alg.alpha_mem k
  have hmain : betaSequence alg.alpha k * C0 ≤
      (B * |C0|) * (1 / (k : ℝ) ^ 2) := by
    calc
      betaSequence alg.alpha k * C0 ≤ betaSequence alg.alpha k * |C0| :=
        mul_le_mul_of_nonneg_left (le_abs_self C0) hbeta_nonneg
      _ ≤ (B * (1 / (k : ℝ) ^ 2)) * |C0| :=
        mul_le_mul_of_nonneg_right hkbeta (abs_nonneg C0)
      _ = (B * |C0|) * (1 / (k : ℝ) ^ 2) := by ring
  have herror : δ k ≤ D * (1 / (k : ℝ) ^ (2 * σ - 1)) :=
    (le_abs_self (δ k)).trans hkdelta
  calc
    f (alg.x k) - f z ≤ betaSequence alg.alpha k * C0 + δ k := hglobal k
    _ ≤ (B * |C0|) * (1 / (k : ℝ) ^ 2) +
        D * (1 / (k : ℝ) ^ (2 * σ - 1)) := add_le_add hmain herror
