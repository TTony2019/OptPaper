import Mathlib
import Foundation.SetValued.Basic
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.thm_3
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_3
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_10
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_4

/-!
# Remark 5.1
In the statement of Theorem 5.1, the operator $A$ is supposed to be of the form
$A = \partial\sigma_C + A_0$. It is possible to show that the conclusions of
Theorem 5.1 hold true for more general operators $A$, provided that there exists
a symmetric operator $L \in \mathcal{L}(H)$ such that
$$e\big(A(x), \partial\sigma_{A(0)}(x) + Lx\big) = \mathrm{O}\Big(|x|^2\Big) \quad
\text{when } x \to 0.$$
The operator $L$ must also verify the coercivity condition: $\langle Lx, x \rangle
\geqslant m|x|^2$ for some $m > 0$ and for every $x \in H$.
-/
open SetValuedOperator
open scoped Topology
open scoped Asymptotics
open scoped Pointwise
open Set
open Filter
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Select the `A` and `B` components from one algorithmic inclusion step. -/
private theorem rem51_algorithm_step_selection (A B : SetValuedOperator H H)
    (lam : ℕ → ℝ) (x : ℕ → H) (halg : AlgorithmA A B x lam) :
    ∀ n, ∃ a b : H,
      a ∈ A ((lam n)⁻¹ • (x (n + 2) - x (n + 1))) ∧
      b ∈ B (x (n + 2)) ∧
      ((lam n)^2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n) + a + b = 0 := by
  intro n
  let v : H := (lam n)⁻¹ • (x (n + 2) - x (n + 1))
  let acc : H := ((lam n)^2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n)
  have hstep : (0 : H) ∈ ({acc} : Set H) + A v + B (x (n + 2)) := by
    simpa [AlgorithmA, acc, v] using halg.step n
  rw [Set.mem_add] at hstep
  rcases hstep with ⟨p, hp, b, hb, hpbeq⟩
  rw [Set.mem_add] at hp
  rcases hp with ⟨c, hc, a, ha, hp_eq⟩
  rw [Set.mem_singleton_iff] at hc
  subst c
  refine ⟨a, b, ?_, hb, ?_⟩
  · simpa [v]
  · have hp_eq' : acc + a = p := by simp [hp_eq]
    rw [← hpbeq, ← hp_eq']

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Pointwise control by the excess when the defining supremum is bounded above. -/
private theorem rem51_excess_point_le_of_bdd {A B : Set H} {a : H} {c : ℝ}
    (hbdd : BddAbove (Set.range (fun x : A => Metric.infDist (x : H) B)))
    (ha : a ∈ A) (h : excess A B ≤ c) : Metric.infDist a B ≤ c := by
  let F : A → ℝ := fun x => Metric.infDist (x : H) B
  have hbot : sSup (∅ : Set ℝ) ≤ ⨆ x : A, F x := by
    simp only [Real.sSup_empty]
    exact le_trans Metric.infDist_nonneg (le_ciSup hbdd ⟨a, ha⟩)
  have hexcess_eq : excess A B = ⨆ x : A, F x := by
    unfold excess
    exact (ciSup_subtype (p := fun x : H => x ∈ A) (f := F) hbdd hbot).symm
  have hsup_le : (⨆ x : A, F x) ≤ c := by
    simpa [hexcess_eq] using h
  have hpoint : F ⟨a, ha⟩ ≤ ⨆ x : A, F x := le_ciSup hbdd ⟨a, ha⟩
  exact le_trans hpoint hsup_le

/-- A selected point of `A z` can be decomposed into a support-model point plus
an error controlled by the local excess, up to an arbitrary positive slack. -/
private theorem rem51_exists_model_error_from_excess (A : SetValuedOperator H H)
    (C : Set H) (L : H →L[ℝ] H) {z a : H} {r εerr : ℝ}
    (ha : a ∈ A z)
    (hmodel_nonempty :
      (subderivative (supportFunction C) z + ({L z} : Set H)).Nonempty)
    (hbdd : BddAbove (Set.range (fun x : A z =>
      Metric.infDist (x : H) (subderivative (supportFunction C) z + ({L z} : Set H)))))
    (hexcess :
      excess (A z) (subderivative (supportFunction C) z + ({L z} : Set H)) ≤ r)
    (hε : 0 < εerr) :
    ∃ s e : H,
      s ∈ subderivative (supportFunction C) z ∧
      a = s + L z + e ∧ ‖e‖ ≤ r + εerr := by
  let model : Set H := subderivative (supportFunction C) z + ({L z} : Set H)
  have hdist_le : Metric.infDist a model ≤ r :=
    rem51_excess_point_le_of_bdd (A := A z) (B := model) hbdd ha (by
      simpa [model] using hexcess)
  have hdist_lt : Metric.infDist a model < r + εerr :=
    lt_of_le_of_lt hdist_le (lt_add_of_pos_right r hε)
  rcases (Metric.infDist_lt_iff (by simpa [model] using hmodel_nonempty)).mp hdist_lt with
    ⟨y, hy_model, hy_dist⟩
  change y ∈ subderivative (supportFunction C) z + ({L z} : Set H) at hy_model
  rw [Set.mem_add] at hy_model
  rcases hy_model with ⟨s, hs, l, hl, hsl⟩
  rw [Set.mem_singleton_iff] at hl
  subst l
  refine ⟨s, a - (s + L z), hs, ?_, ?_⟩
  · abel
  · have hnorm_lt : ‖a - (s + L z)‖ < r + εerr := by
      calc
        ‖a - (s + L z)‖ = dist a (s + L z) := (dist_eq_norm a (s + L z)).symm
        _ = dist a y := by rw [hsl]
        _ < r + εerr := hy_dist
    exact le_of_lt hnorm_lt

/-- Remark 5.1: Theorem 5.1 generalizes to operators A satisfying a quadratic approximation
condition with a symmetric coercive operator L. The conclusion is the same geometric decay
of the velocity as in Theorem 5.1. -/
theorem rem_5_1 (A : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ)
    (hAzero_int : (0 : H) ∈ interior (A (0 : H)))
    (L : H →L[ℝ] H) (hL_symm : ∀ x y, inner ℝ (L x) y = inner ℝ x (L y))
    (m : ℝ) (hm : m > 0) (hL_coercive : ∀ x, inner ℝ (L x) x ≥ m * ‖x‖^2)
    (h_condition : (fun (x : H) =>
      excess (A x) (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H))) =O[𝓝 (0 : H)]
      (fun (x : H) => ‖x‖^2))
    (f : H → ℝ) (hf_conv : ConvexOn ℝ Set.univ f) (hf_C1 : ContDiff ℝ 1 f) (hinf : ∃ m, ∀ x, f x ≥ m)
    (M : ℝ) (hf_strongConv : IsStronglyConvex f M)
    (B : SetValuedOperator H H)
    (hB_eq_grad : B = SetValuedOperator.ofFunction Set.univ
      (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam : ℝ) (hlam : lam > 0) (lam_seq : ℕ → ℝ) (hlam_seq : ∀ n, lam_seq n = lam)
    (x : ℕ → H) (halg : AlgorithmA A B x lam_seq) (xInf : H) (hxInf : Tendsto x atTop (𝓝 xInf)) :
    ∃ (n0 : ℕ) (K : ℝ) (q : ℝ), K > 0 ∧ q > 0 ∧ q < 1 ∧
      ∀ n ≥ n0, ‖x (n+1) - x n‖ ≤ K * q ^ n := by
  sorry
