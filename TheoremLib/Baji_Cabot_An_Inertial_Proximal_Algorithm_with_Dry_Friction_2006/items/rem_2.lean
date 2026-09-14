import Mathlib
import Foundation.SetValued.Basic
import Foundation.SetValued.MaximalMonotone
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
    (ha : a ∈ A) (h : setExcess A B ≤ c) : Metric.infDist a B ≤ c := by
  let F : A → ℝ := fun x => Metric.infDist (x : H) B
  have hexcess_eq : setExcess A B = ⨆ x : A, F x := by
    simpa [F] using setExcess_eq_iSup_infDist A B
  have hsup_le : (⨆ x : A, F x) ≤ c := by
    simpa [hexcess_eq] using h
  have hpoint : F ⟨a, ha⟩ ≤ ⨆ x : A, F x := le_ciSup hbdd ⟨a, ha⟩
  exact le_trans hpoint hsup_le

omit [CompleteSpace H] in
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
      setExcess (A z) (subderivative (supportFunction C) z + ({L z} : Set H)) ≤ r)
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

omit [CompleteSpace H] in
/-- Values of a maximal monotone operator are convex: monotonicity is preserved by
nonnegative convex combinations, and maximality then forces the combination to lie
in the same value. -/
private theorem rem51_value_convex (A : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (x : H) : Convex ℝ (A x) := by
  intro u hu v hv a b ha hb hab
  refine mem_of_monotonically_related_to_graph hA ?_
  intro y w hw
  have hu' : 0 ≤ inner ℝ (u - w) (x - y) := hA.1 (x := x) (y := y) u hu w hw
  have hv' : 0 ≤ inner ℝ (v - w) (x - y) := hA.1 (x := x) (y := y) v hv w hw
  have hsplit : a • u + b • v - w = a • (u - w) + b • (v - w) := by
    have hw : (a + b) • w = w := by rw [hab, one_smul]
    calc
      a • u + b • v - w = a • u + b • v - (a + b) • w := by rw [hw]
      _ = a • (u - w) + b • (v - w) := by
        simp only [add_smul, smul_sub]
        abel
  rw [hsplit, inner_add_left]
  exact add_nonneg (by simpa [real_inner_smul_left] using mul_nonneg ha hu')
    (by simpa [real_inner_smul_left] using mul_nonneg hb hv')

/-- Values of a maximal monotone operator are closed, by weak--strong closedness of
its graph applied to a constant first coordinate. -/
private theorem rem51_value_closed (A : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (x : H) : IsClosed (A x) := by
  refine (isSeqClosed_iff_isClosed).mp ?_
  intro u x0 hu hux
  exact maximal_monotone_graph_weak_strong_closed A hA (fun _ : ℕ => x) u x x0
    (by simp)
    hux hu

omit [CompleteSpace H] in
/-- The support function of a set containing the origin vanishes at the origin. -/
private theorem rem51_supportFunction_zero (C : Set H) (hC0 : (0 : H) ∈ C) :
    supportFunction C (0 : H) = 0 := by
  unfold supportFunction
  have h_image :
      ((fun z : H => (inner ℝ z (0 : H) : EReal)) '' C) = ({0} : Set EReal) := by
    ext r
    constructor
    · rintro ⟨z, _hz, rfl⟩
      simp
    · intro hr
      refine ⟨0, hC0, ?_⟩
      simpa using hr.symm
  rw [h_image]
  simp

omit [CompleteSpace H] in
/-- Every point of a set lies below its support function. -/
private theorem rem51_inner_le_supportFunction {C : Set H} {z y : H} (hz : z ∈ C) :
    (inner ℝ z y : EReal) ≤ supportFunction C y := by
  unfold supportFunction
  exact le_sSup ⟨z, hz, rfl⟩

omit [CompleteSpace H] in
/-- A support-function subgradient bounds the support value by its evaluation. -/
private theorem rem51_subderivative_support_upper {C : Set H} {v xi : H}
    (hC0 : (0 : H) ∈ C) (hxi : xi ∈ subderivative (supportFunction C) v) :
    supportFunction C v ≤ (inner ℝ xi v : EReal) := by
  have h0 := hxi (0 : H)
  have h0' : supportFunction C v - (inner ℝ xi v : EReal) ≤ 0 := by
    simpa [rem51_supportFunction_zero C hC0, sub_eq_add_neg] using h0
  exact EReal.sub_nonpos.mp h0'

omit [CompleteSpace H] in
/-- If the support value at `v` is bounded by its evaluation at `xi ∈ C`, then `v`
belongs to the normal cone of `C` at `xi`. -/
private theorem rem51_supportFunction_upper_mem_normalCone {C : Set H} {v xi : H}
    (hxiC : xi ∈ C) (hsup : supportFunction C v ≤ (inner ℝ xi v : EReal)) :
    v ∈ normalCone C xi := by
  rw [mem_normalCone_iff_forall]
  constructor
  · exact hxiC
  · intro y hy
    have hy_le_sup : (inner ℝ y v : EReal) ≤ supportFunction C v := by
      unfold supportFunction
      exact le_sSup (by exact ⟨y, hy, rfl⟩)
    have hy_le_xi_E : (inner ℝ y v : EReal) ≤ (inner ℝ xi v : EReal) :=
      le_trans hy_le_sup hsup
    have hy_le_xi : inner ℝ y v ≤ inner ℝ xi v := EReal.coe_le_coe_iff.mp hy_le_xi_E
    have hrewrite : inner ℝ v (y - xi) = inner ℝ y v - inner ℝ xi v := by
      rw [inner_sub_right, real_inner_comm v y, real_inner_comm v xi]
    rw [real_inner_comm, hrewrite]
    linarith

/-- Membership in the gradient operator is equality with the gradient. -/
private theorem rem51_mem_gradient_operator_eq (B : SetValuedOperator H H) (g : H → ℝ)
    (hB : B = SetValuedOperator.ofFunction Set.univ
      (fun x : (Set.univ : Set H) => gradient g x.1)) {y b : H}
    (hb : b ∈ B y) : b = gradient g y := by
  rw [hB] at hb
  have hset := SetValuedOperator.ofFunction_apply_of_mem Set.univ
    (fun x : (Set.univ : Set H) => gradient g x.1) (by simp : y ∈ Set.univ)
  rw [hset] at hb
  simpa using hb

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The velocity of Algorithm (A) tends to zero whenever the iterates converge. -/
private theorem rem51_velocity_tendsto_zero (x : ℕ → H) (xInf : H)
    (hx : Tendsto x atTop (𝓝 xInf)) :
    Tendsto (fun n : ℕ => x (n + 1) - x n) atTop (𝓝 (0 : H)) := by
  have hx1 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 xInf) :=
    hx.comp (tendsto_add_atTop_nat 1)
  simpa using hx1.sub hx

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The real-valued excess is nonnegative. -/
private theorem rem51_setExcess_nonneg (A B : Set H) : 0 ≤ setExcess A B := by
  rw [setExcess]
  exact ENNReal.toReal_nonneg

omit [CompleteSpace H] in
/-- The Big-O model hypothesis gives a local quadratic bound with a positive
radius and constant.  This is the quantitative form consumed by the
model-error decomposition. -/
private theorem rem51_excess_quantitative_form
    (A : SetValuedOperator H H) (L : H →L[ℝ] H)
    (h_condition : (fun x : H =>
      setExcess (A x)
        (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H)))
      =O[𝓝 (0 : H)] (fun x : H => ‖x‖ ^ 2)) :
    ∃ ρ > 0, ∃ c > 0, ∀ x : H, ‖x‖ ≤ ρ →
      setExcess (A x)
        (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H))
        ≤ c * ‖x‖ ^ 2 := by
  rcases Asymptotics.isBigO_iff.mp h_condition with ⟨c, hc⟩
  rcases Metric.eventually_nhds_iff.mp hc with ⟨ρ, hρ, hρbound⟩
  refine ⟨ρ / 2, by linarith, max c 1, by positivity, ?_⟩
  intro x hx
  have hdist : dist x (0 : H) < ρ := by
    rw [dist_eq_norm, sub_zero]
    linarith
  have hb := hρbound hdist
  have hf_norm : ‖setExcess (A x)
        (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H))‖ =
      setExcess (A x)
        (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (rem51_setExcess_nonneg _ _)]
  have hg_norm : ‖‖x‖ ^ 2‖ = ‖x‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hf_norm, hg_norm] at hb
  calc
    setExcess (A x)
        (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H))
        ≤ c * ‖x‖ ^ 2 := hb
    _ ≤ max c 1 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left c 1) (sq_nonneg _)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Once the iterates are eventually constant, the velocity has the geometric
decay claimed by the remark. -/
private theorem rem51_geometric_decay_of_eventually_constant (x : ℕ → H)
    (hconst : ∃ N : ℕ, ∀ n ≥ N, x n = x N) :
    ∃ (n0 : ℕ) (K : ℝ) (q : ℝ), K > 0 ∧ q > 0 ∧ q < 1 ∧
      ∀ n ≥ n0, ‖x (n + 1) - x n‖ ≤ K * q ^ n := by
  rcases hconst with ⟨N, hN⟩
  refine ⟨N, 1, (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  intro n hn
  have hn1 : x (n + 1) = x N := hN (n + 1) (Nat.le_succ_of_le hn)
  have hn0 : x n = x N := hN n hn
  rw [hn1, hn0, sub_self, norm_zero]
  positivity

/-- The limit point `-∇f(x∞)` belongs to `A(0)`.  This closes the statement gap
identified in the plan: the algorithm supplies `aₙ ∈ A(zₙ)` with `aₙ → -∇f(x∞)`
and `zₙ → 0`, and maximal monotonicity closes the graph. -/
private theorem rem51_limit_point_mem_A_zero
    (A : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (f : H → ℝ) (hf_C1 : ContDiff ℝ 1 f)
    (B : SetValuedOperator H H)
    (hB_eq_grad : B = SetValuedOperator.ofFunction Set.univ
      (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam : ℝ) (_hlam : lam > 0) (lam_seq : ℕ → ℝ) (hlam_seq : ∀ n, lam_seq n = lam)
    (x : ℕ → H) (halg : AlgorithmA A B x lam_seq) (xInf : H)
    (hxInf : Tendsto x atTop (𝓝 xInf)) :
    -gradient f xInf ∈ A (0 : H) := by
  choose a b ha hb hstep using rem51_algorithm_step_selection A B lam_seq x halg
  let z : ℕ → H := fun n => (lam_seq n)⁻¹ • (x (n + 2) - x (n + 1))
  let acc : ℕ → H :=
    fun n => ((lam_seq n) ^ 2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n)
  have hgrad_cont : Continuous (gradient f) := by
    have hfderiv : Continuous (fun y : H => fderiv ℝ f y) :=
      hf_C1.continuous_fderiv (by norm_num)
    change Continuous (fun y : H => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ f y))
    exact ((InnerProductSpace.toDual ℝ H).symm).continuous.comp hfderiv
  have hx2 : Tendsto (fun n : ℕ => x (n + 2)) atTop (𝓝 xInf) :=
    hxInf.comp (tendsto_add_atTop_nat 2)
  have hx1 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 xInf) :=
    hxInf.comp (tendsto_add_atTop_nat 1)
  have hz0 : Tendsto z atTop (𝓝 (0 : H)) := by
    have hconst : Tendsto (fun n : ℕ => (lam_seq n)⁻¹) atTop (𝓝 lam⁻¹) := by
      simp [hlam_seq]
    have hdiff : Tendsto (fun n : ℕ => x (n + 2) - x (n + 1)) atTop (𝓝 (0 : H)) := by
      simpa using hx2.sub hx1
    simpa [z] using hconst.smul hdiff
  have hacc0 : Tendsto acc atTop (𝓝 (0 : H)) := by
    have hconst : Tendsto (fun n : ℕ => ((lam_seq n) ^ 2)⁻¹) atTop
        (𝓝 ((lam ^ 2)⁻¹)) := by
      simp [hlam_seq]
    have hdiff : Tendsto
        (fun n : ℕ => x (n + 2) - 2 • x (n + 1) + x n) atTop (𝓝 (0 : H)) := by
      have h2 : Tendsto (fun n : ℕ => 2 • x (n + 1)) atTop (𝓝 (2 • xInf)) :=
        hx1.const_smul 2
      have hsum : Tendsto (fun n : ℕ => x (n + 2) - 2 • x (n + 1) + x n) atTop
          (𝓝 (xInf - 2 • xInf + xInf)) := (hx2.sub h2).add hxInf
      have hzero : xInf - 2 • xInf + xInf = (0 : H) := by abel
      simpa [hzero] using hsum
    simpa [acc] using hconst.smul hdiff
  have hb_eq : ∀ n : ℕ, b n = gradient f (x (n + 2)) :=
    fun n => rem51_mem_gradient_operator_eq B f hB_eq_grad (hb n)
  have hb_tendsto : Tendsto b atTop (𝓝 (gradient f xInf)) := by
    have hgrad_seq : Tendsto (fun n : ℕ => gradient f (x (n + 2))) atTop
        (𝓝 (gradient f xInf)) := (hgrad_cont.tendsto xInf).comp hx2
    exact hgrad_seq.congr' (Filter.Eventually.of_forall (fun n => (hb_eq n).symm))
  have ha_eq : ∀ n : ℕ, a n = -acc n - b n := by
    intro n
    have h := hstep n
    calc
      a n = (acc n + a n + b n) - acc n - b n := by abel
      _ = (0 : H) - acc n - b n := by rw [h]
      _ = -acc n - b n := by simp
  have ha_tendsto : Tendsto a atTop (𝓝 (-gradient f xInf)) := by
    have hlim : Tendsto (fun n : ℕ => -acc n - b n) atTop
        (𝓝 (-(0 : H) - gradient f xInf)) := hacc0.neg.sub hb_tendsto
    have hfun : a = fun n : ℕ => -acc n - b n := funext ha_eq
    rw [hfun]
    simpa using hlim
  have hz_weak : Tendsto (fun n : ℕ => toWeakSpace ℝ H (z n)) atTop
      (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (0 : H)).comp hz0
  exact maximal_monotone_graph_weak_strong_closed A hA z a 0 (-gradient f xInf)
    hz_weak ha_tendsto (fun n => by simpa [z] using ha n)

omit [CompleteSpace H] in
/-- The monotonicity pairing that replaces the polyhedral normal-cone argument of
Theorem 5.1: since `p = -∇f(x∞)` lies in `A(0)`, every algorithm pair
`(zₙ,aₙ) ∈ A` satisfies `⟨aₙ - p, zₙ⟩ ≥ 0`. -/
private theorem rem51_monotone_pairing
    (A : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    {z a p : H} (ha : a ∈ A z) (hp : p ∈ A (0 : H)) :
    0 ≤ inner ℝ (a - p) z := by
  simpa using hA.1 (x := z) (y := (0 : H)) a ha p hp

/-- In the algorithm's coordinates, the preceding monotonicity pairing is exactly
the sign inequality needed by the Lyapunov estimate. -/
private theorem rem51_step_pairing_le_zero
    (A : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (f : H → ℝ) (B : SetValuedOperator H H)
    (hB_eq_grad : B = SetValuedOperator.ofFunction Set.univ
      (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam_seq : ℕ → ℝ) (x : ℕ → H) (halg : AlgorithmA A B x lam_seq) (xInf : H)
    (hp : -gradient f xInf ∈ A (0 : H)) (n : ℕ) :
    inner ℝ
      (((lam_seq n) ^ 2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n) +
        gradient f (x (n + 2)) - gradient f xInf)
      ((lam_seq n)⁻¹ • (x (n + 2) - x (n + 1))) ≤ 0 := by
  rcases rem51_algorithm_step_selection A B lam_seq x halg n with ⟨a, b, ha, hb, hstep⟩
  have hb' : b = gradient f (x (n + 2)) :=
    rem51_mem_gradient_operator_eq B f hB_eq_grad hb
  subst b
  have ha_eq : a = -(((lam_seq n) ^ 2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n)) -
      gradient f (x (n + 2)) := by
    calc
      a = ((((lam_seq n) ^ 2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n) + a +
            gradient f (x (n + 2))) -
            (((lam_seq n) ^ 2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n)) -
            gradient f (x (n + 2))) := by abel
      _ = (0 : H) - (((lam_seq n) ^ 2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n)) -
            gradient f (x (n + 2)) := by rw [hstep]
      _ = -(((lam_seq n) ^ 2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n)) -
            gradient f (x (n + 2)) := by simp
  have hpair := rem51_monotone_pairing A hA (z := (lam_seq n)⁻¹ • (x (n + 2) - x (n + 1)))
    (a := a) (p := -gradient f xInf) ha hp
  have hneg : a - (-gradient f xInf) =
      -((((lam_seq n) ^ 2)⁻¹ • (x (n + 2) - 2 • x (n + 1) + x n) +
        gradient f (x (n + 2)) - gradient f xInf)) := by
    rw [ha_eq]
    abel
  rw [hneg, inner_neg_left] at hpair
  linarith

/-- Round-2 notation: `vₙ = x_{n+2} - x_{n+1}`. -/
private def rem52_seqV (x : ℕ → H) (n : ℕ) : H :=
  x (n + 2) - x (n + 1)

/-- Round-2 notation: `accₙ = x_{n+2} - 2 x_{n+1} + xₙ`. -/
private def rem52_seqAcc (x : ℕ → H) (n : ℕ) : H :=
  x (n + 2) - 2 • x (n + 1) + x n

/-- Round-2 notation: `zₙ = λ⁻¹ vₙ`. -/
private noncomputable def rem52_seqZ (x : ℕ → H) (lam : ℝ) (n : ℕ) : H :=
  lam⁻¹ • rem52_seqV x n

/-- The Lyapunov sequence `Gₙ` from the abstract setting. -/
private noncomputable def rem52_seqG (x : ℕ → H) (xInf : H) (lam : ℝ)
    (L : H →L[ℝ] H) (n : ℕ) : ℝ :=
  lam⁻¹ * inner ℝ (x (n + 1) - x n) (x (n + 1) - xInf) +
    (1 / 2 : ℝ) * inner ℝ (L (x (n + 1) - xInf)) (x (n + 1) - xInf)

/-- The second energy sequence `Fₙ` in the abstract setting. -/
private noncomputable def rem52_seqF (x : ℕ → H) (lam : ℝ) (f : H → ℝ)
    (xInf : H) (n : ℕ) : ℝ :=
  (1 / (2 * lam ^ 2)) * ‖x (n + 1) - x n‖ ^ 2 + f (x (n + 1)) -
    f xInf - inner ℝ (gradient f xInf) (x (n + 1) - xInf)

/-- The second-order Lyapunov sequence `Hₙ` from the abstract setting. -/
private noncomputable def rem52_seqH (m η : ℝ) (G F : ℕ → ℝ) (n : ℕ) : ℝ :=
  G n + ((1 + η) / (m - η)) * F n + (1 / (2 * (m - η))) * F (n - 1)

/-- The dual residual `Θₙ = λ⁻² accₙ + L zₙ + ∇f(x_{n+2}) - ∇f(x∞)`. -/
private noncomputable def rem52_pairingU (x : ℕ → H) (xInf : H)
    (L : H →L[ℝ] H) (f : H → ℝ) (lam : ℝ) (z : ℕ → H) (n : ℕ) : H :=
  ((lam ^ 2)⁻¹) • rem52_seqAcc x n + L (z n) + gradient f (x (n + 2)) -
    gradient f xInf

omit [CompleteSpace H] in
private theorem rem52_G_difference_identity_aux
    (a b w : H) (L : H →L[ℝ] H)
    (hL : ∀ a b : H, inner ℝ (L a) b = inner ℝ a (L b))
    (lam : ℝ) (hlam : lam ≠ 0) :
    (lam⁻¹ * inner ℝ b (a + b) +
        1 / 2 * inner ℝ (L (a + b)) (a + b)) -
      (lam⁻¹ * inner ℝ w a + 1 / 2 * inner ℝ (L a) a) =
    lam⁻¹ * inner ℝ ((b - w) + lam • L b) (a + b) +
      lam⁻¹ * inner ℝ w b - 1 / 2 * inner ℝ (L b) b := by
  simp only [map_add, inner_add_left, inner_add_right, inner_sub_left,
    real_inner_smul_left]
  rw [show inner ℝ (L a) b = inner ℝ (L b) a by rw [hL, real_inner_comm]]
  field_simp [hlam]
  ring_nf

omit [CompleteSpace H] in
/-- Equation (29) in the abstract setting: the difference identity for `G`. -/
private theorem rem52_G_difference_identity
    (x : ℕ → H) (xInf : H) (L : H →L[ℝ] H)
    (hL_symm : ∀ a b : H, inner ℝ (L a) b = inner ℝ a (L b))
    (lam : ℝ) (hlam : lam ≠ 0) (n : ℕ) :
    rem52_seqG x xInf lam L (n + 1) - rem52_seqG x xInf lam L n =
      lam⁻¹ * inner ℝ (rem52_seqAcc x n + lam • L (rem52_seqV x n))
        (x (n + 2) - xInf) +
      lam⁻¹ * inner ℝ (x (n + 1) - x n) (rem52_seqV x n) -
      (1 / 2 : ℝ) * inner ℝ (L (rem52_seqV x n)) (rem52_seqV x n) := by
  have h := rem52_G_difference_identity_aux (x (n + 1) - xInf) (rem52_seqV x n)
    (x (n + 1) - x n) L hL_symm lam hlam
  have hv_add : x (n + 1) - xInf + rem52_seqV x n = x (n + 2) - xInf := by
    simp [rem52_seqV]
  have hacc : rem52_seqV x n - (x (n + 1) - x n) = rem52_seqAcc x n := by
    rw [rem52_seqAcc, rem52_seqV]
    abel
  rw [hv_add, hacc] at h
  have hsucc : n + 1 + 1 = n + 2 := by omega
  simpa only [rem52_seqG, rem52_seqV, hsucc] using h

/-- Strong convexity in gradient form implies the value inequality (34). -/
private theorem rem52_strong_convexity_value (f : H → ℝ) (M : ℝ)
    (hf : IsStronglyConvex f M) (x y : H) :
    f x ≥ f y + inner ℝ (gradient f y) (x - y) + (M / 2) * ‖x - y‖ ^ 2 := by
  obtain ⟨_, hC1, hmono⟩ := hf
  set d : H := x - y with hd
  set ρ : ℝ → ℝ := fun t => f (y + t • d) - (M / 2) * t ^ 2 * ‖d‖ ^ 2 with hρdef
  have hderiv_f : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (y + s • d))
      (inner ℝ (gradient f (y + t • d)) d) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => y + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add y
    have hd1 : DifferentiableAt ℝ f (y + t • d) := (hC1.differentiable (by norm_num)) _
    have hf' := hd1.hasFDerivAt
    have hcomp : HasDerivAt (fun s : ℝ => f (y + s • d)) (fderiv ℝ f (y + t • d) d) t := by
      simpa using hf'.comp_hasDerivAt t hlin
    simpa [inner_gradient_left hd1] using hcomp
  have hderiv_p : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (M / 2) * s ^ 2 * ‖d‖ ^ 2)
      (M * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have h2 : HasDerivAt (fun s : ℝ => (M / 2) * s ^ 2 * ‖d‖ ^ 2)
        ((M / 2) * (2 * t) * ‖d‖ ^ 2) t :=
      (h1.const_mul (M / 2)).mul_const (‖d‖ ^ 2)
    have hval : (M / 2) * (2 * t) * ‖d‖ ^ 2 = M * t * ‖d‖ ^ 2 := by ring
    rw [hval] at h2
    exact h2
  have hρ_has : ∀ t : ℝ, HasDerivAt ρ
      (inner ℝ (gradient f (y + t • d)) d - M * t * ‖d‖ ^ 2) t := by
    intro t
    exact (hderiv_f t).sub (hderiv_p t)
  have hρ_diff : Differentiable ℝ ρ := fun t => (hρ_has t).differentiableAt
  have hρ_mono : Monotone (deriv ρ) := by
    intro t1 t2 hle
    rw [(hρ_has t1).deriv, (hρ_has t2).deriv]
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hpos : 0 < t2 - t1 := sub_pos.mpr hlt
      have hz : (y + t2 • d) - (y + t1 • d) = (t2 - t1) • d := by
        rw [add_sub_add_left_eq_sub, sub_smul]
      have hmn := hmono (y + t2 • d) (y + t1 • d)
      rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at hmn
      rw [inner_smul_right] at hmn
      have hfac : M * ((t2 - t1) * ‖d‖) ^ 2 =
          (t2 - t1) * (M * (t2 - t1) * ‖d‖ ^ 2) := by
        ring
      rw [hfac] at hmn
      have hdiv : inner ℝ (gradient f (y + t2 • d) - gradient f (y + t1 • d)) d
          ≥ M * (t2 - t1) * ‖d‖ ^ 2 := by nlinarith [hmn, hpos]
      have hsplit : inner ℝ (gradient f (y + t2 • d)) d -
          inner ℝ (gradient f (y + t1 • d)) d
          = inner ℝ (gradient f (y + t2 • d) - gradient f (y + t1 • d)) d := by
        rw [inner_sub_left]
      nlinarith [hdiv, hsplit]
    · subst heq
      simp
  have hρ_conv : ConvexOn ℝ Set.univ ρ := Monotone.convexOn_univ_of_deriv hρ_diff hρ_mono
  have hslope := hρ_conv.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) (hρ_diff 0)
  rw [(hρ_has 0).deriv] at hslope
  have hs : slope ρ 0 1 = ρ 1 - ρ 0 := by rw [slope_def_field]; norm_num
  rw [hs] at hslope
  have hρ1 : ρ 1 = f x - (M / 2) * ‖d‖ ^ 2 := by
    simp only [hρdef, one_smul, one_pow, mul_one]
    rw [show y + d = x by rw [hd]; abel]
  have hρ0 : ρ 0 = f y := by simp [hρdef]
  rw [hρ1, hρ0] at hslope
  have hgrad0 : inner ℝ (gradient f (y + (0 : ℝ) • d)) d = inner ℝ (gradient f y) d := by
    rw [zero_smul, add_zero]
  rw [hgrad0] at hslope
  rw [hd] at hslope
  linarith [hslope]

omit [CompleteSpace H] in
/-- The support function is subadditive. -/
private theorem rem52_supportFunction_add_le (C : Set H) (u v : H) :
    supportFunction C (u + v) ≤ supportFunction C u + supportFunction C v := by
  unfold supportFunction
  refine sSup_le ?_
  rintro _ ⟨c, hc, rfl⟩
  have hu : (inner ℝ c u : EReal) ≤
      sSup ((fun q : H => (inner ℝ q u : EReal)) '' C) :=
    le_sSup ⟨c, hc, rfl⟩
  have hv : (inner ℝ c v : EReal) ≤
      sSup ((fun q : H => (inner ℝ q v : EReal)) '' C) :=
    le_sSup ⟨c, hc, rfl⟩
  have hsum : ((inner ℝ c u + inner ℝ c v : ℝ) : EReal) ≤
      sSup ((fun q : H => (inner ℝ q u : EReal)) '' C) +
        sSup ((fun q : H => (inner ℝ q v : EReal)) '' C) := by
    simpa [EReal.coe_add] using add_le_add hu hv
  simpa [inner_add_right] using hsum

omit [CompleteSpace H] in
/-- A set containing the origin has nonnegative support function. -/
private theorem rem52_supportFunction_nonneg_of_zero_mem {C : Set H}
    (hC0 : (0 : H) ∈ C) (z : H) :
    (0 : EReal) ≤ supportFunction C z := by
  have h := rem51_inner_le_supportFunction (C := C) (z := (0 : H)) (y := z) hC0
  simpa using h

/-- Support-function subgradient calculus for a closed convex set containing
the origin: subgradients lie in the set, evaluate the support function at `z`,
and satisfy the defining support inequality at every point. -/
private theorem rem52_support_subgradient_calculus
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC0 : (0 : H) ∈ C) {z s : H}
    (hs : s ∈ subderivative (supportFunction C) z) :
    s ∈ C ∧ (inner ℝ s z : EReal) = supportFunction C z ∧
      (∀ y : H, (inner ℝ s y : EReal) ≤ supportFunction C y) ∧
      (0 : EReal) ≤ supportFunction C z := by
  have hsup_le_sz : supportFunction C z ≤ (inner ℝ s z : EReal) :=
    rem51_subderivative_support_upper hC0 hs
  have hsC : s ∈ C := by
    by_contra hs_not
    obtain ⟨u, _hu_ne, hsep⟩ :=
      exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
        ⟨0, hC0⟩ hC_closed hC_convex hs_not
    have hsep' : supportFunction C u < (inner ℝ s u : EReal) := by
      simpa [supportFunction, innerSupremumOn] using hsep
    have hsubgrad := hs (z + u)
    have hsubgrad' : supportFunction C z + (inner ℝ s u : EReal) ≤
        supportFunction C (z + u) := by
      simpa [inner_add_right, EReal.coe_add] using hsubgrad
    have hsubadd := rem52_supportFunction_add_le C z u
    have hchain : supportFunction C z + (inner ℝ s u : EReal) ≤
        supportFunction C z + supportFunction C u := le_trans hsubgrad' hsubadd
    have hsup_ne_top : supportFunction C z ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top (inner ℝ s z)) hsup_le_sz
    have hsup_ne_bot : supportFunction C z ≠ ⊥ := by
      intro hbot
      have hnonneg := rem52_supportFunction_nonneg_of_zero_mem hC0 z
      rw [hbot] at hnonneg
      exact (not_le_of_gt (EReal.bot_lt_coe (0 : ℝ))) hnonneg
    lift supportFunction C z to ℝ using ⟨hsup_ne_top, hsup_ne_bot⟩ with r hr
    have hle : (inner ℝ s u : EReal) ≤ supportFunction C u :=
      (EReal.addLECancellable_coe r).add_le_add_iff_left.mp hchain
    exact (not_lt_of_ge hle) hsep'
  have hinner_le_sup : (inner ℝ s z : EReal) ≤ supportFunction C z :=
    rem51_inner_le_supportFunction hsC
  have hsz_eq : (inner ℝ s z : EReal) = supportFunction C z :=
    le_antisymm hinner_le_sup hsup_le_sz
  have hsupport_le (y : H) : (inner ℝ s y : EReal) ≤ supportFunction C y := by
    have h := hs y
    have h' : (inner ℝ s z : EReal) + (inner ℝ s (y - z) : EReal) ≤
        supportFunction C y := by
      simpa [hsz_eq] using h
    have hrewrite : (inner ℝ s z : EReal) + (inner ℝ s (y - z) : EReal) =
        (inner ℝ s y : EReal) := by
      rw [← EReal.coe_add, inner_sub_right]
      congr 1
      abel
    simpa [hrewrite] using h'
  exact ⟨hsC, hsz_eq, hsupport_le,
    rem52_supportFunction_nonneg_of_zero_mem hC0 z⟩

omit [CompleteSpace H] in
/-- Finite version of the support-function tail estimate used in the
subadditivity argument. -/
private theorem rem52_support_finite_tail_bound
    (C : Set H) {s : H} (hsC : s ∈ C) (z : ℕ → H) (lam : ℝ)
    (hlam : 0 < lam) (n N : ℕ) :
    (inner ℝ s (∑ k ∈ Finset.range N, lam • z (k + n)) : EReal) ≤
      ∑ k ∈ Finset.range N,
        ((lam : EReal) * supportFunction C (z (k + n))) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hterm : (inner ℝ s (lam • z (N + n)) : EReal) ≤
          (lam : EReal) * supportFunction C (z (N + n)) := by
        have hle : (inner ℝ s (z (N + n)) : EReal) ≤
            supportFunction C (z (N + n)) :=
          rem51_inner_le_supportFunction hsC
        have hlamE : (0 : EReal) ≤ (lam : EReal) := by exact_mod_cast (le_of_lt hlam)
        calc
          (inner ℝ s (lam • z (N + n)) : EReal) =
              (lam : EReal) * (inner ℝ s (z (N + n)) : EReal) := by
            rw [real_inner_smul_right]
            exact EReal.coe_mul _ _
          _ ≤ (lam : EReal) * supportFunction C (z (N + n)) :=
            mul_le_mul_of_nonneg_left hle hlamE
      have hsum := add_le_add ih hterm
      simpa [Finset.sum_range_succ, inner_add_right, EReal.coe_add,
        real_inner_smul_right] using hsum

omit [CompleteSpace H] in
private theorem rem52_isClosed_subderivative_supportFunction (C : Set H) (z : H) :
    IsClosed (subderivative (supportFunction C) z) := by
  refine (isSeqClosed_iff_isClosed).mp ?_
  intro s a hs hsa y
  let w : H := y - z
  have hinner_cont : Continuous (fun v : H => inner ℝ v w) := by
    exact continuous_id.inner continuous_const
  have htend_real : Tendsto (fun n : ℕ => inner ℝ (s n) w) atTop (𝓝 (inner ℝ a w)) :=
    (hinner_cont.tendsto a).comp hsa
  have htend_coe : Tendsto (fun n : ℕ => (inner ℝ (s n) w : EReal)) atTop
      (𝓝 (inner ℝ a w : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp htend_real
  have htend_rhs : Tendsto
      (fun n : ℕ => supportFunction C z + (inner ℝ (s n) w : EReal)) atTop
      (𝓝 (supportFunction C z + (inner ℝ a w : EReal))) := by
    have hprod : Tendsto
        (fun n : ℕ => (supportFunction C z, (inner ℝ (s n) w : EReal))) atTop
        (𝓝 (supportFunction C z, (inner ℝ a w : EReal))) :=
      by
        simpa [nhds_prod_eq] using Tendsto.prodMk tendsto_const_nhds htend_coe
    have hcont := (EReal.continuousAt_add
      (p := (supportFunction C z, (inner ℝ a w : EReal)))
      (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto
    exact hcont.comp hprod
  have hle : supportFunction C z + (inner ℝ a w : EReal) ≤ supportFunction C y :=
    le_of_tendsto htend_rhs (Eventually.of_forall fun n => hs n y)
  simpa [w, subderivative] using hle

omit [CompleteSpace H] in
private theorem rem52_isClosed_subderivative_add_singleton
    (C : Set H) (L : H →L[ℝ] H) (z : H) :
    IsClosed (subderivative (supportFunction C) z + ({L z} : Set H)) := by
  refine (isSeqClosed_iff_isClosed).mp ?_
  intro u a hu hua
  have hsubseq : ∀ n : ℕ, u n - L z ∈ subderivative (supportFunction C) z := by
    intro n
    rcases Set.mem_add.mp (hu n) with ⟨s, hs, l, hl, hsl⟩
    rw [Set.mem_singleton_iff] at hl
    subst l
    have : u n - L z = s := by rw [← hsl]; abel
    simpa [this] using hs
  have hlimsub : Tendsto (fun n : ℕ => u n - L z) atTop (𝓝 (a - L z)) :=
    hua.sub tendsto_const_nhds
  have hsubclosed : IsSeqClosed (subderivative (supportFunction C) z) :=
    (isSeqClosed_iff_isClosed).mpr (rem52_isClosed_subderivative_supportFunction C z)
  have hsubmem : a - L z ∈ subderivative (supportFunction C) z :=
    hsubclosed hsubseq hlimsub
  exact Set.mem_add.mpr ⟨a - L z, hsubmem, L z, by simp, by abel⟩

/-! ### Regularity of a full-domain maximal monotone operator

The two side conditions of `rem52_model_error_decomposition` are not extra
paper assumptions: they follow from local boundedness of the maximal monotone
operator `A` whose domain is all of `H`. -/

/-- Fitzpatrick-type auxiliary function used in the local-boundedness proof: the
`EReal`-valued supremum `x ↦ sup_{(y,v) ∈ gra A} ⟪x - y, v⟫ / (1 + ‖y‖)` from
Bauschke--Combettes, Proposition 21.11, whose summands are affine and continuous
in `x`. -/
private noncomputable def rem52_fitzLocal (A : SetValuedOperator H H) (x : H) :
    EReal :=
  ⨆ p : {p : H × H // p.2 ∈ A p.1},
    (((inner ℝ (x - p.val.1) p.val.2) / (1 + ‖p.val.1‖) : ℝ) : EReal)

omit [CompleteSpace H] in
/-- Every graph point of `A` provides a lower bound for the auxiliary supremum. -/
private theorem rem52_fitzLocal_ge (A : SetValuedOperator H H) {x y v : H}
    (hv : v ∈ A y) :
    (((inner ℝ (x - y) v) / (1 + ‖y‖) : ℝ) : EReal) ≤ rem52_fitzLocal A x := by
  dsimp [rem52_fitzLocal]
  exact le_iSup_of_le (⟨(y, v), hv⟩ : {p : H × H // p.2 ∈ A p.1}) le_rfl

omit [CompleteSpace H] in
/-- The auxiliary function is lower semicontinuous: it is a supremum of
continuous affine functions of `x`. -/
private theorem rem52_fitzLocal_lsc (A : SetValuedOperator H H) :
    LowerSemicontinuous (rem52_fitzLocal A) := by
  unfold rem52_fitzLocal
  refine lowerSemicontinuous_iSup ?_
  intro p
  have hreal : Continuous (fun x : H =>
      (inner ℝ (x - p.val.1) p.val.2) / (1 + ‖p.val.1‖)) := by
    exact ((continuous_id.sub continuous_const).inner continuous_const).div_const _
  exact (continuous_coe_real_ereal.comp hreal).lowerSemicontinuous

omit [CompleteSpace H] in
/-- The natural sublevel sets of the auxiliary function are closed. This is the
form in which the Baire category argument consumes lower semicontinuity. -/
private theorem rem52_fitzLocal_closed_sublevel
    (A : SetValuedOperator H H) (N : ℕ) :
    IsClosed {x : H | rem52_fitzLocal A x ≤ ((N : ℝ) : EReal)} := by
  have hlsc := rem52_fitzLocal_lsc A
  rw [lowerSemicontinuous_iff_isClosed_preimage] at hlsc
  simpa [Set.preimage, Set.Iic] using hlsc ((N : ℝ) : EReal)

omit [CompleteSpace H] in
/-- The auxiliary function is convex in the `EReal` sense: each of its summands
is affine, and the supremum of affine functions is convex. -/
private theorem rem52_fitzLocal_convex (A : SetValuedOperator H H) :
    ∀ x y : H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      rem52_fitzLocal A (a • x + b • y) ≤
        (a : EReal) * rem52_fitzLocal A x +
          (b : EReal) * rem52_fitzLocal A y := by
  intro x y a b ha hb hab
  dsimp [rem52_fitzLocal]
  refine iSup_le ?_
  intro p
  let z : H := p.val.1
  let v : H := p.val.2
  let den : ℝ := 1 + ‖z‖
  have hden_pos : 0 < den := by
    dsimp [den]
    positivity
  have hsub : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc
      a • x + b • y - z = a • x + b • y - (a + b) • z := by rw [hab, one_smul]
      _ = a • x + b • y - (a • z + b • z) := by rw [add_smul]
      _ = a • (x - z) + b • (y - z) := by
        simp [smul_sub]
        abel
  have hreal :
      inner ℝ (a • x + b • y - z) v / den =
        a * (inner ℝ (x - z) v / den) + b * (inner ℝ (y - z) v / den) := by
    rw [hsub, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    field_simp [ne_of_gt hden_pos]
  calc
    (((inner ℝ (a • x + b • y - z) v) / den : ℝ) : EReal)
        = ((a * (inner ℝ (x - z) v / den) +
            b * (inner ℝ (y - z) v / den) : ℝ) : EReal) := by
          rw [hreal]
    _ = (a : EReal) * (((inner ℝ (x - z) v) / den : ℝ) : EReal) +
          (b : EReal) * (((inner ℝ (y - z) v) / den : ℝ) : EReal) := by
          simp [EReal.coe_add, EReal.coe_mul]
    _ ≤ (a : EReal) *
          (⨆ p : {p : H × H // p.2 ∈ A p.1},
            (((inner ℝ (x - p.val.1) p.val.2) / (1 + ‖p.val.1‖) : ℝ) : EReal)) +
          (b : EReal) *
          (⨆ p : {p : H × H // p.2 ∈ A p.1},
            (((inner ℝ (y - p.val.1) p.val.2) / (1 + ‖p.val.1‖) : ℝ) : EReal)) := by
          gcongr
          · exact le_iSup_of_le p le_rfl
          · exact le_iSup_of_le p le_rfl

omit [CompleteSpace H] in
/-- Full domain together with monotonicity makes the auxiliary supremum finite
above at every point, so its natural closed sublevels exhaust `H`. -/
private theorem rem52_fitzLocal_finite_above
    (A : SetValuedOperator H H) (hAmono : IsMonotone A) (hdomA : A.dom = Set.univ) :
    ∀ x : H, ∃ N : ℕ, rem52_fitzLocal A x ≤ ((N : ℝ) : EReal) := by
  intro x
  have hxdom : x ∈ A.dom := by
    rw [hdomA]
    simp
  rcases (SetValuedOperator.mem_dom_iff A x).mp hxdom with ⟨u, hu⟩
  rcases exists_nat_ge (‖u‖ * (‖x‖ + 1)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  dsimp [rem52_fitzLocal]
  refine iSup_le ?_
  intro p
  let y : H := p.val.1
  let v : H := p.val.2
  let den : ℝ := 1 + ‖y‖
  have hv : v ∈ A y := p.2
  have hden_pos : 0 < den := by
    dsimp [den]
    positivity
  have hmono := hAmono u hu v hv
  have hinner_le : inner ℝ (x - y) v ≤ inner ℝ (x - y) u := by
    rw [inner_sub_left] at hmono
    have h' : inner ℝ v (x - y) ≤ inner ℝ u (x - y) := sub_nonneg.mp hmono
    simpa [real_inner_comm] using h'
  have hnum_le : inner ℝ (x - y) v ≤ ‖u‖ * (‖x‖ + ‖y‖) := by
    calc
      inner ℝ (x - y) v ≤ inner ℝ (x - y) u := hinner_le
      _ ≤ |inner ℝ (x - y) u| := le_abs_self _
      _ ≤ ‖x - y‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖x‖ + ‖y‖) * ‖u‖ := by
        gcongr
        exact norm_sub_le x y
      _ = ‖u‖ * (‖x‖ + ‖y‖) := by ring
  have hfrac_le :
      inner ℝ (x - y) v / den ≤ ‖u‖ * (‖x‖ + 1) := by
    calc
      inner ℝ (x - y) v / den ≤ (‖u‖ * (‖x‖ + ‖y‖)) / den := by
        gcongr
      _ ≤ ‖u‖ * (‖x‖ + 1) := by
        rw [div_le_iff₀ hden_pos]
        have hmiddle : ‖x‖ + ‖y‖ ≤ (‖x‖ + 1) * (1 + ‖y‖) := by
          nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
        calc
          ‖u‖ * (‖x‖ + ‖y‖)
              ≤ ‖u‖ * ((‖x‖ + 1) * (1 + ‖y‖)) :=
                mul_le_mul_of_nonneg_left hmiddle (norm_nonneg u)
          _ = ‖u‖ * (‖x‖ + 1) * den := by
            dsimp [den]
            ring
  exact EReal.coe_le_coe (le_trans hfrac_le hN)

/-- Baire plus convexity: an `EReal`-valued function with closed natural
sublevels, finite above everywhere, and convex in the `EReal` sense is bounded
above on a ball around every point. This is the convex-analysis core used in
Bauschke--Combettes, Proposition 21.11. -/
private theorem rem52_ereal_convex_finite_locally_bddAbove
    (f : H → EReal)
    (hclosed : ∀ N : ℕ, IsClosed {x : H | f x ≤ ((N : ℝ) : EReal)})
    (hfinite : ∀ x : H, ∃ N : ℕ, f x ≤ ((N : ℝ) : EReal))
    (hconv : ∀ x y : H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y)
    (z : H) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ x ∈ Metric.ball z δ, f x ≤ (M : EReal) := by
  classical
  let C : ℕ → Set H := fun N => {x : H | f x ≤ ((N : ℝ) : EReal)}
  have hcover : (⋃ N : ℕ, C N) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hfinite x with ⟨N, hN⟩
      exact Set.mem_iUnion.2 ⟨N, hN⟩
  rcases nonempty_interior_of_iUnion_of_closed (fun N => by simpa [C] using hclosed N)
      hcover with ⟨N, hNint⟩
  rcases hNint with ⟨c, hc⟩
  have hnhds : C N ∈ 𝓝 c := mem_interior_iff_mem_nhds.mp hc
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hε_subset⟩
  let p : H := (2 : ℝ) • z - c
  rcases hfinite p with ⟨K, hK⟩
  refine ⟨ε / 4, by positivity, ((1 / 2 : ℝ) * (N : ℝ) + (1 / 2 : ℝ) * (K : ℝ)), ?_⟩
  intro x hx
  let q : H := (2 : ℝ) • x - p
  have hq_ball : q ∈ Metric.ball c ε := by
    have hq_sub : q - c = (2 : ℝ) • (x - z) := by
      dsimp [q, p]
      module
    have hx_norm : ‖x - z‖ < ε / 4 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    rw [Metric.mem_ball, dist_eq_norm, hq_sub, norm_smul]
    have htwo : ‖(2 : ℝ)‖ = (2 : ℝ) := by norm_num
    rw [htwo]
    nlinarith [norm_nonneg (x - z)]
  have hqC : f q ≤ ((N : ℝ) : EReal) := hε_subset hq_ball
  have hx_combo : x = (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • p := by
    dsimp [q]
    module
  have hfx := hconv q p (1 / 2) (1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [← hx_combo] at hfx
  calc
    f x ≤ (1 / 2 : EReal) * f q + (1 / 2 : EReal) * f p := hfx
    _ ≤ (1 / 2 : EReal) * ((N : ℝ) : EReal) +
          (1 / 2 : EReal) * ((K : ℝ) : EReal) := by
        gcongr
    _ = (((1 / 2 : ℝ) * (N : ℝ) + (1 / 2 : ℝ) * (K : ℝ) : ℝ) : EReal) := by
        have hhalf : ((1 / 2 : EReal) = ((1 / 2 : ℝ) : EReal)) := by
          change (((1 : ℝ) : EReal) / ((2 : ℝ) : EReal)) = ((1 / 2 : ℝ) : EReal)
          rw [← EReal.coe_div]
        rw [hhalf, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]

/-- Local boundedness of a maximal monotone operator with full domain: for every
point there is a ball on which the operator values are uniformly
norm-bounded. -/
private theorem rem52_monotone_local_boundedness
    (A : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ)
    (x : H) :
    ∃ ρ > 0, ∃ R ≥ 0, ∀ y : H, ‖y - x‖ ≤ ρ → ∀ a : H, a ∈ A y → ‖a‖ ≤ R := by
  let f : H → EReal := rem52_fitzLocal A
  rcases rem52_ereal_convex_finite_locally_bddAbove f
      (by intro N; simpa [f] using rem52_fitzLocal_closed_sublevel A N)
      (by intro x; simpa [f] using rem52_fitzLocal_finite_above A hA.1 hdomA x)
      (by
        intro x y a b ha hb hab
        simpa [f] using rem52_fitzLocal_convex A x y a b ha hb hab)
      x with ⟨ρ, hρ, M, hM⟩
  let Mpos : ℝ := max M 0 + 1
  have hMpos_pos : 0 < Mpos := by
    dsimp [Mpos]
    linarith [le_max_right M 0]
  have hMpos_nonneg : 0 ≤ Mpos := le_of_lt hMpos_pos
  have hM_le_Mpos : M ≤ Mpos := by
    dsimp [Mpos]
    linarith [le_max_left M 0]
  refine ⟨ρ / 4, by positivity, (4 / ρ) * Mpos * (1 + ‖x‖ + ρ / 4), ?_, ?_⟩
  · positivity
  · intro y hy a ha
    by_cases ha0 : a = 0
    · subst a
      have hC_nonneg : 0 ≤ (4 / ρ) * Mpos * (1 + ‖x‖ + ρ / 4) := by positivity
      simpa using hC_nonneg
    · let e : H := ‖a‖⁻¹ • a
      let xeval : H := x + (ρ / 2) • e
      have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
      have ha_norm_ne : ‖a‖ ≠ 0 := ne_of_gt ha_norm_pos
      have he_norm : ‖e‖ = 1 := by
        dsimp [e]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha_norm_pos)]
        exact inv_mul_cancel₀ ha_norm_ne
      have hea : inner ℝ e a = ‖a‖ := by
        dsimp [e]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp [ha_norm_ne]
      have hxeval_ball : xeval ∈ Metric.ball x ρ := by
        have hdist : dist xeval x = ρ / 2 := by
          rw [dist_eq_norm]
          have hsub : xeval - x = (ρ / 2) • e := by
            dsimp [xeval]
            abel
          rw [hsub, norm_smul, he_norm, mul_one]
          rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ρ / 2)]
        rw [Metric.mem_ball, hdist]
        linarith
      have hlocalM : rem52_fitzLocal A xeval ≤ (Mpos : EReal) :=
        le_trans (by simpa [f] using hM xeval hxeval_ball)
          (EReal.coe_le_coe hM_le_Mpos)
      have hfitz_ge :
          (((inner ℝ (xeval - y) a) / (1 + ‖y‖) : ℝ) : EReal) ≤
            rem52_fitzLocal A xeval :=
        rem52_fitzLocal_ge A ha
      have htermE :
          (((inner ℝ (xeval - y) a) / (1 + ‖y‖) : ℝ) : EReal) ≤
            (Mpos : EReal) := le_trans hfitz_ge hlocalM
      have hterm_real :
          inner ℝ (xeval - y) a / (1 + ‖y‖) ≤ Mpos :=
        EReal.coe_le_coe_iff.mp htermE
      have hden_pos : 0 < 1 + ‖y‖ := by positivity
      have hinner_le : inner ℝ (xeval - y) a ≤ Mpos * (1 + ‖y‖) := by
        rwa [div_le_iff₀ hden_pos] at hterm_real
      have hxeval_sub : xeval - y = (x - y) + (ρ / 2) • e := by
        dsimp [xeval]
        abel
      have hinner_eq :
          inner ℝ (xeval - y) a =
            inner ℝ (x - y) a + (ρ / 2) * ‖a‖ := by
        rw [hxeval_sub, inner_add_left, real_inner_smul_left, hea]
      have hxy_le : ‖x - y‖ ≤ ρ / 4 := by
        simpa [norm_sub_rev] using hy
      have hinner_lower :
          -((ρ / 4) * ‖a‖) ≤ inner ℝ (x - y) a := by
        have habs := abs_real_inner_le_norm (x - y) a
        have hneg_abs : -|inner ℝ (x - y) a| ≤ inner ℝ (x - y) a :=
          neg_abs_le _
        have hneg_norm : -(‖x - y‖ * ‖a‖) ≤ -|inner ℝ (x - y) a| :=
          neg_le_neg habs
        have hnormprod : ‖x - y‖ * ‖a‖ ≤ (ρ / 4) * ‖a‖ :=
          mul_le_mul_of_nonneg_right hxy_le (norm_nonneg a)
        nlinarith
      have hmain :
          (ρ / 4) * ‖a‖ ≤ Mpos * (1 + ‖y‖) := by
        rw [hinner_eq] at hinner_le
        nlinarith
      have hy_norm_le : ‖y‖ ≤ ‖x‖ + ρ / 4 := by
        calc
          ‖y‖ ≤ ‖x‖ + ‖x - y‖ := norm_le_norm_add_norm_sub x y
          _ ≤ ‖x‖ + ρ / 4 := by linarith
      have hmain' :
          (ρ / 4) * ‖a‖ ≤ Mpos * (1 + ‖x‖ + ρ / 4) := by
        have harg : 1 + ‖y‖ ≤ 1 + ‖x‖ + ρ / 4 := by linarith
        exact le_trans hmain (mul_le_mul_of_nonneg_left harg hMpos_nonneg)
      have hρ4_pos : 0 < ρ / 4 := by positivity
      have hdiv : ‖a‖ ≤ (Mpos * (1 + ‖x‖ + ρ / 4)) / (ρ / 4) := by
        rw [le_div_iff₀ hρ4_pos]
        nlinarith
      have hconst :
          (Mpos * (1 + ‖x‖ + ρ / 4)) / (ρ / 4) =
            (4 / ρ) * Mpos * (1 + ‖x‖ + ρ / 4) := by
        field_simp [ne_of_gt hρ]
      simpa [hconst] using hdiv

/-- Consequence of local boundedness at the origin: the zero fibre `A(0)` is
norm-bounded. -/
private theorem rem52_zero_fiber_norm_bounded
    (A : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ) :
    ∃ R ≥ 0, ∀ a : H, a ∈ A (0 : H) → ‖a‖ ≤ R := by
  obtain ⟨ρ, hρ, R, hR, hbound⟩ :=
    rem52_monotone_local_boundedness A hA hdomA (0 : H)
  exact ⟨R, hR, fun a ha => hbound (0 : H) (by simpa using hρ.le) a ha⟩

/-- The support function of a nonempty closed bounded convex set is attained in
every direction, and every maximizer is a subgradient of the support function at
that direction. -/
private theorem rem52_support_subgradient_nonempty
    (C : Set H) (hC_ne : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_bdd : ∃ R ≥ 0, ∀ c : H, c ∈ C → ‖c‖ ≤ R) (z : H) :
    ∃ c : H, c ∈ C ∧ supportFunction C z = (inner ℝ c z : EReal) ∧
      c ∈ subderivative (supportFunction C) z := by
  obtain ⟨R, _hR, hRbd⟩ := hC_bdd
  have hBdd : Bornology.IsBounded C :=
    isBounded_iff_forall_norm_le.mpr ⟨R, fun x hx => hRbd x hx⟩
  have hcompact : IsCompact ((toWeakSpace ℝ H) '' C) :=
    weaklyCompact_of_bounded_closed_convex hBdd hC_closed hC_convex
  have hne : ((toWeakSpace ℝ H) '' C).Nonempty := hC_ne.image _
  obtain ⟨w, hw, hmax⟩ := hcompact.exists_isMaxOn hne
    (Continuous.continuousOn (weakSpace_continuous_inner_right (H := H) z))
  obtain ⟨c, hcC, hcw⟩ := hw
  have hmaxq : ∀ q ∈ C, inner ℝ q z ≤ inner ℝ c z := by
    intro q hq
    have h1 := hmax (show toWeakSpace ℝ H q ∈ (toWeakSpace ℝ H) '' C from ⟨q, hq, rfl⟩)
    rw [← hcw] at h1
    simpa using h1
  have hsup_le : supportFunction C z ≤ (inner ℝ c z : EReal) := by
    unfold supportFunction
    refine sSup_le ?_
    rintro r ⟨q, hq, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hmaxq q hq)
  have hsup_ge : (inner ℝ c z : EReal) ≤ supportFunction C z := by
    unfold supportFunction
    exact le_sSup ⟨c, hcC, rfl⟩
  have hsup_eq : supportFunction C z = (inner ℝ c z : EReal) :=
    le_antisymm hsup_le hsup_ge
  refine ⟨c, hcC, hsup_eq, ?_⟩
  intro y
  rw [hsup_eq, ← EReal.coe_add, inner_sub_right]
  have hinner : (inner ℝ c z + (inner ℝ c y - inner ℝ c z) : ℝ) = inner ℝ c y := by ring
  rw [hinner]
  exact rem51_inner_le_supportFunction (C := C) (z := c) (y := y) hcC

/-- Model regularity: for every sequence `zₙ → 0` the model fibres
`∂σ_{A(0)}(zₙ) + {L zₙ}` are eventually nonempty and the distances of `A(zₙ)`
to them are eventually bounded above. These are exactly the two side conditions
consumed by `rem52_model_error_decomposition`. -/
private theorem rem52_model_regularity
    (A : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ)
    (L : H →L[ℝ] H) (z : ℕ → H) (hz : Tendsto z atTop (𝓝 (0 : H))) :
    (∀ᶠ n in atTop,
      (subderivative (supportFunction (A (0 : H))) (z n) +
        ({L (z n)} : Set H)).Nonempty) ∧
      (∀ᶠ n in atTop,
        BddAbove (Set.range (fun x : A (z n) =>
          Metric.infDist (x : H)
            (subderivative (supportFunction (A (0 : H))) (z n) +
              ({L (z n)} : Set H))))) := by
  have hA0ne : (A (0 : H)).Nonempty := by
    have h0 : (0 : H) ∈ A.dom := by rw [hdomA]; trivial
    simpa [SetValuedOperator.dom] using h0
  have hA0closed : IsClosed (A (0 : H)) := rem51_value_closed A hA 0
  have hA0conv : Convex ℝ (A (0 : H)) := rem51_value_convex A hA 0
  obtain ⟨R0, hR0, hA0bd⟩ := rem52_zero_fiber_norm_bounded A hA hdomA
  have hA0bdd : ∃ R ≥ 0, ∀ c : H, c ∈ A (0 : H) → ‖c‖ ≤ R := ⟨R0, hR0, hA0bd⟩
  have hnonempty : ∀ n : ℕ,
      (subderivative (supportFunction (A (0 : H))) (z n) +
        ({L (z n)} : Set H)).Nonempty := by
    intro n
    obtain ⟨c, _hc0, _hsup, hcsub⟩ :=
      rem52_support_subgradient_nonempty (A (0 : H)) hA0ne hA0closed hA0conv hA0bdd (z n)
    exact ⟨c + L (z n), Set.mem_add.mpr ⟨c, hcsub, L (z n), by simp, rfl⟩⟩
  have hlocal := rem52_monotone_local_boundedness A hA hdomA (0 : H)
  obtain ⟨ρ, hρ, Rloc, hRloc, hloc⟩ := hlocal
  have hev : ∀ᶠ n in atTop, ‖z n‖ ≤ ρ := by
    filter_upwards [hz.eventually (Metric.ball_mem_nhds (0 : H) hρ)] with n hn
    simpa [Metric.mem_ball, dist_eq_norm] using hn.le
  refine ⟨Filter.Eventually.of_forall hnonempty, ?_⟩
  filter_upwards [hev] with n hzn
  obtain ⟨c, hc0, _hsup, hcsub⟩ :=
    rem52_support_subgradient_nonempty (A (0 : H)) hA0ne hA0closed hA0conv hA0bdd (z n)
  refine ⟨Rloc + R0 + ‖L‖ * ρ, ?_⟩
  rintro d ⟨x, rfl⟩
  have hxbd : ‖(x : H)‖ ≤ Rloc := hloc (z n) (by simpa using hzn) x x.2
  have hcbd : ‖c‖ ≤ R0 := hA0bd c hc0
  have hmem : c + L (z n) ∈ subderivative (supportFunction (A (0 : H))) (z n) +
      ({L (z n)} : Set H) :=
    Set.mem_add.mpr ⟨c, hcsub, L (z n), by simp, rfl⟩
  have hLz : ‖L (z n)‖ ≤ ‖L‖ * ‖z n‖ := L.le_opNorm (z n)
  have hLρ : ‖L‖ * ‖z n‖ ≤ ‖L‖ * ρ :=
    mul_le_mul_of_nonneg_left hzn (norm_nonneg L)
  calc Metric.infDist (x : H)
        (subderivative (supportFunction (A (0 : H))) (z n) + ({L (z n)} : Set H))
      ≤ dist (x : H) (c + L (z n)) := Metric.infDist_le_dist_of_mem hmem
    _ = ‖(x : H) - (c + L (z n))‖ := dist_eq_norm _ _
    _ ≤ ‖(x : H)‖ + ‖c + L (z n)‖ := norm_sub_le _ _
    _ ≤ ‖(x : H)‖ + (‖c‖ + ‖L (z n)‖) := by
        have h := norm_add_le c (L (z n))
        linarith
    _ ≤ Rloc + R0 + ‖L‖ * ρ := by linarith

omit [CompleteSpace H] in
/-- The quantitative model condition decomposes every selected dual point
`aₙ ∈ A zₙ` into a support subgradient, the linear model term, and a
quadratic error. -/
private theorem rem52_model_error_decomposition
    (A : SetValuedOperator H H) (L : H →L[ℝ] H)
    (h_condition : (fun x : H =>
      setExcess (A x)
        (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H)))
      =O[𝓝 (0 : H)] (fun x : H => ‖x‖ ^ 2))
    (z a : ℕ → H) (hz : Tendsto z atTop (𝓝 (0 : H)))
    (ha : ∀ n, a n ∈ A (z n))
    (hmodel_nonempty : ∀ᶠ n in atTop,
      (subderivative (supportFunction (A (0 : H))) (z n) +
        ({L (z n)} : Set H)).Nonempty)
    (hbdd : ∀ᶠ n in atTop,
      BddAbove (Set.range (fun x : A (z n) =>
        Metric.infDist (x : H)
          (subderivative (supportFunction (A (0 : H))) (z n) +
            ({L (z n)} : Set H))))) :
    ∃ C > 0, ∀ᶠ n in atTop,
      ∃ s e : H,
        s ∈ subderivative (supportFunction (A (0 : H))) (z n) ∧
        a n = s + L (z n) + e ∧ ‖e‖ ≤ C * ‖z n‖ ^ 2 := by
  rcases rem51_excess_quantitative_form A L h_condition with ⟨ρ, hρ, c, hc, hbound⟩
  refine ⟨c + 1, by positivity, ?_⟩
  have hzsmall : ∀ᶠ n in atTop, ‖z n‖ ≤ ρ := by
    filter_upwards [hz.eventually (Metric.ball_mem_nhds (0 : H) hρ)] with n hn
    simpa [Metric.mem_ball, dist_eq_norm] using hn.le
  filter_upwards [hzsmall, hmodel_nonempty, hbdd] with n hzn hne hbddn
  let model : Set H := subderivative (supportFunction (A (0 : H))) (z n) +
    ({L (z n)} : Set H)
  have hexcess : setExcess (A (z n)) model ≤ c * ‖z n‖ ^ 2 := by
    simpa [model] using hbound (z n) hzn
  have hdist_le : Metric.infDist (a n) model ≤ c * ‖z n‖ ^ 2 :=
    rem51_excess_point_le_of_bdd (A := A (z n)) (B := model)
      (by simpa [model] using hbddn) (ha n) hexcess
  by_cases hz0 : z n = 0
  · have hdist0 : Metric.infDist (a n) model = 0 :=
      le_antisymm (by simpa [hz0] using hdist_le) Metric.infDist_nonneg
    have hclosure : a n ∈ closure model :=
      (Metric.mem_closure_iff_infDist_zero (by simpa [model] using hne)).2 hdist0
    have hmodel_closed : IsClosed model := by
      simpa [model] using rem52_isClosed_subderivative_add_singleton (A (0 : H)) L (z n)
    have hamodel : a n ∈ model := by
      rwa [hmodel_closed.closure_eq] at hclosure
    dsimp [model] at hamodel
    rcases Set.mem_add.mp hamodel with ⟨s, hs, l, hl, hsl⟩
    rw [Set.mem_singleton_iff] at hl
    subst l
    refine ⟨s, 0, hs, ?_, ?_⟩
    · simpa [hz0] using hsl.symm
    · simp only [norm_zero]
      positivity
  · have hzn_pos : 0 < ‖z n‖ := norm_pos_iff.mpr hz0
    have hstrict : c * ‖z n‖ ^ 2 < (c + 1) * ‖z n‖ ^ 2 := by
      have hsq : 0 < ‖z n‖ ^ 2 := sq_pos_of_pos hzn_pos
      nlinarith
    have hdist_lt : Metric.infDist (a n) model < (c + 1) * ‖z n‖ ^ 2 :=
      lt_of_le_of_lt hdist_le hstrict
    rcases (Metric.infDist_lt_iff (by simpa [model] using hne)).mp hdist_lt with
      ⟨y, hy, hydist⟩
    dsimp [model] at hy
    rcases Set.mem_add.mp hy with ⟨s, hs, l, hl, hsl⟩
    rw [Set.mem_singleton_iff] at hl
    subst l
    refine ⟨s, a n - (s + L (z n)), hs, ?_, ?_⟩
    · abel
    · calc
        ‖a n - (s + L (z n))‖ = dist (a n) (s + L (z n)) :=
          (dist_eq_norm (a n) (s + L (z n))).symm
        _ = dist (a n) y := by rw [hsl]
        _ ≤ (c + 1) * ‖z n‖ ^ 2 := le_of_lt hydist

omit [CompleteSpace H] in
private theorem rem52_inner_cross_le (a b : H) :
    2 * inner ℝ a b ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h := norm_sub_sq_real a b
  nlinarith [sq_nonneg ‖a - b‖, h]

omit [CompleteSpace H] in
private theorem rem52_G_theta_cross {θ : ℝ} (hθ : 0 < θ) (d u : H) :
    inner ℝ d u ≤ ‖d‖ ^ 2 / (2 * θ) + θ * ‖u‖ ^ 2 / 2 := by
  have h := norm_sub_sq_real d (θ • u)
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hθ] at h
  have h2 : 0 ≤ ‖d - θ • u‖ ^ 2 := sq_nonneg _
  have hkey : 2 * θ * inner ℝ d u ≤ ‖d‖ ^ 2 + θ ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [h, h2]
  rw [div_add_div _ _ (by positivity) (by norm_num)]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hkey]

omit [CompleteSpace H] in
private theorem rem52_tau0_pos (snorm M : ℝ) (hsnorm : 0 ≤ snorm)
    (hM : 0 < M) :
    0 < (Real.sqrt (snorm ^ 2 + 4 * M) - snorm) / 2 := by
  have hsq : snorm ^ 2 < snorm ^ 2 + 4 * M := by nlinarith
  have hsqrt : snorm < Real.sqrt (snorm ^ 2 + 4 * M) := by
    rw [Real.lt_sqrt (by positivity)]
    exact hsq
  linarith

omit [CompleteSpace H] in
private theorem rem52_tau0_quadratic (snorm M : ℝ) (hM : 0 < M) :
    (let τ0 : ℝ := (Real.sqrt (snorm ^ 2 + 4 * M) - snorm) / 2;
      τ0 ^ 2 + snorm * τ0 = M) := by
  intro τ0
  have hs : 0 ≤ snorm ^ 2 + 4 * M := by positivity
  have hsq : (Real.sqrt (snorm ^ 2 + 4 * M)) ^ 2 = snorm ^ 2 + 4 * M :=
    Real.sq_sqrt hs
  dsimp [τ0]
  nlinarith

omit [CompleteSpace H] in
/-- Equations (45) and (46): two-sided quadratic bounds for `Gₙ`. -/
private theorem rem52_G_bounds (x : ℕ → H) (xInf : H) (lam : ℝ)
    (L : H →L[ℝ] H) (m : ℝ) (_hm : 0 < m) (hlam : 0 < lam) (n : ℕ)
    {θ : ℝ} (hθ : 0 < θ)
    (hcoer : ∀ d : H, m * ‖d‖ ^ 2 ≤ inner ℝ d (L d)) :
    rem52_seqG x xInf lam L n ≥
        -‖x (n + 1) - x n‖ ^ 2 / (2 * lam * θ) +
          ((m - θ / lam) / 2) * ‖x (n + 1) - xInf‖ ^ 2 ∧
      rem52_seqG x xInf lam L n ≤
        ‖x (n + 1) - x n‖ ^ 2 / (2 * lam * θ) +
          ((θ / lam + ‖L‖) / 2) * ‖x (n + 1) - xInf‖ ^ 2 := by
  let d : H := x (n + 1) - x n
  let e : H := x (n + 1) - xInf
  constructor
  · have hcross := rem52_G_theta_cross hθ (-d) e
    have hcross' : -inner ℝ d e ≤ ‖d‖ ^ 2 / (2 * θ) + θ * ‖e‖ ^ 2 / 2 := by
      simpa using hcross
    have hmul : lam⁻¹ * (-inner ℝ d e) ≤
        lam⁻¹ * (‖d‖ ^ 2 / (2 * θ) + θ * ‖e‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hcross' (inv_nonneg.mpr (le_of_lt hlam))
    have hmul' : -lam⁻¹ * inner ℝ d e ≤
        ‖d‖ ^ 2 / (2 * lam * θ) + (θ / lam) * ‖e‖ ^ 2 / 2 := by
      convert hmul using 1 <;> ring
    have hcoer_e := hcoer e
    have hcomm : inner ℝ e (L e) = inner ℝ (L e) e := real_inner_comm _ _
    rw [hcomm] at hcoer_e
    have hcoer_half : (m / 2) * ‖e‖ ^ 2 ≤ (1 / 2 : ℝ) * inner ℝ (L e) e := by
      nlinarith
    have hcoef : -‖d‖ ^ 2 / (2 * lam * θ) +
          ((m - θ / lam) / 2) * ‖e‖ ^ 2 =
        -(‖d‖ ^ 2 / (2 * lam * θ) + (θ / lam) * ‖e‖ ^ 2 / 2) +
          (m / 2) * ‖e‖ ^ 2 := by
      ring
    have hmain : -‖d‖ ^ 2 / (2 * lam * θ) +
          ((m - θ / lam) / 2) * ‖e‖ ^ 2 ≤
        lam⁻¹ * inner ℝ d e + (1 / 2 : ℝ) * inner ℝ (L e) e := by
      linarith [hmul', hcoer_half, hcoef]
    simpa [rem52_seqG, d, e] using hmain
  · have hcross := rem52_G_theta_cross hθ d e
    have hmul : lam⁻¹ * inner ℝ d e ≤
        lam⁻¹ * (‖d‖ ^ 2 / (2 * θ) + θ * ‖e‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hcross (inv_nonneg.mpr (le_of_lt hlam))
    have hmul' : lam⁻¹ * inner ℝ d e ≤
        ‖d‖ ^ 2 / (2 * lam * θ) + (θ / lam) * ‖e‖ ^ 2 / 2 := by
      convert hmul using 1
      ring
    have hLnorm := L.le_opNorm e
    have hinner := real_inner_le_norm (L e) e
    have hle : (1 / 2 : ℝ) * inner ℝ (L e) e ≤ (‖L‖ / 2) * ‖e‖ ^ 2 := by
      nlinarith [hLnorm, hinner, norm_nonneg e, norm_nonneg (L e)]
    have hmain : lam⁻¹ * inner ℝ d e + (1 / 2 : ℝ) * inner ℝ (L e) e ≤
        ‖d‖ ^ 2 / (2 * lam * θ) + ((θ / lam + ‖L‖) / 2) * ‖e‖ ^ 2 := by
      nlinarith [hmul', hle]
    simpa [rem52_seqG, d, e] using hmain

/-- Equations (44) and (48): comparison between the `G` and `F` sequences. -/
private theorem rem52_G_F_comparison (x : ℕ → H) (xInf : H) (lam : ℝ)
    (L : H →L[ℝ] H) (f : H → ℝ) (M : ℝ) (m : ℝ) (hm : 0 < m)
    (hM : 0 < M) (hlam : 0 < lam)
    (hG_lower : ∀ n {θ : ℝ}, 0 < θ → rem52_seqG x xInf lam L n ≥
      -‖x (n + 1) - x n‖ ^ 2 / (2 * lam * θ) +
        ((m - θ / lam) / 2) * ‖x (n + 1) - xInf‖ ^ 2)
    (hG_upper : ∀ n {θ : ℝ}, 0 < θ → rem52_seqG x xInf lam L n ≤
      ‖x (n + 1) - x n‖ ^ 2 / (2 * lam * θ) +
        ((θ / lam + ‖L‖) / 2) * ‖x (n + 1) - xInf‖ ^ 2)
    (hF_lower : ∀ n, rem52_seqF x lam f xInf n ≥
        (1 / (2 * lam ^ 2)) * ‖x (n + 1) - x n‖ ^ 2 +
          (M / 2) * ‖x (n + 1) - xInf‖ ^ 2) :
    let τ0 : ℝ := (Real.sqrt (‖L‖ ^ 2 + 4 * M) - ‖L‖) / 2
    (∀ n, rem52_seqF x lam f xInf n ≥ τ0 * rem52_seqG x xInf lam L n) ∧
      (∀ n, rem52_seqG x xInf lam L n ≥
        -(1 / m) * rem52_seqF x lam f xInf n) := by
  let τ0 : ℝ := (Real.sqrt (‖L‖ ^ 2 + 4 * M) - ‖L‖) / 2
  change (∀ n, rem52_seqF x lam f xInf n ≥
      τ0 * rem52_seqG x xInf lam L n) ∧
    (∀ n, rem52_seqG x xInf lam L n ≥ -(1 / m) * rem52_seqF x lam f xInf n)
  have hτ0_pos : 0 < τ0 := by
    simpa [τ0] using rem52_tau0_pos ‖L‖ M (norm_nonneg L) hM
  have hτ0_quad : τ0 ^ 2 + ‖L‖ * τ0 = M := by
    simpa [τ0] using rem52_tau0_quadratic ‖L‖ M hM
  constructor
  · intro n
    let w2 : ℝ := ‖x (n + 1) - x n‖ ^ 2
    let a2 : ℝ := ‖x (n + 1) - xInf‖ ^ 2
    have hw2 : 0 ≤ w2 := by dsimp [w2]; positivity
    have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
    have hθ : 0 < lam * τ0 := mul_pos hlam hτ0_pos
    have hupper := hG_upper n hθ
    have hupper' : rem52_seqG x xInf lam L n ≤
        w2 / (2 * lam * (lam * τ0)) + ((lam * τ0 / lam + ‖L‖) / 2) * a2 := by
      simpa [w2, a2] using hupper
    have hmul := mul_le_mul_of_nonneg_left hupper' (le_of_lt hτ0_pos)
    have hF' : rem52_seqF x lam f xInf n ≥
        (1 / (2 * lam ^ 2)) * w2 + (M / 2) * a2 := by
      simpa [w2, a2] using hF_lower n
    have hfirst : τ0 * (w2 / (2 * lam * (lam * τ0))) =
        (1 / (2 * lam ^ 2)) * w2 := by
      have hden : 2 * lam * (lam * τ0) = 2 * lam ^ 2 * τ0 := by ring
      rw [hden]
      field_simp [ne_of_gt hlam, ne_of_gt hτ0_pos]
    have hsecond : τ0 * (((lam * τ0 / lam + ‖L‖) / 2) * a2) = (M / 2) * a2 := by
      have hc : lam * τ0 / lam = τ0 := mul_div_cancel_left₀ τ0 (ne_of_gt hlam)
      rw [hc]
      have hq : τ0 * ((τ0 + ‖L‖) / 2) = M / 2 := by
        have hmul' : τ0 * (τ0 + ‖L‖) = M := by nlinarith [hτ0_quad]
        rw [← mul_div_assoc, hmul']
      rw [← mul_assoc, hq]
    have hscalar : τ0 *
        (w2 / (2 * lam * (lam * τ0)) + ((lam * τ0 / lam + ‖L‖) / 2) * a2) =
        (1 / (2 * lam ^ 2)) * w2 + (M / 2) * a2 := by
      calc τ0 * (w2 / (2 * lam * (lam * τ0)) +
              ((lam * τ0 / lam + ‖L‖) / 2) * a2)
          = τ0 * (w2 / (2 * lam * (lam * τ0))) +
            τ0 * (((lam * τ0 / lam + ‖L‖) / 2) * a2) := by ring
        _ = (1 / (2 * lam ^ 2)) * w2 + (M / 2) * a2 := by rw [hfirst, hsecond]
    linarith
  · intro n
    let w2 : ℝ := ‖x (n + 1) - x n‖ ^ 2
    let a2 : ℝ := ‖x (n + 1) - xInf‖ ^ 2
    have hw2 : 0 ≤ w2 := by dsimp [w2]; positivity
    have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
    have hθ : 0 < lam * m := mul_pos hlam hm
    have hlower := hG_lower n hθ
    have hlower' : rem52_seqG x xInf lam L n ≥ -w2 / (2 * lam ^ 2 * m) := by
      have hcoef : (m - (lam * m) / lam) / 2 = 0 := by
        field_simp [ne_of_gt hlam]
        ring
      have hden : 2 * lam * (lam * m) = 2 * lam ^ 2 * m := by ring
      simpa [w2, a2, hcoef, hden] using hlower
    have hF' : rem52_seqF x lam f xInf n ≥
        (1 / (2 * lam ^ 2)) * w2 + (M / 2) * a2 := by
      simpa [w2, a2] using hF_lower n
    have hnonneg : 0 ≤ (M / 2) * a2 := mul_nonneg (by positivity) ha2
    have hF'' : rem52_seqF x lam f xInf n ≥ (1 / (2 * lam ^ 2)) * w2 := by
      linarith
    have hdiv : ((1 / (2 * lam ^ 2)) * w2) / m ≤
        (rem52_seqF x lam f xInf n) / m :=
      div_le_div_of_nonneg_right hF'' (le_of_lt hm)
    have hEq : -(1 / m) * rem52_seqF x lam f xInf n =
        -(rem52_seqF x lam f xInf n / m) := by ring
    have hEq2 : -w2 / (2 * lam ^ 2 * m) =
        -(((1 / (2 * lam ^ 2)) * w2) / m) := by
      field_simp [ne_of_gt hm, ne_of_gt hlam]
    rw [hEq]
    linarith

/-- Inequality (37) in the abstract setting: the increment estimate for `G`. -/
private theorem rem52_G_increment_F_bound
    (x : ℕ → H) (xInf : H) (f : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (L : H →L[ℝ] H)
    (hL_symm : ∀ a b : H, inner ℝ (L a) b = inner ℝ a (L b))
    (m δ θ : ℝ) (hm : 0 < m) (hδ : 0 < δ)
    (z err : ℕ → H) (hz : ∀ n, z n = lam⁻¹ • rem52_seqV x n)
    (hpair31 : ∀ᶠ n in atTop,
      inner ℝ (rem52_pairingU x xInf L f lam z n) (x (n + 2) - xInf) ≤
        θ / lam ^ 2 * ‖rem52_seqV x n‖ ^ 2)
    (hrem33 : ∀ᶠ n in atTop,
      |inner ℝ (err n) (x (n + 2) - xInf)| ≤
        δ / lam ^ 2 * ‖rem52_seqV x n‖ ^ 2)
    (hconv34 : ∀ n,
      inner ℝ (gradient f (x (n + 2))) (xInf - x (n + 2)) ≤
        f xInf - f (x (n + 2)))
    (hcoer35 : ∀ d : H, m * ‖d‖ ^ 2 ≤ inner ℝ d (L d)) :
    ∀ᶠ n in atTop,
      rem52_seqG x xInf lam L (n + 1) - rem52_seqG x xInf lam L n +
          lam * rem52_seqF x lam f xInf (n + 1) ≤
        (1 + δ + θ) / lam * ‖rem52_seqV x n‖ ^ 2 +
          (1 / (2 * lam)) * ‖x (n + 1) - x n‖ ^ 2 := by
  filter_upwards [hpair31, hrem33] with n hpair hrem
  let d : H := x (n + 1) - x n
  let v : H := rem52_seqV x n
  let e : H := x (n + 2) - xInf
  let U : H := rem52_pairingU x xInf L f lam z n
  have hdiff := rem52_G_difference_identity x xInf L hL_symm lam (ne_of_gt hlam) n
  have hpair' : inner ℝ U e ≤ θ / lam ^ 2 * ‖v‖ ^ 2 := by
    simpa [U, e] using hpair
  have hrem' : -inner ℝ (err n) e ≤ δ / lam ^ 2 * ‖v‖ ^ 2 :=
    le_trans (neg_le_abs _) (by simpa [v, e] using hrem)
  have hconv' : -inner ℝ (gradient f (x (n + 2))) e ≤ f xInf - f (x (n + 2)) := by
    have h := hconv34 n
    rw [show xInf - x (n + 2) = -(x (n + 2) - xInf) by abel,
      inner_neg_right] at h
    simpa [e] using h
  have hpair_mult : lam * inner ℝ U e ≤ θ / lam * ‖v‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hpair' (le_of_lt hlam)
    have hcoef : lam * (θ / lam ^ 2 * ‖v‖ ^ 2) = θ / lam * ‖v‖ ^ 2 := by
      field_simp [ne_of_gt hlam]
    rwa [hcoef] at h
  have hrem_mult : -lam * inner ℝ (err n) e ≤ δ / lam * ‖v‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hrem' (le_of_lt hlam)
    convert h using 1 <;> field_simp [ne_of_gt hlam]
  have hf_bound :
      -lam * inner ℝ (gradient f (x (n + 2)) - gradient f xInf) e +
        lam * (f (x (n + 2)) - f xInf - inner ℝ (gradient f xInf) e) ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left hconv' (le_of_lt hlam)
    simp only [inner_sub_left] at h ⊢
    nlinarith
  have hcv : inner ℝ d v ≤ (1 / 2 : ℝ) * ‖d‖ ^ 2 + (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
    nlinarith [rem52_inner_cross_le d v]
  have hLv_nonneg : 0 ≤ inner ℝ (L v) v := by
    have h := hcoer35 v
    have hcomm : inner ℝ v (L v) = inner ℝ (L v) v := real_inner_comm _ _
    rw [hcomm] at h
    nlinarith [hm, sq_nonneg ‖v‖]
  have hlast : lam⁻¹ * inner ℝ d v - (1 / 2 : ℝ) * inner ℝ (L v) v ≤
      (1 / (2 * lam)) * ‖d‖ ^ 2 + (1 / (2 * lam)) * ‖v‖ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hcv (inv_nonneg.mpr (le_of_lt hlam))
    have h2 : 0 ≤ (1 / 2 : ℝ) * inner ℝ (L v) v :=
      mul_nonneg (by norm_num) hLv_nonneg
    have hcoef : lam⁻¹ * ((1 / 2 : ℝ) * ‖d‖ ^ 2 + (1 / 2 : ℝ) * ‖v‖ ^ 2) =
        (1 / (2 * lam)) * ‖d‖ ^ 2 + (1 / (2 * lam)) * ‖v‖ ^ 2 := by
      ring
    nlinarith [h1, h2, hcoef]
  have hlast' : lam⁻¹ * inner ℝ d v - (1 / 2 : ℝ) * inner ℝ (L v) v +
        (1 / (2 * lam)) * ‖v‖ ^ 2 ≤
      (1 / (2 * lam)) * ‖d‖ ^ 2 + (1 / lam) * ‖v‖ ^ 2 := by
    have hkin : 0 ≤ (1 / (2 * lam)) * ‖v‖ ^ 2 := by positivity
    have hcoef : (1 / (2 * lam)) * ‖v‖ ^ 2 + (1 / (2 * lam)) * ‖v‖ ^ 2 =
        (1 / lam) * ‖v‖ ^ 2 := by
      field_simp [ne_of_gt hlam]
      ring
    nlinarith [hlast, hkin, hcoef]
  have hdecomp :
      rem52_seqG x xInf lam L (n + 1) - rem52_seqG x xInf lam L n +
          lam * rem52_seqF x lam f xInf (n + 1) =
        lam * inner ℝ U e +
          (-lam * inner ℝ (gradient f (x (n + 2)) - gradient f xInf) e +
            lam * (f (x (n + 2)) - f xInf - inner ℝ (gradient f xInf) e)) +
          (lam⁻¹ * inner ℝ d v - (1 / 2 : ℝ) * inner ℝ (L v) v +
            (1 / (2 * lam)) * ‖v‖ ^ 2) := by
    rw [hdiff]
    have hz' : z n = lam⁻¹ • v := by
      simpa [v] using hz n
    simp only [rem52_seqF, rem52_seqV, U, d, v, e, rem52_pairingU, hz', map_smul,
      inner_add_left, inner_sub_left, real_inner_smul_left]
    ring_nf
    field_simp [ne_of_gt hlam]
    ring
  have hcombined :
      lam * inner ℝ U e +
          (-lam * inner ℝ (gradient f (x (n + 2)) - gradient f xInf) e +
            lam * (f (x (n + 2)) - f xInf - inner ℝ (gradient f xInf) e)) +
          (lam⁻¹ * inner ℝ d v - (1 / 2 : ℝ) * inner ℝ (L v) v +
            (1 / (2 * lam)) * ‖v‖ ^ 2) ≤
        (1 + δ + θ) / lam * ‖v‖ ^ 2 + (1 / (2 * lam)) * ‖d‖ ^ 2 := by
    calc
      lam * inner ℝ U e +
          (-lam * inner ℝ (gradient f (x (n + 2)) - gradient f xInf) e +
            lam * (f (x (n + 2)) - f xInf - inner ℝ (gradient f xInf) e)) +
          (lam⁻¹ * inner ℝ d v - (1 / 2 : ℝ) * inner ℝ (L v) v +
            (1 / (2 * lam)) * ‖v‖ ^ 2)
          ≤ θ / lam * ‖v‖ ^ 2 + 0 +
              ((1 / (2 * lam)) * ‖d‖ ^ 2 + (1 / lam) * ‖v‖ ^ 2) := by
            exact add_le_add (add_le_add hpair_mult hf_bound) hlast'
      _ = (1 + θ) / lam * ‖v‖ ^ 2 + (1 / (2 * lam)) * ‖d‖ ^ 2 := by
            field_simp [ne_of_gt hlam]
            ring
      _ ≤ (1 + δ + θ) / lam * ‖v‖ ^ 2 + (1 / (2 * lam)) * ‖d‖ ^ 2 := by
            gcongr
            field_simp [ne_of_gt hlam]
            linarith [hδ]
  rw [hdecomp]
  simpa [v, d] using hcombined

/-- Equation (42) in the abstract setting: the quantitative decrement of `F`. -/
private theorem rem52_F_difference_bound
    (x : ℕ → H) (xInf : H) (f : H → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (m η θ : ℝ) (_hm : 0 < m) (hη : 0 < η) (_hηm : η < m)
    (hθ : θ ≤ 3 * η * lam / 4)
    (L : H →L[ℝ] H) (z err : ℕ → H)
    (hz : ∀ n, z n = lam⁻¹ • rem52_seqV x n)
    (hpairF : ∀ᶠ n in atTop,
      inner ℝ (rem52_pairingU x xInf L f lam z n) (rem52_seqV x n) ≤
        θ / lam ^ 2 * ‖rem52_seqV x n‖ ^ 2)
    (hrem : ∀ᶠ n in atTop,
      |inner ℝ (err n) (x (n + 2) - xInf)| ≤
          (η / 4) / lam ^ 2 * ‖rem52_seqV x n‖ ^ 2 ∧
        |inner ℝ (err n) (rem52_seqV x n)| ≤
          (η / 4) / lam * ‖rem52_seqV x n‖ ^ 2)
    (hconv : ∀ n, f (x (n + 2)) ≤ f (x (n + 1)) +
      inner ℝ (gradient f (x (n + 2))) (x (n + 2) - x (n + 1)))
    (hcoer : ∀ d : H, m * ‖d‖ ^ 2 ≤ inner ℝ d (L d)) :
    ∀ᶠ n in atTop,
      rem52_seqF x lam f xInf (n + 1) - rem52_seqF x lam f xInf n ≤
        -((m - η) / lam) * ‖rem52_seqV x n‖ ^ 2 := by
  filter_upwards [hrem, hpairF] with n hremn hpairn
  let w : H := x (n + 1) - x n
  let v : H := rem52_seqV x n
  let acc : H := rem52_seqAcc x n
  let U : H := rem52_pairingU x xInf L f lam z n
  have hv_def : v = x (n + 2) - x (n + 1) := rfl
  have hacc_eq : acc = v - w := by
    dsimp [acc, v, w, rem52_seqAcc, rem52_seqV]
    abel
  have hz_eq : z n = lam⁻¹ • v := by
    simpa [v] using hz n
  have hdiff_id : rem52_seqF x lam f xInf (n + 1) - rem52_seqF x lam f xInf n =
      (1 / (2 * lam ^ 2)) * (‖v‖ ^ 2 - ‖w‖ ^ 2) +
        (f (x (n + 2)) - f (x (n + 1))) - inner ℝ (gradient f xInf) v := by
    have hsucc : n + 1 + 1 = n + 2 := by omega
    simp only [rem52_seqF, v, w, rem52_seqV, hsucc, inner_sub_right]
    ring
  have hnorm_id : ‖v‖ ^ 2 - ‖w‖ ^ 2 = 2 * inner ℝ acc v - ‖acc‖ ^ 2 := by
    rw [hacc_eq]
    have h1 := norm_sub_sq_real v w
    have hsub : inner ℝ (v - w) v = inner ℝ v v - inner ℝ w v := by
      rw [inner_sub_left]
    have hvv : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    have hwv : inner ℝ w v = inner ℝ v w := (real_inner_comm w v).symm
    nlinarith [h1, hsub, hvv, hwv]
  have hU_bound : inner ℝ U v ≤ θ / lam ^ 2 * ‖v‖ ^ 2 := by
    simpa [U, rem52_pairingU, v] using hpairn
  have hrem_v : |inner ℝ (err n) v| ≤ (η / 4) / lam * ‖v‖ ^ 2 := by
    simpa [v] using hremn.2
  have hrem_v' : -inner ℝ (err n) v ≤ (η / 4) / lam * ‖v‖ ^ 2 :=
    le_trans (neg_le_abs _) hrem_v
  have hcoer_v' : -(1 / lam) * inner ℝ (L v) v ≤ -(m / lam) * ‖v‖ ^ 2 := by
    have hcoer_v := hcoer v
    have hcomm : inner ℝ v (L v) = inner ℝ (L v) v := real_inner_comm _ _
    rw [hcomm] at hcoer_v
    have hmul : (1 / lam) * (m * ‖v‖ ^ 2) ≤ (1 / lam) * inner ℝ (L v) v :=
      mul_le_mul_of_nonneg_left hcoer_v (by positivity)
    have hneg := neg_le_neg hmul
    have heq : -((1 / lam) * (m * ‖v‖ ^ 2)) = -(m / lam) * ‖v‖ ^ 2 := by ring
    linarith
  have hconv_v' : f (x (n + 2)) - f (x (n + 1)) -
      inner ℝ (gradient f (x (n + 2))) v ≤ 0 := by
    have h := hconv n
    rw [hv_def]
    linarith
  have hmain_ineq : rem52_seqF x lam f xInf (n + 1) - rem52_seqF x lam f xInf n ≤
      inner ℝ U v - (1 / lam) * inner ℝ (L v) v +
        (f (x (n + 2)) - f (x (n + 1)) -
          inner ℝ (gradient f (x (n + 2))) v) := by
    rw [hdiff_id, hnorm_id]
    simp only [U, rem52_pairingU, acc, hz_eq, map_smul, real_inner_smul_left,
      inner_add_left, inner_sub_left]
    field_simp [ne_of_gt hlam]
    nlinarith [sq_nonneg ‖acc‖]
  refine le_trans hmain_ineq ?_
  have hsum := add_le_add (add_le_add hU_bound hcoer_v') hconv_v'
  have hη4 : (θ / lam ^ 2 - m / lam) * ‖v‖ ^ 2 ≤
      -((m - η) / lam) * ‖v‖ ^ 2 := by
    have hcoef : θ / lam ^ 2 - m / lam ≤ -((m - η) / lam) := by
      field_simp [ne_of_gt hlam]
      nlinarith [hθ, hη]
    exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖v‖)
  linarith [hmain_ineq, hsum, hη4]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Inequalities (43) and (51) in the abstract setting: the two-step Lyapunov
inputs for `H`. -/
private theorem rem52_H_eventual_inputs
    (x : ℕ → H) (lam m η : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hη : 0 < η) (hηm : η < m) (G F : ℕ → ℝ)
    (hF_nonneg : ∀ᶠ n in atTop, 0 ≤ F n)
    (hG_increment : ∀ᶠ n in atTop,
      G (n + 1) - G n + lam * F (n + 1) ≤
        (1 + η / 4) / lam * ‖rem52_seqV x n‖ ^ 2 +
          (1 / (2 * lam)) * ‖x (n + 1) - x n‖ ^ 2)
    (hF_decrement : ∀ᶠ n in atTop,
      F (n + 1) - F n ≤ -((m - η) / lam) * ‖rem52_seqV x n‖ ^ 2)
    (hG_lower : ∀ n, G n ≥ -(1 / m) * F n) :
    (∀ᶠ n in atTop,
        rem52_seqH m η G F (n + 1) - rem52_seqH m η G F n +
          lam * F (n + 1) ≤ 0) ∧
      (∀ᶠ n in atTop, 0 ≤ rem52_seqH m η G F n) ∧
      (∀ᶠ n in atTop, F (n + 1) ≤ F n) := by
  have hηpos : 0 < m - η := sub_pos.mpr hηm
  let A : ℝ := (1 + η) / (m - η)
  let B : ℝ := 1 / (2 * (m - η))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by linarith) (le_of_lt hηpos)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (by norm_num) (le_of_lt (by positivity : (0 : ℝ) < 2 * (m - η)))
  rcases eventually_atTop.mp hG_increment with ⟨NG, hGinc⟩
  rcases eventually_atTop.mp hF_decrement with ⟨NF, hFdec⟩
  rcases eventually_atTop.mp hF_nonneg with ⟨NFnn, hFnn⟩
  let N : ℕ := max NG (max (NF + 1) (NFnn + 1))
  have hN_inc : ∀ n ≥ N, NG ≤ n := by
    intro n hn
    exact le_trans (le_trans (le_max_left NG (max (NF + 1) (NFnn + 1))) hn) le_rfl
  have hN_dec : ∀ n ≥ N, NF ≤ n := by
    intro n hn
    have hle : NF + 1 ≤ n :=
      le_trans (le_trans (le_max_left (NF + 1) (NFnn + 1))
        (le_max_right NG (max (NF + 1) (NFnn + 1)))) hn
    omega
  have hN_nonneg : ∀ n ≥ N, NFnn ≤ n := by
    intro n hn
    have hle : NFnn + 1 ≤ n :=
      le_trans (le_trans (le_max_right (NF + 1) (NFnn + 1))
        (le_max_right NG (max (NF + 1) (NFnn + 1)))) hn
    omega
  have hN_one : ∀ n ≥ N, 1 ≤ n := by
    intro n hn
    have hle : NF + 1 ≤ n := by
      exact le_trans (le_trans (le_max_left (NF + 1) (NFnn + 1))
        (le_max_right NG (max (NF + 1) (NFnn + 1)))) hn
    omega
  constructor
  · filter_upwards [eventually_ge_atTop N] with n hn
    have hn1 : 1 ≤ n := hN_one n hn
    have hinc := hGinc n (hN_inc n hn)
    have hdecn := hFdec n (hN_dec n hn)
    have hdecprev := hFdec (n - 1) (by omega)
    have hdecprev' : F n - F (n - 1) ≤
        -((m - η) / lam) * ‖rem52_seqV x (n - 1)‖ ^ 2 := by
      simpa [Nat.sub_add_cancel hn1] using hdecprev
    have hAdec := mul_le_mul_of_nonneg_left hdecn hA
    have hAdec' : A * (F (n + 1) - F n) ≤
        -((1 + η) / lam) * ‖rem52_seqV x n‖ ^ 2 := by
      have hcoef : A * (-((m - η) / lam) * ‖rem52_seqV x n‖ ^ 2) =
          -((1 + η) / lam) * ‖rem52_seqV x n‖ ^ 2 := by
        dsimp [A]
        field_simp [ne_of_gt hηpos, ne_of_gt hlam]
      exact le_trans hAdec (le_of_eq hcoef)
    have hvprev : rem52_seqV x (n - 1) = x (n + 1) - x n := by
      dsimp [rem52_seqV]
      have h1 : n - 1 + 2 = n + 1 := by omega
      have h2 : n - 1 + 1 = n := by omega
      rw [h1, h2]
    have hBdec := mul_le_mul_of_nonneg_left hdecprev' hB
    have hBdec' : B * (F n - F (n - 1)) ≤
        -(1 / (2 * lam)) * ‖x (n + 1) - x n‖ ^ 2 := by
      rw [hvprev] at hBdec
      have hcoef : B * (-((m - η) / lam) * ‖x (n + 1) - x n‖ ^ 2) =
          -(1 / (2 * lam)) * ‖x (n + 1) - x n‖ ^ 2 := by
        dsimp [B]
        field_simp [ne_of_gt hηpos, ne_of_gt hlam]
      exact le_trans hBdec (le_of_eq hcoef)
    have hHdiff :
        rem52_seqH m η G F (n + 1) - rem52_seqH m η G F n + lam * F (n + 1) =
          (G (n + 1) - G n + lam * F (n + 1)) +
            A * (F (n + 1) - F n) + B * (F n - F (n - 1)) := by
      dsimp [rem52_seqH, A, B]
      ring
    rw [hHdiff]
    have hsum := add_le_add (add_le_add hinc hAdec') hBdec'
    have hcoef : (1 + η / 4) / lam - (1 + η) / lam = -(3 * η) / (4 * lam) := by
      field_simp [ne_of_gt hlam]
      ring
    have hv_nonneg : 0 ≤ ‖rem52_seqV x n‖ ^ 2 := sq_nonneg _
    have hnonpos : ((1 + η / 4) / lam - (1 + η) / lam) *
        ‖rem52_seqV x n‖ ^ 2 ≤ 0 := by
      rw [hcoef]
      have hcoef_nonneg : 0 ≤ (3 * η) / (4 * lam) :=
        div_nonneg (mul_nonneg (by norm_num) (le_of_lt hη)) (by positivity)
      have hcoef_nonpos : -(3 * η) / (4 * lam) ≤ 0 := by
        have hrewrite : -(3 * η) / (4 * lam) = -((3 * η) / (4 * lam)) := by ring
        rw [hrewrite]
        exact neg_nonpos.mpr hcoef_nonneg
      exact mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos hv_nonneg
    nlinarith [hsum, hnonpos]
  constructor
  · filter_upwards [eventually_ge_atTop N] with n hn
    have hn1 : 1 ≤ n := hN_one n hn
    have hG := hG_lower n
    have hFnnn := hFnn n (hN_nonneg n hn)
    have hdecprev := hFdec (n - 1) (by omega)
    have hdecprev' : F n - F (n - 1) ≤
        -((m - η) / lam) * ‖rem52_seqV x (n - 1)‖ ^ 2 := by
      simpa [Nat.sub_add_cancel hn1] using hdecprev
    have hFmono_prev : F n ≤ F (n - 1) := by
      have hv_nonneg : 0 ≤ ‖rem52_seqV x (n - 1)‖ ^ 2 := sq_nonneg _
      have hcoef_nonneg : 0 ≤ (m - η) / lam :=
        div_nonneg (le_of_lt hηpos) (le_of_lt hlam)
      have hterm_nonneg : 0 ≤ ((m - η) / lam) * ‖rem52_seqV x (n - 1)‖ ^ 2 :=
        mul_nonneg hcoef_nonneg hv_nonneg
      linarith
    have hBF : B * F n ≤ B * F (n - 1) := mul_le_mul_of_nonneg_left hFmono_prev hB
    have hcoef_nonneg : 0 ≤ A + B - 1 / m := by
      dsimp [A, B]
      field_simp [ne_of_gt hm, ne_of_gt hηpos]
      nlinarith [hm, hη, hηm]
    have hcoefF : 0 ≤ (A + B - 1 / m) * F n := mul_nonneg hcoef_nonneg hFnnn
    have hHnonneg : 0 ≤ G n + A * F n + B * F (n - 1) := by
      nlinarith [hG, hBF, hcoefF]
    simpa [rem52_seqH, A, B] using hHnonneg
  · filter_upwards [eventually_ge_atTop N] with n hn
    have hdec := hFdec n (hN_dec n hn)
    have hv_nonneg : 0 ≤ ‖rem52_seqV x n‖ ^ 2 := sq_nonneg _
    have hcoef_nonneg : 0 ≤ (m - η) / lam :=
      div_nonneg (le_of_lt hηpos) (le_of_lt hlam)
    have hterm_nonneg : 0 ≤ ((m - η) / lam) * ‖rem52_seqV x n‖ ^ 2 :=
      mul_nonneg hcoef_nonneg hv_nonneg
    linarith

private theorem rem52_geometric_of_two_step (H : ℕ → ℝ) (c β : ℝ) (N : ℕ)
    (hβ : 0 < β) (hc : c = 1 / (1 + β))
    (hH_nonneg : ∀ n ≥ N, 0 ≤ H n)
    (hcontr : ∀ n ≥ N, (1 + β) * H (n + 2) ≤ H n) :
    ∃ Kg : ℝ, ∃ nH : ℕ, 0 < Kg ∧ 0 < c ∧ c < 1 ∧
      ∀ n ≥ nH, H n ≤ Kg * c ^ ((n : ℝ) / 2) := by
  have hβ1pos : 0 < 1 + β := by linarith
  have hc_pos : 0 < c := by rw [hc]; positivity
  have hc_lt_one : c < 1 := by
    rw [hc]
    rw [div_lt_one hβ1pos]
    linarith
  let base : ℝ := max (H N) (H (N + 1)) + 1
  have hbase_pos : 0 < base := by
    have hHN : 0 ≤ H N := hH_nonneg N le_rfl
    have hmax : 0 ≤ max (H N) (H (N + 1)) := le_trans hHN (le_max_left _ _)
    dsimp [base]
    linarith
  let Kg : ℝ := base / c ^ (((N + 1 : ℕ) : ℝ) / 2)
  have hKg_pos : 0 < Kg := by
    dsimp [Kg]
    exact div_pos hbase_pos (Real.rpow_pos_of_pos hc_pos _)
  have hKg_base : Kg * c ^ (((N + 1 : ℕ) : ℝ) / 2) = base := by
    dsimp [Kg]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hc_pos _)]
  have hmain : ∀ n, N ≤ n → H n ≤ Kg * c ^ ((n : ℝ) / 2) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn
    by_cases hnN : n = N
    · subst hnN
      have hexp : ((n : ℝ) / 2) ≤ (((n + 1 : ℕ) : ℝ) / 2) := by
        push_cast
        nlinarith
      have hpow : c ^ (((n + 1 : ℕ) : ℝ) / 2) ≤ c ^ ((n : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hc_pos (le_of_lt hc_lt_one) hexp
      have hbase_le : base ≤ Kg * c ^ ((n : ℝ) / 2) := by
        calc
          base = Kg * c ^ (((n + 1 : ℕ) : ℝ) / 2) := hKg_base.symm
          _ ≤ Kg * c ^ ((n : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hpow (le_of_lt hKg_pos)
      have hbase_ge_HN : H n ≤ base := by
        dsimp [base]
        linarith [le_max_left (H n) (H (n + 1))]
      exact le_trans hbase_ge_HN hbase_le
    · by_cases hnN1 : n = N + 1
      · subst hnN1
        have hle : H (N + 1) ≤ Kg * c ^ (((N + 1 : ℕ) : ℝ) / 2) := by
          rw [hKg_base]
          dsimp [base]
          linarith [le_max_right (H N) (H (N + 1))]
        simpa using hle
      · have hn2 : N ≤ n - 2 := by omega
        have hlt : n - 2 < n := by omega
        have hn2ge2 : 2 ≤ n := by omega
        have hih := ih (n - 2) hlt hn2
        have hrec0 := hcontr (n - 2) hn2
        have hrec : (1 + β) * H n ≤ H (n - 2) := by
          simpa only [Nat.sub_add_cancel hn2ge2] using hrec0
        have hdiv : H n ≤ H (n - 2) / (1 + β) := by
          have h := div_le_div_of_nonneg_right hrec (le_of_lt hβ1pos)
          simpa [mul_div_cancel_left₀ (H n) (ne_of_gt hβ1pos)] using h
        have hc_inv : c = (1 + β)⁻¹ := by
          rw [hc]
          exact one_div _
        have hdiv' : H n ≤ H (n - 2) * c := by
          simpa [hc_inv, div_eq_mul_inv] using hdiv
        have hmul := mul_le_mul_of_nonneg_right hih (le_of_lt hc_pos)
        have hexp : ((n - 2 : ℕ) : ℝ) / 2 + 1 = (n : ℝ) / 2 := by
          rw [Nat.cast_sub hn2ge2]
          push_cast
          ring
        calc
          H n ≤ H (n - 2) * c := hdiv'
          _ ≤ (Kg * c ^ (((n - 2 : ℕ) : ℝ) / 2)) * c := hmul
          _ = Kg * c ^ ((n : ℝ) / 2) := by
            calc
              (Kg * c ^ (((n - 2 : ℕ) : ℝ) / 2)) * c
                  = Kg * (c ^ (((n - 2 : ℕ) : ℝ) / 2) * c ^ (1 : ℝ)) := by
                    rw [Real.rpow_one]
                    ring
              _ = Kg * c ^ (((n - 2 : ℕ) : ℝ) / 2 + 1) := by
                    rw [← Real.rpow_add hc_pos]
              _ = Kg * c ^ ((n : ℝ) / 2) := by rw [hexp]
  exact ⟨Kg, N, hKg_pos, hc_pos, hc_lt_one, hmain⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The Lyapunov inequality and comparison estimates give geometric decay of
`H`. -/
private theorem rem52_H_decay_geometric
    (_x : ℕ → H) (m η lam : ℝ) (_hm : 0 < m) (hη : 0 < η)
    (hηm : η < m) (hlam : 0 < lam) (tau0 : ℝ) (htau0 : 0 < tau0)
    (G F H : ℕ → ℝ)
    (hF_nonneg : ∀ᶠ n in atTop, 0 ≤ F n)
    (hF_nonincreasing : ∀ᶠ n in atTop, F (n + 1) ≤ F n)
    (_hG_lower : ∀ n, G n ≥ -(1 / m) * F n)
    (hG_upper : ∀ n, G n ≤ (1 / tau0) * F n)
    (hH_ineq : ∀ᶠ n in atTop,
      H (n + 1) - H n + lam * F (n + 1) ≤ 0)
    (hH_nonneg : ∀ᶠ n in atTop, 0 ≤ H n)
    (hH_def : ∀ n, H n = G n + ((1 + η) / (m - η)) * F n +
      (1 / (2 * (m - η))) * F (n - 1)) :
    let α : ℝ := (m - η) / (3 / 2 + η)
    let c : ℝ := (tau0 + α) / (tau0 + α + lam * tau0 * α)
    ∃ (Kg : ℝ) (nH : ℕ), 0 < Kg ∧ 0 < c ∧ c < 1 ∧
      ∀ n ≥ nH, H n ≤ Kg * c ^ ((n : ℝ) / 2) := by
  let α : ℝ := (m - η) / (3 / 2 + η)
  let c : ℝ := (tau0 + α) / (tau0 + α + lam * tau0 * α)
  change ∃ (Kg : ℝ) (nH : ℕ), 0 < Kg ∧ 0 < c ∧ c < 1 ∧
    ∀ n ≥ nH, H n ≤ Kg * c ^ ((n : ℝ) / 2)
  have hηpos : 0 < m - η := sub_pos.mpr hηm
  have hdenα : 0 < 3 / 2 + η := by norm_num; linarith
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos hηpos hdenα
  have hταpos : 0 < tau0 + α := add_pos htau0 hαpos
  have hβpos : 0 < lam * tau0 * α / (tau0 + α) :=
    div_pos (mul_pos (mul_pos hlam htau0) hαpos) hταpos
  have hc_eq : c = 1 / (1 + lam * tau0 * α / (tau0 + α)) := by
    dsimp [c]
    field_simp [ne_of_gt hταpos]
  rcases eventually_atTop.mp hF_nonneg with ⟨N1, hN1⟩
  rcases eventually_atTop.mp hF_nonincreasing with ⟨N2, hN2⟩
  rcases eventually_atTop.mp hH_ineq with ⟨N3, hN3⟩
  rcases eventually_atTop.mp hH_nonneg with ⟨N4, hN4⟩
  let N : ℕ := max (max N1 N2) (max N3 N4)
  have hN1N : N1 ≤ N := le_trans (le_max_left N1 N2) (le_max_left _ _)
  have hN2N : N2 ≤ N := le_trans (le_max_right N1 N2) (le_max_left _ _)
  have hN3N : N3 ≤ N := le_trans (le_max_left N3 N4) (le_max_right _ _)
  have hN4N : N4 ≤ N := le_trans (le_max_right N3 N4) (le_max_right _ _)
  have hFnn : ∀ n ≥ N, 0 ≤ F n := fun n hn => hN1 n (le_trans hN1N hn)
  have hFmono : ∀ n ≥ N, F (n + 1) ≤ F n :=
    fun n hn => hN2 n (le_trans hN2N hn)
  have hHineq : ∀ n ≥ N, H (n + 1) - H n + lam * F (n + 1) ≤ 0 :=
    fun n hn => hN3 n (le_trans hN3N hn)
  have hHnn : ∀ n ≥ N, 0 ≤ H n := fun n hn => hN4 n (le_trans hN4N hn)
  have hHmono : ∀ n ≥ N, H (n + 1) ≤ H n := by
    intro n hn
    have hineq := hHineq n hn
    have hFpos := hFnn (n + 1) (by omega)
    have hlamF : 0 ≤ lam * F (n + 1) := mul_nonneg (le_of_lt hlam) hFpos
    linarith
  have hcoef : (1 / tau0) + (1 + η) / (m - η) + 1 / (2 * (m - η)) =
      (tau0 + α) / (tau0 * α) := by
    dsimp [α]
    field_simp [ne_of_gt htau0, ne_of_gt hηpos]
    ring
  have hH_upper : ∀ n ≥ N,
      H (n + 2) ≤ ((tau0 + α) / (tau0 * α)) * F (n + 1) := by
    intro n hn
    have hGle := hG_upper (n + 2)
    have hFmono1 : F (n + 2) ≤ F (n + 1) := hFmono (n + 1) (by omega)
    have hG' : G (n + 2) ≤ (1 / tau0) * F (n + 1) := by
      calc
        G (n + 2) ≤ (1 / tau0) * F (n + 2) := hGle
        _ ≤ (1 / tau0) * F (n + 1) :=
          mul_le_mul_of_nonneg_left hFmono1 (by positivity)
    have hA_nonneg : 0 ≤ (1 + η) / (m - η) :=
      div_nonneg (by linarith) (le_of_lt hηpos)
    have hB_nonneg : 0 ≤ 1 / (2 * (m - η)) :=
      div_nonneg (by norm_num) (by positivity)
    have hdef := hH_def (n + 2)
    calc
      H (n + 2) = G (n + 2) + ((1 + η) / (m - η)) * F (n + 2) +
          (1 / (2 * (m - η))) * F (n + 1) := hdef
      _ ≤ (1 / tau0) * F (n + 1) + ((1 + η) / (m - η)) * F (n + 1) +
          (1 / (2 * (m - η))) * F (n + 1) := by
        gcongr
      _ = ((tau0 + α) / (tau0 * α)) * F (n + 1) := by
        rw [← hcoef]
        ring
  have hKpos : 0 < (tau0 + α) / (tau0 * α) :=
    div_pos hταpos (mul_pos htau0 hαpos)
  have hrecip : (tau0 * α) / (tau0 + α) * ((tau0 + α) / (tau0 * α)) = 1 := by
    field_simp [ne_of_gt hταpos, ne_of_gt htau0, ne_of_gt hαpos]
  have hF_from_H : ∀ n ≥ N,
      ((tau0 * α) / (tau0 + α)) * H (n + 2) ≤ F (n + 1) := by
    intro n hn
    have h := hH_upper n hn
    have hmul := mul_le_mul_of_nonneg_left h
      (le_of_lt (div_pos (mul_pos htau0 hαpos) hταpos))
    have hright : ((tau0 * α) / (tau0 + α)) *
        (((tau0 + α) / (tau0 * α)) * F (n + 1)) = F (n + 1) := by
      rw [← mul_assoc, hrecip, one_mul]
    exact le_trans hmul (le_of_eq hright)
  have hcontr : ∀ n ≥ N,
      (1 + lam * tau0 * α / (tau0 + α)) * H (n + 2) ≤ H n := by
    intro n hn
    have hineq := hHineq n hn
    have hFbound := hF_from_H n hn
    have hlamF := mul_le_mul_of_nonneg_left hFbound (le_of_lt hlam)
    have hlamF' : (lam * ((tau0 * α) / (tau0 + α))) * H (n + 2) ≤
        lam * F (n + 1) := by
      simpa [mul_assoc] using hlamF
    have hstep : H (n + 1) - H n +
        (lam * ((tau0 * α) / (tau0 + α))) * H (n + 2) ≤ 0 := by
      linarith [hineq, hlamF']
    have hmonoH := hHmono (n + 1) (by omega)
    have hKnonneg : 0 ≤ lam * ((tau0 * α) / (tau0 + α)) :=
      mul_nonneg (le_of_lt hlam) (le_of_lt (div_pos (mul_pos htau0 hαpos) hταpos))
    have hmonoHK := mul_le_mul_of_nonneg_right hmonoH hKnonneg
    have hsum : H (n + 2) + (lam * ((tau0 * α) / (tau0 + α))) * H (n + 2) ≤ H n := by
      linarith [hstep, hmonoHK]
    have htarget : (1 + lam * tau0 * α / (tau0 + α)) * H (n + 2) =
        H (n + 2) + (lam * ((tau0 * α) / (tau0 + α))) * H (n + 2) := by ring
    rw [htarget]
    exact hsum
  exact rem52_geometric_of_two_step H c (lam * tau0 * α / (tau0 + α)) N
    hβpos hc_eq hHnn hcontr

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Final extraction of the velocity decay from the geometric decay of `H`. -/
private theorem rem52_final_velocity_extraction
    (x : ℕ → H) (lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (F H : ℕ → ℝ) (K c : ℝ) (hK : 0 < K) (hc : 0 < c)
    (hc_lt_one : c < 1)
    (hF_lower : ∀ n,
      (1 / (2 * lam ^ 2)) * ‖x (n + 1) - x n‖ ^ 2 ≤ F n)
    (hH_lower : ∀ᶠ n in atTop, (1 / (2 * m)) * F n ≤ H n)
    (hH_decay : ∀ᶠ n in atTop, H n ≤ K * c ^ ((n : ℝ) / 2)) :
    ∃ (n0 : ℕ) (K' : ℝ) (q : ℝ), 0 < K' ∧ 0 < q ∧ q < 1 ∧
      ∀ n ≥ n0, ‖x (n + 1) - x n‖ ≤ K' * q ^ n := by
  rcases eventually_atTop.mp hH_decay with ⟨n0, hdecay⟩
  rcases eventually_atTop.mp hH_lower with ⟨n1, hlower⟩
  let n0' : ℕ := max n0 n1
  let S : ℝ := 4 * lam ^ 2 * m * K
  let K' : ℝ := Real.sqrt S
  let q : ℝ := c ^ (1 / 4 : ℝ)
  have hS_pos : 0 < S := by dsimp [S]; positivity
  have hK'_pos : 0 < K' := by
    dsimp [K']
    exact Real.sqrt_pos.2 hS_pos
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos hc _
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact (Real.rpow_lt_one_iff_of_pos hc).2 (Or.inr ⟨hc_lt_one, by norm_num⟩)
  have hq_pow_sq (n : ℕ) : (q ^ n) ^ 2 = c ^ ((n : ℝ) / 2) := by
    dsimp [q]
    rw [← pow_mul]
    rw [← Real.rpow_natCast (c ^ (1 / 4 : ℝ)) (n * 2)]
    rw [← Real.rpow_mul (le_of_lt hc)]
    congr 1
    push_cast
    ring
  refine ⟨n0', K', q, hK'_pos, hq_pos, hq_lt_one, ?_⟩
  intro n hn
  have hn0 : n0 ≤ n := le_trans (le_max_left n0 n1) hn
  have hn1 : n1 ≤ n := le_trans (le_max_right n0 n1) hn
  have hqn_nonneg : 0 ≤ q ^ n := pow_nonneg hq_nonneg n
  have hdecay_n : H n ≤ K * (q ^ n) ^ 2 := by
    rw [hq_pow_sq n]
    exact hdecay n hn0
  have hF_le_H : F n ≤ (2 * m) * H n := by
    have h := mul_le_mul_of_nonneg_left (hlower n hn1)
      (le_of_lt (by positivity : (0 : ℝ) < 2 * m))
    convert h using 1; field_simp [ne_of_gt hm]
  have hF_le : F n ≤ (2 * m * K) * (q ^ n) ^ 2 := by
    calc
      F n ≤ (2 * m) * H n := hF_le_H
      _ ≤ (2 * m) * (K * (q ^ n) ^ 2) :=
        mul_le_mul_of_nonneg_left hdecay_n (by positivity)
      _ = (2 * m * K) * (q ^ n) ^ 2 := by ring
  have hd_sq_le_F : ‖x (n + 1) - x n‖ ^ 2 ≤ (2 * lam ^ 2) * F n := by
    have h := mul_le_mul_of_nonneg_left (hF_lower n)
      (le_of_lt (by positivity : (0 : ℝ) < 2 * lam ^ 2))
    convert h using 1; field_simp [ne_of_gt hlam]
  have hd_sq_le_S : ‖x (n + 1) - x n‖ ^ 2 ≤ S * (q ^ n) ^ 2 := by
    calc
      ‖x (n + 1) - x n‖ ^ 2 ≤ (2 * lam ^ 2) * F n := hd_sq_le_F
      _ ≤ (2 * lam ^ 2) * ((2 * m * K) * (q ^ n) ^ 2) :=
        mul_le_mul_of_nonneg_left hF_le (by positivity)
      _ = S * (q ^ n) ^ 2 := by dsimp [S]; ring
  have htarget_sq : S * (q ^ n) ^ 2 = (K' * q ^ n) ^ 2 := by
    dsimp [K']
    rw [mul_pow, Real.sq_sqrt (le_of_lt hS_pos)]
  have hsq : ‖x (n + 1) - x n‖ ^ 2 ≤ (K' * q ^ n) ^ 2 := by
    rwa [← htarget_sq]
  have habs := sq_le_sq.mp hsq
  have hKq_nonneg : 0 ≤ K' * q ^ n := mul_nonneg (le_of_lt hK'_pos) hqn_nonneg
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hKq_nonneg] using habs

omit [CompleteSpace H] in
/-- The model-error decomposition identifies the moving support subgradient as
`sₙ = aₙ - Lzₙ - errₙ`. Since `aₙ → p`, `zₙ → 0`, and the quadratic error
bound forces `errₙ → 0`, the support subgradients converge to `p`. -/
private theorem rem52_model_subgradient_converges
    (a s err z : ℕ → H) (L : H →L[ℝ] H) (p : H) (Cerr : ℝ)
    (_hCerr : 0 < Cerr)
    (hz : Tendsto z atTop (𝓝 (0 : H)))
    (ha : Tendsto a atTop (𝓝 p))
    (hdecomp : ∀ᶠ n in atTop, a n = s n + L (z n) + err n)
    (herr : ∀ᶠ n in atTop, ‖err n‖ ≤ Cerr * ‖z n‖ ^ 2) :
    Tendsto s atTop (𝓝 p) := by
  have hz_norm : Tendsto (fun n : ℕ => ‖z n‖) atTop (𝓝 (0 : ℝ)) :=
    by simpa using (continuous_norm.tendsto (0 : H)).comp hz
  have hz_sq : Tendsto (fun n : ℕ => Cerr * ‖z n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul (hz_norm.pow 2)
  have herr_zero : Tendsto err atTop (𝓝 (0 : H)) :=
    squeeze_zero_norm' herr hz_sq
  have hLz_zero : Tendsto (fun n : ℕ => L (z n)) atTop (𝓝 (0 : H)) := by
    simpa using L.continuous.tendsto (0 : H) |>.comp hz
  have hlim : Tendsto (fun n : ℕ => a n - L (z n) - err n) atTop (𝓝 p) := by
    simpa using (ha.sub hLz_zero).sub herr_zero
  have hs_event : s =ᶠ[atTop] fun n : ℕ => a n - L (z n) - err n := by
    filter_upwards [hdecomp] with n hn
    rw [hn]
    abel
  exact hlim.congr' hs_event.symm

omit [CompleteSpace H] in
/-- Property (21): for a convex polyhedron `C`, normal-cone directions at
points `sₙ → p` are eventually normal-cone directions at the fixed point `p`. -/
private theorem rem52_polyhedron_normal_eventual_containment
    (C : Set H) (hC_poly : ConvexPolyhedron C) (p : H) (hp : p ∈ C)
    (s z : ℕ → H)
    (hs_mem : ∀ᶠ n in atTop, s n ∈ C)
    (hs_tendsto : Tendsto s atTop (𝓝 p))
    (hz_mem : ∀ᶠ n in atTop, z n ∈ normalCone C (s n)) :
    ∀ᶠ n in atTop, z n ∈ normalCone C p := by
  classical
  rcases hC_poly with ⟨m, a, b, hCeq⟩
  let V : Set H :=
    {x | ∀ i : Fin m, inner ℝ (a i) p < b i → inner ℝ (a i) x < b i}
  have hV_nhds : V ∈ 𝓝 p := by
    rw [← Filter.eventually_iff]
    rw [Filter.eventually_all]
    intro i
    by_cases hlt : inner ℝ (a i) p < b i
    · filter_upwards
        [((continuous_const.inner continuous_id).tendsto p).eventually_lt_const hlt]
        with x hx _
      exact hx
    · filter_upwards [] with x hx
      exact (hlt hx).elim
  have hsV : ∀ᶠ n in atTop, s n ∈ V := hs_tendsto.eventually hV_nhds
  filter_upwards [hsV, hs_mem, hz_mem] with n hsVn hsn hzn
  have hstable : normalCone C (s n) ⊆ normalCone C p := by
    intro u hu
    rw [mem_normalCone_iff_forall] at hu ⊢
    constructor
    · exact hp
    · intro y hyC
      by_contra hnot
      have hpos : 0 < inner ℝ (y - p) u := lt_of_not_ge hnot
      have hx_constraints : ∀ i : Fin m, inner ℝ (a i) (s n) ≤ b i := by
        have hx' : s n ∈ {z | ∀ i : Fin m, inner ℝ (a i) z ≤ b i} := by
          simpa [hCeq] using hu.1
        exact hx'
      have hp_constraints : ∀ i : Fin m, inner ℝ (a i) p ≤ b i := by
        have hp' : p ∈ {z | ∀ i : Fin m, inner ℝ (a i) z ≤ b i} := by
          simpa [hCeq] using hp
        exact hp'
      have hy_constraints : ∀ i : Fin m, inner ℝ (a i) y ≤ b i := by
        have hy' : y ∈ {z | ∀ i : Fin m, inner ℝ (a i) z ≤ b i} := by
          simpa [hCeq] using hyC
        exact hy'
      have hstep_event :
          ∀ᶠ t in 𝓝[>] (0 : ℝ),
            ∀ i : Fin m, inner ℝ (a i) (s n + t • (y - p)) ≤ b i := by
        rw [Filter.eventually_all]
        intro i
        by_cases hxlt : inner ℝ (a i) (s n) < b i
        · have htend :
              Tendsto (fun t : ℝ => inner ℝ (a i) (s n + t • (y - p)))
                (𝓝 (0 : ℝ)) (𝓝 (inner ℝ (a i) (s n))) := by
            have hcont : Continuous
                (fun t : ℝ => inner ℝ (a i) (s n + t • (y - p))) := by
              exact continuous_const.inner
                (continuous_const.add (continuous_id.smul continuous_const))
            simpa using hcont.tendsto 0
          filter_upwards
            [htend.eventually_lt_const hxlt |>.filter_mono nhdsWithin_le_nhds]
            with t ht
          exact le_of_lt ht
        · have hxeq : inner ℝ (a i) (s n) = b i :=
            le_antisymm (hx_constraints i) (le_of_not_gt hxlt)
          have hp_not_lt : ¬ inner ℝ (a i) p < b i := by
            intro hplt
            have hxlt' := hsVn i hplt
            rw [hxeq] at hxlt'
            exact (lt_irrefl (b i)) hxlt'
          have hpeq : inner ℝ (a i) p = b i :=
            le_antisymm (hp_constraints i) (le_of_not_gt hp_not_lt)
          have hdir : inner ℝ (a i) (y - p) ≤ 0 := by
            rw [inner_sub_right]
            linarith [hy_constraints i, hpeq]
          filter_upwards [self_mem_nhdsWithin] with t ht
          have ht_nonneg : 0 ≤ t := le_of_lt ht
          calc
            inner ℝ (a i) (s n + t • (y - p))
                = inner ℝ (a i) (s n) + t * inner ℝ (a i) (y - p) := by
                  rw [inner_add_right, inner_smul_right]
            _ ≤ b i := by nlinarith
      have hpos_event : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
      rcases (hstep_event.and hpos_event).exists with ⟨t, ht_constraints, ht_pos⟩
      let w : H := s n + t • (y - p)
      have hwC : w ∈ C := by
        rw [hCeq]
        exact ht_constraints
      have hnormal : inner ℝ u (w - s n) ≤ 0 := by
        simpa [real_inner_comm] using hu.2 w hwC
      have hinner_pos : 0 < inner ℝ (w - s n) u := by
        have hwsub : w - s n = t • (y - p) := by
          dsimp [w]
          abel
        rw [hwsub, inner_smul_left]
        exact mul_pos ht_pos hpos
      have hnormal' : inner ℝ (w - s n) u ≤ 0 := by
        simpa [real_inner_comm] using hnormal
      linarith
  exact hstable hzn

/-- Fixed-normal step of Proposition 5.1: if `C` is a convex polyhedron, the
points `sₙ ∈ C` are support-function subgradients at `zₙ`, and `sₙ → p` with
`p ∈ C`, then `zₙ` is eventually a normal direction to `C` at the fixed point
`p`. The subgradient relation turns `zₙ` into a normal direction at the moving
point `sₙ`, and polyhedral stability transfers it to `p`. -/
private theorem rem52_fixed_normal_from_polyhedron
    (C : Set H) (hC_poly : ConvexPolyhedron C) (hC0 : (0 : H) ∈ C)
    (p : H) (hp : p ∈ C) (s z : ℕ → H)
    (hs_mem : ∀ᶠ n in atTop, s n ∈ C)
    (hsub : ∀ᶠ n in atTop, s n ∈ subderivative (supportFunction C) (z n))
    (hs_tendsto : Tendsto s atTop (𝓝 p)) :
    ∀ᶠ n in atTop, z n ∈ normalCone C p := by
  have hC_closed : IsClosed C := by
    rcases hC_poly with ⟨m, a, b, hCeq⟩
    rw [hCeq]
    have hclosed : IsClosed (⋂ i : Fin m, {x : H | inner ℝ (a i) x ≤ b i}) :=
      isClosed_iInter fun i : Fin m => by
        have hcont : Continuous fun x : H => inner ℝ (a i) x := by fun_prop
        exact isClosed_le hcont (continuous_const : Continuous fun _ : H => b i)
    convert hclosed using 1
    ext x
    simp
  have hC_convex : Convex ℝ C := by
    rcases hC_poly with ⟨m, a, b, hCeq⟩
    rw [hCeq]
    intro x hx y hy α β hα hβ hαβ i
    calc
      inner ℝ (a i) (α • x + β • y)
          = α * inner ℝ (a i) x + β * inner ℝ (a i) y := by
            rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ ≤ α * b i + β * b i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) hα)
          (mul_le_mul_of_nonneg_left (hy i) hβ)
      _ = b i := by rw [← add_mul, hαβ, one_mul]
  have hz_mem : ∀ᶠ n in atTop, z n ∈ normalCone C (s n) := by
    filter_upwards [hs_mem, hsub] with n hsn hsubn
    have hcalc := rem52_support_subgradient_calculus C hC_closed hC_convex hC0 hsubn
    exact rem51_supportFunction_upper_mem_normalCone hcalc.1 (le_of_eq hcalc.2.1.symm)
  exact rem52_polyhedron_normal_eventual_containment C hC_poly p hp s z hs_mem
    hs_tendsto hz_mem

omit [CompleteSpace H] in
/-- Summing the eventual velocity inclusions in a fixed normal cone and taking
the order limit gives the corresponding inclusion of the tail
`x∞ - x(n+2)`. -/
private theorem rem52_normal_cone_tail_from_velocity
    (C : Set H) (p : H) (hp : p ∈ C) (x : ℕ → H) (xInf : H)
    (hx : Tendsto x atTop (𝓝 xInf))
    (hvel : ∀ᶠ n in atTop, x (n + 1) - x n ∈ normalCone C p) :
    ∀ᶠ n in atTop, xInf - x (n + 2) ∈ normalCone C p := by
  rcases eventually_atTop.mp hvel with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [mem_normalCone_iff_forall]
  constructor
  · exact hp
  · intro y hy
    let d : H := y - p
    have hpartial : ∀ K : ℕ, inner ℝ (x (n + 2 + K) - x (n + 2)) d ≤ 0 := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
          have hinc : x (n + 2 + (K + 1)) - x (n + 2) =
              (x (n + 2 + K) - x (n + 2)) +
                (x (n + 2 + (K + 1)) - x (n + 2 + K)) := by
            abel
          have hstep_mem :
              x (n + 2 + K + 1) - x (n + 2 + K) ∈ normalCone C p := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hN (n + 2 + K) (by omega)
          have hstep_ineq :
              inner ℝ (x (n + 2 + (K + 1)) - x (n + 2 + K)) d ≤ 0 := by
            rw [mem_normalCone_iff_forall] at hstep_mem
            have hstep_fun :
                ∀ y' ∈ C, inner ℝ (x (n + 2 + (K + 1)) - x (n + 2 + K))
                  (y' - p) ≤ 0 := by
              intro y' hy'
              simpa [real_inner_comm] using hstep_mem.2 y' hy'
            simpa [d] using hstep_fun y hy
          rw [hinc, inner_add_left]
          exact add_nonpos ih hstep_ineq
    have hshift : Tendsto (fun K : ℕ => n + 2 + K) atTop atTop :=
      Filter.tendsto_atTop_mono (fun K => Nat.le_add_left K (n + 2)) tendsto_id
    have hxshift : Tendsto (fun K : ℕ => x (n + 2 + K)) atTop (𝓝 xInf) :=
      hx.comp hshift
    have hlimH : Tendsto (fun K : ℕ => x (n + 2 + K) - x (n + 2)) atTop
        (𝓝 (xInf - x (n + 2))) := hxshift.sub tendsto_const_nhds
    have hlimR :
        Tendsto (fun K : ℕ => inner ℝ (x (n + 2 + K) - x (n + 2)) d) atTop
          (𝓝 (inner ℝ (xInf - x (n + 2)) d)) := by
      have hcont : Continuous (fun w : H => inner ℝ w d) :=
        continuous_id.inner continuous_const
      exact hcont.tendsto _ |>.comp hlimH
    rw [real_inner_comm]
    exact isClosed_Iic.mem_of_tendsto hlimR (Eventually.of_forall hpartial)

/-- The normal-cone tail and the model identities give the tail pairing (31).
The normal-cone inequality controls `⟨p - sₙ, x(n+2) - x∞⟩`, while the
quadratic error bound and `x(n+2) → x∞` absorb `⟨errₙ, x(n+2) - x∞⟩` into
every multiple of `‖vₙ‖²`. -/
private theorem rem52_tail_pairing_from_opposite_normal_cone
    (A : SetValuedOperator H H) (L : H →L[ℝ] H) (f : H → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (x : ℕ → H) (xInf p : H)
    (s err : ℕ → H) (Cerr : ℝ)
    (hCerr : 0 < Cerr)
    (_hp : p = -gradient f xInf)
    (htail : ∀ᶠ n in atTop,
      x (n + 2) - xInf ∈ -(normalCone (A (0 : H)) p))
    (hs_mem : ∀ᶠ n in atTop, s n ∈ A (0 : H))
    (hU : ∀ᶠ n in atTop,
      rem52_pairingU x xInf L f lam (rem52_seqZ x lam) n = p - s n - err n)
    (herr : ∀ᶠ n in atTop,
      ‖err n‖ ≤ Cerr * ‖rem52_seqZ x lam n‖ ^ 2)
    (_hz : Tendsto (rem52_seqZ x lam) atTop (𝓝 (0 : H)))
    (he : Tendsto (fun n : ℕ => x (n + 2) - xInf) atTop (𝓝 (0 : H))) :
    ∀ η > 0, ∀ᶠ n in atTop,
      inner ℝ (rem52_pairingU x xInf L f lam (rem52_seqZ x lam) n)
        (x (n + 2) - xInf) ≤ η * ‖rem52_seqV x n‖ ^ 2 := by
  intro η hη
  let eps : ℝ := η / (Cerr * lam⁻¹ ^ 2)
  have hden_pos : 0 < Cerr * lam⁻¹ ^ 2 :=
    mul_pos hCerr (sq_pos_of_pos (inv_pos.mpr hlam))
  have heps_pos : 0 < eps := div_pos hη hden_pos
  have he_norm : Tendsto (fun n : ℕ => ‖x (n + 2) - xInf‖) atTop (𝓝 (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mp he
  have he_small : ∀ᶠ n in atTop, ‖x (n + 2) - xInf‖ ≤ eps := by
    have hev := he_norm (Metric.ball_mem_nhds (0 : ℝ) heps_pos)
    filter_upwards [hev] with n hn
    have hlt : ‖x (n + 2) - xInf‖ < eps := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using hn
    exact le_of_lt hlt
  have hz_norm : ∀ n : ℕ,
      ‖rem52_seqZ x lam n‖ = lam⁻¹ * ‖rem52_seqV x n‖ := by
    intro n
    dsimp [rem52_seqZ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
  filter_upwards [htail, hs_mem, hU, herr, he_small] with n htailn hsn hUn herrn hen
  have htailn' : -(x (n + 2) - xInf) ∈ normalCone (A (0 : H)) p := by
    simpa using htailn
  have hsupport_pair : 0 ≤
      inner ℝ (s n - p) (x (n + 2) - xInf) := by
    have hnc := htailn'
    rw [mem_normalCone_iff_forall] at hnc
    have hineq := hnc.2 (s n) hsn
    rw [inner_neg_right] at hineq
    have hineq' : 0 ≤ inner ℝ (s n - p) (x (n + 2) - xInf) := by
      linarith
    exact hineq'
  have hUe : inner ℝ (rem52_pairingU x xInf L f lam (rem52_seqZ x lam) n)
        (x (n + 2) - xInf) =
      -inner ℝ (s n - p) (x (n + 2) - xInf) -
        inner ℝ (err n) (x (n + 2) - xInf) := by
    rw [hUn]
    simp only [inner_sub_left]
    ring
  have hzsq : ‖rem52_seqZ x lam n‖ ^ 2 =
      lam⁻¹ ^ 2 * ‖rem52_seqV x n‖ ^ 2 := by
    rw [hz_norm n]
    ring
  have herr_tail :
      |inner ℝ (err n) (x (n + 2) - xInf)| ≤ η * ‖rem52_seqV x n‖ ^ 2 := by
    calc
      |inner ℝ (err n) (x (n + 2) - xInf)| ≤
          ‖err n‖ * ‖x (n + 2) - xInf‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (Cerr * ‖rem52_seqZ x lam n‖ ^ 2) *
          ‖x (n + 2) - xInf‖ :=
        mul_le_mul_of_nonneg_right herrn (norm_nonneg _)
      _ ≤ (Cerr * ‖rem52_seqZ x lam n‖ ^ 2) * eps :=
        mul_le_mul_of_nonneg_left hen (by positivity)
      _ = η * ‖rem52_seqV x n‖ ^ 2 := by
        rw [hzsq]
        dsimp [eps]
        field_simp [ne_of_gt hCerr, ne_of_gt (sq_pos_of_pos (inv_pos.mpr hlam))]
  calc
    inner ℝ (rem52_pairingU x xInf L f lam (rem52_seqZ x lam) n)
        (x (n + 2) - xInf)
        = -inner ℝ (s n - p) (x (n + 2) - xInf) -
            inner ℝ (err n) (x (n + 2) - xInf) := hUe
    _ ≤ -inner ℝ (err n) (x (n + 2) - xInf) := by
      have hnonpos : -inner ℝ (s n - p) (x (n + 2) - xInf) ≤ 0 :=
        neg_nonpos.mpr hsupport_pair
      linarith
    _ ≤ |inner ℝ (err n) (x (n + 2) - xInf)| := neg_le_abs _
    _ ≤ η * ‖rem52_seqV x n‖ ^ 2 := herr_tail

/-- Number (31) once the polyhedrality of `A(0)` is supplied: the model error
decomposition identifies support-function subgradients `sₙ ∈ A(0)` with
`sₙ → p = -∇f(x∞)`, the fixed-normal step yields `zₙ ∈ N_{A(0)}(p)` eventually,
the cone property upgrades this to `vₙ = λzₙ ∈ N_{A(0)}(p)`, the telescoped
tail `x∞ - x(n+2)` stays in the cone, and the opposite-normal-cone estimate
produces the tail pairing `⟨Uₙ, x(n+2) - x∞⟩ ≤ η‖vₙ‖²`. -/
private theorem rem52_tail_pairing_from_polyhedron
    (A : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ)
    (hAzero_int : (0 : H) ∈ interior (A (0 : H)))
    (hAz_poly : ConvexPolyhedron (A (0 : H)))
    (L : H →L[ℝ] H) (_hL_symm : ∀ x y, inner ℝ (L x) y = inner ℝ x (L y))
    (m : ℝ) (_hm : m > 0) (_hL_coercive : ∀ x, inner ℝ (L x) x ≥ m * ‖x‖ ^ 2)
    (h_condition : (fun (x : H) =>
      setExcess (A x) (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H)))
      =O[𝓝 (0 : H)] (fun (x : H) => ‖x‖ ^ 2))
    (f : H → ℝ) (_hf_conv : ConvexOn ℝ Set.univ f) (hf_C1 : ContDiff ℝ 1 f)
    (_hinf : ∃ m, ∀ x, f x ≥ m)
    (M : ℝ) (_hf_strongConv : IsStronglyConvex f M)
    (B : SetValuedOperator H H)
    (hB_eq_grad : B = SetValuedOperator.ofFunction Set.univ
      (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam : ℝ) (hlam : lam > 0) (lam_seq : ℕ → ℝ) (hlam_seq : ∀ n, lam_seq n = lam)
    (x : ℕ → H) (halg : AlgorithmA A B x lam_seq) (xInf : H)
    (hxInf : Tendsto x atTop (𝓝 xInf)) :
    ∀ η > 0, ∀ᶠ n in atTop,
      inner ℝ (rem52_pairingU x xInf L f lam (rem52_seqZ x lam) n)
        (x (n + 2) - xInf) ≤ η * ‖rem52_seqV x n‖ ^ 2 := by
  classical
  let z : ℕ → H := rem52_seqZ x lam
  let acc : ℕ → H := fun n => ((lam_seq n) ^ 2)⁻¹ • rem52_seqAcc x n
  have hshift1 : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  have hshift2 : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n 2) tendsto_id
  have hx1 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 xInf) :=
    hxInf.comp hshift1
  have hx2 : Tendsto (fun n : ℕ => x (n + 2)) atTop (𝓝 xInf) :=
    hxInf.comp hshift2
  have hv_tendsto : Tendsto (rem52_seqV x) atTop (𝓝 (0 : H)) := by
    simpa [rem52_seqV] using hx2.sub hx1
  have hz_tendsto : Tendsto z atTop (𝓝 (0 : H)) := by
    have hc : Tendsto (fun _ : ℕ => lam⁻¹) atTop (𝓝 lam⁻¹) := tendsto_const_nhds
    simpa [z, rem52_seqZ] using hc.smul hv_tendsto
  have he_tendsto : Tendsto (fun n : ℕ => x (n + 2) - xInf) atTop (𝓝 (0 : H)) := by
    have hconst : Tendsto (fun _ : ℕ => xInf) atTop (𝓝 xInf) := tendsto_const_nhds
    simpa using hx2.sub hconst
  have hgrad_cont : Continuous (gradient f) := by
    have hfderiv : Continuous (fun y : H => fderiv ℝ f y) :=
      hf_C1.continuous_fderiv (by norm_num)
    change Continuous (fun y : H => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ f y))
    exact ((InnerProductSpace.toDual ℝ H).symm).continuous.comp hfderiv
  choose a b ha hb hstep using rem51_algorithm_step_selection A B lam_seq x halg
  have ha_mem : ∀ n, a n ∈ A (z n) := by
    intro n
    have h := ha n
    simpa [z, rem52_seqZ, hlam_seq n] using h
  have hb_eq : ∀ n : ℕ, b n = gradient f (x (n + 2)) :=
    fun n => rem51_mem_gradient_operator_eq B f hB_eq_grad (hb n)
  have hacc_tendsto : Tendsto acc atTop (𝓝 (0 : H)) := by
    have hconst : Tendsto (fun n : ℕ => ((lam_seq n) ^ 2)⁻¹) atTop
        (𝓝 ((lam ^ 2)⁻¹)) := by
      simp [hlam_seq]
    have hdiff : Tendsto
        (fun n : ℕ => x (n + 2) - 2 • x (n + 1) + x n) atTop (𝓝 (0 : H)) := by
      have h2 : Tendsto (fun n : ℕ => 2 • x (n + 1)) atTop (𝓝 (2 • xInf)) :=
        hx1.const_smul 2
      have hsum : Tendsto (fun n : ℕ => x (n + 2) - 2 • x (n + 1) + x n) atTop
          (𝓝 (xInf - 2 • xInf + xInf)) := (hx2.sub h2).add hxInf
      have hzero : xInf - 2 • xInf + xInf = (0 : H) := by abel
      simpa [hzero] using hsum
    simpa [acc, rem52_seqAcc, smul_add] using hconst.smul hdiff
  have hb_tendsto : Tendsto b atTop (𝓝 (gradient f xInf)) := by
    have hgrad_seq : Tendsto (fun n : ℕ => gradient f (x (n + 2))) atTop
        (𝓝 (gradient f xInf)) := (hgrad_cont.tendsto xInf).comp hx2
    exact hgrad_seq.congr' (Filter.Eventually.of_forall (fun n => (hb_eq n).symm))
  have ha_eq : ∀ n : ℕ, a n = -acc n - b n := by
    intro n
    have h : acc n + a n + b n = 0 := by
      simpa [acc, rem52_seqAcc, smul_add, add_assoc] using hstep n
    calc
      a n = (acc n + a n + b n) - acc n - b n := by abel
      _ = (0 : H) - acc n - b n := by rw [h]
      _ = -acc n - b n := by simp
  have ha_tendsto : Tendsto a atTop (𝓝 (-gradient f xInf)) := by
    have hlim : Tendsto (fun n : ℕ => -acc n - b n) atTop
        (𝓝 (-(0 : H) - gradient f xInf)) := hacc_tendsto.neg.sub hb_tendsto
    have hfun : a = fun n : ℕ => -acc n - b n := funext ha_eq
    rw [hfun]
    simpa using hlim
  have hp_mem : -gradient f xInf ∈ A (0 : H) :=
    rem51_limit_point_mem_A_zero A hA f hf_C1 B hB_eq_grad lam hlam lam_seq
      hlam_seq x halg xInf hxInf
  rcases rem52_model_regularity A hA hdomA L z hz_tendsto with ⟨hmodel_nonempty, hbdd⟩
  rcases rem52_model_error_decomposition A L h_condition z a hz_tendsto ha_mem
      hmodel_nonempty hbdd with ⟨Cerr, hCerr_pos, hdecomp⟩
  let P : ℕ → Prop := fun n => ∃ s err : H,
    s ∈ subderivative (supportFunction (A (0 : H))) (z n) ∧
    a n = s + L (z n) + err ∧ ‖err‖ ≤ Cerr * ‖z n‖ ^ 2
  let s : ℕ → H := fun n => if h : P n then Classical.choose h else 0
  let err : ℕ → H := fun n =>
    if h : P n then Classical.choose (Classical.choose_spec h) else 0
  have hs_event : ∀ᶠ n in atTop,
      s n ∈ subderivative (supportFunction (A (0 : H))) (z n) := by
    filter_upwards [hdecomp] with n hn
    dsimp [s]
    rw [dif_pos hn]
    exact (Classical.choose_spec (Classical.choose_spec hn)).1
  have herr_bound_event : ∀ᶠ n in atTop,
      ‖err n‖ ≤ Cerr * ‖z n‖ ^ 2 := by
    filter_upwards [hdecomp] with n hn
    dsimp [err]
    rw [dif_pos hn]
    exact (Classical.choose_spec (Classical.choose_spec hn)).2.2
  have ha_decomp_event : ∀ᶠ n in atTop,
      a n = s n + L (z n) + err n := by
    filter_upwards [hdecomp] with n hn
    dsimp [s, err]
    rw [dif_pos hn, dif_pos hn]
    exact (Classical.choose_spec (Classical.choose_spec hn)).2.1
  let p : H := -gradient f xInf
  have hp : p = -gradient f xInf := rfl
  have hp_mem' : p ∈ A (0 : H) := by simpa [p] using hp_mem
  have hs_tendsto : Tendsto s atTop (𝓝 p) := by
    simpa [p] using rem52_model_subgradient_converges a s err z L (-gradient f xInf)
      Cerr hCerr_pos hz_tendsto ha_tendsto ha_decomp_event herr_bound_event
  have hC0 : (0 : H) ∈ A (0 : H) := interior_subset hAzero_int
  have hC_closed : IsClosed (A (0 : H)) := rem51_value_closed A hA 0
  have hC_convex : Convex ℝ (A (0 : H)) := rem51_value_convex A hA 0
  have hs_mem : ∀ᶠ n in atTop, s n ∈ A (0 : H) := by
    filter_upwards [hs_event] with n hsn
    exact (rem52_support_subgradient_calculus (A (0 : H)) hC_closed hC_convex hC0 hsn).1
  have hz_normal : ∀ᶠ n in atTop, z n ∈ normalCone (A (0 : H)) p :=
    rem52_fixed_normal_from_polyhedron (A (0 : H)) hAz_poly hC0 p hp_mem' s z
      hs_mem hs_event hs_tendsto
  have hv_normal : ∀ᶠ n in atTop, rem52_seqV x n ∈ normalCone (A (0 : H)) p := by
    filter_upwards [hz_normal] with n hn
    have hv_eq : rem52_seqV x n = lam • z n := by
      dsimp [z, rem52_seqZ, rem52_seqV]
      rw [smul_smul]
      have hmul : lam * lam⁻¹ = 1 := by field_simp [ne_of_gt hlam]
      rw [hmul, one_smul]
    rw [hv_eq]
    rw [mem_normalCone_iff_forall] at hn ⊢
    constructor
    · exact hn.1
    · intro y hy
      rw [inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hlam) (hn.2 y hy)
  have htail_y :
      ∀ᶠ n in atTop, xInf - x ((n + 1) + 2) ∈ normalCone (A (0 : H)) p := by
    exact rem52_normal_cone_tail_from_velocity (A (0 : H)) p hp_mem'
      (fun n : ℕ => x (n + 1)) xInf hx1 (by
        filter_upwards [hv_normal] with n hn
        simpa [rem52_seqV, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn)
  have htail : ∀ᶠ n in atTop,
      x (n + 2) - xInf ∈ -(normalCone (A (0 : H)) p) := by
    rcases eventually_atTop.mp htail_y with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop (N + 1)] with n hn
    have hn1 : 1 ≤ n := by omega
    have hk : n - 1 + 2 = n + 1 := by omega
    have hm : xInf - x (n + 2) ∈ normalCone (A (0 : H)) p := by
      have h := hN (n - 1) (by omega)
      simpa [hk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    rw [Set.mem_neg]
    simpa using hm
  have hU : ∀ᶠ n in atTop,
      rem52_pairingU x xInf L f lam z n = p - s n - err n := by
    filter_upwards [ha_decomp_event] with n hdec
    have hb_eq_n : b n = gradient f (x (n + 2)) := hb_eq n
    have hstep_acc : ((lam ^ 2)⁻¹) • rem52_seqAcc x n =
        -a n - gradient f (x (n + 2)) := by
      have h' : ((lam ^ 2)⁻¹) • rem52_seqAcc x n + a n +
          gradient f (x (n + 2)) = 0 := by
        simpa [hlam_seq n, hb_eq_n, rem52_seqAcc, acc] using hstep n
      have hneg : -(((lam ^ 2)⁻¹) • rem52_seqAcc x n) =
          a n + gradient f (x (n + 2)) := by
        have h0 : ((lam ^ 2)⁻¹) • rem52_seqAcc x n +
            (a n + gradient f (x (n + 2))) = 0 := by
          simpa [add_assoc] using h'
        exact (eq_neg_of_add_eq_zero_right h0).symm
      calc
        ((lam ^ 2)⁻¹) • rem52_seqAcc x n =
            -(-(((lam ^ 2)⁻¹) • rem52_seqAcc x n)) := by simp
        _ = -(a n + gradient f (x (n + 2))) := by rw [hneg]
        _ = -a n - gradient f (x (n + 2)) := by abel
    dsimp [rem52_pairingU, p]
    rw [hstep_acc, hdec]
    module
  exact rem52_tail_pairing_from_opposite_normal_cone A L f lam hlam x xInf p s err
    Cerr hCerr_pos hp htail hs_mem hU herr_bound_event hz_tendsto he_tendsto

set_option maxHeartbeats 1200000 in -- long `linarith` chains over the Lyapunov estimates
/-- Remark 5.1 assembly, conditional on the paper's unproved tail pairing (31):
with `Uₙ = λ⁻²accₙ + Lzₙ + ∇f(x_{n+2}) - ∇f(x∞)`, `zₙ = λ⁻¹vₙ`, assume that for
every `η > 0` eventually `⟨Uₙ, x(n+2) - x∞⟩ ≤ η‖vₙ‖²`. Then the proved model
decomposition, the `G`/`F` increment estimates, the `H` comparison, the
geometric decay lemma, and the final velocity extraction yield the
velocity-decay conclusion of `rem_5_1`. This helper isolates the missing
pairing as an explicit premise instead of assuming it as a theorem. -/
private theorem rem52_assembly_from_tail_pairing
    (A : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ)
    (hAzero_int : (0 : H) ∈ interior (A (0 : H)))
    (L : H →L[ℝ] H) (hL_symm : ∀ x y, inner ℝ (L x) y = inner ℝ x (L y))
    (m : ℝ) (hm : m > 0) (hL_coercive : ∀ x, inner ℝ (L x) x ≥ m * ‖x‖ ^ 2)
    (h_condition : (fun (x : H) =>
      setExcess (A x) (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H)))
      =O[𝓝 (0 : H)] (fun (x : H) => ‖x‖ ^ 2))
    (f : H → ℝ) (_hf_conv : ConvexOn ℝ Set.univ f) (hf_C1 : ContDiff ℝ 1 f)
    (_hinf : ∃ m, ∀ x, f x ≥ m)
    (M : ℝ) (hf_strongConv : IsStronglyConvex f M)
    (B : SetValuedOperator H H)
    (hB_eq_grad : B = SetValuedOperator.ofFunction Set.univ
      (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam : ℝ) (hlam : lam > 0) (lam_seq : ℕ → ℝ) (hlam_seq : ∀ n, lam_seq n = lam)
    (x : ℕ → H) (halg : AlgorithmA A B x lam_seq) (xInf : H)
    (hxInf : Tendsto x atTop (𝓝 xInf))
    (htail : ∀ η > 0, ∀ᶠ n in atTop,
      inner ℝ (rem52_pairingU x xInf L f lam (rem52_seqZ x lam) n) (x (n + 2) - xInf)
        ≤ η * ‖rem52_seqV x n‖ ^ 2) :
    ∃ (n0 : ℕ) (K : ℝ) (q : ℝ), K > 0 ∧ q > 0 ∧ q < 1 ∧
      ∀ n ≥ n0, ‖x (n+1) - x n‖ ≤ K * q ^ n := by
  classical
  let v : ℕ → H := rem52_seqV x
  let z : ℕ → H := rem52_seqZ x lam
  have hshift1 : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  have hshift2 : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n 2) tendsto_id
  have hx1 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 xInf) :=
    hxInf.comp hshift1
  have hx2 : Tendsto (fun n : ℕ => x (n + 2)) atTop (𝓝 xInf) :=
    hxInf.comp hshift2
  have hv_tendsto : Tendsto v atTop (𝓝 (0 : H)) := by
    simpa [v, rem52_seqV] using hx2.sub hx1
  have hz_tendsto : Tendsto z atTop (𝓝 (0 : H)) := by
    have hc : Tendsto (fun _ : ℕ => lam⁻¹) atTop (𝓝 lam⁻¹) := tendsto_const_nhds
    simpa [z, rem52_seqZ, v] using hc.smul hv_tendsto
  have hsmall_norm : ∀ (u : ℕ → H), Tendsto u atTop (𝓝 (0 : H)) →
      ∀ {ε : ℝ}, 0 < ε → ∀ᶠ n in atTop, ‖u n‖ ≤ ε := by
    intro u hu ε hε
    have hnorm : Tendsto (fun n : ℕ => ‖u n‖) atTop (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm.tendsto (0 : H)).comp hu
    have hev := hnorm (Metric.ball_mem_nhds (0 : ℝ) hε)
    filter_upwards [hev] with n hn
    have hlt : ‖u n‖ < ε := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using hn
    exact le_of_lt hlt
  have hsmall_v : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ n in atTop, ‖v n‖ ≤ ε :=
    fun {ε} hε => hsmall_norm v hv_tendsto hε
  have htail_tendsto : Tendsto (fun n : ℕ => x (n + 2) - xInf) atTop (𝓝 (0 : H)) := by
    have hconst : Tendsto (fun _ : ℕ => xInf) atTop (𝓝 xInf) := tendsto_const_nhds
    simpa using hx2.sub hconst
  have hsmall_tail : ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ n in atTop, ‖x (n + 2) - xInf‖ ≤ ε :=
    fun {ε} hε => hsmall_norm (fun n : ℕ => x (n + 2) - xInf) htail_tendsto hε
  have hz_norm_sq : ∀ n : ℕ, ‖z n‖ ^ 2 = lam⁻¹ ^ 2 * ‖v n‖ ^ 2 := by
    intro n
    have hz_norm : ‖z n‖ = lam⁻¹ * ‖v n‖ := by
      dsimp [z, rem52_seqZ]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
    rw [hz_norm]
    ring
  choose a b ha hb hstep using rem51_algorithm_step_selection A B lam_seq x halg
  have ha_mem : ∀ n, a n ∈ A (z n) := by
    intro n
    have h := ha n
    simpa [z, rem52_seqZ, v, rem52_seqV, hlam_seq n] using h
  have hp : -gradient f xInf ∈ A (0 : H) :=
    rem51_limit_point_mem_A_zero A hA f hf_C1 B hB_eq_grad lam hlam lam_seq
      hlam_seq x halg xInf hxInf
  rcases rem52_model_regularity A hA hdomA L z hz_tendsto with ⟨hmodel_nonempty, hbdd⟩
  rcases rem52_model_error_decomposition A L h_condition z a hz_tendsto ha_mem
      hmodel_nonempty hbdd with ⟨Cerr, hCerr_pos, hdecomp⟩
  let P : ℕ → Prop := fun n => ∃ s err : H,
    s ∈ subderivative (supportFunction (A (0 : H))) (z n) ∧
    a n = s + L (z n) + err ∧ ‖err‖ ≤ Cerr * ‖z n‖ ^ 2
  let s : ℕ → H := fun n => if h : P n then Classical.choose h else 0
  let err : ℕ → H := fun n =>
    if h : P n then Classical.choose (Classical.choose_spec h) else 0
  have hs_event : ∀ᶠ n in atTop,
      s n ∈ subderivative (supportFunction (A (0 : H))) (z n) := by
    filter_upwards [hdecomp] with n hn
    dsimp [s]
    rw [dif_pos hn]
    exact (Classical.choose_spec (Classical.choose_spec hn)).1
  have herr_bound_event : ∀ᶠ n in atTop,
      ‖err n‖ ≤ Cerr * ‖z n‖ ^ 2 := by
    filter_upwards [hdecomp] with n hn
    dsimp [err]
    rw [dif_pos hn]
    exact (Classical.choose_spec (Classical.choose_spec hn)).2.2
  have ha_decomp_event : ∀ᶠ n in atTop,
      a n = s n + L (z n) + err n := by
    filter_upwards [hdecomp] with n hn
    dsimp [s, err]
    rw [dif_pos hn, dif_pos hn]
    exact (Classical.choose_spec (Classical.choose_spec hn)).2.1
  let eta : ℝ := m / 2
  have heta_pos : 0 < eta := by dsimp [eta]; positivity
  have heta_lt : eta < m := by dsimp [eta]; linarith
  let theta : ℝ := min (eta / 16) (3 * eta * lam / 32)
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    positivity
  have htheta_le : theta ≤ 3 * eta * lam / 4 := by
    have h1 : theta ≤ 3 * eta * lam / 32 := by
      dsimp [theta]
      exact min_le_right _ _
    have h2 : 3 * eta * lam / 32 ≤ 3 * eta * lam / 4 := by
      nlinarith [mul_pos heta_pos hlam]
    exact le_trans h1 h2
  let delta : ℝ := eta / 4 - theta
  have hdelta_pos : 0 < delta := by
    have hle : theta ≤ eta / 16 := by
      dsimp [theta]
      exact min_le_left _ _
    dsimp [delta]
    linarith
  have hdelta_theta : delta + theta = eta / 4 := by
    dsimp [delta]
    ring
  have hpair31 : ∀ᶠ n in atTop,
      inner ℝ (rem52_pairingU x xInf L f lam z n) (x (n + 2) - xInf) ≤
        theta / lam ^ 2 * ‖rem52_seqV x n‖ ^ 2 := by
    have hθ : 0 < theta / lam ^ 2 := div_pos htheta_pos (sq_pos_of_pos hlam)
    simpa [z, v] using htail (theta / lam ^ 2) hθ
  have hpairF_event : ∀ᶠ n in atTop,
      inner ℝ (rem52_pairingU x xInf L f lam z n) (rem52_seqV x n) ≤
        theta / lam ^ 2 * ‖rem52_seqV x n‖ ^ 2 := by
    have hvsmall : ∀ᶠ n in atTop, ‖v n‖ ≤ theta / Cerr :=
      hsmall_v (div_pos htheta_pos hCerr_pos)
    filter_upwards [hs_event, ha_decomp_event, herr_bound_event, hvsmall] with
      n hs hdec herr hvsmall
    let p : H := -gradient f xInf
    have hp_mem : p ∈ A (0 : H) := by simpa [p] using hp
    have hC0 : (0 : H) ∈ A (0 : H) := interior_subset hAzero_int
    have hcalc := rem52_support_subgradient_calculus (A (0 : H))
      (rem51_value_closed A hA 0) (rem51_value_convex A hA 0) hC0 hs
    have hp_le_sup : (inner ℝ p (z n) : EReal) ≤
        (inner ℝ (s n) (z n) : EReal) := by
      calc
        (inner ℝ p (z n) : EReal) ≤ supportFunction (A (0 : H)) (z n) :=
          rem51_inner_le_supportFunction (C := A (0 : H)) hp_mem
        _ = (inner ℝ (s n) (z n) : EReal) := hcalc.2.1.symm
    have hspairz : 0 ≤ inner ℝ (s n - p) (z n) := by
      have hreal := EReal.coe_le_coe_iff.mp hp_le_sup
      rw [inner_sub_left]
      linarith
    have hzv : v n = lam • z n := by
      dsimp [v, z, rem52_seqZ, rem52_seqV]
      rw [smul_smul]
      have hmul : lam * lam⁻¹ = 1 := by field_simp [ne_of_gt hlam]
      rw [hmul, one_smul]
    have hspairv : 0 ≤ inner ℝ (s n - p) (v n) := by
      rw [hzv, inner_smul_right]
      exact mul_nonneg (le_of_lt hlam) hspairz
    have hb_eq : b n = gradient f (x (n + 2)) :=
      rem51_mem_gradient_operator_eq B f hB_eq_grad (hb n)
    have hstep_acc : ((lam ^ 2)⁻¹) • rem52_seqAcc x n =
        -a n - gradient f (x (n + 2)) := by
      have h' : ((lam ^ 2)⁻¹) • rem52_seqAcc x n + a n +
          gradient f (x (n + 2)) = 0 := by
        simpa [hlam_seq n, hb_eq, rem52_seqAcc] using hstep n
      have hneg : -(((lam ^ 2)⁻¹) • rem52_seqAcc x n) =
          a n + gradient f (x (n + 2)) := by
        have h0 : ((lam ^ 2)⁻¹) • rem52_seqAcc x n +
            (a n + gradient f (x (n + 2))) = 0 := by
          simpa [add_assoc] using h'
        exact (eq_neg_of_add_eq_zero_right h0).symm
      calc
        ((lam ^ 2)⁻¹) • rem52_seqAcc x n =
            -(-(((lam ^ 2)⁻¹) • rem52_seqAcc x n)) := by simp
        _ = -(a n + gradient f (x (n + 2))) := by rw [hneg]
        _ = -a n - gradient f (x (n + 2)) := by abel
    have hU_eq : rem52_pairingU x xInf L f lam z n = -(s n - p) - err n := by
      dsimp [rem52_pairingU, p]
      rw [hstep_acc, hdec]
      module
    have hpairv_eq : inner ℝ (rem52_pairingU x xInf L f lam z n) (v n) =
        -inner ℝ (s n - p) (v n) - inner ℝ (err n) (v n) := by
      rw [hU_eq, inner_sub_left, inner_neg_left]
    have herrpair : |inner ℝ (err n) (v n)| ≤
        theta / lam ^ 2 * ‖v n‖ ^ 2 := by
      have hCv : Cerr * ‖v n‖ ≤ theta := by
        simpa [mul_comm] using (le_div_iff₀ hCerr_pos).mp hvsmall
      calc
        |inner ℝ (err n) (v n)| ≤ ‖err n‖ * ‖v n‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (Cerr * ‖z n‖ ^ 2) * ‖v n‖ :=
          mul_le_mul_of_nonneg_right herr (norm_nonneg _)
        _ = (Cerr * ‖v n‖) * (lam⁻¹ ^ 2 * ‖v n‖ ^ 2) := by
          rw [hz_norm_sq n]
          ring
        _ ≤ theta * (lam⁻¹ ^ 2 * ‖v n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hCv (by positivity)
        _ = theta / lam ^ 2 * ‖v n‖ ^ 2 := by
          ring
    calc
      inner ℝ (rem52_pairingU x xInf L f lam z n) (rem52_seqV x n) =
          -inner ℝ (s n - p) (v n) - inner ℝ (err n) (v n) := by
            simpa [v] using hpairv_eq
      _ ≤ -inner ℝ (err n) (v n) := by
            have hnonpos : -inner ℝ (s n - p) (v n) ≤ 0 := neg_nonpos.mpr hspairv
            linarith
      _ ≤ |inner ℝ (err n) (v n)| := neg_le_abs _
      _ ≤ theta / lam ^ 2 * ‖v n‖ ^ 2 := herrpair
  have hrem_tail_any : ∀ κ : ℝ, 0 < κ → ∀ᶠ n in atTop,
      |inner ℝ (err n) (x (n + 2) - xInf)| ≤
        κ / lam ^ 2 * ‖v n‖ ^ 2 := by
    intro κ hκ
    have htail_small : ∀ᶠ n in atTop, ‖x (n + 2) - xInf‖ ≤ κ / Cerr :=
      hsmall_tail (div_pos hκ hCerr_pos)
    filter_upwards [herr_bound_event, htail_small] with n herr htail
    calc
      |inner ℝ (err n) (x (n + 2) - xInf)| ≤
          ‖err n‖ * ‖x (n + 2) - xInf‖ := abs_real_inner_le_norm _ _
      _ ≤ (Cerr * ‖z n‖ ^ 2) * ‖x (n + 2) - xInf‖ :=
          mul_le_mul_of_nonneg_right herr (norm_nonneg _)
      _ ≤ (Cerr * ‖z n‖ ^ 2) * (κ / Cerr) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = ‖z n‖ ^ 2 * κ := by
          field_simp [ne_of_gt hCerr_pos]
      _ = κ / lam ^ 2 * ‖v n‖ ^ 2 := by
          rw [hz_norm_sq n]
          ring_nf
  have hrem_v_any : ∀ κ : ℝ, 0 < κ → ∀ᶠ n in atTop,
      |inner ℝ (err n) (v n)| ≤ κ / lam * ‖v n‖ ^ 2 := by
    intro κ hκ
    have hvsmall : ∀ᶠ n in atTop, ‖v n‖ ≤ κ * lam / Cerr :=
      hsmall_v (div_pos (mul_pos hκ hlam) hCerr_pos)
    filter_upwards [herr_bound_event, hvsmall] with n herr hvsmall
    have hCv : Cerr * ‖v n‖ ≤ κ * lam := by
      simpa [mul_comm] using (le_div_iff₀ hCerr_pos).mp hvsmall
    calc
      |inner ℝ (err n) (v n)| ≤ ‖err n‖ * ‖v n‖ := abs_real_inner_le_norm _ _
      _ ≤ (Cerr * ‖z n‖ ^ 2) * ‖v n‖ :=
          mul_le_mul_of_nonneg_right herr (norm_nonneg _)
      _ = (Cerr * ‖v n‖) * (lam⁻¹ ^ 2 * ‖v n‖ ^ 2) := by
          rw [hz_norm_sq n]
          ring
      _ ≤ (κ * lam) * (lam⁻¹ ^ 2 * ‖v n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hCv (by positivity)
      _ = κ / lam * ‖v n‖ ^ 2 := by
          field_simp [ne_of_gt hlam]
  have hMpos : 0 < M := hf_strongConv.1
  have hL_coercive' : ∀ d : H, m * ‖d‖ ^ 2 ≤ inner ℝ d (L d) := by
    intro d
    simpa [real_inner_comm] using hL_coercive d
  have hconv34 : ∀ n,
      inner ℝ (gradient f (x (n + 2))) (xInf - x (n + 2)) ≤
        f xInf - f (x (n + 2)) := by
    intro n
    have hsc := rem52_strong_convexity_value f M hf_strongConv xInf (x (n + 2))
    have hnonneg : 0 ≤ (M / 2) * ‖xInf - x (n + 2)‖ ^ 2 := by positivity
    linarith
  have hconvF : ∀ n,
      f (x (n + 2)) ≤ f (x (n + 1)) +
        inner ℝ (gradient f (x (n + 2))) (x (n + 2) - x (n + 1)) := by
    intro n
    have hsc := rem52_strong_convexity_value f M hf_strongConv (x (n + 1)) (x (n + 2))
    have hnormeq : ‖x (n + 1) - x (n + 2)‖ = ‖x (n + 2) - x (n + 1)‖ := by
      rw [← norm_neg]
      congr 1
      abel
    have hnonneg : 0 ≤ (M / 2) * ‖x (n + 1) - x (n + 2)‖ ^ 2 := by positivity
    rw [hnormeq] at hnonneg
    rw [show x (n + 1) - x (n + 2) = -(x (n + 2) - x (n + 1)) by abel,
      inner_neg_right, norm_neg] at hsc
    linarith
  have hF_lower_seq : ∀ n,
      rem52_seqF x lam f xInf n ≥
        (1 / (2 * lam ^ 2)) * ‖x (n + 1) - x n‖ ^ 2 +
          (M / 2) * ‖x (n + 1) - xInf‖ ^ 2 := by
    intro n
    have hsc := rem52_strong_convexity_value f M hf_strongConv (x (n + 1)) xInf
    dsimp [rem52_seqF]
    nlinarith
  let G : ℕ → ℝ := fun n => rem52_seqG x xInf lam L n
  let F : ℕ → ℝ := fun n => rem52_seqF x lam f xInf n
  let tau0 : ℝ := (Real.sqrt (‖L‖ ^ 2 + 4 * M) - ‖L‖) / 2
  have htau0_pos : 0 < tau0 := by
    simpa [tau0] using rem52_tau0_pos ‖L‖ M (norm_nonneg L) hMpos
  have hGF : (∀ n, F n ≥ tau0 * G n) ∧
      (∀ n, G n ≥ -(1 / m) * F n) := by
    simpa [G, F, tau0] using
      (rem52_G_F_comparison x xInf lam L f M m hm hMpos hlam
        (fun n {θ} hθ => (rem52_G_bounds x xInf lam L m hm hlam n hθ hL_coercive').1)
        (fun n {θ} hθ => (rem52_G_bounds x xInf lam L m hm hlam n hθ hL_coercive').2)
        hF_lower_seq)
  have hF_nonneg : ∀ n, 0 ≤ F n := by
    intro n
    have h := hF_lower_seq n
    have hw : 0 ≤ (1 / (2 * lam ^ 2)) * ‖x (n + 1) - x n‖ ^ 2 := by positivity
    have ha : 0 ≤ (M / 2) * ‖x (n + 1) - xInf‖ ^ 2 := by positivity
    dsimp [F]
    linarith
  have hGinc_raw := rem52_G_increment_F_bound x xInf f lam hlam L hL_symm
    m delta theta hm hdelta_pos z err (by intro n; rfl) hpair31
    (hrem_tail_any delta hdelta_pos) hconv34 hL_coercive'
  have hGinc : ∀ᶠ n in atTop,
      G (n + 1) - G n + lam * F (n + 1) ≤
        (1 + eta / 4) / lam * ‖rem52_seqV x n‖ ^ 2 +
          (1 / (2 * lam)) * ‖x (n + 1) - x n‖ ^ 2 := by
    have hsumdt : 1 + delta + theta = 1 + eta / 4 := by
      rw [← hdelta_theta]
      ring
    filter_upwards [hGinc_raw] with n hn
    simpa [G, F, hsumdt] using hn
  have hremF : ∀ᶠ n in atTop,
      |inner ℝ (err n) (x (n + 2) - xInf)| ≤
          (eta / 4) / lam ^ 2 * ‖rem52_seqV x n‖ ^ 2 ∧
        |inner ℝ (err n) (rem52_seqV x n)| ≤
          (eta / 4) / lam * ‖rem52_seqV x n‖ ^ 2 := by
    filter_upwards [hrem_tail_any (eta / 4) (by positivity),
      hrem_v_any (eta / 4) (by positivity)] with n htail hvel
    exact ⟨htail, hvel⟩
  have hFdec_raw := rem52_F_difference_bound x xInf f lam hlam m eta theta hm
    heta_pos heta_lt htheta_le L z err (by intro n; rfl) hpairF_event hremF hconvF
    hL_coercive'
  have hFdec : ∀ᶠ n in atTop,
      F (n + 1) - F n ≤ -((m - eta) / lam) * ‖rem52_seqV x n‖ ^ 2 := by
    simpa [F] using hFdec_raw
  have hHinputs := rem52_H_eventual_inputs x lam m eta hlam hm heta_pos heta_lt G F
    (Eventually.of_forall hF_nonneg) hGinc hFdec hGF.2
  rcases hHinputs with ⟨hHineq, hHnonneg, hFmono⟩
  have hG_upper : ∀ n, G n ≤ (1 / tau0) * F n := by
    intro n
    have h := hGF.1 n
    have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1 / tau0)
    have hleft : (1 / tau0) * (tau0 * G n) = G n := by
      field_simp [ne_of_gt htau0_pos]
    rwa [hleft] at hmul
  let H : ℕ → ℝ := rem52_seqH m eta G F
  have hHdecay := rem52_H_decay_geometric x m eta lam hm heta_pos heta_lt hlam
    tau0 htau0_pos G F H (Eventually.of_forall hF_nonneg) hFmono hGF.2 hG_upper
    hHineq hHnonneg (by intro n; rfl)
  let α : ℝ := (m - eta) / (3 / 2 + eta)
  let cdec : ℝ := (tau0 + α) / (tau0 + α + lam * tau0 * α)
  have hHdecay_c : ∃ (Kg : ℝ) (nH : ℕ), 0 < Kg ∧ 0 < cdec ∧ cdec < 1 ∧
      ∀ n ≥ nH, H n ≤ Kg * cdec ^ ((n : ℝ) / 2) := by
    simpa [H, tau0, α, cdec] using hHdecay
  rcases hHdecay_c with ⟨Kg, nH, hKg_pos, hc_pos, hc_lt_one, hHdecay_bound⟩
  have hF_lower_final : ∀ n,
      (1 / (2 * lam ^ 2)) * ‖x (n + 1) - x n‖ ^ 2 ≤ F n := by
    intro n
    have h := hF_lower_seq n
    have hnonneg : 0 ≤ (M / 2) * ‖x (n + 1) - xInf‖ ^ 2 := by positivity
    dsimp [F]
    linarith
  have hFprev : ∀ᶠ n in atTop, F n ≤ F (n - 1) := by
    rcases eventually_atTop.mp hFmono with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop (max (N + 1) 1)] with n hn
    have hNle : N + 1 ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have h := hN (n - 1) (by omega)
    simpa [Nat.sub_add_cancel hn1] using h
  have hH_lower : ∀ᶠ n in atTop, (1 / (2 * m)) * F n ≤ H n := by
    have hcoef_nonneg :
        0 ≤ (1 + eta) / (m - eta) + 1 / (2 * (m - eta)) - 1 / m - 1 / (2 * m) := by
      have hmp : 0 < m - eta := sub_pos.mpr heta_lt
      field_simp [ne_of_gt hm, ne_of_gt hmp]
      nlinarith [heta_pos, heta_lt]
    filter_upwards [hFprev] with n hprev
    have hGlo := hGF.2 n
    have hFnn := hF_nonneg n
    have hcoefF :
        0 ≤ ((1 + eta) / (m - eta) + 1 / (2 * (m - eta)) - 1 / m - 1 / (2 * m)) * F n :=
      mul_nonneg hcoef_nonneg hFnn
    have hB_nonneg : 0 ≤ 1 / (2 * (m - eta)) := by
      exact div_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (le_of_lt (sub_pos.mpr heta_lt)))
    have hBF : (1 / (2 * (m - eta))) * F n ≤
        (1 / (2 * (m - eta))) * F (n - 1) :=
      mul_le_mul_of_nonneg_left hprev hB_nonneg
    dsimp [H, rem52_seqH]
    nlinarith
  exact rem52_final_velocity_extraction x lam m hlam hm F H Kg
    cdec hKg_pos hc_pos hc_lt_one
    hF_lower_final hH_lower
    (by
      filter_upwards [eventually_atTop.mpr ⟨nH, hHdecay_bound⟩] with n hn
      simpa [H, cdec] using hn)

/-- Remark 5.1: Theorem 5.1 generalizes to operators `A` satisfying a quadratic
approximation condition with a symmetric coercive operator `L`, provided that
`A(0)` is a convex polyhedron. The conclusion is the same geometric decay of
the velocity as in Theorem 5.1.

The polyhedrality of `A(0)` is the standing hypothesis of Section 5 of the
paper ("Analysis of the Boundary Case (II): A(0) Convex Polyhedron"); Remark 5.1
inherits it through "the arguments of the proof are the same as previously",
i.e. through Proposition 5.1, which states it explicitly and then applies the
local normal-cone stability property (21) with `C := A(0)`. In Theorem 5.1 the
same hypothesis is discharged because there `A(0) = ∂σ_C(0) = C`. -/
theorem rem_5_1 (A : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ)
    (hAzero_int : (0 : H) ∈ interior (A (0 : H)))
    (h_poly : ConvexPolyhedron (A (0 : H)))
    (L : H →L[ℝ] H) (hL_symm : ∀ x y, inner ℝ (L x) y = inner ℝ x (L y))
    (m : ℝ) (hm : m > 0) (hL_coercive : ∀ x, inner ℝ (L x) x ≥ m * ‖x‖ ^ 2)
    (h_condition : (fun (x : H) =>
      setExcess (A x) (subderivative (supportFunction (A (0 : H))) x + ({L x} : Set H)))
      =O[𝓝 (0 : H)] (fun (x : H) => ‖x‖ ^ 2))
    (f : H → ℝ) (hf_conv : ConvexOn ℝ Set.univ f) (hf_C1 : ContDiff ℝ 1 f)
    (hinf : ∃ m, ∀ x, f x ≥ m)
    (M : ℝ) (hf_strongConv : IsStronglyConvex f M)
    (B : SetValuedOperator H H)
    (hB_eq_grad : B = SetValuedOperator.ofFunction Set.univ
      (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam : ℝ) (hlam : lam > 0) (lam_seq : ℕ → ℝ) (hlam_seq : ∀ n, lam_seq n = lam)
    (x : ℕ → H) (halg : AlgorithmA A B x lam_seq) (xInf : H) (hxInf : Tendsto x atTop (𝓝 xInf)) :
    ∃ (n0 : ℕ) (K : ℝ) (q : ℝ), K > 0 ∧ q > 0 ∧ q < 1 ∧
      ∀ n ≥ n0, ‖x (n+1) - x n‖ ≤ K * q ^ n := by
  have htail_pairing : ∀ η > 0, ∀ᶠ n in atTop,
      inner ℝ (rem52_pairingU x xInf L f lam (rem52_seqZ x lam) n)
        (x (n + 2) - xInf) ≤ η * ‖rem52_seqV x n‖ ^ 2 := by
    exact rem52_tail_pairing_from_polyhedron A hA hdomA hAzero_int h_poly L hL_symm
      m hm hL_coercive h_condition f hf_conv hf_C1 hinf M hf_strongConv B hB_eq_grad
      lam hlam lam_seq hlam_seq x halg xInf hxInf
  exact rem52_assembly_from_tail_pairing A hA hdomA hAzero_int L hL_symm m hm
    hL_coercive h_condition f hf_conv hf_C1 hinf M hf_strongConv B hB_eq_grad
    lam hlam lam_seq hlam_seq x halg xInf hxInf htail_pairing
