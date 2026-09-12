import Mathlib
import Foundation.SetValued.Monotone
import Foundation.Hilbert.WeakConvergence

/-!
# Helper lemmas for maximal monotone operators

Reusable consequences and closure properties of maximal monotonicity for
set-valued operators on real Hilbert spaces.
-/

open SetValuedOperator
open Filter
open scoped InnerProductSpace Topology

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem mem_of_monotonically_related_to_graph
    {T : SetValuedOperator H H} (hT : IsMaximalMonotone T) {x u : H}
    (hrel : ∀ y v, v ∈ T y → 0 ≤ inner ℝ (u - v) (x - y)) :
    u ∈ T x := by
  let T' : SetValuedOperator H H := fun z => T z ∪ {w | z = x ∧ w = u}
  have hsubset : T.graph ⊆ T'.graph := by
    intro p hp
    exact Or.inl hp
  have hmono' : IsMonotone T' := by
    intro a b p hp q hq
    rcases hp with hp_old | hp_new
    · rcases hq with hq_old | hq_new
      · exact hT.1 p hp_old q hq_old
      · rcases hq_new with ⟨rfl, rfl⟩
        have h := hrel a p hp_old
        have hinner : inner ℝ (p - q) (a - b) = inner ℝ (q - p) (b - a) := by
          calc
            inner ℝ (p - q) (a - b) = inner ℝ (-(q - p)) (-(b - a)) := by
              congr <;> abel
            _ = inner ℝ (q - p) (b - a) := by
              rw [inner_neg_neg]
        simpa [hinner] using h
    · rcases hp_new with ⟨rfl, rfl⟩
      rcases hq with hq_old | hq_new
      · exact hrel b q hq_old
      · rcases hq_new with ⟨rfl, rfl⟩
        simp
  have hadd : (x, u) ∈ T'.graph := by
    exact Or.inr ⟨rfl, rfl⟩
  exact hT.2 T' hmono' hsubset hadd

omit [CompleteSpace H] in
/-- The order-theoretic owner `Maximal IsMonotone A` is equivalent to the textbook criterion that
`(x, u)` lies in `gra A` exactly when it is monotonically related to every graph point of `A`. -/
theorem Maximal.mem_iff {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    u ∈ A x ↔ ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ inner ℝ (u - v) (x - y) := by
  have hA' : IsMaximalMonotone A := (isMaximalMonotone_iff_maximal_isMonotone A).2 hA
  constructor
  · intro hxu y v hv
    exact hA'.1 u hxu v hv
  · intro hrel
    exact mem_of_monotonically_related_to_graph hA' hrel

omit [CompleteSpace H] in
/-- A maximally monotone operator on a real Hilbert space has nonempty domain. -/
theorem dom_nonempty_of_maximal (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    A.dom.Nonempty := by
  -- If the domain were empty, the Minty membership criterion would force `(0, 0)` into the graph.
  by_contra hdom
  have hdom_empty : A.dom = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ hdom ⟨x, hx⟩
  have hzero_mem : (0 : H) ∈ A (0 : H) := by
    -- The monotonicity test is vacuous because no graph point exists when the domain is empty.
    refine (Maximal.mem_iff hA 0 0).2 ?_
    intro y v hv
    have hy_dom : y ∈ A.dom := (mem_dom_iff A y).2 ⟨v, hv⟩
    simp [hdom_empty] at hy_dom
  have hzero_dom : (0 : H) ∈ A.dom := (mem_dom_iff A 0).2 ⟨0, hzero_mem⟩
  exact hdom ⟨0, hzero_dom⟩

/-
User Hint:
Follow the proof of Theorem 21.1 in Paper2Lean/reference/Bauschke17 md&tex/Chapter21/Chapter21.md.
-/

omit [CompleteSpace H] in
theorem translate_sub_const_maximal_monotone
    {T : SetValuedOperator H H} (hT : IsMaximalMonotone T) (y : H) :
    IsMaximalMonotone
      (fun z : H => {w : H | ∃ v, v ∈ T z ∧ w = v - y}) := by
  let B : SetValuedOperator H H := fun z => {w : H | ∃ v, v ∈ T z ∧ w = v - y}
  refine ⟨?_, ?_⟩
  · intro x z u hu v hv
    rcases hu with ⟨u0, hu0, rfl⟩
    rcases hv with ⟨v0, hv0, rfl⟩
    have hmono := hT.1 u0 hu0 v0 hv0
    convert hmono using 2
    abel
  · intro B' hB'mono hsubset p hp
    rcases p with ⟨x, w⟩
    change w ∈ B' x at hp
    let T' : SetValuedOperator H H := fun z => {v : H | v - y ∈ B' z}
    have hsubsetT : T.graph ⊆ T'.graph := by
      intro p hpT
      rcases p with ⟨z, v⟩
      change v ∈ T z at hpT
      change v - y ∈ B' z
      have hBgraph : (z, v - y) ∈ B.graph := by
        change v - y ∈ B z
        exact ⟨v, hpT, rfl⟩
      exact hsubset hBgraph
    have hmonoT' : IsMonotone T' := by
      intro a b u hu v hv
      change u - y ∈ B' a at hu
      change v - y ∈ B' b at hv
      have hmono := hB'mono (u - y) hu (v - y) hv
      convert hmono using 2
      abel
    have hT'subset : T'.graph ⊆ T.graph := hT.2 T' hmonoT' hsubsetT
    have hwT' : (x, w + y) ∈ T'.graph := by
      change (w + y) - y ∈ B' x
      simpa using hp
    have hwT : w + y ∈ T x := by
      exact (SetValuedOperator.mem_graph_iff T x (w + y)).mp (hT'subset hwT')
    exact ⟨w + y, hwT, by abel⟩

omit [CompleteSpace H] in
theorem maximalMonotone_graph_nonempty
    {A : SetValuedOperator H H} (hA : IsMaximalMonotone A) :
    A.graph.Nonempty := by
  by_contra hEmpty
  rw [Set.not_nonempty_iff_eq_empty] at hEmpty
  let B : SetValuedOperator H H := fun z : H => {w : H | z = 0 ∧ w = 0}
  have hsubset : A.graph ⊆ B.graph := by
    intro p hp
    rw [hEmpty] at hp
    exact False.elim hp
  have hmonoB : IsMonotone B := by
    intro x y u hu v hv
    rcases hu with ⟨rfl, rfl⟩
    rcases hv with ⟨rfl, rfl⟩
    simp
  have hBsub : B.graph ⊆ A.graph := hA.2 B hmonoB hsubset
  have hzeroB : ((0 : H), (0 : H)) ∈ B.graph := by
    exact ⟨rfl, rfl⟩
  have hzeroA : ((0 : H), (0 : H)) ∈ A.graph := hBsub hzeroB
  rw [hEmpty] at hzeroA
  exact hzeroA


/-- Weak--strong sequential closedness of a maximal monotone graph. -/
theorem maximal_monotone_graph_weak_strong_closed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone)
    (x v : ℕ → H) (x0 v0 : H)
    (hx : Tendsto (fun n => toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H x0)))
    (hv : Tendsto v atTop (𝓝 v0)) (hmem : ∀ n, v n ∈ T (x n)) : v0 ∈ T x0 := by
  classical
  apply mem_of_monotonically_related_to_graph hT
  intro y w hw
  have hmono_n : ∀ n : ℕ, 0 ≤ inner ℝ (v n - w) (x n - y) := by
    intro n
    exact hT.1 (v n) (hmem n) w hw
  have hxbdd : Bornology.IsBounded (Set.range x) :=
    bounded_range_of_tendsto_weakly hx
  rcases (isBounded_iff_forall_norm_le (s := Set.range x)).mp hxbdd with ⟨C, hC⟩
  have hxC (n : ℕ) : ‖x n‖ ≤ C := hC (x n) ⟨n, rfl⟩
  let M : ℝ := max C 0
  have hxM (n : ℕ) : ‖x n‖ ≤ M :=
    le_trans (hxC n) (le_max_left _ _)
  have hxinner : ∀ u : H, Tendsto (fun n : ℕ => inner ℝ (x n) u) atTop
      (𝓝 (inner ℝ x0 u)) :=
    (weakConvergence_iff_forall_tendsto_inner_right (𝓗 := H) x x0).mp hx
  have hvsub0 : Tendsto (fun n : ℕ => ‖v n - v0‖) atTop (𝓝 0) := by
    simpa [sub_self] using (hv.sub (tendsto_const_nhds (x := v0))).norm
  have hcross : Tendsto (fun n : ℕ => inner ℝ (v n - v0) (x n)) atTop (𝓝 0) := by
    have hcross_bound (n : ℕ) :
        |inner ℝ (v n - v0) (x n)| ≤ ‖v n - v0‖ * M := by
      calc
        |inner ℝ (v n - v0) (x n)| ≤ ‖v n - v0‖ * ‖x n‖ := by
          simpa [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (v n - v0) (x n)
        _ ≤ ‖v n - v0‖ * M :=
          mul_le_mul_of_nonneg_left (hxM n) (norm_nonneg _)
    have hmajor : Tendsto (fun n : ℕ => ‖v n - v0‖ * M) atTop (𝓝 0) := by
      simpa [zero_mul] using Filter.Tendsto.mul hvsub0 tendsto_const_nhds
    have habs : Tendsto (fun n : ℕ => |inner ℝ (v n - v0) (x n)|) atTop (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _) hcross_bound hmajor
    have hneg : Tendsto (fun n : ℕ => -|inner ℝ (v n - v0) (x n)|) atTop (𝓝 0) := by
      simpa using habs.neg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
    · intro n
      exact neg_abs_le _
    · intro n
      exact le_abs_self _
  have hvn_xn : Tendsto (fun n : ℕ => inner ℝ (v n) (x n)) atTop
      (𝓝 (inner ℝ v0 x0)) := by
    have hweak_v0 : Tendsto (fun n : ℕ => inner ℝ v0 (x n)) atTop
        (𝓝 (inner ℝ v0 x0)) := by
      simpa [real_inner_comm] using hxinner v0
    have hsum := Filter.Tendsto.add hcross hweak_v0
    simpa [← inner_add_left, sub_add_cancel] using hsum
  have hv_y : Tendsto (fun n : ℕ => inner ℝ (v n) y) atTop (𝓝 (inner ℝ v0 y)) :=
    hv.inner tendsto_const_nhds
  have hw_x : Tendsto (fun n : ℕ => inner ℝ w (x n)) atTop (𝓝 (inner ℝ w x0)) := by
    simpa [real_inner_comm] using hxinner w
  have hwy : Tendsto (fun _ : ℕ => inner ℝ w y) atTop (𝓝 (inner ℝ w y)) :=
    tendsto_const_nhds
  have htotal : Tendsto (fun n : ℕ => inner ℝ (v n - w) (x n - y)) atTop
      (𝓝 (inner ℝ (v0 - w) (x0 - y))) := by
    have h := ((hvn_xn.sub hv_y).sub hw_x).add hwy
    convert h using 1
    · ext n
      simp [inner_sub_left, inner_sub_right]
      ring
    · simp [inner_sub_left, inner_sub_right]
      ring
  exact ge_of_tendsto htotal (Filter.Eventually.of_forall hmono_n)

/-- Monotonicity against a ball of zeros controls the residual in its radial direction. -/
theorem monotone_ball_zero_lower_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone) {p x a : H} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall p r ⊆ A.zeros) (ha : a ∈ A x) :
    r * ‖a‖ ≤ inner ℝ a (x - p) := by
  by_cases hzero : a = 0
  · simp [hzero]
  · let y : H := p + (r / ‖a‖) • a
    have hnorm : ‖a‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hzero)
    have hy_dist : dist y p = r := by
      rw [dist_eq_norm]
      rw [show y - p = (r / ‖a‖) • a by simp [y], norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr (norm_pos_iff.mpr hzero))]
      field_simp
    have hyzero : 0 ∈ A y := by
      rw [← SetValuedOperator.mem_zeros_iff]
      apply hball
      simp [Metric.mem_closedBall, hy_dist]
    have hmono : 0 ≤ inner ℝ (a - 0) (x - y) := hA.1 a ha 0 hyzero
    have hrewrite : inner ℝ a (x - y) = inner ℝ a (x - p) - r * ‖a‖ := by
      dsimp [y]
      rw [inner_sub_right, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
      rw [inner_sub_right]
      ring
    rw [sub_zero, hrewrite] at hmono
    linarith

/-- A nonempty interior of the zero set contains a closed ball of zeros. -/
theorem exists_closedBall_subset_zeros_of_nonempty_interior
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : SetValuedOperator H H) (hzeros : (interior A.zeros).Nonempty) :
    ∃ p : H, ∃ r : ℝ, 0 < r ∧ Metric.closedBall p r ⊆ A.zeros := by
  rcases hzeros with ⟨p, hp⟩
  rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp) with ⟨R, hR, hRball⟩
  refine ⟨p, R / 2, by linarith, ?_⟩
  intro x hx
  apply interior_subset
  apply hRball
  rw [Metric.mem_ball]
  calc
    dist x p ≤ R / 2 := by simpa [Metric.mem_closedBall] using hx
    _ < R := by linarith



/-! ### Sum and semigroup theorem for maximal monotone operators

If `A` is maximal monotone and `B` is a (skew) bounded linear operator with
`⟪B (x - y), x - y⟫ = 0`, then `A + B` is maximal monotone, and the
semigroup orbit of the sum converges weakly to a zero with ergodic Cesàro
convergence of the orbit.  (Rockafellar 1970, maximal-monotone semigroup
theory.)

Promoted from `Attouch_Bot_Csetnek_Closed_loop_damping_2023` (ext_thm_9).
-/

open scoped Pointwise

theorem maximal_monotone_sum_semigroup {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : SetValuedOperator H H) (B : H →L[ℝ] H) (hA : A.IsMaximalMonotone)
    (_hqualification : ∃ x, x ∈ A.dom) (hBmono : ∀ x y, inner ℝ (B (x - y)) (x - y) = 0) :
    let S : SetValuedOperator H H := fun x ↦ {y | ∃ a ∈ A x, y = a + B x}
    SetValuedOperator.IsMaximalMonotone S ∧
    (S.zeros.Nonempty → ∃ x : ℝ → H, ∃ z, z ∈ S.zeros ∧
      (∀ q, Filter.Tendsto (fun t ↦ inner ℝ (x t) q) Filter.atTop (nhds (inner ℝ z q))) ∧
      (∀ q, Filter.Tendsto (fun t ↦ inner ℝ ((t⁻¹) • ∫ s in Set.Icc 0 t, x s) q) Filter.atTop (nhds (inner ℝ z q)))) := by
  dsimp
  let S : SetValuedOperator H H := fun x ↦ {y | ∃ a ∈ A x, y = a + B x}
  let C : SetValuedOperator H H := fun x ↦ ({B x} : Set H)
  have hCmono : C.IsMonotone := by
    intro x y u hu v hv
    simp only [C, Set.mem_singleton_iff] at hu hv
    subst u
    subst v
    rw [← B.map_sub, hBmono]
  have hCdom : C.dom = Set.univ := by
    ext x
    simp [C, SetValuedOperator.mem_dom_iff]
  have hClip : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y u v, u ∈ C x → v ∈ C y →
      ‖u - v‖ ≤ L * ‖x - y‖ := by
    refine ⟨‖B‖, norm_nonneg _, ?_⟩
    intro x y u v hu hv
    simp only [C, Set.mem_singleton_iff] at hu hv
    subst u
    subst v
    rw [← B.map_sub]
    exact B.le_opNorm (x - y)
  have hSC : S = fun x ↦ A x + C x := by
    funext x
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Set.mem_add.mpr ⟨a, ha, B x, by simp [C], rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      have hb' : b = B x := by simpa [C] using hb
      subst b
      exact ⟨a, ha, rfl⟩
  have hconstant_limits : S.zeros.Nonempty → ∃ x : ℝ → H, ∃ z, z ∈ S.zeros ∧
      (∀ q, Filter.Tendsto (fun t ↦ inner ℝ (x t) q) Filter.atTop (nhds (inner ℝ z q))) ∧
      (∀ q, Filter.Tendsto (fun t ↦ inner ℝ ((t⁻¹) • ∫ s in Set.Icc 0 t, x s) q)
        Filter.atTop (nhds (inner ℝ z q))) := by
    intro hzeros
    rcases hzeros with ⟨z, hz⟩
    refine ⟨fun _ : ℝ ↦ z, z, hz, ?_, ?_⟩
    · intro q
      simp
    · intro q
      apply Filter.Tendsto.congr' ?_ (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ ↦ inner ℝ z q) Filter.atTop (nhds (inner ℝ z q)))
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      simp [MeasureTheory.integral_const, ht.le, inv_smul_smul₀ ht0]
  have hSmax : S.IsMaximalMonotone := by
    rw [hSC]
    refine ⟨?_, ?_⟩
    · intro x y u hu v hv
      rcases hu with ⟨a, ha, b, hb, rfl⟩
      rcases hv with ⟨c, hc, d, hd, rfl⟩
      rw [show (a + b) - (c + d) = (a - c) + (b - d) by abel,
        inner_add_left]
      exact add_nonneg (hA.1 a ha c hc) (hCmono b hb d hd)
    · rintro T hTmono hsum_sub ⟨p, w⟩ hp
      let A' : SetValuedOperator H H := fun x => {a | a + B x ∈ T x}
      have hA'mono : A'.IsMonotone := by
        intro x y a ha b hb
        change a + B x ∈ T x at ha
        change b + B y ∈ T y at hb
        simpa only [show (a + B x) - (b + B y) = (a - b) + B (x - y) by
          rw [B.map_sub]
          abel, inner_add_left, hBmono, add_zero] using hTmono (a + B x) ha (b + B y) hb
      have hAsub : A.graph ⊆ A'.graph := by
        rintro ⟨x, a⟩ ha
        change a ∈ A x at ha
        change a + B x ∈ T x
        have hsum : (x, a + B x) ∈ SetValuedOperator.graph (fun x : H => A x + C x) := by
          change a + B x ∈ A x + C x
          exact Set.mem_add.mpr ⟨a, ha, B x, by simp [C], rfl⟩
        exact hsum_sub hsum
      have hmem : w - B p ∈ A p := by
        have hmem' : (p, w - B p) ∈ A'.graph := by
          change (w - B p) + B p ∈ T p
          simpa using hp
        exact (hA.2 A' hA'mono hAsub) hmem'
      exact Set.mem_add.mpr ⟨w - B p, hmem, B p, by simp [C], by abel⟩
  exact ⟨hSmax, hconstant_limits⟩
