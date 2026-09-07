import Mathlib
namespace Alvarez2002
open Filter
/-- A classical solution on a time set. -/
def IsClassicalSolutionOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → X) (Y₀ : X) (I : Set ℝ) (Y : ℝ → X) : Prop :=
  0 ∈ I ∧ Y 0 = Y₀ ∧ ∀ t ∈ I, HasDerivAt Y (F (Y t)) t

/-- Maximality is with respect to extension of the time interval. -/
def IsMaximalClassicalSolution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → X) (Y₀ : X) (Tmax : WithTop ℝ) (Y : ℝ → X) : Prop :=
  0 < Tmax ∧
    IsClassicalSolutionOn F Y₀ {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax} Y ∧
    ∀ (I : Set ℝ) (Z : ℝ → X), Set.OrdConnected I → 0 ∈ I →
      IsClassicalSolutionOn F Y₀ I Z →
      {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax} ⊆ I →
      (∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax → Y t = Z t) →
      I ∩ Set.Ici 0 ⊆ {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax}

/-- Local Picard--Lindelöf existence from the neighbourhood formulation of
local Lipschitz continuity. -/
private theorem local_classical_solution_of_locally_lipschitz
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    (t0 : ℝ) (x : X) : ∃ ε : ℝ, 0 < ε ∧ ∃ α : ℝ → X, α t0 = x ∧
      ∀ t ∈ Set.Ioo (t0 - ε) (t0 + ε), HasDerivAt α (F (α t)) t := by
  rcases hF x with ⟨U, hxU, L, hL0, hLip⟩
  rcases Metric.mem_nhds_iff.mp hxU with ⟨r, hr, hrU⟩
  let a : ℝ := r / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hballU (u : X) (hu : u ∈ Metric.closedBall x a) : u ∈ U := by
    apply hrU
    rw [Metric.mem_ball]
    have hdist : dist u x ≤ a := by
      simpa [dist_comm] using (Metric.mem_closedBall.mp hu)
    dsimp [a] at hdist ⊢
    linarith
  let M : ℝ := L * a + ‖F x‖ + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hbound (u : X) (hu : u ∈ Metric.closedBall x a) : ‖F u‖ ≤ M := by
    calc
      ‖F u‖ ≤ ‖F u - F x‖ + ‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ L * ‖u - x‖ + ‖F x‖ := by
        gcongr
        exact hLip u (hballU u hu) x (mem_of_mem_nhds hxU)
      _ ≤ L * a + ‖F x‖ := by
        gcongr
        simpa [dist_eq_norm_sub] using (Metric.mem_closedBall.mp hu)
      _ ≤ M := by dsimp [M]; linarith
  let K : NNReal := ⟨L, hL0⟩
  let Mnn : NNReal := ⟨M, hM.le⟩
  have hLipBall : LipschitzOnWith K F (Metric.closedBall x a) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    simpa only [dist_eq_norm] using hLip u (hballU u hu) v (hballU v hv)
  let ann : NNReal := ⟨a, ha.le⟩
  let ε : ℝ := a / (2 * M)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have htime : Mnn * max ((t0 + ε) - t0) (t0 - (t0 - ε)) ≤ ann - 0 := by
    have htime' : M * max ((t0 + ε) - t0) (t0 - (t0 - ε)) ≤ a := by
      rw [show (t0 + ε) - t0 = ε by ring,
        show t0 - (t0 - ε) = ε by ring, max_self]
      dsimp [ε]
      field_simp
      ring_nf
      linarith
    simpa [Mnn, ann] using htime'
  let pl := IsPicardLindelof.of_time_independent (tmin := t0 - ε) (tmax := t0 + ε)
    (t₀ := ⟨t0, by constructor <;> linarith⟩)
    (a := ann) (r := 0) (L := Mnn) (K := K) hbound hLipBall htime
  obtain ⟨α, hα0, hα⟩ := pl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨ε, hε, α, hα0, fun t ht ↦ ?_⟩
  apply (hα t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
  exact Icc_mem_nhds ht.1 ht.2

/-- Two classical germs through the same point agree near that point.  This is
the local uniqueness ingredient needed when the vector field is only locally
Lipschitz. -/
private theorem ode_eq_eventually_of_locally_lipschitz
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    {t0 : ℝ} (u v : ℝ → X)
    (hu : ∀ᶠ t in nhds t0, HasDerivAt u (F (u t)) t)
    (hv : ∀ᶠ t in nhds t0, HasDerivAt v (F (v t)) t)
    (huv : u t0 = v t0) : u =ᶠ[nhds t0] v := by
  rcases hF (u t0) with ⟨U, hU, L, hL0, hLip⟩
  have hu0 : HasDerivAt u (F (u t0)) t0 := hu.self_of_nhds
  have hv0 : HasDerivAt v (F (v t0)) t0 := hv.self_of_nhds
  have huU : ∀ᶠ t in nhds t0, u t ∈ U := hu0.continuousAt hU
  have hvU : ∀ᶠ t in nhds t0, v t ∈ U := by
    have hUv : U ∈ nhds (v t0) := by simpa [huv] using hU
    exact hv0.continuousAt hUv
  let K : NNReal := ⟨L, hL0⟩
  have hLipU : LipschitzOnWith K F U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    simpa only [dist_eq_norm] using hLip y hy z hz
  have hLipEv : ∀ᶠ _ : ℝ in nhds t0, LipschitzOnWith K F U :=
    Filter.Eventually.of_forall fun _ => hLipU
  apply ODE_solution_unique_of_eventually hLipEv
  · filter_upwards [hu, huU] with t ht hUt
    exact ⟨ht, hUt⟩
  · filter_upwards [hv, hvU] with t ht hUt
    exact ⟨ht, hUt⟩
  · exact huv

/-- Local uniqueness propagates along an interval on which both curves solve
the autonomous equation.  We use the equality locus in a compact subinterval:
it is closed by continuity and open by germ uniqueness. -/
private theorem ode_eqOn_Ioo_of_locally_lipschitz
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    {a b t0 : ℝ} (ht0 : t0 ∈ Set.Ioo a b) (u v : ℝ → X)
    (hu : ∀ t ∈ Set.Ioo a b, HasDerivAt u (F (u t)) t)
    (hv : ∀ t ∈ Set.Ioo a b, HasDerivAt v (F (v t)) t)
    (huv : u t0 = v t0) : Set.EqOn u v (Set.Ioo a b) := by
  intro t ht
  let A : ℝ := (a + min t t0) / 2
  let B : ℝ := (max t t0 + b) / 2
  have hmin : a < min t t0 := lt_min ht.1 ht0.1
  have hmax : max t t0 < b := max_lt ht.2 ht0.2
  have hA : a < A := by dsimp [A]; linarith
  have hB : B < b := by dsimp [B]; linarith
  have htI : t ∈ Set.Ioo A B := by
    constructor <;> dsimp [A, B]
    · have h : A < min t t0 := by dsimp [A]; linarith
      exact lt_of_lt_of_le h (min_le_left _ _)
    · have h : max t t0 < B := by dsimp [B]; linarith
      exact lt_of_le_of_lt (le_max_left _ _) h
  have ht0I : t0 ∈ Set.Ioo A B := by
    constructor <;> dsimp [A, B]
    · have h : A < min t t0 := by dsimp [A]; linarith
      exact lt_of_lt_of_le h (min_le_right _ _)
    · have h : max t t0 < B := by dsimp [B]; linarith
      exact lt_of_le_of_lt (le_max_right _ _) h
  have hIcc : Set.Icc A B ⊆ Set.Ioo a b := by
    intro s hs
    exact ⟨lt_of_lt_of_le hA hs.1, lt_of_le_of_lt hs.2 hB⟩
  have huc : ContinuousOn u (Set.Icc A B) :=
    HasDerivAt.continuousOn fun s hs => hu s (hIcc hs)
  have hvc : ContinuousOn v (Set.Icc A B) :=
    HasDerivAt.continuousOn fun s hs => hv s (hIcc hs)
  let fu : Set.Icc A B → X := fun s => u s
  let fv : Set.Icc A B → X := fun s => v s
  have hfu : Continuous fu := huc.restrict
  have hfv : Continuous fv := hvc.restrict
  let E : Set (Set.Icc A B) := {s | fu s = fv s}
  have hEclosed : IsClosed E := by
    simpa [E] using isClosed_eq hfu hfv
  have hEopen : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hu' : ∀ᶠ r in nhds (s : ℝ), HasDerivAt u (F (u r)) r :=
      by
        filter_upwards [Ioo_mem_nhds (hIcc s.2).1 (hIcc s.2).2] with r hr
        exact hu r hr
    have hv' : ∀ᶠ r in nhds (s : ℝ), HasDerivAt v (F (v r)) r :=
      by
        filter_upwards [Ioo_mem_nhds (hIcc s.2).1 (hIcc s.2).2] with r hr
        exact hv r hr
    have heq : u =ᶠ[nhds (s : ℝ)] v :=
      ode_eq_eventually_of_locally_lipschitz F hF u v hu' hv' hs
    have heq' : {r : Set.Icc A B | u r = v r} ∈ nhds s :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds heq
    simpa [E, fu, fv] using heq'
  have hE : IsClopen E := ⟨hEclosed, hEopen⟩
  have ht0E : (⟨t0, Set.Ioo_subset_Icc_self ht0I⟩ : Set.Icc A B) ∈ E := by
    simpa [E, fu, fv] using huv
  have hpre : IsPreconnected (Set.univ : Set (Set.Icc A B)) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    simpa using (isPreconnected_Icc : IsPreconnected (Set.Icc A B))
  have hall : Set.univ ⊆ E :=
    hpre.subset_isClopen hE
      ⟨_, Set.mem_univ _, ht0E⟩
  have htE : (⟨t, Set.Ioo_subset_Icc_self htI⟩ : Set.Icc A B) ∈ E := hall (Set.mem_univ _)
  simpa [E, fu, fv] using htE

/-- A local solution together with its open connected time domain.  This is
the object ordered in the Zorn construction of a maximal solution. -/
private structure PointedSolution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → X) (Y₀ : X) where
  dom : Set ℝ
  curve : ℝ → X
  open_dom : IsOpen dom
  preconnected_dom : IsPreconnected dom
  zero_mem : 0 ∈ dom
  initial : curve 0 = Y₀
  ode : ∀ t ∈ dom, HasDerivAt curve (F (curve t)) t

private instance pointedSolutionPreorder
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → X) (Y₀ : X) : Preorder (PointedSolution F Y₀) where
  le p q := p.dom ⊆ q.dom ∧ Set.EqOn p.curve q.curve p.dom
  le_refl p := ⟨fun _ h => h, fun _ _ => rfl⟩
  le_trans p q r hpq hqr :=
    ⟨hpq.1.trans hqr.1, fun t ht => (hpq.2 ht).trans (hqr.2 (hpq.1 ht))⟩

/-- An open connected real domain contains an open interval around any two of
its points. -/
private theorem open_preconnected_segment_thickening {I : Set ℝ}
    (hopen : IsOpen I) (hconn : IsPreconnected I) {u v : ℝ}
    (hu : u ∈ I) (hv : v ∈ I) :
    ∃ A B : ℝ, u ∈ Set.Ioo A B ∧ v ∈ Set.Ioo A B ∧ Set.Ioo A B ⊆ I := by
  let lo := min u v
  let hi := max u v
  have hlo : lo ∈ I := by
    rcases le_total u v with huv | hvu
    · simpa [lo, min_eq_left huv] using hu
    · simpa [lo, min_eq_right hvu] using hv
  have hhi : hi ∈ I := by
    rcases le_total u v with huv | hvu
    · simpa [hi, max_eq_right huv] using hv
    · simpa [hi, max_eq_left hvu] using hu
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds hlo)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds hhi)
  refine ⟨lo - δ / 2, hi + η / 2, ?_, ?_, ?_⟩
  · constructor <;> dsimp [lo, hi] <;> linarith [min_le_left u v, le_max_left u v]
  · constructor <;> dsimp [lo, hi] <;> linarith [min_le_right u v, le_max_right u v]
  · have hA : lo - δ / 2 ∈ I := hδsub (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [sub_sub_cancel_left, abs_of_nonpos (by linarith)]
      linarith)
    have hB : hi + η / 2 ∈ I := hηsub (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [add_sub_cancel_left, abs_of_pos (by linarith)]
      linarith)
    intro t ht
    exact hconn.ordConnected.out hA hB ⟨ht.1.le, ht.2.le⟩

/-- Pointed solutions for a locally Lipschitz field agree on their overlap. -/
private theorem pointedSolution_eqOn_inter
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    (Y₀ : X) (p q : PointedSolution F Y₀) :
    Set.EqOn p.curve q.curve (p.dom ∩ q.dom) := by
  intro t ht
  obtain ⟨A, B, h0, htI, hsub⟩ := open_preconnected_segment_thickening
    (p.open_dom.inter q.open_dom)
    (Set.OrdConnected.isPreconnected
      (p.preconnected_dom.ordConnected.inter q.preconnected_dom.ordConnected))
    ⟨p.zero_mem, q.zero_mem⟩ ht
  exact (ode_eqOn_Ioo_of_locally_lipschitz F hF h0 p.curve q.curve
    (fun s hs => p.ode s (hsub hs).1)
    (fun s hs => q.ode s (hsub hs).2)
    (p.initial.trans q.initial.symm)) htI

/-- Two compatible pointed germs have an open connected union.  The curve is
chosen from the left branch on the overlap; overlap uniqueness makes this
choice independent and transfers the derivative equation to the union. -/
private theorem pointedSolution_binary_upper_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    (Y₀ : X) (p q : PointedSolution F Y₀) :
    ∃ r : PointedSolution F Y₀, p ≤ r ∧ q ≤ r := by
  classical
  let D : Set ℝ := p.dom ∪ q.dom
  let curve : ℝ → X := fun t => if t ∈ p.dom then p.curve t else q.curve t
  have hcurvep : ∀ t ∈ p.dom, curve t = p.curve t := by
    intro t ht
    simp [curve, ht]
  have hcurveq : ∀ t ∈ q.dom, curve t = q.curve t := by
    intro t ht
    by_cases htp : t ∈ p.dom
    · rw [show curve t = p.curve t by simp [curve, htp]]
      exact pointedSolution_eqOn_inter F hF Y₀ p q ⟨htp, ht⟩
    · simp [curve, htp]
  refine ⟨{ dom := D
            curve := curve
            open_dom := p.open_dom.union q.open_dom
            preconnected_dom := IsPreconnected.union 0 p.zero_mem q.zero_mem
              p.preconnected_dom q.preconnected_dom
            zero_mem := Or.inl p.zero_mem
            initial := (hcurvep 0 p.zero_mem).trans p.initial
            ode := ?_ }, ?_, ?_⟩
  · intro t ht
    rcases ht with htp | htq
    · have heq : curve =ᶠ[nhds t] p.curve := by
        filter_upwards [p.open_dom.mem_nhds htp] with s hs
        exact hcurvep s hs
      have hval : curve t = p.curve t := hcurvep t htp
      simpa [hval] using (p.ode t htp).congr_of_eventuallyEq heq
    · have heq : curve =ᶠ[nhds t] q.curve := by
        filter_upwards [q.open_dom.mem_nhds htq] with s hs
        exact hcurveq s hs
      have hval : curve t = q.curve t := hcurveq t htq
      simpa [hval] using (q.ode t htq).congr_of_eventuallyEq heq
  · refine ⟨Set.subset_union_left, ?_⟩
    intro t ht
    exact (hcurvep t ht).symm
  · refine ⟨Set.subset_union_right, ?_⟩
    intro t ht
    exact (hcurveq t ht).symm

/-- Adjoin a local ODE germ to a pointed solution when the two curves agree on
their nonempty open overlap.  Keeping this construction separate is useful at
a finite endpoint: the local germ need not itself contain time zero. -/
private theorem pointedSolution_extend_of_eqOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → X) (Y₀ : X) (p : PointedSolution F Y₀)
    {a b : ℝ} (_hab : a < b) (α : ℝ → X)
    (hα : ∀ t ∈ Set.Ioo a b, HasDerivAt α (F (α t)) t)
    (hEq : Set.EqOn p.curve α (p.dom ∩ Set.Ioo a b))
    (hc : ∃ c, c ∈ p.dom ∧ c ∈ Set.Ioo a b) :
    ∃ q : PointedSolution F Y₀, p ≤ q ∧ Set.Ioo a b ⊆ q.dom ∧
      Set.EqOn q.curve α (Set.Ioo a b) := by
  classical
  let D : Set ℝ := p.dom ∪ Set.Ioo a b
  let curve : ℝ → X := fun t => if t ∈ p.dom then p.curve t else α t
  have hcurvep : ∀ t ∈ p.dom, curve t = p.curve t := by
    intro t ht
    simp [curve, ht]
  have hcurveα : ∀ t ∈ Set.Ioo a b, curve t = α t := by
    intro t ht
    by_cases htp : t ∈ p.dom
    · rw [show curve t = p.curve t by simp [curve, htp]]
      exact hEq ⟨htp, ht⟩
    · simp [curve, htp]
  rcases hc with ⟨c, hcdom, hcIoo⟩
  refine ⟨{ dom := D
            curve := curve
            open_dom := p.open_dom.union isOpen_Ioo
            preconnected_dom := IsPreconnected.union c hcdom hcIoo
              p.preconnected_dom isPreconnected_Ioo
            zero_mem := Or.inl p.zero_mem
            initial := (hcurvep 0 p.zero_mem).trans p.initial
            ode := ?_ }, ?_, Set.subset_union_right, hcurveα⟩
  · intro t ht
    rcases ht with htp | htα
    · have heq : curve =ᶠ[nhds t] p.curve := by
        filter_upwards [p.open_dom.mem_nhds htp] with s hs
        exact hcurvep s hs
      have hval : curve t = p.curve t := hcurvep t htp
      simpa [hval] using (p.ode t htp).congr_of_eventuallyEq heq
    · have heq : curve =ᶠ[nhds t] α := by
        filter_upwards [isOpen_Ioo.mem_nhds htα] with s hs
        exact hcurveα s hs
      have hval : curve t = α t := hcurveα t htα
      simpa [hval] using (hα t htα).congr_of_eventuallyEq heq
  · refine ⟨Set.subset_union_left, ?_⟩
    intro t ht
    exact (hcurvep t ht).symm

/-- The local Picard--Lindelöf theorem supplies the nonempty seed for Zorn. -/
private theorem pointedSolution_nonempty
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    (Y₀ : X) : Nonempty (PointedSolution F Y₀) := by
  obtain ⟨ε, hε, α, hα0, hα⟩ :=
    local_classical_solution_of_locally_lipschitz F hF 0 Y₀
  let p : PointedSolution F Y₀ :=
    { dom := Set.Ioo (-ε) ε
      curve := α
      open_dom := isOpen_Ioo
      preconnected_dom := isPreconnected_Ioo
      zero_mem := by constructor <;> linarith
      initial := hα0
      ode := by
        intro t ht
        simpa using hα t (by simpa using ht) }
  exact ⟨p⟩

/-- The union of a chain of pointed solutions is again a pointed solution. -/
private theorem pointedSolution_chain_upper_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    (Y₀ : X) : ∀ C : Set (PointedSolution F Y₀),
      IsChain (· ≤ ·) C → BddAbove C := by
  classical
  intro C hC
  by_cases hCempty : C.Nonempty
  · let D : Set ℝ := ⋃₀ (PointedSolution.dom '' C)
    have howner : ∀ t, t ∈ D → ∃ p : PointedSolution F Y₀, p ∈ C ∧ t ∈ p.dom := by
      intro t ht
      rcases Set.mem_sUnion.mp ht with ⟨d, hd, htd⟩
      rcases hd with ⟨p, hp, rfl⟩
      exact ⟨p, hp, htd⟩
    let owner : ∀ t, t ∈ D → PointedSolution F Y₀ :=
      fun t ht => Classical.choose (howner t ht)
    have owner_mem (t : ℝ) (ht : t ∈ D) : owner t ht ∈ C :=
      (Classical.choose_spec (howner t ht)).1
    have owner_dom (t : ℝ) (ht : t ∈ D) : t ∈ (owner t ht).dom :=
      (Classical.choose_spec (howner t ht)).2
    let curve : ℝ → X := fun t => if ht : t ∈ D then (owner t ht).curve t else Y₀
    have hopen : IsOpen D := by
      dsimp [D]
      apply isOpen_sUnion
      intro d hd
      rcases hd with ⟨p, hp, rfl⟩
      exact p.open_dom
    have hconn : IsPreconnected D := by
      apply isPreconnected_sUnion 0 (PointedSolution.dom '' C)
      · intro d hd
        rcases hd with ⟨p, hp, rfl⟩
        exact p.zero_mem
      · intro d hd
        rcases hd with ⟨p, hp, rfl⟩
        exact p.preconnected_dom
    have hzero : 0 ∈ D := by
      rcases hCempty with ⟨p, hp⟩
      exact Set.mem_sUnion.mpr ⟨p.dom, ⟨p, hp, rfl⟩, p.zero_mem⟩
    let upper : PointedSolution F Y₀ :=
      { dom := D
        curve := curve
        open_dom := hopen
        preconnected_dom := hconn
        zero_mem := hzero
        initial := by
          rw [show curve 0 = (owner 0 hzero).curve 0 by simp [curve, hzero]]
          exact (owner 0 hzero).initial
        ode := by
          intro t ht
          have hcurve : curve t = (owner t ht).curve t := by simp [curve, ht]
          rw [hcurve]
          have hder := (owner t ht).ode t (owner_dom t ht)
          apply hder.congr_of_eventuallyEq
          filter_upwards [(owner t ht).open_dom.mem_nhds (owner_dom t ht)] with s hs
          have hsD : s ∈ D := Set.mem_sUnion.mpr
            ⟨(owner t ht).dom, ⟨owner t ht, owner_mem t ht, rfl⟩, hs⟩
          have heq := pointedSolution_eqOn_inter F hF Y₀ (owner s hsD) (owner t ht)
            ⟨owner_dom s hsD, hs⟩
          simpa [curve, hsD] using heq }
    refine ⟨upper, ?_⟩
    intro p hp
    refine ⟨?_, ?_⟩
    · intro t ht
      exact Set.mem_sUnion.mpr ⟨p.dom, ⟨p, hp, rfl⟩, ht⟩
    · intro t ht
      have htD : t ∈ D := Set.mem_sUnion.mpr ⟨p.dom, ⟨p, hp, rfl⟩, ht⟩
      have heq := pointedSolution_eqOn_inter F hF Y₀ p (owner t htD)
        ⟨ht, owner_dom t htD⟩
      have hcurve : curve t = (owner t htD).curve t := by simp [curve, htD]
      exact heq.trans hcurve.symm
  · obtain ⟨p⟩ := pointedSolution_nonempty F hF Y₀
    refine ⟨p, ?_⟩
    intro q hq
    exact (hCempty ⟨q, hq⟩).elim

/-- The nonnegative part of an open connected real domain is an initial
interval, with a finite or infinite right endpoint. -/
private theorem forward_endpoint_of_open_preconnected {D : Set ℝ}
    (hopen : IsOpen D) (hconn : IsPreconnected D) (h0 : 0 ∈ D) :
    ∃ Tmax : WithTop ℝ, 0 < Tmax ∧
      D ∩ Set.Ici 0 = {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax} := by
  let S : Set ℝ := D ∩ Set.Ici 0
  have hS0 : 0 ∈ S := ⟨h0, by simp⟩
  have hbetween {t u : ℝ} (ht : 0 ≤ t) (hu : u ∈ S) (htu : t ≤ u) : t ∈ D := by
    exact hconn.ordConnected.out h0 hu.1 ⟨ht, htu⟩
  by_cases hbounded : BddAbove S
  · obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds h0)
    have hδ2 : δ / 2 ∈ S := by
      constructor
      · apply hδsub
        rw [Metric.mem_ball, Real.dist_eq]
        rw [sub_zero, abs_of_pos (by positivity)]
        linarith
      · simp
        linarith
    have hpos : 0 < sSup S := lt_csSup_of_lt hbounded hδ2 (by linarith)
    refine ⟨(sSup S : ℝ), by simpa using hpos, ?_⟩
    · ext t
      constructor
      · intro ht
        rcases Metric.mem_nhds_iff.1 (hopen.mem_nhds ht.1) with ⟨δ, hδ, hδsub⟩
        have hu : t + δ / 2 ∈ S := by
          constructor
          · apply hδsub
            rw [Metric.mem_ball, Real.dist_eq]
            rw [add_sub_cancel_left, abs_of_pos (by linarith)]
            linarith
          · simp
            have ht0 : 0 ≤ t := by simpa using ht.2
            linarith
        have hlt : t < sSup S := lt_csSup_of_lt hbounded hu (by linarith)
        exact ⟨ht.2, by simpa using hlt⟩
      · rintro ⟨ht0, ht⟩
        have ht' : t < sSup S := by simpa using ht
        obtain ⟨u, hu, htu⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ ht'
        exact ⟨hbetween ht0 hu htu.le, ht0⟩
  · refine ⟨⊤, by simp, ?_⟩
    ext t
    constructor
    · intro ht
      exact ⟨ht.2, by simp⟩
    · rintro ⟨ht0, ht⟩
      have hexists : ∃ u ∈ S, t < u := by
        by_contra h
        push Not at h
        apply hbounded
        exact ⟨t, h⟩
      rcases hexists with ⟨u, hu, htu⟩
      exact ⟨hbetween ht0 hu htu.le, ht0⟩

/-- Filling a finite left endpoint by its limiting value preserves continuity
on a closed interval.  This isolates the topological part of continuation from
the ODE uniqueness argument. -/
private theorem continuousOn_fill_left_endpoint
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a T : ℝ} (_haT : a < T) (u : ℝ → X) (l : X)
    (hulim : Tendsto u (nhdsWithin T (Set.Iio T)) (nhds l))
    (hcont : ∀ s ∈ Set.Icc a T, s < T → ContinuousAt u s) :
    ContinuousOn (fun s => if s = T then l else u s) (Set.Icc a T) := by
  intro s hs
  by_cases hsT : s = T
  · subst s
    have hconst : Tendsto (fun _ : ℝ => l)
        (nhdsWithin T (Set.Icc a T ∩ {x : ℝ | x = T})) (nhds l) :=
      tendsto_const_nhds.mono_left nhdsWithin_le_nhds
    have hu : Tendsto u
        (nhdsWithin T (Set.Icc a T ∩ {x : ℝ | ¬ x = T})) (nhds l) := by
      apply tendsto_nhdsWithin_mono_left _ hulim
      intro r hr
      exact lt_of_le_of_ne hr.1.2 hr.2
    simpa only [ContinuousWithinAt, if_pos] using
      (Filter.Tendsto.if_nhdsWithin (p := fun x : ℝ => x = T) hconst hu)
  · have hslt : s < T := lt_of_le_of_ne hs.2 hsT
    apply (hcont s hs hslt).continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Iio_mem_nhds hslt)] with r hr
      simp [ne_of_lt hr]
    · simp [hsT]

/-- A solution which converges to the value of a local germ at a finite right
endpoint agrees with that germ on a left neighbourhood of the endpoint. -/
private theorem ode_eqOn_left_of_tendsto
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    {T ε : ℝ} (hε : 0 < ε) {u v : ℝ → X} {l : X}
    (hu : ∀ s ∈ Set.Ioo (T - ε) T, HasDerivAt u (F (u s)) s)
    (hv : ∀ s ∈ Set.Ioo (T - ε) (T + ε), HasDerivAt v (F (v s)) s)
    (hulim : Tendsto u (nhdsWithin T (Set.Iio T)) (nhds l)) (hvT : v T = l) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ Set.EqOn u v (Set.Ioo (T - ρ) T) := by
  rcases hF l with ⟨U, hU, L, hL0, hLip⟩
  let K : NNReal := ⟨L, hL0⟩
  have hLipU : LipschitzOnWith K F U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    simpa only [dist_eq_norm] using hLip y hy z hz
  rcases Metric.mem_nhds_iff.mp hU with ⟨r, hr, hrU⟩
  have huU : ∀ᶠ s in nhdsWithin T (Set.Iio T), u s ∈ Metric.ball l r :=
    hulim.eventually (Metric.ball_mem_nhds l hr)
  change {s | u s ∈ Metric.ball l r} ∈ nhdsWithin T (Set.Iio T) at huU
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at huU
  rcases huU with ⟨V, hV, hVsub⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨δu, hδu, hδuV⟩
  have hu_mem (s : ℝ) (hs : T - δu < s) (hsT : s < T) : u s ∈ U := by
    apply hrU
    apply hVsub
    constructor
    · apply hδuV
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_nonpos (by linarith)]
      linarith
    · exact hsT
  have hvcont : ContinuousAt v T :=
    (hv T ⟨by linarith, by linarith⟩).continuousAt
  have hvU : ∀ᶠ s in nhds T, v s ∈ Metric.ball l r := by
    rw [← hvT]
    exact hvcont.eventually (Metric.ball_mem_nhds _ hr)
  rcases Metric.mem_nhds_iff.mp hvU with ⟨δv, hδv, hδvsub⟩
  have hv_mem (s : ℝ) (hs : |s - T| < δv) : v s ∈ U := by
    exact hrU (hδvsub (by simpa [Metric.mem_ball, Real.dist_eq] using hs))
  let ρ : ℝ := min (ε / 2) (min (δu / 2) (δv / 2))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hρε : ρ < ε := by
    have : ρ ≤ ε / 2 := min_le_left _ _
    linarith
  have hρu : ρ < δu := by
    have : ρ ≤ δu / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hρv : ρ < δv := by
    have : ρ ≤ δv / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  let uT : ℝ → X := fun s => if s = T then l else u s
  have huTcont : ContinuousOn uT (Set.Icc (T - ρ) T) := by
    apply continuousOn_fill_left_endpoint (by linarith [hρ]) u l hulim
    intro s hs hsT
    rcases hs with ⟨hslo, _⟩
    exact (hu s ⟨by linarith [hρε], hsT⟩).continuousAt
  have hvcont' : ContinuousOn v (Set.Icc (T - ρ) T) := by
    apply HasDerivAt.continuousOn
    intro s hs
    rcases hs with ⟨hslo, hshi⟩
    exact hv s ⟨by linarith [hρε], by linarith⟩
  have huTder : ∀ s ∈ Set.Ioc (T - ρ) T,
      HasDerivWithinAt uT (F (uT s)) (Set.Iic s) s := by
    intro s hs
    rcases hs with ⟨hslo, hsle⟩
    by_cases hsT_eq : s = T
    · subst s
      have hdiff : DifferentiableOn ℝ uT (Set.Ioo (T - ρ) T) := by
        intro x hx
        have hEq : uT =ᶠ[nhds x] u := by
          filter_upwards [Iio_mem_nhds hx.2] with y hy
          change y < T at hy
          simp [uT, show y ≠ T by linarith]
        exact ((hu x ⟨by linarith [hρε, hx.1], hx.2⟩).congr_of_eventuallyEq hEq).differentiableAt.differentiableWithinAt
      have hlim : ContinuousWithinAt uT (Set.Ioo (T - ρ) T) T :=
        (huTcont T ⟨by linarith [hρ], le_rfl⟩).mono Set.Ioo_subset_Icc_self
      have hFcont : ContinuousAt F l :=
        (hLipU.continuousOn l (mem_of_mem_nhds hU)).continuousAt hU
      have hderiv_eq : (fun x => deriv uT x) =ᶠ[nhdsWithin T (Set.Iio T)]
          fun x => F (u x) := by
        filter_upwards [Ioo_mem_nhdsLT (a := T - ρ) (b := T) (by linarith [hρ])] with x hx
        have hEq : uT =ᶠ[nhds x] u := by
          filter_upwards [Iio_mem_nhds hx.2] with y hy
          change y < T at hy
          simp [uT, show y ≠ T by linarith]
        rw [hEq.deriv_eq]
        exact (hu x ⟨by linarith [hρε, hx.1], hx.2⟩).deriv
      have hderiv_lim : Tendsto (fun x => deriv uT x)
          (nhdsWithin T (Set.Iio T)) (nhds (F l)) := by
        exact (hFcont.tendsto.comp hulim).congr' hderiv_eq.symm
      simpa [uT] using hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hlim
        (Ioo_mem_nhdsLT (a := T - ρ) (b := T) (by linarith [hρ])) hderiv_lim
    · have hsT : s < T := lt_of_le_of_ne hsle hsT_eq
      have hEq : uT =ᶠ[nhds s] u := by
        filter_upwards [Iio_mem_nhds hsT] with x hx
        change x < T at hx
        simp [uT, show x ≠ T by linarith]
      simpa [uT, ne_of_lt hsT] using
        ((hu s ⟨by linarith [hρε], hsT⟩).congr_of_eventuallyEq hEq).hasDerivWithinAt (s := Set.Iic s)
  have hvder : ∀ s ∈ Set.Ioc (T - ρ) T,
      HasDerivWithinAt v (F (v s)) (Set.Iic s) s := by
    intro s hs
    rcases hs with ⟨hslo, hsle⟩
    exact (hv s ⟨by linarith [hρε], by linarith⟩).hasDerivWithinAt
  have huTrange : ∀ s ∈ Set.Ioc (T - ρ) T, uT s ∈ U := by
    intro s hs
    rcases hs with ⟨hslo, hsle⟩
    rcases lt_or_eq_of_le hsle with hsT | rfl
    · rw [show uT s = u s by simp [uT, ne_of_lt hsT]]
      apply hu_mem s
      · linarith [hρu]
      · exact hsT
    · simp [uT, mem_of_mem_nhds hU]
  have hvrange : ∀ s ∈ Set.Ioc (T - ρ) T, v s ∈ U := by
    intro s hs
    rcases hs with ⟨hslo, hsle⟩
    apply hv_mem s
    rw [abs_of_nonpos (by linarith)]
    linarith [hρv]
  have heq := ODE_solution_unique_of_mem_Icc_left (fun _ _ => hLipU)
    huTcont huTder huTrange hvcont' hvder hvrange (by simp [uT, hvT])
  refine ⟨ρ, hρ, hρε, ?_⟩
  intro s hs
  have hs' : s ∈ Set.Icc (T - ρ) T := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have := heq hs'
  simpa [uT, ne_of_lt hs.2] using this

/-- A Zorn-maximal pointed solution cannot be extended forward by an arbitrary
order-connected classical representative.  The only subtle point is that the
representative need not have an open domain; its value at the endpoint supplies
the left limit needed to attach a local open germ. -/
private theorem pointedSolution_forward_maximal_of_ordConnected
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    (Y₀ : X) (p : PointedSolution F Y₀)
    (hpmax : ∀ q : PointedSolution F Y₀, p ≤ q → q ≤ p)
    {T : ℝ} (hTpos : 0 < T)
    (hforward : p.dom ∩ Set.Ici 0 = {t : ℝ | 0 ≤ t ∧ t < T})
    (I : Set ℝ) (Z : ℝ → X) (hIconn : Set.OrdConnected I) (_hI0 : 0 ∈ I)
    (hZ : IsClassicalSolutionOn F Y₀ I Z)
    (hsub : {t : ℝ | 0 ≤ t ∧ t < T} ⊆ I)
    (heq : ∀ t : ℝ, 0 ≤ t → t < T → p.curve t = Z t) :
    I ∩ Set.Ici 0 ⊆ {t : ℝ | 0 ≤ t ∧ t < T} := by
  rintro t ⟨htI, ht0⟩
  refine ⟨ht0, ?_⟩
  by_contra hlt
  have hTt : T ≤ t := le_of_not_gt hlt
  have hsI : T / 2 ∈ I := hsub ⟨by linarith, by linarith⟩
  have hTI : T ∈ I := hIconn.out hsI htI ⟨by linarith, hTt⟩
  let l : X := Z T
  have hZT : HasDerivAt Z (F (Z T)) T := hZ.2.2 T hTI
  have hZlim : Tendsto Z (nhdsWithin T (Set.Iio T)) (nhds l) := by
    simpa [l] using hZT.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hevent : p.curve =ᶠ[nhdsWithin T (Set.Iio T)] Z := by
    filter_upwards [Ioo_mem_nhdsLT (a := T / 2) (b := T) (by linarith)] with r hr
    exact heq r (by linarith [hTpos, hr.1]) hr.2
  have hplim : Tendsto p.curve (nhdsWithin T (Set.Iio T)) (nhds l) :=
    Filter.Tendsto.congr' hevent.symm hZlim
  obtain ⟨ε, hε, α, hαT, hα⟩ :=
    local_classical_solution_of_locally_lipschitz F hF T l
  let ε₀ : ℝ := min ε (T / 2)
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min hε (by linarith)
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀T : ε₀ ≤ T / 2 := min_le_right _ _
  have hα₀ : ∀ r ∈ Set.Ioo (T - ε₀) (T + ε₀),
      HasDerivAt α (F (α r)) r := by
    intro r hr
    apply hα r
    constructor <;> linarith [hε₀ε, hr.1, hr.2]
  have hpode : ∀ r ∈ Set.Ioo (T - ε₀) T,
      HasDerivAt p.curve (F (p.curve r)) r := by
    intro r hr
    apply p.ode r
    have hrforward : r ∈ {t : ℝ | 0 ≤ t ∧ t < T} :=
      ⟨by linarith [hε₀T, hr.1], hr.2⟩
    rw [← hforward] at hrforward
    exact hrforward.1
  obtain ⟨ρ, hρ, hρε₀, hleft⟩ :=
    ode_eqOn_left_of_tendsto F hF hε₀ hpode hα₀ hplim hαT
  have hEq : Set.EqOn p.curve α (p.dom ∩ Set.Ioo (T - ρ) (T + ε₀)) := by
    rintro r ⟨hrdom, hr⟩
    have hrT : r < T := by
      by_contra h
      have hTr : T ≤ r := le_of_not_gt h
      have hr0 : 0 ≤ r := by linarith
      have hrforward : r ∈ p.dom ∩ Set.Ici 0 := ⟨hrdom, hr0⟩
      have hrlt : r < T := (hforward ▸ hrforward).2
      linarith
    exact hleft ⟨hr.1, hrT⟩
  have hcdom : T - ρ / 2 ∈ p.dom := by
    have hcforward : T - ρ / 2 ∈ {t : ℝ | 0 ≤ t ∧ t < T} :=
      ⟨by linarith [hε₀T, hρε₀], by linarith [hρ]⟩
    rw [← hforward] at hcforward
    exact hcforward.1
  have hcIoo : T - ρ / 2 ∈ Set.Ioo (T - ρ) (T + ε₀) := by
    constructor <;> linarith
  obtain ⟨q, hpq, hαq, -⟩ := pointedSolution_extend_of_eqOn F Y₀ p
    (a := T - ρ) (b := T + ε₀) (by linarith [hρ, hε₀]) α
    (fun r hr => hα₀ r ⟨by linarith [hρε₀, hr.1], hr.2⟩)
    hEq ⟨T - ρ / 2, hcdom, hcIoo⟩
  have hrq : T + ρ / 2 ∈ q.dom := hαq (by constructor <;> linarith)
  have hrp : T + ρ / 2 ∈ p.dom := (hpmax q hpq).1 hrq
  have hrforward : T + ρ / 2 ∈ p.dom ∩ Set.Ici 0 :=
    ⟨hrp, by
      change 0 ≤ T + ρ / 2
      linarith⟩
  rw [hforward] at hrforward
  have hrlt : T + ρ / 2 < T := hrforward.2
  linarith [hρ]

/-- Classical forward representatives with the same initial value agree at
every time at which both are defined. -/
private theorem classicalSolution_eq_of_below_both
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖)
    (Y₀ : X) {T₁ T₂ : WithTop ℝ} {Y₁ Y₂ : ℝ → X}
    (h₁ : IsClassicalSolutionOn F Y₀ {t | 0 ≤ t ∧ (t : WithTop ℝ) < T₁} Y₁)
    (h₂ : IsClassicalSolutionOn F Y₀ {t | 0 ≤ t ∧ (t : WithTop ℝ) < T₂} Y₂) :
    ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < T₁ → (t : WithTop ℝ) < T₂ → Y₁ t = Y₂ t := by
  intro t ht0 ht₁ ht₂
  by_cases ht : t = 0
  · subst t
    exact h₁.2.1.trans h₂.2.1.symm
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  obtain ⟨B, htB, hB₁, hB₂⟩ : ∃ B : ℝ, t < B ∧
      (∀ r ∈ Set.Ioo 0 B, r ∈ {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < T₁}) ∧
      (∀ r ∈ Set.Ioo 0 B, r ∈ {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < T₂}) := by
    induction T₁ using WithTop.recTopCoe with
    | top =>
      induction T₂ using WithTop.recTopCoe with
      | top =>
        refine ⟨t + 1, by linarith, ?_, ?_⟩ <;>
          intro r hr <;> exact ⟨hr.1.le, by simp⟩
      | coe C =>
        have htC : t < C := by simpa using ht₂
        refine ⟨(t + C) / 2, by linarith, ?_, ?_⟩
        · intro r hr; exact ⟨hr.1.le, by simp⟩
        · intro r hr
          refine ⟨hr.1.le, ?_⟩
          exact_mod_cast (show r < C by linarith [hr.2])
    | coe A =>
      induction T₂ using WithTop.recTopCoe with
      | top =>
        have htA : t < A := by simpa using ht₁
        refine ⟨(t + A) / 2, by linarith, ?_, ?_⟩
        · intro r hr
          refine ⟨hr.1.le, ?_⟩
          exact_mod_cast (show r < A by linarith [hr.2])
        · intro r hr; exact ⟨hr.1.le, by simp⟩
      | coe C =>
        have htA : t < A := by simpa using ht₁
        have htC : t < C := by simpa using ht₂
        let B := t + min (A - t) (C - t) / 2
        have hAt : 0 < A - t := sub_pos.mpr htA
        have hCt : 0 < C - t := sub_pos.mpr htC
        have hd : 0 < min (A - t) (C - t) / 2 := by positivity
        have hBA : B < A := by
          dsimp [B]
          have := min_le_left (A - t) (C - t)
          linarith
        have hBC : B < C := by
          dsimp [B]
          have := min_le_right (A - t) (C - t)
          linarith
        refine ⟨B, by dsimp [B]; linarith, ?_, ?_⟩
        · intro r hr
          refine ⟨hr.1.le, ?_⟩
          exact_mod_cast (lt_trans hr.2 hBA)
        · intro r hr
          refine ⟨hr.1.le, ?_⟩
          exact_mod_cast (lt_trans hr.2 hBC)
  rcases hF Y₀ with ⟨U, hU, L, hL0, hLip⟩
  let K : NNReal := ⟨L, hL0⟩
  have hLipU : LipschitzOnWith K F U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    simpa only [dist_eq_norm] using hLip y hy z hz
  have hcont₁ : ContinuousAt Y₁ 0 := (h₁.2.2 0 h₁.1).continuousAt
  have hcont₂ : ContinuousAt Y₂ 0 := (h₂.2.2 0 h₂.1).continuousAt
  have hU₁ : U ∈ nhds (Y₁ 0) := by simpa [h₁.2.1] using hU
  rcases Metric.mem_nhds_iff.mp (hcont₁ hU₁) with ⟨δ₁, hδ₁, hδ₁U⟩
  have hU₂ : U ∈ nhds (Y₂ 0) := by simpa [h₁.2.1, h₂.2.1] using hU
  rcases Metric.mem_nhds_iff.mp (hcont₂ hU₂) with ⟨δ₂, hδ₂, hδ₂U⟩
  let δ : ℝ := min (B / 2) (min (δ₁ / 2) (δ₂ / 2))
  have hBpos : 0 < B := lt_trans htpos htB
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδB : δ < B := by
    have h : δ ≤ B / 2 := min_le_left _ _
    linarith
  have hδ₁' : δ < δ₁ := by
    have h : δ ≤ δ₁ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδ₂' : δ < δ₂ := by
    have h : δ ≤ δ₂ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hI₁ : ∀ r ∈ Set.Icc 0 δ,
      r ∈ {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < T₁} := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | hr0
    · exact h₁.1
    · exact hB₁ r ⟨hr0, lt_of_le_of_lt hr.2 hδB⟩
  have hI₂ : ∀ r ∈ Set.Icc 0 δ,
      r ∈ {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < T₂} := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | hr0
    · exact h₂.1
    · exact hB₂ r ⟨hr0, lt_of_le_of_lt hr.2 hδB⟩
  have hY₁c : ContinuousOn Y₁ (Set.Icc 0 δ) := by
    intro r hr
    exact (h₁.2.2 r (hI₁ r hr)).continuousAt.continuousWithinAt
  have hY₂c : ContinuousOn Y₂ (Set.Icc 0 δ) := by
    intro r hr
    exact (h₂.2.2 r (hI₂ r hr)).continuousAt.continuousWithinAt
  have hY₁d : ∀ r ∈ Set.Ico 0 δ,
      HasDerivWithinAt Y₁ (F (Y₁ r)) (Set.Ici r) r := by
    intro r hr
    exact (h₁.2.2 r (hI₁ r ⟨hr.1, hr.2.le⟩)).hasDerivWithinAt
  have hY₂d : ∀ r ∈ Set.Ico 0 δ,
      HasDerivWithinAt Y₂ (F (Y₂ r)) (Set.Ici r) r := by
    intro r hr
    exact (h₂.2.2 r (hI₂ r ⟨hr.1, hr.2.le⟩)).hasDerivWithinAt
  have hY₁U : ∀ r ∈ Set.Ico 0 δ, Y₁ r ∈ U := by
    intro r hr
    apply hδ₁U
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_of_nonneg hr.1]
    exact lt_trans hr.2 hδ₁'
  have hY₂U : ∀ r ∈ Set.Ico 0 δ, Y₂ r ∈ U := by
    intro r hr
    apply hδ₂U
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_of_nonneg hr.1]
    exact lt_trans hr.2 hδ₂'
  have heq := ODE_solution_unique_of_mem_Icc_right (fun _ _ => hLipU)
    hY₁c hY₁d hY₁U hY₂c hY₂d hY₂U (h₁.2.1.trans h₂.2.1.symm)
  have hseed : Y₁ (δ / 2) = Y₂ (δ / 2) :=
    heq ⟨by linarith, by linarith⟩
  have hprop := ode_eqOn_Ioo_of_locally_lipschitz F hF
    (show δ / 2 ∈ Set.Ioo 0 B by constructor <;> linarith [hδ, hδB]) Y₁ Y₂
    (fun r hr => h₁.2.2 r (hB₁ r ⟨hr.1, hr.2⟩))
    (fun r hr => h₂.2.2 r (hB₂ r ⟨hr.1, hr.2⟩)) hseed
  exact hprop ⟨htpos, htB⟩

private theorem withTop_le_of_forward_subset {A B : WithTop ℝ} (hA : 0 < A)
    (hsub : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < A → (t : WithTop ℝ) < B) : A ≤ B := by
  induction A using WithTop.recTopCoe with
  | top =>
      induction B using WithTop.recTopCoe with
      | top => simp
      | coe b =>
          exfalso
          let r : ℝ := max 0 (b + 1)
          have hr0 : 0 ≤ r := le_max_left _ _
          have hbr : b < r := by
            dsimp [r]
            linarith [le_max_right 0 (b + 1)]
          have := hsub r hr0 (by simp)
          have : r < b := by simpa using this
          linarith
  | coe a =>
      induction B using WithTop.recTopCoe with
      | top => simp
      | coe b =>
          have ha : 0 < a := by simpa using hA
          simp only [WithTop.coe_le_coe]
          by_contra hab
          have hba : b < a := lt_of_not_ge hab
          let c : ℝ := max 0 b
          have hc0 : 0 ≤ c := le_max_left _ _
          have hca : c < a := by
            dsimp [c]
            exact max_lt ha hba
          let m : ℝ := (a + c) / 2
          have hm0 : 0 ≤ m := by dsimp [m]; linarith
          have hma : m < a := by dsimp [m]; linarith
          have hbm : b < m := by
            have : b ≤ c := le_max_right _ _
            dsimp [m]
            linarith
          have hmb := hsub m hm0 (by simpa using hma)
          have : m < b := by simpa using hmb
          linarith
/-- Cauchy--Lipschitz continuation theorem for a locally Lipschitz vector field. -/
theorem cauchy_lipschitz_continuation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (F : X → X) (Y₀ : X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖) :
    ∃ Tmax : WithTop ℝ, ∃ Y : ℝ → X,
      IsMaximalClassicalSolution F Y₀ Tmax Y ∧
        (∀ Tmax' Y', IsMaximalClassicalSolution F Y₀ Tmax' Y' →
          Tmax' = Tmax ∧ ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax → Y' t = Y t) ∧
        (∀ T : ℝ, Tmax = (T : WithTop ℝ) →
          ∀ l : X, Tendsto Y
            (nhdsWithin T {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax}) (nhds l) →
              ∃ S : ℝ, T < S ∧ ∃ Z,
                IsClassicalSolutionOn F Y₀ {t : ℝ | 0 ≤ t ∧ t < S} Z ∧
                (∀ t, 0 ≤ t → t < T → Z t = Y t)) := by
  classical
  obtain ⟨p, hpmax⟩ := zorn_le (pointedSolution_chain_upper_bound F hF Y₀)
  obtain ⟨Tmax, hTmax_pos, hforward⟩ :=
    forward_endpoint_of_open_preconnected p.open_dom p.preconnected_dom p.zero_mem
  let D : Set ℝ := {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax}
  have hD : D = p.dom ∩ Set.Ici 0 := hforward.symm
  have hpclassical : IsClassicalSolutionOn F Y₀ D p.curve := by
    refine ⟨?_, p.initial, ?_⟩
    · rw [hD]
      exact ⟨p.zero_mem, by simp⟩
    · intro t ht
      have htp : t ∈ p.dom := (hD ▸ ht).1
      exact p.ode t htp
  have hmaxp : IsMaximalClassicalSolution F Y₀ Tmax p.curve := by
    refine ⟨hTmax_pos, hpclassical, ?_⟩
    induction Tmax using WithTop.recTopCoe with
    | top =>
        intro I Z hIconn hI0 hZ hsub heq t ht
        exact ⟨ht.2, by simp⟩
    | coe T =>
        intro I Z hIconn hI0 hZ hsub heq
        have hTpos : 0 < T := by simpa using hTmax_pos
        have hforward' : p.dom ∩ Set.Ici 0 = {t : ℝ | 0 ≤ t ∧ t < T} := by
          simpa using hforward
        have hsub' : {t : ℝ | 0 ≤ t ∧ t < T} ⊆ I := by
          simpa using hsub
        have heq' : ∀ t : ℝ, 0 ≤ t → t < T → p.curve t = Z t := by
          intro t ht0 ht
          exact heq t ht0 (by simpa using ht)
        simpa using pointedSolution_forward_maximal_of_ordConnected F hF Y₀ p hpmax
          hTpos hforward' I Z hIconn hI0 hZ hsub' heq'
  -- The remaining two fields use the same bridge together with forward
  -- uniqueness and the endpoint-gluing construction.
  refine ⟨Tmax, p.curve, hmaxp, ?_⟩
  refine ⟨?_, ?_⟩
  · intro Tmax' Y' hmax'
    let D' : Set ℝ := {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax'}
    have hcommon : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax →
        (t : WithTop ℝ) < Tmax' → p.curve t = Y' t :=
      classicalSolution_eq_of_below_both F hF Y₀ hpclassical hmax'.2.1
    have hDconn : Set.OrdConnected D := by
      rw [hD]
      exact p.preconnected_dom.ordConnected.inter Set.ordConnected_Ici
    have hD'conn : Set.OrdConnected D' := by
      induction Tmax' using WithTop.recTopCoe with
      | top =>
          rw [show D' = Set.Ici 0 by ext t; simp [D']]
          exact Set.ordConnected_Ici
      | coe T' =>
          rw [show D' = Set.Ico 0 T' by ext t; simp [D']]
          exact Set.ordConnected_Ico
    have hle : Tmax ≤ Tmax' := by
      by_contra hnot
      have hlt : Tmax' < Tmax := lt_of_not_ge hnot
      have hD'sub : D' ⊆ D := by
        intro t ht
        exact ⟨ht.1, lt_trans ht.2 hlt⟩
      have hsub := hmax'.2.2 D p.curve hDconn hpclassical.1 hpclassical hD'sub
        (fun t ht0 ht' => (hcommon t ht0 (hD'sub ⟨ht0, ht'⟩).2 ht').symm)
      have hDom : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax →
          (t : WithTop ℝ) < Tmax' := by
        intro t ht0 ht
        have := hsub ⟨⟨ht0, ht⟩, ht0⟩
        exact this.2
      exact (not_le_of_gt hlt) (withTop_le_of_forward_subset hmaxp.1 hDom)
    have hDsub : D ⊆ D' := by
      intro t ht
      change 0 ≤ t ∧ (t : WithTop ℝ) < Tmax at ht
      change 0 ≤ t ∧ (t : WithTop ℝ) < Tmax'
      exact ⟨ht.1, lt_of_lt_of_le ht.2 hle⟩
    have hge : Tmax' ≤ Tmax := by
      by_contra hnot
      have hlt : Tmax < Tmax' := lt_of_not_ge hnot
      have hsub := hmaxp.2.2 D' Y' hD'conn hmax'.2.1.1 hmax'.2.1 hDsub
        (fun t ht0 ht => hcommon t ht0 ht (lt_trans ht hlt))
      have hDom : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax' →
          (t : WithTop ℝ) < Tmax := by
        intro t ht0 ht
        have := hsub ⟨⟨ht0, ht⟩, ht0⟩
        exact this.2
      exact (not_le_of_gt hlt) (withTop_le_of_forward_subset hmax'.1 hDom)
    have heq : Tmax' = Tmax := le_antisymm hge hle
    refine ⟨heq, ?_⟩
    intro t ht0 ht
    exact (hcommon t ht0 ht (by simpa [heq] using ht)).symm
  · intro T hTmax l hlim
    have hTpos : 0 < T := by simpa [hTmax] using hTmax_pos
    have hsmall : Set.Ioo (T / 2) T ⊆ D := by
      intro r hr
      change 0 ≤ r ∧ (r : WithTop ℝ) < Tmax
      constructor
      · linarith [hTpos, hr.1]
      · simpa [hTmax] using hr.2
    have hlimsmall := tendsto_nhdsWithin_mono_left hsmall hlim
    have hplim : Tendsto p.curve (nhdsWithin T (Set.Iio T)) (nhds l) := by
      rw [nhdsWithin_Ioo_eq_nhdsLT (by linarith [hTpos])] at hlimsmall
      exact hlimsmall
    obtain ⟨ε, hε, α, hαT, hα⟩ :=
      local_classical_solution_of_locally_lipschitz F hF T l
    let ε₀ : ℝ := min ε (T / 2)
    have hε₀ : 0 < ε₀ := by dsimp [ε₀]; exact lt_min hε (by linarith)
    have hε₀ε : ε₀ ≤ ε := min_le_left _ _
    have hε₀T : ε₀ ≤ T / 2 := min_le_right _ _
    have hα₀ : ∀ r ∈ Set.Ioo (T - ε₀) (T + ε₀),
        HasDerivAt α (F (α r)) r := by
      intro r hr
      apply hα r
      exact ⟨lt_of_le_of_lt (sub_le_sub_left hε₀ε T) hr.1,
        by linarith [hε₀ε, hr.2]⟩
    have hpode : ∀ r ∈ Set.Ioo (T - ε₀) T,
        HasDerivAt p.curve (F (p.curve r)) r := by
      intro r hr
      apply p.ode r
      have : r ∈ D := by
        change 0 ≤ r ∧ (r : WithTop ℝ) < Tmax
        constructor
        · linarith [hε₀T, hr.1]
        · simpa [hTmax] using hr.2
      rw [hD] at this
      exact this.1
    obtain ⟨ρ, hρ, hρε₀, hleft⟩ :=
      ode_eqOn_left_of_tendsto F hF hε₀ hpode hα₀ hplim hαT
    have hEq : Set.EqOn p.curve α (p.dom ∩ Set.Ioo (T - ρ) (T + ε₀)) := by
      rintro r ⟨hrdom, hr⟩
      have hrT : r < T := by
        by_contra hn
        have hTr : T ≤ r := le_of_not_gt hn
        have hr0 : 0 ≤ r := by linarith
        have hmem : r ∈ D := by rw [hD]; exact ⟨hrdom, hr0⟩
        have : r < T := by simpa [hTmax] using hmem.2
        linarith
      exact hleft ⟨hr.1, hrT⟩
    have hcdom : T - ρ / 2 ∈ p.dom := by
      have hmem : T - ρ / 2 ∈ D := by
        constructor
        · linarith [hε₀T, hρε₀]
        · rw [hTmax]
          exact_mod_cast (show T - ρ / 2 < T by linarith [hρ])
      exact (hD ▸ hmem).1
    have hcIoo : T - ρ / 2 ∈ Set.Ioo (T - ρ) (T + ε₀) := by constructor <;> linarith
    obtain ⟨q, hpq, hαq, _⟩ := pointedSolution_extend_of_eqOn F Y₀ p
      (a := T - ρ) (b := T + ε₀) (by linarith) α
      (fun r hr => hα₀ r ⟨by linarith [hρε₀, hr.1], hr.2⟩) hEq ⟨T - ρ / 2, hcdom, hcIoo⟩
    let S : ℝ := T + ρ / 2
    refine ⟨S, by dsimp [S]; linarith, q.curve, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · constructor
        · exact le_rfl
        · dsimp [S]; linarith
      · exact (hpq.2 p.zero_mem).symm.trans p.initial
      · intro t ht
        rcases lt_or_ge t T with htT | htT
        · apply q.ode t (hpq.1 ?_)
          have hmem : t ∈ D := ⟨ht.1, by simpa [hTmax] using htT⟩
          exact (hD ▸ hmem).1
        · apply q.ode t (hαq ?_)
          constructor <;> dsimp [S] at ht ⊢ <;> linarith [hρ, hρε₀]
    · intro t ht0 htT
      exact (hpq.2 ((hD ▸ (show t ∈ D from ⟨ht0, by simpa [hTmax] using htT⟩)).1)).symm
end Alvarez2002
