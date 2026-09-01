import Mathlib

/-!
# Ordinary differential equations

Classical-solution theory for autonomous and non-autonomous ODEs: local
existence and maximal continuation of locally Lipschitz vector fields
(Cauchy--Lipschitz), the integral Gronwall inequality, and a comparison lemma
for scalar second-order estimates.

Promoted from `Attouch_Bot_Csetnek_Closed_loop_damping_2023` (ext_thm_3,
ext_thm_6, lem_1),
`Attouch_Complexity_Analysis_Based_on_Tuning_the_Viscosity_Parameter_of_the_Su_Boyd_Cand_s_Inertial_Gradient_Dynamics_2024`
(ext_thm_2),
`Attouch_Asymptotic_stabilization_of_inertial_gradient_dynamics_with_time_dependent_viscosity_2017`
(def_2, ext_thm_1, ext_lem_2) and
`Attouch_Balhag_Chbani_Riahi_Tikhonov_Inertial_Dynamics_2022` (ext_thm_3,
thm_4; non-autonomous ODE theory).
-/

open Filter

/-- A classical solution on a time set.
See also `IsClassicalSolutionOn_nonautonomous` for the time-dependent
generalization (arbitrary initial time). -/
def IsClassicalSolutionOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → X) (Y₀ : X) (I : Set ℝ) (Y : ℝ → X) : Prop :=
  0 ∈ I ∧ Y 0 = Y₀ ∧ ∀ t ∈ I, HasDerivAt Y (F (Y t)) t

/-- Maximality is with respect to extension of the time interval.
See also `IsMaximalClassicalSolution_nonautonomous` for the time-dependent
generalization. -/
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
  have hbetween {t u : ℝ} (ht : 0 ≤ t) (hu : u ∈ S) (htu : t ≤ u) : t ∈ D :=
    hconn.ordConnected.out h0 hu.1 ⟨ht, htu⟩
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
  have hv_mem (s : ℝ) (hs : |s - T| < δv) : v s ∈ U :=
    hrU (hδvsub (by simpa [Metric.mem_ball, Real.dist_eq] using hs))
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
          (nhdsWithin T (Set.Iio T)) (nhds (F l)) :=
        (hFcont.tendsto.comp hulim).congr' hderiv_eq.symm
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
/-- Cauchy--Lipschitz continuation theorem for a locally Lipschitz vector field.
See also `locallyLipschitz_ode_continuation_nonautonomous` for the
time-dependent generalization. -/
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



/-! ### Non-autonomous ODEs (time-dependent fields)

Local existence, uniqueness, and maximal continuation for classical
solutions of `z' = F(t,z)` when the field `F : ℝ → H → H` is
time-dependent and locally Lipschitz in the state variable, with an
arbitrary initial time `t0`.  This is the non-autonomous generalization
of the autonomous theory above; the declarations are kept under distinct
`_nonautonomous` names because the initial datum is bundled differently
(a start time `t0` with value `z0` here, versus `Y₀` with `0 ∈ I` there).

Promoted from
`Attouch_Balhag_Chbani_Riahi_Tikhonov_Inertial_Dynamics_2022`
(items/ext_thm_3, items/thm_4).
-/


/-- A classical solution of `z' = F(t,z)` on the half-open time interval `[t0, T)`.  Non-autonomous generalization of `IsClassicalSolutionOn` (time-dependent field, arbitrary initial time). -/
def IsClassicalSolutionOn_nonautonomous {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H → H) (z : ℝ → H) (t0 T : ℝ) : Prop :=
  ∀ t ∈ Set.Ico t0 T, HasDerivAt z (F t (z t)) t

/-- Local Lipschitz continuity in the state variable, uniform on a neighborhood of each point.  Non-autonomous counterpart of the local Lipschitz hypothesis used in `cauchy_lipschitz_continuation`. -/
def IsLocallyLipschitzInState_nonautonomous {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H → H) : Prop :=
  ∀ (t : ℝ) (x : H), ∃ U : Set H, U ∈ nhds x ∧ ∃ L : ℝ, 0 ≤ L ∧
    ∀ (y : H), y ∈ U → ∀ (z : H), z ∈ U → ‖F t y - F t z‖ ≤ L * ‖y - z‖

/-- Local state Lipschitz bounds which remain valid on a time neighbourhood.
This is the non-autonomous hypothesis required by Picard--Lindelöf; see
`locallyLipschitz_ode_continuation_nonautonomous`. -/
def IsUniformLocallyLipschitzInState_nonautonomous {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (F : ℝ → H → H) : Prop :=
  ∀ (t : ℝ) (x : H), ∃ I : Set ℝ, I ∈ nhds t ∧ ∃ U : Set H, U ∈ nhds x ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ I, ∀ y ∈ U, ∀ z ∈ U,
      ‖F s y - F s z‖ ≤ L * ‖y - z‖

/-- The local Cauchy--Lipschitz conclusion under the time-uniform local
Lipschitz hypothesis. -/
private theorem local_classical_solution_of_uniform_locally_lipschitz
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hcont : Continuous fun p : ℝ × H => F p.1 p.2)
    (hlip : IsUniformLocallyLipschitzInState_nonautonomous F) (t0 : ℝ) (z0 : H) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℝ → H, z t0 = z0 ∧
      ∀ t ∈ Set.Ioo (t0 - eta) (t0 + eta), HasDerivAt z (F t (z t)) t := by
  rcases hlip t0 z0 with ⟨I, htI, U, hzU, L, hL, hLip⟩
  rcases Metric.mem_nhds_iff.mp hzU with ⟨r, hr, hrU⟩
  rcases Metric.mem_nhds_iff.mp htI with ⟨d, hd, hdI⟩
  have hFcont : Continuous fun t : ℝ => F t z0 :=
    hcont.comp (continuous_id.prodMk continuous_const)
  rcases Metric.mem_nhds_iff.mp (hFcont.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds _ zero_lt_one)) with ⟨e, he, heF⟩
  let a : ℝ := r / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let q : ℝ := min d e
  have hq : 0 < q := lt_min hd he
  have hballU (u : H) (hu : u ∈ Metric.closedBall z0 a) : u ∈ U := by
    apply hrU
    rw [Metric.mem_ball]
    have : dist u z0 ≤ a := by simpa [dist_comm] using Metric.mem_closedBall.mp hu
    dsimp [a] at this ⊢
    linarith
  let M : ℝ := L * a + ‖F t0 z0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let eta : ℝ := min (q / 2) (a / (2 * M))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta_q : eta < q := by
    calc eta ≤ q / 2 := min_le_left _ _
         _ < q := by linarith
  have htime (t : ℝ) (ht : t ∈ Set.Icc (t0 - eta) (t0 + eta)) : t ∈ I := by
    apply hdI
    rw [Metric.mem_ball, Real.dist_eq]
    have : |t - t0| ≤ eta := by
      rw [abs_sub_comm]
      exact abs_le.mpr (by constructor <;> linarith [ht.1, ht.2])
    exact lt_of_le_of_lt this (lt_of_lt_of_le heta_q (min_le_left _ _))
  have hFnear (t : ℝ) (ht : t ∈ Set.Icc (t0 - eta) (t0 + eta)) :
      ‖F t z0 - F t0 z0‖ < 1 := by
    have : t ∈ Metric.ball t0 e := by
      rw [Metric.mem_ball, Real.dist_eq]
      have : |t - t0| ≤ eta := by
        rw [abs_sub_comm]
        exact abs_le.mpr (by constructor <;> linarith [ht.1, ht.2])
      exact lt_of_le_of_lt this (lt_of_lt_of_le heta_q (min_le_right _ _))
    simpa [Metric.mem_ball, dist_eq_norm] using heF this
  let K : NNReal := ⟨L, hL⟩
  let Mnn : NNReal := ⟨M, hM.le⟩
  let ann : NNReal := ⟨a, ha.le⟩
  have hPL : IsPicardLindelof F (tmin := t0 - eta) (tmax := t0 + eta)
      ⟨t0, by constructor <;> linarith⟩ z0 ann 0 Mnn K := by
    refine { lipschitzOnWith := ?_, continuousOn := ?_, norm_le := ?_, mul_max_le := ?_ }
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro u hu v hv
      simpa only [dist_eq_norm] using hLip t (htime t ht) u (hballU u hu) v (hballU v hv)
    · intro u hu
      simpa only [Function.comp_apply] using
        hcont.comp (continuous_id.prodMk continuous_const) |>.continuousOn
    · intro t ht u hu
      rw [show (Mnn : ℝ) = M by rfl]
      have huLip : ‖F t u - F t z0‖ ≤ L * ‖u - z0‖ :=
        hLip t (htime t ht) u (hballU u hu) z0
          (hballU z0 (Metric.mem_closedBall_self ha.le))
      have htri : ‖F t z0‖ ≤ ‖F t z0 - F t0 z0‖ + ‖F t0 z0‖ := by
        calc
          ‖F t z0‖ = ‖(F t z0 - F t0 z0) + F t0 z0‖ := by rw [sub_add_cancel]
          _ ≤ ‖F t z0 - F t0 z0‖ + ‖F t0 z0‖ :=
            norm_add_le (F t z0 - F t0 z0) (F t0 z0)
      calc
        ‖F t u‖ ≤ ‖F t u - F t z0‖ + ‖F t z0‖ := norm_le_norm_sub_add _ _
        _ ≤ L * ‖u - z0‖ + (‖F t z0 - F t0 z0‖ + ‖F t0 z0‖) :=
          add_le_add huLip htri
        _ ≤ L * a + (1 + ‖F t0 z0‖) := by
          gcongr
          · simpa [dist_eq_norm_sub] using Metric.mem_closedBall.mp hu
          · exact (hFnear t ht).le
        _ = M := by dsimp [M]; ring
    · have htime' : M * max ((t0 + eta) - t0) (t0 - (t0 - eta)) ≤ a := by
        have hleft : (t0 + eta) - t0 = eta := by ring
        have hright : t0 - (t0 - eta) = eta := by ring
        have hmax : max ((t0 + eta) - t0) (t0 - (t0 - eta)) = eta := by
          rw [hleft, hright, max_self]
        rw [hmax]
        have hη : eta ≤ a / (2 * M) := min_le_right _ _
        calc M * eta ≤ M * (a / (2 * M)) := mul_le_mul_of_nonneg_left hη hM.le
             _ = a / 2 := by field_simp [ne_of_gt hM]
             _ ≤ a := by linarith
      simpa [Mnn, ann] using htime'
  obtain ⟨z, hz0, hz⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨eta, heta, z, hz0, fun t ht => ?_⟩
  exact (hz t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Two local classical solution germs through one point coincide. -/
private theorem ode_eq_eventually_of_uniform_locally_lipschitz
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hlip : IsUniformLocallyLipschitzInState_nonautonomous F) {t0 : ℝ}
    (u v : ℝ → H)
    (hu : ∀ᶠ t in nhds t0, HasDerivAt u (F t (u t)) t)
    (hv : ∀ᶠ t in nhds t0, HasDerivAt v (F t (v t)) t)
    (huv : u t0 = v t0) : u =ᶠ[nhds t0] v := by
  rcases hlip t0 (u t0) with ⟨I, htI, U, huU, L, hL, hLip⟩
  have hu0 : HasDerivAt u (F t0 (u t0)) t0 := hu.self_of_nhds
  have hv0 : HasDerivAt v (F t0 (v t0)) t0 := hv.self_of_nhds
  have hu_mem : ∀ᶠ t in nhds t0, u t ∈ U := hu0.continuousAt huU
  have hv_mem : ∀ᶠ t in nhds t0, v t ∈ U := by
    have : U ∈ nhds (v t0) := by simpa [huv] using huU
    exact hv0.continuousAt this
  let K : NNReal := ⟨L, hL⟩
  have hLipEv : ∀ᶠ t in nhds t0, LipschitzOnWith K (F t) U := by
    filter_upwards [htI] with t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    simpa only [dist_eq_norm] using hLip t ht y hy z hz
  apply ODE_solution_unique_of_eventually hLipEv
  · filter_upwards [hu, hu_mem] with t ht hmem
    exact ⟨ht, hmem⟩
  · filter_upwards [hv, hv_mem] with t ht hmem
    exact ⟨ht, hmem⟩
  · exact huv

/-- Local uniqueness propagates along an interval on which both curves solve
the non-autonomous equation. -/
private theorem ode_eqOn_Ioo_of_uniform_locally_lipschitz
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hlip : IsUniformLocallyLipschitzInState_nonautonomous F)
    {a b t0 : ℝ} (ht0 : t0 ∈ Set.Ioo a b) (u v : ℝ → H)
    (hu : ∀ t ∈ Set.Ioo a b, HasDerivAt u (F t (u t)) t)
    (hv : ∀ t ∈ Set.Ioo a b, HasDerivAt v (F t (v t)) t)
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
  let fu : Set.Icc A B → H := fun s => u s
  let fv : Set.Icc A B → H := fun s => v s
  have hfu : Continuous fu := huc.restrict
  have hfv : Continuous fv := hvc.restrict
  let E : Set (Set.Icc A B) := {s | fu s = fv s}
  have hEclosed : IsClosed E := by
    simpa [E] using isClosed_eq hfu hfv
  have hEopen : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hu' : ∀ᶠ r in nhds (s : ℝ), HasDerivAt u (F r (u r)) r := by
      filter_upwards [Ioo_mem_nhds (hIcc s.2).1 (hIcc s.2).2] with r hr
      exact hu r hr
    have hv' : ∀ᶠ r in nhds (s : ℝ), HasDerivAt v (F r (v r)) r := by
      filter_upwards [Ioo_mem_nhds (hIcc s.2).1 (hIcc s.2).2] with r hr
      exact hv r hr
    have heq : u =ᶠ[nhds (s : ℝ)] v :=
      ode_eq_eventually_of_uniform_locally_lipschitz F hlip u v hu' hv' hs
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
    hpre.subset_isClopen hE ⟨_, Set.mem_univ _, ht0E⟩
  have htE : (⟨t, Set.Ioo_subset_Icc_self htI⟩ : Set.Icc A B) ∈ E :=
    hall (Set.mem_univ _)
  simpa [E, fu, fv] using htE

private structure PointedSolution_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H → H) (t0 : ℝ) (z0 : H) where
  dom : Set ℝ
  curve : ℝ → H
  open_dom : IsOpen dom
  preconnected_dom : IsPreconnected dom
  t0_mem : t0 ∈ dom
  initial : curve t0 = z0
  ode : ∀ t ∈ dom, HasDerivAt curve (F t (curve t)) t

private instance pointedSolutionPreorder_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H → H) (t0 : ℝ) (z0 : H) : Preorder (PointedSolution_nonautonomous F t0 z0) where
  le p q := p.dom ⊆ q.dom ∧ Set.EqOn p.curve q.curve p.dom
  le_refl p := ⟨fun _ h => h, fun _ _ => rfl⟩
  le_trans p q r hpq hqr :=
    ⟨hpq.1.trans hqr.1, fun t ht => (hpq.2 ht).trans (hqr.2 (hpq.1 ht))⟩

private theorem open_preconnected_segment_thickening_nonautonomous {I : Set ℝ}
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

private theorem pointedSolution_eqOn_inter_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hlip : IsUniformLocallyLipschitzInState_nonautonomous F)
    (t0 : ℝ) (z0 : H) (p q : PointedSolution_nonautonomous F t0 z0) :
    Set.EqOn p.curve q.curve (p.dom ∩ q.dom) := by
  intro t ht
  obtain ⟨A, B, h0, htI, hsub⟩ := open_preconnected_segment_thickening_nonautonomous
    (p.open_dom.inter q.open_dom)
    (Set.OrdConnected.isPreconnected
      (p.preconnected_dom.ordConnected.inter q.preconnected_dom.ordConnected))
    ⟨p.t0_mem, q.t0_mem⟩ ht
  exact (ode_eqOn_Ioo_of_uniform_locally_lipschitz F hlip h0 p.curve q.curve
    (fun s hs => p.ode s (hsub hs).1)
    (fun s hs => q.ode s (hsub hs).2)
    (p.initial.trans q.initial.symm)) htI

private theorem pointedSolution_binary_upper_bound_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hlip : IsUniformLocallyLipschitzInState_nonautonomous F)
    (t0 : ℝ) (z0 : H) (p q : PointedSolution_nonautonomous F t0 z0) :
    ∃ r : PointedSolution_nonautonomous F t0 z0, p ≤ r ∧ q ≤ r := by
  classical
  let D : Set ℝ := p.dom ∪ q.dom
  let curve : ℝ → H := fun t => if t ∈ p.dom then p.curve t else q.curve t
  have hcurvep : ∀ t ∈ p.dom, curve t = p.curve t := by
    intro t ht
    simp [curve, ht]
  have hcurveq : ∀ t ∈ q.dom, curve t = q.curve t := by
    intro t ht
    by_cases htp : t ∈ p.dom
    · rw [show curve t = p.curve t by simp [curve, htp]]
      exact pointedSolution_eqOn_inter_nonautonomous F hlip t0 z0 p q ⟨htp, ht⟩
    · simp [curve, htp]
  refine ⟨{ dom := D
            curve := curve
            open_dom := p.open_dom.union q.open_dom
            preconnected_dom := IsPreconnected.union t0 p.t0_mem q.t0_mem
              p.preconnected_dom q.preconnected_dom
            t0_mem := Or.inl p.t0_mem
            initial := (hcurvep t0 p.t0_mem).trans p.initial
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

private theorem pointedSolution_nonempty_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hcont : Continuous fun p : ℝ × H => F p.1 p.2)
    (hlip : IsUniformLocallyLipschitzInState_nonautonomous F) (t0 : ℝ) (z0 : H) :
    Nonempty (PointedSolution_nonautonomous F t0 z0) := by
  obtain ⟨ε, hε, α, hα0, hα⟩ :=
    local_classical_solution_of_uniform_locally_lipschitz F hcont hlip t0 z0
  let p : PointedSolution_nonautonomous F t0 z0 :=
    { dom := Set.Ioo (t0 - ε) (t0 + ε)
      curve := α
      open_dom := isOpen_Ioo
      preconnected_dom := isPreconnected_Ioo
      t0_mem := by constructor <;> linarith
      initial := hα0
      ode := fun t ht => hα t ht }
  exact ⟨p⟩

private theorem pointedSolution_chain_upper_bound_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hcont : Continuous fun p : ℝ × H => F p.1 p.2)
    (hlip : IsUniformLocallyLipschitzInState_nonautonomous F) (t0 : ℝ) (z0 : H) :
    ∀ C : Set (PointedSolution_nonautonomous F t0 z0), IsChain (· ≤ ·) C → BddAbove C := by
  classical
  intro C hC
  by_cases hCempty : C.Nonempty
  · let D : Set ℝ := ⋃₀ (PointedSolution_nonautonomous.dom '' C)
    have howner : ∀ t, t ∈ D → ∃ p : PointedSolution_nonautonomous F t0 z0, p ∈ C ∧ t ∈ p.dom := by
      intro t ht
      rcases Set.mem_sUnion.mp ht with ⟨d, hd, htd⟩
      rcases hd with ⟨p, hp, rfl⟩
      exact ⟨p, hp, htd⟩
    let owner : ∀ t, t ∈ D → PointedSolution_nonautonomous F t0 z0 :=
      fun t ht => Classical.choose (howner t ht)
    have owner_mem (t : ℝ) (ht : t ∈ D) : owner t ht ∈ C :=
      (Classical.choose_spec (howner t ht)).1
    have owner_dom (t : ℝ) (ht : t ∈ D) : t ∈ (owner t ht).dom :=
      (Classical.choose_spec (howner t ht)).2
    let curve : ℝ → H := fun t => if ht : t ∈ D then (owner t ht).curve t else z0
    have hopen : IsOpen D := by
      dsimp [D]
      apply isOpen_sUnion
      intro d hd
      rcases hd with ⟨p, hp, rfl⟩
      exact p.open_dom
    have hconn : IsPreconnected D := by
      apply isPreconnected_sUnion t0 (PointedSolution_nonautonomous.dom '' C)
      · intro d hd
        rcases hd with ⟨p, hp, rfl⟩
        exact p.t0_mem
      · intro d hd
        rcases hd with ⟨p, hp, rfl⟩
        exact p.preconnected_dom
    have ht0 : t0 ∈ D := by
      rcases hCempty with ⟨p, hp⟩
      exact Set.mem_sUnion.mpr ⟨p.dom, ⟨p, hp, rfl⟩, p.t0_mem⟩
    let upper : PointedSolution_nonautonomous F t0 z0 :=
      { dom := D
        curve := curve
        open_dom := hopen
        preconnected_dom := hconn
        t0_mem := ht0
        initial := by
          rw [show curve t0 = (owner t0 ht0).curve t0 by simp [curve, ht0]]
          exact (owner t0 ht0).initial
        ode := by
          intro t ht
          have hcurve : curve t = (owner t ht).curve t := by simp [curve, ht]
          rw [hcurve]
          have hder := (owner t ht).ode t (owner_dom t ht)
          apply hder.congr_of_eventuallyEq
          filter_upwards [(owner t ht).open_dom.mem_nhds (owner_dom t ht)] with s hs
          have hsD : s ∈ D := Set.mem_sUnion.mpr
            ⟨(owner t ht).dom, ⟨owner t ht, owner_mem t ht, rfl⟩, hs⟩
          have heq := pointedSolution_eqOn_inter_nonautonomous F hlip t0 z0 (owner s hsD) (owner t ht)
            ⟨owner_dom s hsD, hs⟩
          simpa [curve, hsD] using heq }
    refine ⟨upper, ?_⟩
    intro p hp
    refine ⟨?_, ?_⟩
    · intro t ht
      exact Set.mem_sUnion.mpr ⟨p.dom, ⟨p, hp, rfl⟩, ht⟩
    · intro t ht
      have htD : t ∈ D := Set.mem_sUnion.mpr ⟨p.dom, ⟨p, hp, rfl⟩, ht⟩
      have heq := pointedSolution_eqOn_inter_nonautonomous F hlip t0 z0 p (owner t htD)
        ⟨ht, owner_dom t htD⟩
      have hcurve : curve t = (owner t htD).curve t := by simp [curve, htD]
      exact heq.trans hcurve.symm
  · obtain ⟨p⟩ := pointedSolution_nonempty_nonautonomous F hcont hlip t0 z0
    refine ⟨p, ?_⟩
    intro q hq
    exact (hCempty ⟨q, hq⟩).elim

private theorem forward_endpoint_of_open_preconnected_nonautonomous {D : Set ℝ} {t0 : ℝ}
    (hopen : IsOpen D) (hconn : IsPreconnected D) (ht0 : t0 ∈ D) :
    ∃ Tmax : WithTop ℝ, t0 < Tmax ∧
      D ∩ Set.Ici t0 = {t : ℝ | t0 ≤ t ∧ (t : WithTop ℝ) < Tmax} := by
  let S : Set ℝ := D ∩ Set.Ici t0
  have hSt0 : t0 ∈ S := ⟨ht0, by simp⟩
  have hbetween {t u : ℝ} (ht : t0 ≤ t) (hu : u ∈ S) (htu : t ≤ u) : t ∈ D := by
    exact hconn.ordConnected.out ht0 hu.1 ⟨ht, htu⟩
  by_cases hbounded : BddAbove S
  · obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds ht0)
    have hδ2 : t0 + δ / 2 ∈ S := by
      constructor
      · apply hδsub
        rw [Metric.mem_ball, Real.dist_eq]
        have : |(t0 + δ / 2) - t0| < δ := by
          rw [show (t0 + δ / 2) - t0 = δ / 2 by ring, abs_of_pos (by linarith)]
          linarith
        exact this
      · change t0 ≤ t0 + δ / 2
        linarith
    have hpos : t0 < sSup S := lt_csSup_of_lt hbounded hδ2 (by linarith)
    refine ⟨(sSup S : ℝ), by simpa using hpos, ?_⟩
    ext t
    constructor
    · intro ht
      rcases Metric.mem_nhds_iff.1 (hopen.mem_nhds ht.1) with ⟨δ, hδ, hδsub⟩
      have hu : t + δ / 2 ∈ S := by
        constructor
        · apply hδsub
          rw [Metric.mem_ball, Real.dist_eq]
          have : |(t + δ / 2) - t| < δ := by
            rw [show (t + δ / 2) - t = δ / 2 by ring, abs_of_pos (by linarith)]
            linarith
          exact this
        · change t0 ≤ t + δ / 2
          have ht0le : t0 ≤ t := ht.2
          linarith
      have hlt : t < sSup S := lt_csSup_of_lt hbounded hu (by linarith)
      exact ⟨ht.2, by simpa using hlt⟩
    · rintro ⟨ht0le, ht⟩
      have ht' : t < sSup S := by simpa using ht
      obtain ⟨u, hu, htu⟩ := exists_lt_of_lt_csSup ⟨t0, hSt0⟩ ht'
      exact ⟨hbetween ht0le hu htu.le, ht0le⟩
  · refine ⟨⊤, by simp, ?_⟩
    ext t
    constructor
    · intro ht
      exact ⟨ht.2, by simp⟩
    · rintro ⟨ht0le, ht⟩
      have hexists : ∃ u ∈ S, t < u := by
        by_contra h
        push Not at h
        apply hbounded
        exact ⟨t, h⟩
      rcases hexists with ⟨u, hu, htu⟩
      exact ⟨hbetween ht0le hu htu.le, ht0le⟩

/-- Adjoin a local classical germ to a pointed solution on a nonempty overlap. -/
private theorem pointedSolution_extend_of_eqOn_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H → H) (t0 : ℝ) (z0 : H) (p : PointedSolution_nonautonomous F t0 z0)
    {a b : ℝ} (_hab : a < b) (alpha : ℝ → H)
    (halpha : ∀ t ∈ Set.Ioo a b, HasDerivAt alpha (F t (alpha t)) t)
    (heq : Set.EqOn p.curve alpha (p.dom ∩ Set.Ioo a b))
    (hoverlap : (p.dom ∩ Set.Ioo a b).Nonempty) :
    ∃ q : PointedSolution_nonautonomous F t0 z0, p ≤ q ∧ Set.EqOn q.curve alpha (Set.Ioo a b) ∧
      Set.Ioo a b ⊆ q.dom := by
  classical
  let D : Set ℝ := p.dom ∪ Set.Ioo a b
  let curve : ℝ → H := fun t => if t ∈ p.dom then p.curve t else alpha t
  have hcurvep : ∀ t ∈ p.dom, curve t = p.curve t := by
    intro t ht
    simp [curve, ht]
  have hcurvealpha : ∀ t ∈ Set.Ioo a b, curve t = alpha t := by
    intro t ht
    by_cases htp : t ∈ p.dom
    · rw [show curve t = p.curve t by simp [curve, htp]]
      exact heq ⟨htp, ht⟩
    · simp [curve, htp]
  rcases hoverlap with ⟨c, hcdom, hcIoo⟩
  refine ⟨{ dom := D
            curve := curve
            open_dom := p.open_dom.union isOpen_Ioo
            preconnected_dom := IsPreconnected.union c hcdom hcIoo
              p.preconnected_dom isPreconnected_Ioo
            t0_mem := Or.inl p.t0_mem
            initial := (hcurvep t0 p.t0_mem).trans p.initial
            ode := ?_ }, ?_, ?_, Set.subset_union_right⟩
  · intro t ht
    rcases ht with htp | hta
    · have hevent : curve =ᶠ[nhds t] p.curve := by
        filter_upwards [p.open_dom.mem_nhds htp] with s hs
        exact hcurvep s hs
      have hval : curve t = p.curve t := hcurvep t htp
      simpa [hval] using (p.ode t htp).congr_of_eventuallyEq hevent
    · have hevent : curve =ᶠ[nhds t] alpha := by
        filter_upwards [isOpen_Ioo.mem_nhds hta] with s hs
        exact hcurvealpha s hs
      have hval : curve t = alpha t := hcurvealpha t hta
      simpa [hval] using (halpha t hta).congr_of_eventuallyEq hevent
  · refine ⟨Set.subset_union_left, ?_⟩
    intro t ht
    exact (hcurvep t ht).symm
  · intro t ht
    exact hcurvealpha t ht

/-- Filling a finite left endpoint by its limiting value preserves continuity. -/
private theorem continuousOn_fill_left_endpoint_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a T : ℝ} (_haT : a < T) (u : ℝ → H) (l : H)
    (hulim : Filter.Tendsto u (nhdsWithin T (Set.Iio T)) (nhds l))
    (hcont : ∀ s ∈ Set.Icc a T, s < T → ContinuousAt u s) :
    ContinuousOn (fun s => if s = T then l else u s) (Set.Icc a T) := by
  intro s hs
  by_cases hsT : s = T
  · subst s
    have hconst : Filter.Tendsto (fun _ : ℝ => l)
        (nhdsWithin T (Set.Icc a T ∩ {x : ℝ | x = T})) (nhds l) :=
      tendsto_const_nhds.mono_left nhdsWithin_le_nhds
    have hu : Filter.Tendsto u
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

private theorem ode_eqOn_left_of_tendsto_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hcont : Continuous fun p : ℝ × H => F p.1 p.2)
    (hlip : IsUniformLocallyLipschitzInState_nonautonomous F) {T eps : ℝ} (heps : 0 < eps)
    {u v : ℝ → H} {l : H}
    (hu : ∀ s ∈ Set.Ioo (T - eps) T, HasDerivAt u (F s (u s)) s)
    (hv : ∀ s ∈ Set.Ioo (T - eps) (T + eps), HasDerivAt v (F s (v s)) s)
    (hulim : Filter.Tendsto u (nhdsWithin T (Set.Iio T)) (nhds l))
    (hvT : v T = l) :
    ∃ rho, 0 < rho ∧ rho < eps ∧ Set.EqOn u v (Set.Ioo (T - rho) T) := by
  rcases hlip T l with ⟨I, hTI, U, hlU, L, hL, hLip⟩
  let K : NNReal := ⟨L, hL⟩
  have hLipOn : ∀ s ∈ I, LipschitzOnWith K (F s) U := by
    intro s hs
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_eq_norm] using hLip s hs x hx y hy
  rcases Metric.mem_nhds_iff.mp hlU with ⟨r, hr, hrU⟩
  rcases Metric.mem_nhds_iff.mp hTI with ⟨d, hd, hdI⟩
  have huU : ∀ᶠ s in nhdsWithin T (Set.Iio T), u s ∈ Metric.ball l r :=
    hulim.eventually (Metric.ball_mem_nhds l hr)
  change {s | u s ∈ Metric.ball l r} ∈ nhdsWithin T (Set.Iio T) at huU
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at huU
  rcases huU with ⟨V, hV, hVsub⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨du, hdu, hduV⟩
  have hu_mem (s : ℝ) (hs : T - du < s) (hsT : s < T) : u s ∈ U := by
    apply hrU
    apply hVsub
    constructor
    · apply hduV
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    · exact hsT
  have hvcont : ContinuousAt v T :=
    (hv T ⟨by linarith, by linarith⟩).continuousAt
  have hvU : ∀ᶠ s in nhds T, v s ∈ Metric.ball l r := by
    rw [← hvT]
    exact hvcont.eventually (Metric.ball_mem_nhds _ hr)
  rcases Metric.mem_nhds_iff.mp hvU with ⟨dv, hdv, hdvsub⟩
  have hv_mem (s : ℝ) (hs : |s - T| < dv) : v s ∈ U :=
    hrU (hdvsub (by simpa [Metric.mem_ball, Real.dist_eq] using hs))
  let rho : ℝ := min (eps / 2) (min (d / 2) (min (du / 2) (dv / 2)))
  have hrho : 0 < rho := by
    dsimp [rho]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hrhoe : rho < eps := by have h := min_le_left (eps / 2) (min (d / 2) (min (du / 2) (dv / 2))); linarith
  have hrhod : rho < d := by
    have h : rho ≤ d / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hrhou : rho < du := by
    have h : rho ≤ du / 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith
  have hrhov : rho < dv := by
    have h : rho ≤ dv / 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith
  let uT : ℝ → H := fun s => if s = T then l else u s
  have huTcont : ContinuousOn uT (Set.Icc (T - rho) T) := by
    apply continuousOn_fill_left_endpoint_nonautonomous (by linarith [hrho]) u l hulim
    intro s hs hsT
    exact (hu s ⟨by linarith [hs.1, hrhoe], hsT⟩).continuousAt
  have hvcont' : ContinuousOn v (Set.Icc (T - rho) T) := by
    apply HasDerivAt.continuousOn
    intro s hs
    exact hv s ⟨by linarith [hrhoe, hs.1], by linarith [hs.2]⟩
  have htime (s : ℝ) (hs : s ∈ Set.Icc (T-rho) T) : s ∈ I := by
    apply hdI
    rw [Metric.mem_ball, Real.dist_eq]
    have : |s - T| ≤ rho := by rw [abs_of_nonpos (by linarith [hs.2])]; linarith [hs.1]
    exact lt_of_le_of_lt this hrhod
  have huTder : ∀ s ∈ Set.Ioc (T-rho) T,
      HasDerivWithinAt uT (F s (uT s)) (Set.Iic s) s := by
    intro s hs
    rcases hs with ⟨hslo, hsle⟩
    by_cases hsT : s = T
    · subst s
      have hdiff : DifferentiableOn ℝ uT (Set.Ioo (T-rho) T) := by
        intro x hx
        have heq : uT =ᶠ[nhds x] u := by
          filter_upwards [Iio_mem_nhds hx.2] with y hy
          change y < T at hy
          simp [uT, ne_of_lt hy]
        exact ((hu x ⟨by linarith [hx.1, hrhoe], hx.2⟩).congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
      have hlim : ContinuousWithinAt uT (Set.Ioo (T-rho) T) T :=
        (huTcont T ⟨by linarith [hrho], le_rfl⟩).mono Set.Ioo_subset_Icc_self
      have hderiv_eq : (fun x => deriv uT x) =ᶠ[nhdsWithin T (Set.Iio T)]
          fun x => F x (u x) := by
        filter_upwards [Ioo_mem_nhdsLT (a := T-rho) (b := T) (by linarith [hrho])] with x hx
        have heq : uT =ᶠ[nhds x] u := by
          filter_upwards [Iio_mem_nhds hx.2] with y hy
          change y < T at hy
          simp [uT, ne_of_lt hy]
        rw [heq.deriv_eq]
        exact (hu x ⟨by linarith [hx.1, hrhoe], hx.2⟩).deriv
      have hFlim : Filter.Tendsto (fun x => F x (u x))
          (nhdsWithin T (Set.Iio T)) (nhds (F T l)) := by
        have hid : Filter.Tendsto (fun x : ℝ => x)
            (nhdsWithin T (Set.Iio T)) (nhds T) :=
          tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id
        exact (hcont.tendsto (T, l)).comp (hid.prodMk_nhds hulim)
      have hderiv_lim : Filter.Tendsto (fun x => deriv uT x)
          (nhdsWithin T (Set.Iio T)) (nhds (F T l)) :=
        hFlim.congr' hderiv_eq.symm
      simpa [uT] using hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hlim
        (Ioo_mem_nhdsLT (a := T-rho) (b := T) (by linarith [hrho])) hderiv_lim
    · have hslt : s < T := lt_of_le_of_ne hsle hsT
      have heq : uT =ᶠ[nhds s] u := by
        filter_upwards [Iio_mem_nhds hslt] with x hx
        change x < T at hx
        simp [uT, ne_of_lt hx]
      simpa [uT, ne_of_lt hslt] using
        ((hu s ⟨by linarith [hslo, hrhoe], hslt⟩).congr_of_eventuallyEq heq).hasDerivWithinAt
  have hvder : ∀ s ∈ Set.Ioc (T-rho) T,
      HasDerivWithinAt v (F s (v s)) (Set.Iic s) s := by
    intro s hs
    exact (hv s ⟨by linarith [hrhoe, hs.1], by linarith [hs.2]⟩).hasDerivWithinAt
  have huTrange : ∀ s ∈ Set.Ioc (T-rho) T, uT s ∈ U := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hsT | rfl
    · rw [show uT s = u s by simp [uT, ne_of_lt hsT]]
      exact hu_mem s (by linarith [hs.1, hrhou]) hsT
    · simp [uT, mem_of_mem_nhds hlU]
  have hvrange : ∀ s ∈ Set.Ioc (T-rho) T, v s ∈ U := by
    intro s hs
    apply hv_mem s
    rw [abs_of_nonpos (by linarith [hs.2])]
    linarith [hs.1, hrhov]
  have heq := ODE_solution_unique_of_mem_Icc_left
    (fun s hs => hLipOn s (htime s ⟨hs.1.le, hs.2⟩))
    huTcont huTder huTrange hvcont' hvder hvrange (by simp [uT, hvT])
  refine ⟨rho, hrho, hrhoe, ?_⟩
  intro s hs
  have h := heq ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  simpa [uT, ne_of_lt hs.2] using h
/-- Forward maximal classical solution of `z' = F(t,z)` starting at time `t0`
from `z0`, with maximal existence time `Tmax`.  Non-autonomous generalization
of `IsMaximalClassicalSolution`. -/
def IsMaximalClassicalSolution_nonautonomous {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H → H) (t0 : ℝ) (z0 : H) (Tmax : WithTop ℝ) (z : ℝ → H) : Prop :=
  t0 < Tmax ∧ z t0 = z0 ∧
    (∀ t, t0 ≤ t → (t : WithTop ℝ) < Tmax → HasDerivAt z (F t (z t)) t) ∧
    ∀ (I : Set ℝ) (w : ℝ → H), Set.OrdConnected I → t0 ∈ I →
      (∀ t ∈ I, HasDerivAt w (F t (w t)) t) →
      {t : ℝ | t0 ≤ t ∧ (t : WithTop ℝ) < Tmax} ⊆ I →
      (∀ t, t0 ≤ t → (t : WithTop ℝ) < Tmax → z t = w t) →
      I ∩ Set.Ici t0 ⊆ {t : ℝ | t0 ≤ t ∧ (t : WithTop ℝ) < Tmax}

private theorem pointedSolution_forward_maximal_of_ordConnected_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hcont : Continuous fun p : ℝ × H => F p.1 p.2)
    (hlip : IsUniformLocallyLipschitzInState_nonautonomous F) (t0 : ℝ) (z0 : H)
    (p : PointedSolution_nonautonomous F t0 z0)
    (hpmax : ∀ q : PointedSolution_nonautonomous F t0 z0, p ≤ q → q ≤ p)
    {T : ℝ} (hT : t0 < T)
    (hforward : p.dom ∩ Set.Ici t0 = {t : ℝ | t0 ≤ t ∧ t < T})
    (I : Set ℝ) (Z : ℝ → H) (hIconn : Set.OrdConnected I) (_hIt0 : t0 ∈ I)
    (hZ : ∀ t ∈ I, HasDerivAt Z (F t (Z t)) t)
    (hsub : {t : ℝ | t0 ≤ t ∧ t < T} ⊆ I)
    (heq : ∀ t : ℝ, t0 ≤ t → t < T → p.curve t = Z t) :
    I ∩ Set.Ici t0 ⊆ {t : ℝ | t0 ≤ t ∧ t < T} := by
  rintro t ⟨htI, ht0⟩
  refine ⟨ht0, ?_⟩
  by_contra hlt
  have hTt : T ≤ t := le_of_not_gt hlt
  let m : ℝ := (t0 + T) / 2
  have hmI : m ∈ I := hsub ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hTI : T ∈ I := hIconn.out hmI htI ⟨by dsimp [m]; linarith, hTt⟩
  let l : H := Z T
  have hZT : HasDerivAt Z (F T (Z T)) T := hZ T hTI
  have hZlim : Filter.Tendsto Z (nhdsWithin T (Set.Iio T)) (nhds l) := by
    simpa [l] using hZT.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hevent : p.curve =ᶠ[nhdsWithin T (Set.Iio T)] Z := by
    filter_upwards [Ioo_mem_nhdsLT (a := m) (b := T) (by dsimp [m]; linarith)] with r hr
    have hmt0 : t0 < m := by dsimp [m]; linarith
    have hrt0 : t0 < r := lt_trans hmt0 hr.1
    exact heq r hrt0.le hr.2
  have hplim : Filter.Tendsto p.curve (nhdsWithin T (Set.Iio T)) (nhds l) :=
    Filter.Tendsto.congr' hevent.symm hZlim
  obtain ⟨eps, heps, alpha, halphaT, halpha⟩ :=
    local_classical_solution_of_uniform_locally_lipschitz F hcont hlip T l
  let eps0 : ℝ := min eps ((T - t0) / 2)
  have heps0 : 0 < eps0 := by dsimp [eps0]; exact lt_min heps (by linarith)
  have heps0eps : eps0 ≤ eps := min_le_left _ _
  have heps0T : eps0 ≤ (T - t0) / 2 := min_le_right _ _
  have halpha0 : ∀ r ∈ Set.Ioo (T - eps0) (T + eps0),
      HasDerivAt alpha (F r (alpha r)) r := by
    intro r hr
    apply halpha r
    constructor
    · exact lt_of_le_of_lt (sub_le_sub_left heps0eps T) hr.1
    · linarith [heps0eps, hr.2]
  have hpode : ∀ r ∈ Set.Ioo (T - eps0) T,
      HasDerivAt p.curve (F r (p.curve r)) r := by
    intro r hr
    apply p.ode r
    have hmid : t0 ≤ T - eps0 := by
      calc
        t0 ≤ T - (T - t0) / 2 := by linarith
        _ ≤ T - eps0 := sub_le_sub_left heps0T T
    have hrf : r ∈ {t : ℝ | t0 ≤ t ∧ t < T} := ⟨le_trans hmid hr.1.le, hr.2⟩
    rw [← hforward] at hrf
    exact hrf.1
  obtain ⟨rho, hrho, hrhoe, hleft⟩ :=
    ode_eqOn_left_of_tendsto_nonautonomous F hcont hlip heps0 hpode halpha0 hplim halphaT
  have hEq : Set.EqOn p.curve alpha (p.dom ∩ Set.Ioo (T - rho) (T + eps0)) := by
    rintro r ⟨hrdom, hr⟩
    have hrT : r < T := by
      by_contra h
      have hTr : T ≤ r := le_of_not_gt h
      have hrt0 : t0 ≤ r := by linarith
      have hrf : r ∈ p.dom ∩ Set.Ici t0 := ⟨hrdom, hrt0⟩
      have : r < T := (hforward ▸ hrf).2
      linarith
    exact hleft ⟨hr.1, hrT⟩
  have hcdom : T - rho / 2 ∈ p.dom := by
    have hcf : T - rho / 2 ∈ {t : ℝ | t0 ≤ t ∧ t < T} := ⟨by linarith, by linarith⟩
    rw [← hforward] at hcf
    exact hcf.1
  have hcIoo : T - rho / 2 ∈ Set.Ioo (T - rho) (T + eps0) := by constructor <;> linarith
  obtain ⟨q, hpq, halphaq, hsubq⟩ := pointedSolution_extend_of_eqOn_nonautonomous F t0 z0 p
    (a := T - rho) (b := T + eps0) (by linarith) alpha
    (fun r hr => halpha0 r
      ⟨by linarith [hrhoe, hr.1], by linarith [heps0eps, hr.2]⟩) hEq
      ⟨T - rho / 2, hcdom, hcIoo⟩
  have hrq : T + rho / 2 ∈ q.dom := hsubq (by constructor <;> linarith [hrhoe])
  have hrp : T + rho / 2 ∈ p.dom := (hpmax q hpq).1 hrq
  have hrf : T + rho / 2 ∈ p.dom ∩ Set.Ici t0 :=
    ⟨hrp, le_trans hT.le (by linarith [hrho])⟩
  have : T + rho / 2 < T := (hforward ▸ hrf).2
  linarith [hrho]

/- Classical forward representatives with the same datum agree wherever both
are defined.  The short initial interval is kept inside one time/state
Lipschitz rectangle before the interval uniqueness bridge propagates it. -/
private theorem classicalSolution_eq_of_below_both_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (hlip : IsUniformLocallyLipschitzInState_nonautonomous F) (t0 : ℝ) (z0 : H)
    {T1 T2 : WithTop ℝ} {z1 z2 : ℝ → H} (hz1_0 : z1 t0 = z0) (hz2_0 : z2 t0 = z0)
    (h1 : ∀ r, t0 ≤ r → (r : WithTop ℝ) < T1 → HasDerivAt z1 (F r (z1 r)) r)
    (h2 : ∀ r, t0 ≤ r → (r : WithTop ℝ) < T2 → HasDerivAt z2 (F r (z2 r)) r) :
    ∀ t, t0 ≤ t → (t : WithTop ℝ) < T1 → (t : WithTop ℝ) < T2 → z1 t = z2 t := by
  intro t ht0 ht1 ht2
  by_cases ht : t = t0
  · subst t
    exact hz1_0.trans hz2_0.symm
  have htpos : t0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  obtain ⟨B, htB, hB1, hB2⟩ : ∃ B : ℝ, t < B ∧
      (∀ r ∈ Set.Ioo t0 B, t0 ≤ r ∧ (r : WithTop ℝ) < T1) ∧
      (∀ r ∈ Set.Ioo t0 B, t0 ≤ r ∧ (r : WithTop ℝ) < T2) := by
    induction T1 using WithTop.recTopCoe with
    | top =>
      induction T2 using WithTop.recTopCoe with
      | top =>
        refine ⟨t + 1, by linarith, ?_, ?_⟩ <;> intro r hr
        · exact ⟨hr.1.le, by simp⟩
        · exact ⟨hr.1.le, by simp⟩
      | coe C =>
        have htC : t < C := by simpa using ht2
        refine ⟨(t + C) / 2, by linarith, ?_, ?_⟩
        · intro r hr
          exact ⟨hr.1.le, by simp⟩
        · intro r hr
          refine ⟨hr.1.le, ?_⟩
          exact_mod_cast (show r < C by linarith [hr.2])
    | coe A =>
      induction T2 using WithTop.recTopCoe with
      | top =>
        have htA : t < A := by simpa using ht1
        refine ⟨(t + A) / 2, by linarith, ?_, ?_⟩
        · intro r hr
          refine ⟨hr.1.le, ?_⟩
          exact_mod_cast (show r < A by linarith [hr.2])
        · intro r hr
          exact ⟨hr.1.le, by simp⟩
      | coe C =>
        have htA : t < A := by simpa using ht1
        have htC : t < C := by simpa using ht2
        let B := t + min (A - t) (C - t) / 2
        have hBA : B < A := by
          dsimp [B]
          have h := min_le_left (A - t) (C - t)
          linarith
        have hBC : B < C := by
          dsimp [B]
          have h := min_le_right (A - t) (C - t)
          linarith
        have hd : 0 < min (A - t) (C - t) / 2 := by
          exact div_pos (lt_min (sub_pos.mpr htA) (sub_pos.mpr htC)) (by norm_num)
        refine ⟨B, by dsimp [B]; linarith, ?_, ?_⟩
        · intro r hr
          exact ⟨hr.1.le, by exact_mod_cast lt_trans hr.2 hBA⟩
        · intro r hr
          exact ⟨hr.1.le, by exact_mod_cast lt_trans hr.2 hBC⟩
  rcases hlip t0 z0 with ⟨I, hI, U, hU, L, hL, hLip⟩
  let K : NNReal := ⟨L, hL⟩
  have hLipOn : ∀ s ∈ I, LipschitzOnWith K (F s) U := by
    intro s hs
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_eq_norm] using hLip s hs x hx y hy
  have hz1cont : ContinuousAt z1 t0 :=
    (h1 t0 le_rfl (lt_of_le_of_lt (by exact_mod_cast ht0) ht1)).continuousAt
  have hz2cont : ContinuousAt z2 t0 :=
    (h2 t0 le_rfl (lt_of_le_of_lt (by exact_mod_cast ht0) ht2)).continuousAt
  have hU1 : U ∈ nhds (z1 t0) := by simpa [hz1_0] using hU
  have hU2 : U ∈ nhds (z2 t0) := by simpa [hz1_0, hz2_0] using hU
  rcases Metric.mem_nhds_iff.mp (hz1cont hU1) with ⟨d1, hd1, hd1U⟩
  rcases Metric.mem_nhds_iff.mp (hz2cont hU2) with ⟨d2, hd2, hd2U⟩
  rcases Metric.mem_nhds_iff.mp hI with ⟨dt, hdt, hdtI⟩
  let delta : ℝ := min ((B - t0) / 2) (min (dt / 2) (min (d1 / 2) (d2 / 2)))
  have hBpos : 0 < B - t0 := by linarith
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hdeltaB : delta < B - t0 := by
    have h := min_le_left ((B - t0) / 2) (min (dt / 2) (min (d1 / 2) (d2 / 2)))
    linarith
  have hdeltat : delta < dt := by
    have h : delta ≤ dt / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hd1' : delta < d1 := by
    have h : delta ≤ d1 / 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith
  have hd2' : delta < d2 := by
    have h : delta ≤ d2 / 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith
  have hder1 (r : ℝ) (hr : r ∈ Set.Icc t0 (t0 + delta)) :
      HasDerivAt z1 (F r (z1 r)) r := by
    rcases eq_or_lt_of_le hr.1 with rfl | hr0
    · exact h1 t0 le_rfl (lt_of_le_of_lt (by exact_mod_cast ht0) ht1)
    · exact h1 r hr.1 (hB1 r ⟨hr0, by linarith [hr.2, hdeltaB]⟩).2
  have hder2 (r : ℝ) (hr : r ∈ Set.Icc t0 (t0 + delta)) :
      HasDerivAt z2 (F r (z2 r)) r := by
    rcases eq_or_lt_of_le hr.1 with rfl | hr0
    · exact h2 t0 le_rfl (lt_of_le_of_lt (by exact_mod_cast ht0) ht2)
    · exact h2 r hr.1 (hB2 r ⟨hr0, by linarith [hr.2, hdeltaB]⟩).2
  have htime (r : ℝ) (hr : r ∈ Set.Icc t0 (t0 + delta)) : r ∈ I := by
    apply hdtI
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hr.1])]
    linarith [hr.2, hdeltat]
  have hz1U (r : ℝ) (hr : r ∈ Set.Ico t0 (t0 + delta)) : z1 r ∈ U := by
    apply hd1U
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hr.1])]
    linarith [hr.2, hd1']
  have hz2U (r : ℝ) (hr : r ∈ Set.Ico t0 (t0 + delta)) : z2 r ∈ U := by
    apply hd2U
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hr.1])]
    linarith [hr.2, hd2']
  have heq := ODE_solution_unique_of_mem_Icc_right
    (fun r hr => hLipOn r (htime r ⟨hr.1, hr.2.le⟩))
    (HasDerivAt.continuousOn hder1)
    (fun r hr => (hder1 r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt) hz1U
    (HasDerivAt.continuousOn hder2)
    (fun r hr => (hder2 r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt) hz2U
    (hz1_0.trans hz2_0.symm)
  have hseed : z1 (t0 + delta / 2) = z2 (t0 + delta / 2) :=
    heq ⟨by linarith, by linarith⟩
  have hprop := ode_eqOn_Ioo_of_uniform_locally_lipschitz F hlip
    (show t0 + delta / 2 ∈ Set.Ioo t0 B by constructor <;> linarith [hdelta, hdeltaB]) z1 z2
    (fun r hr => h1 r hr.1.le (hB1 r hr).2)
    (fun r hr => h2 r hr.1.le (hB2 r hr).2) hseed
  exact hprop ⟨htpos, htB⟩

private theorem withTop_le_of_forward_subset_nonautonomous {t0 : ℝ} {A B : WithTop ℝ} (hA : t0 < A)
    (hsub : ∀ t : ℝ, t0 ≤ t → (t : WithTop ℝ) < A → (t : WithTop ℝ) < B) : A ≤ B := by
  induction A using WithTop.recTopCoe with
  | top =>
      induction B using WithTop.recTopCoe with
      | top => simp
      | coe b =>
          exfalso
          let r : ℝ := max t0 (b + 1)
          have hrt0 : t0 ≤ r := le_max_left _ _
          have hbr : b < r := by dsimp [r]; linarith [le_max_right t0 (b + 1)]
          have h := hsub r hrt0 (by simp)
          have : r < b := by simpa using h
          linarith
  | coe a =>
      induction B using WithTop.recTopCoe with
      | top => simp
      | coe b =>
          have hta : t0 < a := by simpa using hA
          simp only [WithTop.coe_le_coe]
          by_contra hab
          have hba : b < a := lt_of_not_ge hab
          let c : ℝ := max t0 b
          have hca : c < a := by dsimp [c]; exact max_lt hta hba
          let m : ℝ := (a + c) / 2
          have hmt0 : t0 ≤ m := by dsimp [m]; linarith [le_max_left t0 b]
          have hma : m < a := by dsimp [m]; linarith
          have hbm : b < m := by dsimp [m]; linarith [le_max_right t0 b]
          have h := hsub m hmt0 (by simpa using hma)
          have : m < b := by simpa using h
          linarith

/-- A locally Lipschitz ODE has a unique maximal solution; bounded finite-endpoint
solutions extend.  Non-autonomous generalization of
`cauchy_lipschitz_continuation`. -/
theorem locallyLipschitz_ode_continuation_nonautonomous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H → H) (t0 : ℝ) (z0 : H)
    (hcont : Continuous fun p : ℝ × H => F p.1 p.2)
    (hlip : IsUniformLocallyLipschitzInState_nonautonomous F) :
    ∃ Tmax : WithTop ℝ, ∃ z : ℝ → H,
      IsMaximalClassicalSolution_nonautonomous F t0 z0 Tmax z ∧
        (∀ Tmax' z', IsMaximalClassicalSolution_nonautonomous F t0 z0 Tmax' z' →
          Tmax' = Tmax ∧ ∀ t, t0 ≤ t → (t : WithTop ℝ) < Tmax → z' t = z t) ∧
        (∀ T : ℝ, Tmax = (T : WithTop ℝ) → ∀ l : H,
          Filter.Tendsto z (nhdsWithin T {t : ℝ | t0 ≤ t ∧ (t : WithTop ℝ) < Tmax}) (nhds l) →
          ∃ S : ℝ, T < S ∧ ∃ w : ℝ → H,
            (∀ t, t0 ≤ t → t < S → HasDerivAt w (F t (w t)) t) ∧
            ∀ t, t0 ≤ t → t < T → w t = z t) := by
  classical
  obtain ⟨p, hpmax⟩ := zorn_le (pointedSolution_chain_upper_bound_nonautonomous F hcont hlip t0 z0)
  obtain ⟨Tmax, hTmax_pos, hforward⟩ :=
    forward_endpoint_of_open_preconnected_nonautonomous p.open_dom p.preconnected_dom p.t0_mem
  let D : Set ℝ := {t : ℝ | t0 ≤ t ∧ (t : WithTop ℝ) < Tmax}
  have hD : D = p.dom ∩ Set.Ici t0 := hforward.symm
  have hmaxp : IsMaximalClassicalSolution_nonautonomous F t0 z0 Tmax p.curve := by
    refine ⟨hTmax_pos, p.initial, ?_, ?_⟩
    · intro t ht0 ht
      have hmem : t ∈ D := ⟨ht0, ht⟩
      exact p.ode t (hD ▸ hmem).1
    · induction Tmax using WithTop.recTopCoe with
      | top =>
        intro I Z hIconn hIt0 hZ hsub heq t ht
        exact ⟨ht.2, by simp⟩
      | coe T =>
        intro I Z hIconn hIt0 hZ hsub heq
        have hT : t0 < T := by simpa using hTmax_pos
        have hforward' : p.dom ∩ Set.Ici t0 = {t : ℝ | t0 ≤ t ∧ t < T} := by
          simpa using hforward
        have hsub' : {t : ℝ | t0 ≤ t ∧ t < T} ⊆ I := by simpa using hsub
        have heq' : ∀ t : ℝ, t0 ≤ t → t < T → p.curve t = Z t := by
          intro t ht0 ht
          exact heq t ht0 (by simpa using ht)
        simpa using pointedSolution_forward_maximal_of_ordConnected_nonautonomous F hcont hlip t0 z0 p hpmax
          hT hforward' I Z hIconn hIt0 hZ hsub' heq'
  refine ⟨Tmax, p.curve, hmaxp, ?_, ?_⟩
  · intro Tmax' z' hmax'
    let D' : Set ℝ := {t : ℝ | t0 ≤ t ∧ (t : WithTop ℝ) < Tmax'}
    have hcommon : ∀ t : ℝ, t0 ≤ t → (t : WithTop ℝ) < Tmax →
        (t : WithTop ℝ) < Tmax' → p.curve t = z' t :=
      classicalSolution_eq_of_below_both_nonautonomous F hlip t0 z0 p.initial hmax'.2.1
        hmaxp.2.2.1 hmax'.2.2.1
    have hDconn : Set.OrdConnected D := by
      rw [hD]
      exact p.preconnected_dom.ordConnected.inter Set.ordConnected_Ici
    have hD'conn : Set.OrdConnected D' := by
      induction Tmax' using WithTop.recTopCoe with
      | top =>
        rw [show D' = Set.Ici t0 by ext t; simp [D']]
        exact Set.ordConnected_Ici
      | coe T' =>
        rw [show D' = Set.Ico t0 T' by ext t; simp [D']]
        exact Set.ordConnected_Ico
    have hle : Tmax ≤ Tmax' := by
      by_contra hnot
      have hlt : Tmax' < Tmax := lt_of_not_ge hnot
      have hD'sub : D' ⊆ D := fun t ht => ⟨ht.1, lt_trans ht.2 hlt⟩
      have hD0 : t0 ∈ D := hD.symm ▸ ⟨p.t0_mem, show t0 ≤ t0 from le_rfl⟩
      have hsub := hmax'.2.2.2 D p.curve hDconn hD0
        (fun t ht => p.ode t (hD ▸ ht).1) hD'sub
        (fun t ht0 ht' => (hcommon t ht0 (hD'sub ⟨ht0, ht'⟩).2 ht').symm)
      have hDom : ∀ t : ℝ, t0 ≤ t → (t : WithTop ℝ) < Tmax →
          (t : WithTop ℝ) < Tmax' := by
        intro t ht0 ht
        exact (hsub ⟨⟨ht0, ht⟩, ht0⟩).2
      exact (not_le_of_gt hlt) (withTop_le_of_forward_subset_nonautonomous hmaxp.1 hDom)
    have hDsub : D ⊆ D' := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hle⟩
    have hge : Tmax' ≤ Tmax := by
      by_contra hnot
      have hlt : Tmax < Tmax' := lt_of_not_ge hnot
      have hD'0 : t0 ∈ D' := ⟨le_rfl, hmax'.1⟩
      have hsub := hmaxp.2.2.2 D' z' hD'conn hD'0
        (fun t ht => hmax'.2.2.1 t ht.1 ht.2) hDsub
        (fun t ht0 ht => hcommon t ht0 ht (lt_trans ht hlt))
      have hDom : ∀ t : ℝ, t0 ≤ t → (t : WithTop ℝ) < Tmax' →
          (t : WithTop ℝ) < Tmax := by
        intro t ht0 ht
        exact (hsub ⟨⟨ht0, ht⟩, ht0⟩).2
      exact (not_le_of_gt hlt) (withTop_le_of_forward_subset_nonautonomous hmax'.1 hDom)
    have heq : Tmax' = Tmax := le_antisymm hge hle
    refine ⟨heq, ?_⟩
    intro t ht0 ht
    exact (hcommon t ht0 ht (by simpa [heq] using ht)).symm
  · intro T hTmax l hlim
    have hTpos : t0 < T := by simpa [hTmax] using hTmax_pos
    have hsmall : Set.Ioo ((t0 + T) / 2) T ⊆ D := by
      intro r hr
      have hmid : t0 < (t0 + T) / 2 := by linarith [hTpos]
      exact ⟨hmid.le.trans hr.1.le, by simpa [hTmax] using hr.2⟩
    have hlimsmall := tendsto_nhdsWithin_mono_left hsmall hlim
    have hplim : Filter.Tendsto p.curve (nhdsWithin T (Set.Iio T)) (nhds l) := by
      rw [nhdsWithin_Ioo_eq_nhdsLT (by linarith [hTpos])] at hlimsmall
      exact hlimsmall
    obtain ⟨eps, heps, alpha, halphaT, halpha⟩ :=
      local_classical_solution_of_uniform_locally_lipschitz F hcont hlip T l
    let eps0 : ℝ := min eps ((T - t0) / 2)
    have heps0 : 0 < eps0 := by dsimp [eps0]; exact lt_min heps (by linarith)
    have heps0eps : eps0 ≤ eps := min_le_left _ _
    have heps0T : eps0 ≤ (T - t0) / 2 := min_le_right _ _
    have halpha0 : ∀ r ∈ Set.Ioo (T - eps0) (T + eps0),
        HasDerivAt alpha (F r (alpha r)) r := by
      intro r hr
      exact halpha r ⟨by linarith [heps0eps, hr.1], by linarith [heps0eps, hr.2]⟩
    have hpode : ∀ r ∈ Set.Ioo (T - eps0) T,
        HasDerivAt p.curve (F r (p.curve r)) r := by
      intro r hr
      apply p.ode r
      have hmem : r ∈ D := ⟨by linarith [heps0T, hr.1], by simpa [hTmax] using hr.2⟩
      exact (hD ▸ hmem).1
    obtain ⟨rho, hrho, hrhoe, hleft⟩ :=
      ode_eqOn_left_of_tendsto_nonautonomous F hcont hlip heps0 hpode halpha0 hplim halphaT
    have hEq : Set.EqOn p.curve alpha (p.dom ∩ Set.Ioo (T - rho) (T + eps0)) := by
      rintro r ⟨hrdom, hr⟩
      have hrT : r < T := by
        by_contra hn
        have hTr : T ≤ r := le_of_not_gt hn
        have hr0 : t0 ≤ r := by linarith
        have hmem : r ∈ D := hD.symm ▸ ⟨hrdom, hr0⟩
        have : r < T := by simpa [hTmax] using hmem.2
        linarith
      exact hleft ⟨hr.1, hrT⟩
    have hcdom : T - rho / 2 ∈ p.dom := by
      have hmem : T - rho / 2 ∈ D := ⟨by linarith [heps0T, hrhoe],
        by rw [hTmax]; exact_mod_cast (show T - rho / 2 < T by linarith)⟩
      exact (hD ▸ hmem).1
    have hcIoo : T - rho / 2 ∈ Set.Ioo (T - rho) (T + eps0) := by constructor <;> linarith
    obtain ⟨q, hpq, halphaq, hsubq⟩ := pointedSolution_extend_of_eqOn_nonautonomous F t0 z0 p
      (a := T - rho) (b := T + eps0) (by linarith) alpha
      (fun r hr => halpha0 r ⟨by linarith [hrhoe, hr.1], by linarith [heps0eps, hr.2]⟩)
      hEq ⟨T - rho / 2, hcdom, hcIoo⟩
    let S : ℝ := T + rho / 2
    refine ⟨S, by dsimp [S]; linarith, q.curve, ?_, ?_⟩
    · intro t ht0 ht
      rcases lt_or_ge t T with htT | htT
      · apply q.ode t (hpq.1 ?_)
        have hmem : t ∈ D := ⟨ht0, by simpa [hTmax] using htT⟩
        exact (hD ▸ hmem).1
      · apply q.ode t (hsubq ?_)
        constructor <;> dsimp [S] at ht ⊢ <;> linarith [hrho, hrhoe]
    · intro t ht0 htT
      have hmem : t ∈ D := ⟨ht0, by simpa [hTmax] using htT⟩
      exact (hpq.2 ((hD ▸ hmem).1)).symm


/-! Source item: Attouch_Balhag_Chbani_Riahi_Tikhonov_Inertial_Dynamics_2022
items/thm_4 (proof helper). -/


private theorem norm_sub_le_of_hasDerivAt_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t M : ℝ} {u du : ℝ → E} (hst : s ≤ t)
    (hdu : ∀ r, s ≤ r → r ≤ t → HasDerivAt u (du r) r)
    (hbound : ∀ r, s ≤ r → r ≤ t → ‖du r‖ ≤ M) :
    ‖u t - u s‖ ≤ M * (t - s) := by
  have hcont : ContinuousOn u (Set.Icc s t) := by
    intro r hr
    exact (hdu r hr.1 hr.2).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ u (Set.Ioo s t) := by
    intro r hr
    exact (hdu r hr.1.le hr.2.le).differentiableAt.differentiableWithinAt
  have hderiv_bound : ∀ᵐ r : ℝ, r ∈ Set.Ioo s t → ‖deriv u r‖ ≤ M := by
    filter_upwards [] with r hr
    simpa [(hdu r hr.1.le hr.2.le).deriv] using hbound r hr.1.le hr.2.le
  calc
    ‖u t - u s‖ ≤ ∫ r in s..t, M :=
      norm_sub_le_integral_of_norm_deriv_le_of_le hst hcont hdiff hderiv_bound
        intervalIntegrable_const
    _ = M * (t - s) := by simp [mul_comm]

/-- If `u` is differentiable on `[a, b)` with derivative bounded by `M`, then
`u` has a limit at `b` from the right (Cauchy criterion).  Generic analysis
helper used in the proof of Theorem 4 of
Attouch--Balhag--Chbani--Riahi 2022. -/
theorem tendsto_at_right_of_norm_deriv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b M : ℝ} {u du : ℝ → E} (hab : a < b) (hM : 0 ≤ M)
    (hderiv : ∀ t, a ≤ t → t < b → HasDerivAt u (du t) t)
    (hbound : ∀ t, a ≤ t → t < b → ‖du t‖ ≤ M) :
    ∃ l : E, Filter.Tendsto u (nhdsWithin b (Set.Ico a b)) (nhds l) := by
  have hne : (nhdsWithin b (Set.Ico a b)).NeBot := by
    rw [nhdsWithin_neBot]
    intro U hU
    have hclosure : b ∈ closure (Set.Ico a b) := by
      rw [closure_Ico (ne_of_lt hab)]
      exact ⟨hab.le, le_rfl⟩
    exact mem_closure_iff_nhds.mp hclosure U hU
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨hne.map u, ?_⟩
  intro η hη
  let ρ : ℝ := min ((b - a) / 2) (η / (M + 1))
  have hden : 0 < M + 1 := by linarith
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (div_pos hη hden)
  have hρa : ρ ≤ (b - a) / 2 := min_le_left _ _
  have hρη : ρ ≤ η / (M + 1) := min_le_right _ _
  have hMρ : M * ρ < η := by
    calc
      M * ρ ≤ M * (η / (M + 1)) := mul_le_mul_of_nonneg_left hρη hM
      _ = (M * η) / (M + 1) := by ring
      _ < η := (div_lt_iff₀ hden).2 (by nlinarith)
  let U : Set ℝ := Set.Ioo (b - ρ) b ∩ Set.Ico a b
  have hU : U ∈ nhdsWithin b (Set.Ico a b) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi (b - ρ), Ioi_mem_nhds (by linarith), ?_⟩
    intro t ht
    constructor
    · exact ⟨ht.1, ht.2.2⟩
    · exact ht.2
  refine ⟨u '' U, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact Filter.mem_of_superset hU (fun t ht => ⟨t, ht, rfl⟩)
  · intro x hx y hy
    rcases hx with ⟨x, hx, rfl⟩
    rcases hy with ⟨y, hy, rfl⟩
    rcases le_total x y with hxy | hyx
    · have hxyρ : y - x < ρ := by
        have hxl : b - ρ < x := hx.1.1
        have hyb : y < b := hy.1.2
        linarith
      calc
        dist (u x) (u y) = ‖u y - u x‖ := by rw [dist_eq_norm_sub, norm_sub_rev]
        _ ≤ M * (y - x) := norm_sub_le_of_hasDerivAt_bound hxy
          (fun r hr hs => hderiv r (hx.2.1.trans hr) (lt_of_le_of_lt hs hy.2.2))
          (fun r hr hs => hbound r (hx.2.1.trans hr) (lt_of_le_of_lt hs hy.2.2))
        _ ≤ M * ρ := mul_le_mul_of_nonneg_left hxyρ.le hM
        _ < η := hMρ
    · have hyxρ : x - y < ρ := by
        have hyl : b - ρ < y := hy.1.1
        have hxb : x < b := hx.1.2
        linarith
      calc
        dist (u x) (u y) = ‖u x - u y‖ := dist_eq_norm_sub _ _
        _ ≤ M * (x - y) := norm_sub_le_of_hasDerivAt_bound hyx
          (fun r hr hs => hderiv r (hy.2.1.trans hr) (lt_of_le_of_lt hs hx.2.2))
          (fun r hr hs => hbound r (hy.2.1.trans hr) (lt_of_le_of_lt hs hx.2.2))
        _ ≤ M * ρ := mul_le_mul_of_nonneg_left hyxρ.le hM
        _ < η := hMρ


/-- The function `x ↦ exp(-∫₀ˣ δ s)`, the exponential of the negative of an
  integrable primitive, is absolutely continuous on `[a,b]`, with derivative
  `-δ x * exp(-∫₀ˣ δ s)` almost everywhere. -/
theorem ac_exp_neg_intervalIntegral (a b : ℝ) (δ : ℝ → ℝ) (hab : a ≤ b)
    (hδ : MeasureTheory.IntegrableOn δ (Set.Icc a b)) :
    AbsolutelyContinuousOnInterval (fun x : ℝ => Real.exp (-∫ s in a..x, δ s)) a b ∧
      ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc a b),
        HasDerivAt (fun y : ℝ => Real.exp (-∫ s in a..y, δ s))
          (-δ x * Real.exp (-∫ s in a..x, δ s)) x := by
  have hδII : IntervalIntegrable δ MeasureTheory.volume a b := by
    rw [← Set.uIcc_of_le hab] at hδ
    exact hδ.intervalIntegrable
  have hderiv : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc a b),
      HasDerivAt (fun y : ℝ => ∫ s in a..y, δ s) (δ x) x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hδII.ae_hasDerivAt_integral] with x hx
    intro hxa
    exact hx (by simpa only [Set.uIcc_of_le hab] using hxa) a (by simp)
  constructor
  · have hD_ac : AbsolutelyContinuousOnInterval (fun x : ℝ => ∫ s in a..x, δ s) a b :=
      hδII.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
    obtain ⟨C, hC⟩ := hD_ac.exists_bound
    have hD_mem : ∀ x ∈ Set.uIcc a b, (∫ s in a..x, δ s) ∈ Set.Icc (-C) C := by
      intro x hx
      have hxC := hC x hx
      rw [Real.norm_eq_abs] at hxC
      constructor <;> linarith [le_abs_self (∫ s in a..x, δ s),
        neg_le_abs (∫ s in a..x, δ s)]
    have hexp_lip : ∀ x y, x ∈ Set.Icc (-C) C → y ∈ Set.Icc (-C) C →
        ‖Real.exp (-y) - Real.exp (-x)‖ ≤ Real.exp C * ‖y - x‖ := by
      intro x y hx hy
      exact Convex.norm_image_sub_le_of_norm_deriv_le
        (f := fun z : ℝ => Real.exp (-z))
        (s := Set.Icc (-C) C) (C := Real.exp C)
        (fun z hz => ((Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)).differentiableAt)
        (fun z hz => by
          have hφ' : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
            convert (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z) using 1 <;> ring
          rw [hφ'.deriv]
          rw [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          linarith [hz.1])
        (convex_Icc (-C) C) hx hy
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    obtain ⟨η, hηpos, hη⟩ :=
      (absolutelyContinuousOnInterval_iff _ _ _).mp hD_ac
        (ε / (Real.exp C + 1)) (by positivity)
    refine ⟨η, hηpos, ?_⟩
    intro E hE_disj hE_length
    have hDsum := hη E hE_disj hE_length
    calc
      ∑ i ∈ Finset.range E.1,
          dist (Real.exp (-∫ s in a..(E.2 i).1, δ s))
            (Real.exp (-∫ s in a..(E.2 i).2, δ s))
        ≤ ∑ i ∈ Finset.range E.1,
            Real.exp C * dist (∫ s in a..(E.2 i).1, δ s)
              (∫ s in a..(E.2 i).2, δ s) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi_mem := hE_disj.left i hi
            simpa only [Real.dist_eq, norm_sub_rev] using
              hexp_lip _ _ (hD_mem _ hi_mem.left) (hD_mem _ hi_mem.right)
      _ = Real.exp C *
          ∑ i ∈ Finset.range E.1,
            dist (∫ s in a..(E.2 i).1, δ s)
              (∫ s in a..(E.2 i).2, δ s) := by rw [Finset.mul_sum]
      _ < Real.exp C * (ε / (Real.exp C + 1)) := by gcongr
      _ < (Real.exp C + 1) * (ε / (Real.exp C + 1)) := by
            have hC_lt : Real.exp C < Real.exp C + 1 := by linarith [Real.exp_pos C]
            gcongr
      _ = ε := by field_simp
  · filter_upwards [hderiv] with x hx
    convert hx.neg.exp using 1; simp only [Pi.neg_apply]; ring

/-- An absolutely continuous function whose derivative is nonpositive almost
  everywhere is nonincreasing. -/
theorem ac_nonincreasing_of_ae_deriv_nonpos {a b : ℝ} {G : ℝ → ℝ} (hab : a ≤ b)
    (hG : AbsolutelyContinuousOnInterval G a b)
    (hG' : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc a b), deriv G x ≤ 0) :
    ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc a b → v ∈ Set.Icc a b → u ≤ v → G v ≤ G u := by
  intro u v hu hv huv
  have huvab : Set.uIcc u v ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc hu.1 hv.2
  have hGuv := hG.mono huvab
  have hderiv : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc u v), deriv G x ≤ 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hG'] with x hx hxu
    exact hx (Set.Icc_subset_Icc hu.1 hv.2 hxu)
  have hInt : ∫ x in u..v, deriv G x ≤ 0 := by
    have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume u v :=
      intervalIntegrable_const
    simpa using intervalIntegral.integral_mono_ae_restrict huv hGuv.intervalIntegrable_deriv hzero hderiv
  rw [hGuv.integral_deriv_eq_sub] at hInt
  linarith

/-- Integral Gronwall inequality for an absolutely continuous scalar function. -/
theorem gronwall_inequality (y a b : ℝ → ℝ) (_hy : ∀ t, 0 ≤ y t)
    (hAC : ∀ T : ℝ, 0 < T → AbsolutelyContinuousOnInterval y 0 T)
    (ha : MeasureTheory.LocallyIntegrable a) (hb : MeasureTheory.LocallyIntegrable b)
    (hineq : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)), deriv y t ≤ a t * y t + b t) :
    ∀ t, 0 ≤ t → y t ≤ Real.exp (∫ s in Set.Icc 0 t, a s) * (y 0 + ∫ s in Set.Icc 0 t, Real.exp (-∫ q in Set.Icc 0 s, a q) * b s) := by
  intro t ht
  rcases ht.eq_or_lt with rfl | ht0
  · simp
  have haIcc : MeasureTheory.IntegrableOn a (Set.Icc 0 t) :=
    ha.integrableOn_isCompact isCompact_Icc
  have hbIcc : MeasureTheory.IntegrableOn b (Set.Icc 0 t) :=
    hb.integrableOn_isCompact isCompact_Icc
  have haII : IntervalIntegrable a MeasureTheory.volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0.le]
    exact haIcc
  have hbII : IntervalIntegrable b MeasureTheory.volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0.le]
    exact hbIcc
  let A : ℝ → ℝ := fun x => ∫ r in 0..x, a r
  let E : ℝ → ℝ := fun x => Real.exp (-A x)
  let P : ℝ → ℝ := fun x => ∫ r in 0..x, E r * b r
  let q : ℝ → ℝ := fun x => E x * y x
  let H : ℝ → ℝ := fun x => q x - P x
  obtain ⟨hEAC, hEderiv⟩ := ac_exp_neg_intervalIntegral 0 t a ht0.le haIcc
  have hEAC' : AbsolutelyContinuousOnInterval E 0 t := by simpa [E, A] using hEAC
  have hEbII : IntervalIntegrable (fun r => E r * b r) MeasureTheory.volume 0 t := by
    simpa [mul_comm] using hbII.mul_continuousOn hEAC'.continuousOn
  have hPAC : AbsolutelyContinuousOnInterval P 0 t := by
    simpa [P] using hEbII.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hPderiv : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc 0 t),
      HasDerivAt P (E x * b x) x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hEbII.ae_hasDerivAt_integral] with x hx hxt
    simpa [P, Set.uIcc_of_le ht0.le] using hx (by simpa [Set.uIcc_of_le ht0.le] using hxt) 0 (by simp)
  have hineqIcc : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc 0 t),
      deriv y x ≤ a x * y x + b x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    rw [MeasureTheory.restrict_Ioi_eq_restrict_Ici] at hineq
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hineq] with x hx hxt
    exact hx (Set.mem_Ici.mpr hxt.1)
  have hqAC : AbsolutelyContinuousOnInterval q 0 t := by simpa [q] using hEAC'.fun_mul (hAC t ht0)
  have hqderiv : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc 0 t), deriv q x ≤ E x * b x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hEderiv,
      (hAC t ht0).ae_differentiableAt,
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hineqIcc] with x hE hy' hi hxt
    have hyD : HasDerivAt y (deriv y x) x :=
      (hy' (by simpa [Set.uIcc_of_le ht0.le] using hxt)).hasDerivAt
    have hED : HasDerivAt E (-a x * E x) x := by simpa [E, A] using hE hxt
    have hp := hED.mul hyD
    change deriv (E * y) x ≤ E x * b x
    rw [hp.deriv]
    have hcalc : (-a x * E x) * y x + E x * deriv y x = E x * (deriv y x - a x * y x) := by ring
    rw [hcalc]
    apply mul_le_mul_of_nonneg_left
    · linarith [hi hxt]
    · exact (Real.exp_pos _).le
  have hHAC : AbsolutelyContinuousOnInterval H 0 t := by simpa [H] using hqAC.sub hPAC
  have hHderiv : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc 0 t), deriv H x ≤ 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hEderiv,
      (hAC t ht0).ae_differentiableAt,
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hPderiv,
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hineqIcc] with x hE hy' hP hi hxt
    have hyD : HasDerivAt y (deriv y x) x :=
      (hy' (by simpa [Set.uIcc_of_le ht0.le] using hxt)).hasDerivAt
    have hED : HasDerivAt E (-a x * E x) x := by simpa [E, A] using hE hxt
    have hqD := hED.mul hyD
    have hs := hqD.sub (hP hxt)
    change deriv ((E * y) - P) x ≤ 0
    rw [hs.deriv]
    have hcalc : (-a x * E x) * y x + E x * deriv y x =
        E x * (deriv y x - a x * y x) := by ring
    rw [hcalc]
    have hq : E x * (deriv y x - a x * y x) ≤ E x * b x := by
      apply mul_le_mul_of_nonneg_left
      · linarith [hi hxt]
      · exact (Real.exp_pos _).le
    linarith
  have hH := ac_nonincreasing_of_ae_deriv_nonpos ht0.le hHAC (by simpa [H] using hHderiv)
    (show 0 ∈ Set.Icc 0 t from ⟨le_rfl, ht0.le⟩) (show t ∈ Set.Icc 0 t from ⟨ht0.le, le_rfl⟩) ht0.le
  have hcancel : Real.exp (A t) * (E t * y t) = y t := by
    dsimp [E]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  have hmain : y t ≤ Real.exp (A t) * (y 0 + P t) := by
    have hcore : E t * y t ≤ y 0 + P t := by
      dsimp [H, q, P, E, A] at hH
      simp at hH
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hcore (Real.exp_pos (A t)).le
    rw [hcancel] at hscaled
    exact hscaled
  have hA : A t = ∫ s in Set.Icc 0 t, a s := by
    dsimp [A]
    rw [intervalIntegral.integral_of_le ht0.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hP : P t = ∫ s in Set.Icc 0 t, Real.exp (-∫ q in Set.Icc 0 s, a q) * b s := by
    dsimp [P]
    rw [intervalIntegral.integral_of_le ht0.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    apply MeasureTheory.integral_congr_ae
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards with s hs
    congr 2
    dsimp [E, A]
    rw [intervalIntegral.integral_of_le hs.1,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hA, hP] at hmain
  exact hmain

/-- Integral Gronwall inequality in the squared form (Brezis, Lemma A.5): if
`u² ≤ 2 * ∫ a*u + b²` on `[s0, T]` with `b` monotone, then `u ≤ 2 * ∫ a + b`. -/
theorem integral_gronwall_inequality (s0 T : ℝ) (u a b : ℝ → ℝ)
    (hu : ContinuousOn u (Set.Icc s0 T)) (ha : IntervalIntegrable a MeasureTheory.volume s0 T)
    (hb : ContinuousOn b (Set.Icc s0 T)) (hpos : ∀ s ∈ Set.Icc s0 T,
      0 ≤ u s ∧ 0 ≤ a s ∧ 0 ≤ b s) (hmono : MonotoneOn b (Set.Icc s0 T))
    (hineq : ∀ s ∈ Set.Icc s0 T, u s ^ 2 ≤ (2 * ∫ τ in s0..s, a τ * u τ) + b s ^ 2) :
    ∀ s ∈ Set.Icc s0 T, u s ≤ (2 * ∫ τ in s0..s, a τ) + b s := by
  intro s hs
  have hs0 : s0 ≤ s := hs.1
  have hsub : Set.Icc s0 s ⊆ Set.Icc s0 T := fun x hx => ⟨hx.1, hx.2.trans hs.2⟩
  have ha_s : IntervalIntegrable a MeasureTheory.volume s0 s := by
    apply ha.mono
    apply Set.uIcc_subset_uIcc
    · exact (show s0 ∈ Set.uIcc s0 T by simp)
    · exact (show s ∈ Set.uIcc s0 T by simp [Set.mem_uIcc, hs0, hs.2])
    exact le_rfl
  have hcont : ContinuousOn (fun t => u t - b t) (Set.Icc s0 s) :=
    (hu.mono hsub).sub (hb.mono hsub)
  obtain ⟨r, hr, hrmax⟩ := isCompact_Icc.exists_isMaxOn ⟨s0, ⟨le_rfl, hs0⟩⟩ hcont
  have hrT : r ∈ Set.Icc s0 T := hsub hr
  have ha_r : IntervalIntegrable a MeasureTheory.volume s0 r := by
    apply ha_s.mono
    simpa only [Set.uIcc_of_le hs0, Set.uIcc_of_le hr.1] using
      (show Set.Icc s0 r ⊆ Set.Icc s0 s from fun x hx => ⟨hx.1, hx.2.trans hr.2⟩)
    exact le_rfl
  have hu_r : ContinuousOn u (Set.uIcc s0 r) := by
    simpa only [Set.uIcc_of_le hr.1] using hu.mono
      (show Set.Icc s0 r ⊆ Set.Icc s0 T from fun x hx => ⟨hx.1, (hx.2.trans hr.2).trans hs.2⟩)
  have hprod_r : IntervalIntegrable (fun t => a t * u t) MeasureTheory.volume s0 r :=
    ha_r.mul_continuousOn hu_r
  have hprod_le : (∫ t in s0..r, a t * u t) ≤ u r * ∫ t in s0..r, a t := by
    calc
      (∫ t in s0..r, a t * u t) ≤ ∫ t in s0..r, a t * u r := by
        apply intervalIntegral.integral_mono_on hr.1 hprod_r (ha_r.mul_const _)
        intro t ht
        have htT : t ∈ Set.Icc s0 T := ⟨ht.1, (ht.2.trans hr.2).trans hs.2⟩
        have htu : u t ≤ u r := by
          have hdiff := (isMaxOn_iff.mp hrmax t ⟨ht.1, ht.2.trans hr.2⟩)
          have hbmono : b t ≤ b r := hmono htT hrT ht.2
          linarith
        exact mul_le_mul_of_nonneg_left htu (hpos t htT).2.1
      _ = u r * ∫ t in s0..r, a t := by
        rw [intervalIntegral.integral_mul_const, mul_comm]
  have hinta_r : 0 ≤ ∫ t in s0..r, a t := by
    apply intervalIntegral.integral_nonneg hr.1
    intro t ht
    exact (hpos t ⟨ht.1, (ht.2.trans hr.2).trans hs.2⟩).2.1
  have hmain_r : u r - b r ≤ 2 * ∫ t in s0..r, a t := by
    have hi := hineq r hrT
    have hur : 0 ≤ u r := (hpos r hrT).1
    have hbr : 0 ≤ b r := (hpos r hrT).2.2
    have hi' : u r ^ 2 ≤ 2 * (u r * ∫ t in s0..r, a t) + b r ^ 2 := by
      have h2prod : 2 * (∫ t in s0..r, a t * u t) ≤ 2 * (u r * ∫ t in s0..r, a t) :=
        mul_le_mul_of_nonneg_left hprod_le (by norm_num)
      exact hi.trans (add_le_add_left h2prod _)
    by_contra h
    have hlt : 2 * ∫ t in s0..r, a t < u r - b r := lt_of_not_ge h
    have hur_pos : 0 < u r := by nlinarith
    have hmul : u r * (2 * ∫ t in s0..r, a t) < u r * (u r - b r) :=
      mul_lt_mul_of_pos_left hlt hur_pos
    nlinarith
  have hinta_rs : (∫ t in s0..r, a t) ≤ ∫ t in s0..s, a t := by
    apply intervalIntegral.integral_mono_interval (a := s0) (b := r) (c := s0) (d := s) le_rfl hr.1 hr.2
    · apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2
      exact Filter.Eventually.of_forall fun t ht => (hpos t ⟨ht.1.le, ht.2.trans hs.2⟩).2.1
    · exact ha_s
  have hdiff_s : u s - b s ≤ 2 * ∫ t in s0..s, a t := by
    calc
      u s - b s ≤ u r - b r := isMaxOn_iff.mp hrmax s ⟨hs0, le_rfl⟩
      _ ≤ 2 * ∫ t in s0..r, a t := hmain_r
      _ ≤ 2 * ∫ t in s0..s, a t := mul_le_mul_of_nonneg_left hinta_rs (by positivity)
  exact sub_le_iff_le_add.mp hdiff_s

/-- A positive derivative satisfying `v'' ≥ -c(v')²` stays positive and has divergent primitive. -/
theorem increasing_unbounded_of_second_derivative_bound
    (v : ℝ → ℝ) (c : ℝ) (h : 0 < c)
    (hv : ContDiff ℝ 2 v)
    (hv0 : 0 < deriv v 0)
    (hvv : ∀ t : ℝ, 0 ≤ t → -c * (deriv v t)^2 ≤ deriv (deriv v) t) :
    (∀ t : ℝ, 0 ≤ t → MonotoneOn v (Set.Ici 0)) ∧ Filter.Tendsto v Filter.atTop Filter.atTop := by
  let w : ℝ → ℝ := fun t => Real.exp (c * v t)
  have hv1 : ∀ t : ℝ, HasDerivAt v (deriv v t) t := fun t =>
    (hv.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hv2 : ∀ t : ℝ, HasDerivAt (deriv v) (deriv (deriv v) t) t := fun t =>
    hv.differentiable_deriv_two.differentiableAt.hasDerivAt
  have hws : ∀ t : ℝ, HasDerivAt w (c * Real.exp (c * v t) * deriv v t) t := by
    intro t
    have hcv : HasDerivAt (fun s => c * v s) (c * deriv v t) t :=
      (hv1 t).const_mul c
    convert hcv.exp using 1
    dsimp [w]
    ring
  have hwd : ∀ t : ℝ, deriv w t = c * Real.exp (c * v t) * deriv v t := by
    intro t
    exact (hws t).deriv
  have hwds : ∀ t : ℝ, HasDerivAt (deriv w)
      (c * Real.exp (c * v t) * (deriv (deriv v) t + c * (deriv v t)^2)) t := by
    intro t
    have hcv : HasDerivAt (fun s => c * v s) (c * deriv v t) t :=
      (hv1 t).const_mul c
    have he : HasDerivAt (fun s => c * Real.exp (c * v s))
        (c * (Real.exp (c * v t) * (c * deriv v t))) t :=
      (hcv.exp).const_mul c
    have hp := he.mul (hv2 t)
    rw [show deriv w = fun s => c * Real.exp (c * v s) * deriv v s by
      funext s
      exact hwd s]
    convert hp using 1
    ring
  have hwdd : ∀ t : ℝ, deriv (deriv w) t =
      c * Real.exp (c * v t) * (deriv (deriv v) t + c * (deriv v t)^2) := by
    intro t
    exact (hwds t).deriv
  have hwdd_nonneg : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ deriv (deriv w) t := by
    intro t ht
    rw [hwdd t]
    exact mul_nonneg (mul_nonneg h.le (Real.exp_pos _).le) (by linarith [hvv t ht])
  have hw_cont : ContinuousOn w (Set.Ici 0) := by
    intro t ht
    exact (hws t).continuousAt.continuousWithinAt
  have hwd_diff : DifferentiableOn ℝ (deriv w) (interior (Set.Ici 0)) := by
    intro t ht
    exact (hwds t).differentiableAt.differentiableWithinAt
  have hwd_mono : MonotoneOn (deriv w) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) (by
      intro t ht
      exact (hwds t).continuousAt.continuousWithinAt) hwd_diff
      (by intro t ht; exact hwdd_nonneg t (interior_subset ht))
  have hwd0 : 0 < deriv w 0 := by
    rw [hwd 0]
    positivity
  have hwd_pos : ∀ t : ℝ, 0 ≤ t → 0 < deriv w t := by
    intro t ht
    exact lt_of_lt_of_le hwd0 (hwd_mono (by simp) ht ht)
  have hv_pos : ∀ t : ℝ, 0 ≤ t → 0 < deriv v t := by
    intro t ht
    have ht' := hwd_pos t ht
    rw [hwd t] at ht'
    rcases mul_pos_iff.mp ht' with hp | hp
    · exact hp.2
    · exact False.elim ((not_lt_of_ge (mul_nonneg h.le (Real.exp_pos _).le)) hp.1)
  have hv_mono : MonotoneOn v (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hv.continuous.continuousOn
      ((hv.differentiable (by norm_num)).differentiableOn)
      (by intro t ht; exact (hv_pos t (interior_subset ht)).le)
  have h_affine : ∀ t : ℝ, 0 ≤ t → w 0 + deriv w 0 * t ≤ w t := by
    intro t ht
    let q : ℝ → ℝ := fun s => w s - deriv w 0 * s
    have hq_deriv : ∀ s : ℝ, deriv q s = deriv w s - deriv w 0 := by
      intro s
      have hs : HasDerivAt (fun x => deriv w 0 * x) (deriv w 0) s := by
        have hid := (hasDerivAt_id s).const_mul (deriv w 0)
        convert hid using 1
        simp
      simpa only [q, hwd] using ((hws s).sub hs).deriv
    have hq_cont : ContinuousOn q (Set.Ici 0) := by
      intro s hs
      have hs' : HasDerivAt (fun x => deriv w 0 * x) (deriv w 0) s := by
        have hid := (hasDerivAt_id s).const_mul (deriv w 0)
        convert hid using 1
        simp
      simpa only [q] using ((hws s).sub hs').continuousAt.continuousWithinAt
    have hq_diff : DifferentiableOn ℝ q (interior (Set.Ici 0)) := by
      intro s hs
      have hs' : HasDerivAt (fun x => deriv w 0 * x) (deriv w 0) s := by
        have hid := (hasDerivAt_id s).const_mul (deriv w 0)
        convert hid using 1
        simp
      have hqs : HasDerivAt q (deriv q s) s := by
        have hraw : HasDerivAt q
            (c * Real.exp (c * v s) * deriv v s - deriv w 0) s := by
          simpa only [q] using (hws s).sub hs'
        rw [hq_deriv, hwd]
        exact hraw
      exact hqs.differentiableAt.differentiableWithinAt
    have hq_mono : MonotoneOn q (Set.Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0) hq_cont hq_diff (by
        intro s hs
        rw [hq_deriv]
        exact sub_nonneg.mpr (hwd_mono (by simp) (interior_subset hs)
          (show 0 ≤ s from le_trans (by norm_num) (interior_subset hs))))
    have hqt := hq_mono (by simp) ht ht
    dsimp [q] at hqt
    linarith
  constructor
  · intro _ _
    exact hv_mono
  · rw [Filter.tendsto_atTop]
    intro B
    let T : ℝ := max 0 ((Real.exp (c * B) - w 0) / deriv w 0 + 1)
    filter_upwards [Filter.eventually_atTop.2 ⟨T, fun t ht => ht⟩] with t ht
    have hT0 : 0 ≤ t := le_trans (le_max_left _ _) ht
    have hT : (Real.exp (c * B) - w 0) / deriv w 0 + 1 ≤ t :=
      le_trans (le_max_right _ _) ht
    have hlin := h_affine t hT0
    have hd : 0 < deriv w 0 := hwd0
    have hexp : Real.exp (c * B) < w t := by
      have : Real.exp (c * B) < w 0 + deriv w 0 * t := by
        have hdiv : (Real.exp (c * B) - w 0) / deriv w 0 < t :=
          lt_of_lt_of_le (lt_add_one _) hT
        have hmul := (div_lt_iff₀ hd).mp hdiv
        linarith
      exact lt_of_lt_of_le this hlin
    have : c * B < c * v t := by
      rw [show w t = Real.exp (c * v t) by rfl] at hexp
      exact Real.exp_lt_exp.mp hexp
    nlinarith

/-! ### Absolute continuity and the damped second-order system
Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/def_3 -/

/-- A function `x : ℝ → H` and its derivative `dx` are locally absolutely
  continuous if for every `T > 0` both are absolutely continuous on `[0,T]`. -/
def IsLocallyAbsolutelyContinuous {H : Type*} [NormedAddCommGroup H]
    (x dx : ℝ → H) : Prop :=
  ∀ T > (0 : ℝ), AbsolutelyContinuousOnInterval x 0 T ∧ AbsolutelyContinuousOnInterval dx 0 T

/-- A strong global solution of the damped second-order system
  `ẍ(t) + γ ẋ(t) + A x(t) = 0` for almost every `t ≥ 0`, with initial data
  `x(0) = u₀`, `ẋ(0) = v₀`, and `x`, `ẋ` locally absolutely continuous. -/
def StrongSolutionOfDampedSystem {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : H → H) (γ : ℝ) (u₀ v₀ : H) (x dx ddx : ℝ → H) : Prop :=
  IsLocallyAbsolutelyContinuous x dx ∧ x 0 = u₀ ∧ dx 0 = v₀ ∧
    ∀ᵐ t ∂ MeasureTheory.volume, t ≥ (0 : ℝ) → ddx t + γ • dx t + A (x t) = 0

/-! Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/ext_def_3 -/

/-- The inertial gradient-like dynamics (DIN):
  `ẍ_μ + γ ẋ_μ + β ∇²φ_μ(x_μ) ẋ_μ + ∇φ_μ(x_μ) = 0` for a.e. `t ≥ 0`, with the
  stated initial data; `x_μ` and `ẋ_μ` are locally absolutely continuous. -/
def DIN {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (_φ : H → ℝ) (gradφ : H → H) (hessφ : H → H → H) (γ β : ℝ)
    (u₀ v₀ : H) (x dx ddx : ℝ → H) : Prop :=
  IsLocallyAbsolutelyContinuous x dx ∧ x 0 = u₀ ∧ dx 0 = v₀ ∧
    ∀ᵐ t ∂ MeasureTheory.volume, t ≥ (0 : ℝ) →
      ddx t + γ • dx t + β • (hessφ (x t) (dx t)) + gradφ (x t) = 0

/-! Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/ext_def_4 -/

/-- The sup norm `‖x‖_∞ := sup_{t∈[0,T]} ‖x(t)‖` over the time interval `[0,T]`. -/
noncomputable def pathSupNorm {H : Type*} [NormedAddCommGroup H] (T : ℝ) (x : ℝ → H) : ℝ :=
  sSup {q : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) T, q = ‖x t‖}

/-- The integral map `Γ_{A,u₀,v₀}(x)(t) := u₀ + t v₀ + ∫₀ᵗ (s-t)[γ ẋ(s) + A x(s)] ds`,
  the Picard operator of the damped second-order system. -/
noncomputable def integralMap {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : H → H) (γ : ℝ) (u₀ v₀ : H) (x dx : ℝ → H) (t : ℝ) : H :=
  u₀ + t • v₀ + ∫ s in (0 : ℝ)..t, (s - t) • (γ • dx s + A (x s))

/-! ### Nonlinear Gronwall inequality with a fractional-power kernel
Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/ext_lem_1 -/

/-- Composition of an absolutely continuous function with a locally Lipschitz
  function on the image is absolutely continuous. -/
theorem ac_comp_of_lipschitzOn_image {f phi : ℝ → ℝ} {l u : ℝ} {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f l u)
    (hphi : LipschitzOnWith K phi (f '' Set.uIcc l u)) :
    AbsolutelyContinuousOnInterval (fun s => phi (f s)) l u := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  rcases (absolutelyContinuousOnInterval_iff _ _ _).mp hf (ε / (K + 1))
      (by positivity) with ⟨δ, hδ, hδ_bound⟩
  refine ⟨δ, hδ, fun (n, I) hnI₁ hnI₂ => ?_⟩
  calc
    ∑ i ∈ Finset.range n, dist (phi (f (I i).1)) (phi (f (I i).2))
        ≤ ∑ i ∈ Finset.range n, K * dist (f (I i).1) (f (I i).2) := by
          apply Finset.sum_le_sum
          intro i hi
          have h := hphi ⟨(I i).1, (hnI₁.left i hi).left, rfl⟩
            ⟨(I i).2, (hnI₁.left i hi).right, rfl⟩
          apply ENNReal.toReal_mono
            (ENNReal.mul_ne_top (by simp) (edist_ne_top _ _)) at h
          rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at h
    _ = K * ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) := by
          rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by
          gcongr
          simpa using (hδ_bound (n, I) hnI₁ hnI₂).le
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field

/-- `(exp(-A/q))^q = exp(-A)` for `q > 0`. -/
theorem exp_neg_div_rpow {A q : ℝ} (hq : 0 < q) :
    (Real.exp (-A / q)) ^ q = Real.exp (-A) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  field_simp [ne_of_gt hq]

/-- `x^α (x+ε)^(-α) ≤ 1` for `x ≥ 0`, `α ≥ 0`, `ε > 0`. -/
theorem rpow_ratio_le_one {x alpha epsilon : ℝ} (hx : 0 ≤ x)
    (halpha : 0 ≤ alpha) (hepsilon : 0 < epsilon) :
    x ^ alpha * (x + epsilon) ^ (-alpha) ≤ 1 := by
  have hxe : x ≤ x + epsilon := by linarith
  have hxepos : 0 < x + epsilon := by linarith
  have hp : 0 < (x + epsilon) ^ alpha := Real.rpow_pos_of_pos hxepos _
  have hpow : x ^ alpha ≤ (x + epsilon) ^ alpha :=
    Real.rpow_le_rpow hx hxe halpha
  rw [Real.rpow_neg hxepos.le]
  calc
    x ^ alpha * ((x + epsilon) ^ alpha)⁻¹ ≤
        (x + epsilon) ^ alpha * ((x + epsilon) ^ alpha)⁻¹ :=
      mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr hp.le)
    _ = 1 := mul_inv_cancel₀ hp.ne'

/-- A positive shift of a nonnegative absolutely continuous function, raised to
  a real power, is absolutely continuous. -/
theorem shifted_rpow_ac {f : ℝ → ℝ} {l u q epsilon : ℝ} (hlu : l ≤ u)
    (hf : AbsolutelyContinuousOnInterval f l u)
    (hnonneg : ∀ x, x ∈ Set.Icc l u → 0 ≤ f x) (hepsilon : 0 < epsilon) :
    AbsolutelyContinuousOnInterval (fun x => (f x + epsilon) ^ q) l u := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hC0 : 0 ≤ C := by
    have h := hC l (by simpa [Set.uIcc_of_le hlu])
    exact (norm_nonneg _).trans h
  have hmem : ∀ x ∈ Set.uIcc l u, f x ∈ Set.Icc 0 C := by
    intro x hx
    constructor
    · exact hnonneg x (by simpa [Set.uIcc_of_le hlu] using hx)
    · exact (le_abs_self _).trans (hC x hx)
  have hcd : ContDiffOn ℝ 1 (fun x : ℝ => (x + epsilon) ^ q) (Set.Icc 0 C) := by
    apply (contDiffOn_id.add contDiffOn_const).rpow_const_of_ne
    intro x hx hzero
    dsimp at hzero
    linarith [hx.1]
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine ac_comp_of_lipschitzOn_image (K := K) (phi := fun x : ℝ => (x + epsilon) ^ q) hf ?_
  intro x hx y hy
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  exact hK (hmem x' hx') (hmem y' hy')

/-- The linear Gronwall inequality on an interval for an absolutely continuous
  function: `z u ≤ z l exp(∫ₗᵘ a) + ∫ₗᵘ exp(∫ₛᵘ a) c`. -/
theorem linear_gronwall_interval {z a c : ℝ → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hzac : AbsolutelyContinuousOnInterval z l u)
    (ha : MeasureTheory.IntegrableOn a (Set.Icc l u) MeasureTheory.volume)
    (hc : MeasureTheory.IntegrableOn c (Set.Icc l u) MeasureTheory.volume)
    (hderiv : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Icc l u →
      deriv z s ≤ a s * z s + c s) :
    z u ≤ z l * Real.exp (∫ r in l..u, a r) +
      ∫ s in l..u, Real.exp (∫ r in s..u, a r) * c s := by
  have haII : IntervalIntegrable a MeasureTheory.volume l u := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlu]
    exact ha
  have hcII : IntervalIntegrable c MeasureTheory.volume l u := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlu]
    exact hc
  let A : ℝ → ℝ := fun x => ∫ r in l..x, a r
  let E : ℝ → ℝ := fun x => Real.exp (-A x)
  let P : ℝ → ℝ := fun x => ∫ r in l..x, E r * c r
  let H : ℝ → ℝ := fun x => E x * z x - P x
  obtain ⟨hEAC, hEderiv⟩ := ac_exp_neg_intervalIntegral l u a hlu ha
  have hEAC' : AbsolutelyContinuousOnInterval E l u := by simpa [E, A] using hEAC
  have hEcII : IntervalIntegrable (fun r => E r * c r) MeasureTheory.volume l u := by
    simpa [mul_comm] using hcII.mul_continuousOn hEAC'.continuousOn
  have hPAC : AbsolutelyContinuousOnInterval P l u := by
    simpa [P] using hEcII.absolutelyContinuousOnInterval_intervalIntegral (c := l) (by simp)
  have hPderiv : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc l u),
      HasDerivAt P (E x * c x) x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hEcII.ae_hasDerivAt_integral] with x hx hxu
    simpa [P, Set.uIcc_of_le hlu] using hx (by simpa [Set.uIcc_of_le hlu] using hxu) l (by simp)
  have hderivIcc : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc l u),
      deriv z x ≤ a x * z x + c x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hderiv] with x hx hxu
    exact hx hxu
  have hHAC : AbsolutelyContinuousOnInterval H l u := by
    simpa [H] using hEAC'.fun_mul hzac |>.sub hPAC
  have hHderiv : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Icc l u), deriv H x ≤ 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hEderiv,
      hzac.ae_differentiableAt,
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hPderiv,
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hderivIcc] with x hE hz hP hd hxu
    have hzD : HasDerivAt z (deriv z x) x :=
      (hz (by simpa [Set.uIcc_of_le hlu] using hxu)).hasDerivAt
    have hED : HasDerivAt E (-a x * E x) x := by simpa [E, A] using hE hxu
    have hHD := (hED.mul hzD).sub (hP hxu)
    change deriv ((E * z) - P) x ≤ 0
    rw [hHD.deriv]
    have hcalc : (-a x * E x) * z x + E x * deriv z x =
        E x * (deriv z x - a x * z x) := by ring
    rw [hcalc]
    have hq : E x * (deriv z x - a x * z x) ≤ E x * c x := by
      exact mul_le_mul_of_nonneg_left (by linarith [hd hxu]) (Real.exp_pos _).le
    linarith
  have hH := ac_nonincreasing_of_ae_deriv_nonpos hlu hHAC (by simpa [H] using hHderiv)
    (show l ∈ Set.Icc l u from ⟨le_rfl, hlu⟩) (show u ∈ Set.Icc l u from ⟨hlu, le_rfl⟩) hlu
  have hcore : E u * z u ≤ z l + P u := by
    dsimp [H, E, A, P] at hH
    simp at hH
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hcore (Real.exp_pos (A u)).le
  have hcancel : Real.exp (A u) * (E u * z u) = z u := by
    dsimp [E, A]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  rw [hcancel] at hscaled
  have hkernel : Real.exp (A u) * P u =
      ∫ s in l..u, Real.exp (∫ r in s..u, a r) * c s := by
    dsimp [P]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    have hsI : s ∈ Set.Ioc l u := Set.uIoc_of_le hlu ▸ hs
    have hsl : l ≤ s := hsI.1.le
    have hsu : s ≤ u := hsI.2
    have hlsII : IntervalIntegrable a MeasureTheory.volume l s :=
      haII.mono_set (by
        rw [Set.uIcc_of_le hsl, Set.uIcc_of_le hlu]
        exact Set.Icc_subset_Icc le_rfl hsu)
    have hsuII : IntervalIntegrable a MeasureTheory.volume s u :=
      haII.mono_set (by
        rw [Set.uIcc_of_le hsu, Set.uIcc_of_le hlu]
        exact Set.Icc_subset_Icc hsl le_rfl)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hlsII hsuII
    dsimp [A]
    rw [← hsplit]
    dsimp [E, A]
    change Real.exp ((∫ x in l..s, a x) + ∫ x in s..u, a x) *
      (Real.exp (-∫ x in l..s, a x) * c s) =
      Real.exp (∫ x in s..u, a x) * c s
    have hcancelE : Real.exp (∫ x in l..s, a x) * Real.exp (-∫ x in l..s, a x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [Real.exp_add]
    calc
      (Real.exp (∫ x in l..s, a x) * Real.exp (∫ x in s..u, a x)) *
          (Real.exp (-∫ x in l..s, a x) * c s) =
          Real.exp (∫ x in s..u, a x) *
            (Real.exp (∫ x in l..s, a x) * Real.exp (-∫ x in l..s, a x)) * c s := by ring
      _ = Real.exp (∫ x in s..u, a x) * c s := by rw [hcancelE]; ring
  calc
    z u ≤ Real.exp (A u) * (z l + P u) := by simpa only [mul_add] using hscaled
    _ = z l * Real.exp (∫ r in l..u, a r) +
        ∫ s in l..u, Real.exp (∫ r in s..u, a r) * c s := by
      rw [show A u = ∫ r in l..u, a r by rfl, mul_add, hkernel]
      ring

/-- The conjugated, shifted rpow of a subsolution of the nonlinear differential
  inequality is itself a subsolution of a linear one. -/
theorem conjugated_shifted_rpow_subsolution
    {w a b : ℝ → ℝ} {l u alpha epsilon : ℝ}
    (hlu : l ≤ u) (halpha : 0 ≤ alpha) (halpha_lt : alpha < 1)
    (hwac : AbsolutelyContinuousOnInterval w l u)
    (hwnonneg : ∀ s, s ∈ Set.Icc l u -> 0 ≤ w s)
    (ha : MeasureTheory.IntegrableOn a (Set.Icc l u) MeasureTheory.volume)
    (hbnonneg : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Icc l u -> 0 ≤ b s)
    (hineq : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Icc l u ->
      (1 - alpha) * deriv w s <= a s * w s + b s * (w s) ^ alpha)
    (hepsilon : 0 < epsilon) :
    AbsolutelyContinuousOnInterval
        (fun s => (Real.exp (-(∫ r in l..s, a r) / (1 - alpha)) * w s + epsilon) ^
          (1 - alpha)) l u ∧
    ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Icc l u ->
      deriv (fun x =>
        (Real.exp (-(∫ r in l..x, a r) / (1 - alpha)) * w x + epsilon) ^
          (1 - alpha)) s <= b s * Real.exp (-∫ r in l..s, a r) := by
  let q : ℝ := 1 - alpha
  let A : ℝ → ℝ := fun s => ∫ r in l..s, a r
  let R : ℝ → ℝ := fun s => Real.exp (-A s / q)
  let v : ℝ → ℝ := fun s => R s * w s
  have hq : 0 < q := by dsimp [q]; linarith
  have ha_div : MeasureTheory.IntegrableOn (fun r => a r / q) (Set.Icc l u)
      MeasureTheory.volume := by
    simpa [div_eq_mul_inv, mul_comm] using ha.const_mul (1 / q)
  obtain ⟨hRAC, hRderiv⟩ := ac_exp_neg_intervalIntegral l u (fun r => a r / q) hlu ha_div
  have hRAC' : AbsolutelyContinuousOnInterval R l u := by
    simpa [R, A, q, div_eq_mul_inv] using hRAC
  have hvAC : AbsolutelyContinuousOnInterval v l u := hRAC'.fun_mul hwac
  have hv_nonneg : ∀ s, s ∈ Set.Icc l u → 0 ≤ v s := by
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le (hwnonneg s hs)
  constructor
  · simpa [v, R, A, q] using shifted_rpow_ac hlu hvAC hv_nonneg hepsilon
  · filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hRderiv,
      hwac.ae_differentiableAt,
      hineq, hbnonneg] with s hRD hwD hi hb hs
    have hwD' : HasDerivAt w (deriv w s) s :=
      (hwD (by simpa [Set.uIcc_of_le hlu] using hs)).hasDerivAt
    have hRD' : HasDerivAt R (-(a s / q) * R s) s := by
      simpa [R, A, q, div_eq_mul_inv] using hRD hs
    have hvD : HasDerivAt v ((-(a s / q) * R s) * w s + R s * deriv w s) s :=
      hRD'.mul hwD'
    have hzD := (hvD.const_add epsilon).rpow_const (p := q)
      (Or.inl (by linarith [hv_nonneg s hs] : epsilon + v s ≠ 0))
    have hv_deriv : deriv v s = R s * (deriv w s - (a s / q) * w s) := by
      rw [hvD.deriv]
      ring
    have hforce : R s * b s * (w s ^ alpha) =
        b s * (R s ^ q) * (v s ^ alpha) := by
      change R s * b s * w s ^ alpha = b s * R s ^ q * ((R s * w s) ^ alpha)
      rw [Real.mul_rpow (Real.exp_pos _).le (hwnonneg s hs)]
      have hRsplit : R s ^ q * R s ^ alpha = R s := by
        rw [← Real.rpow_add (Real.exp_pos _)]
        have hsum : q + alpha = 1 := by dsimp [q]; linarith
        rw [hsum, Real.rpow_one]
      calc
        R s * b s * w s ^ alpha = b s * (R s ^ q * R s ^ alpha) * w s ^ alpha := by
          rw [hRsplit]
          ring
        _ = b s * R s ^ q * (R s ^ alpha * w s ^ alpha) := by ring
    have hRq : R s ^ q = Real.exp (-A s) := by
      dsimp [R]
      exact exp_neg_div_rpow hq
    have hvineq : q * deriv v s ≤ b s * (R s ^ q) * (v s ^ alpha) := by
      rw [hv_deriv]
      have hq' : q = 1 - alpha := rfl
      rw [hq']
      calc
        (1 - alpha) * (R s * (deriv w s - (a s / q) * w s))
            = R s * ((1 - alpha) * deriv w s - a s * w s) := by
                dsimp [R]; field_simp [ne_of_gt hq]; ring
        _ ≤ R s * (b s * w s ^ alpha) := by
              gcongr
              linarith [hi hs]
        _ = b s * (R s ^ q) * (v s ^ alpha) := by
              rw [← hforce]
              ring
    change deriv (fun x => (v x + epsilon) ^ q) s ≤ b s * Real.exp (-A s)
    rw [show (fun x => (v x + epsilon) ^ q) = (fun x => (epsilon + v x) ^ q) by
      funext x; rw [add_comm], hzD.deriv]
    have hbase : 0 < v s + epsilon := by linarith [hv_nonneg s hs]
    have hpowpos : 0 < (v s + epsilon) ^ alpha := Real.rpow_pos_of_pos hbase _
    have hratio := rpow_ratio_le_one (hv_nonneg s hs) halpha hepsilon
    have hcoeff : 0 ≤ b s * R s ^ q := by
      exact mul_nonneg (hb hs) (Real.rpow_nonneg (Real.exp_pos _).le _)
    have hmain : q * ((v s + epsilon) ^ (q - 1) * deriv v s) ≤ b s * R s ^ q := by
      rw [show q - 1 = -alpha by dsimp [q]; ring]
      have hmul := mul_le_mul_of_nonneg_right hvineq
        (Real.rpow_nonneg hbase.le (-alpha))
      calc
        q * ((v s + epsilon) ^ (-alpha) * deriv v s) =
            (q * deriv v s) * (v s + epsilon) ^ (-alpha) := by ring
        _ ≤ (b s * R s ^ q) * (v s ^ alpha * (v s + epsilon) ^ (-alpha)) := by
              convert hmul using 1; ring
        _ ≤ (b s * R s ^ q) * 1 := mul_le_mul_of_nonneg_left hratio hcoeff
        _ = b s * R s ^ q := by ring
    calc
      ((-(a s / q) * R s * w s) + R s * deriv w s) * q *
          (epsilon + v s) ^ (q - 1) =
          q * ((v s + epsilon) ^ (q - 1) * deriv v s) := by
            rw [hv_deriv]
            rw [add_comm epsilon]
            ring
      _ ≤ b s * R s ^ q := hmain
      _ = b s * Real.exp (-A s) := by rw [hRq]

/-- Lemma 2.6 (nonlinear Gronwall inequality): Let `T > 0`, `a, b ∈ L¹(t₀,t₀+T;ℝ)`
  with `b(t) ≥ 0` for a.e. `t`, `0 ≤ α < 1`, and let `w : [t₀,t₀+T] → ℝ₊` be
  absolutely continuous satisfying `(1-α) w'(t) ≤ a(t) w(t) + b(t) w^α(t)` for
  a.e. `t ∈ [t₀,t₀+T]`. Then for all `t ∈ [t₀,t₀+T]`,
  `w^{1-α}(t) ≤ w^{1-α}(t₀) e^{∫_{t₀}^t a(τ) dτ} + ∫_{t₀}^t e^{∫_s^t a(τ) dτ} b(s) ds`. -/
theorem nonlinear_gronwall_inequality {w a b : ℝ → ℝ} {t₀ T α : ℝ} (hT : 0 < T)
    (hα₁ : 0 ≤ α) (hα₂ : α < 1)
    (hac : AbsolutelyContinuousOnInterval w t₀ (t₀ + T))
    (hw_nonneg : ∀ t, t ∈ Set.Icc t₀ (t₀ + T) → 0 ≤ w t)
    (ha_int : MeasureTheory.IntegrableOn a (Set.Icc t₀ (t₀ + T)) MeasureTheory.volume)
    (hb_int : MeasureTheory.IntegrableOn b (Set.Icc t₀ (t₀ + T)) MeasureTheory.volume)
    (hb_nonneg : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc t₀ (t₀ + T) → 0 ≤ b t)
    (hineq : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc t₀ (t₀ + T) →
      (1 - α) * deriv w t ≤ a t * w t + b t * (w t) ^ α) :
    ∀ t : ℝ, t₀ ≤ t → t ≤ t₀ + T →
      w t ^ (1 - α) ≤ w t₀ ^ (1 - α) * Real.exp (∫ τ in t₀..t, a τ) +
        ∫ s in t₀..t, Real.exp (∫ τ in s..t, a τ) * b s := by
  intro t ht₀ htT
  have hq : 0 < 1 - α := by linarith
  have hq0 : 0 ≤ 1 - α := hq.le
  have hle : t₀ ≤ t₀ + T := by linarith
  have ht : t ∈ Set.Icc t₀ (t₀ + T) := ⟨ht₀, htT⟩
  have hsub : Set.Icc t₀ t ⊆ Set.Icc t₀ (t₀ + T) := by
    intro s hs
    exact ⟨hs.1, hs.2.trans htT⟩
  have ha_t : MeasureTheory.IntegrableOn a (Set.Icc t₀ t) MeasureTheory.volume :=
    ha_int.mono_set hsub
  have hb_t : MeasureTheory.IntegrableOn b (Set.Icc t₀ t) MeasureTheory.volume :=
    hb_int.mono_set hsub
  have hw_t : 0 ≤ w t := hw_nonneg t ht
  have hw_0 : 0 ≤ w t₀ := hw_nonneg t₀ ⟨le_rfl, hle⟩
  have hshifted_ac : ∀ ε : ℝ, 0 < ε →
      AbsolutelyContinuousOnInterval (fun s => (w s + ε) ^ (1 - α)) t₀ t := by
    intro ε hε
    exact shifted_rpow_ac ht₀ (hac.mono (by
      rw [Set.uIcc_of_le ht₀, Set.uIcc_of_le hle]
      exact hsub))
      (fun s hs => hw_nonneg s (hsub hs)) hε
  have hregularized : ∀ ε : ℝ, 0 < ε →
      (Real.exp (-(∫ r in t₀..t, a r) / (1 - α)) * w t + ε) ^ (1 - α) ≤
        (w t₀ + ε) ^ (1 - α) +
          ∫ s in t₀..t, b s * Real.exp (-∫ r in t₀..s, a r) := by
    intro ε hε
    obtain ⟨hzac, hzderiv⟩ := conjugated_shifted_rpow_subsolution ht₀ hα₁ hα₂
      (hac.mono (by
        rw [Set.uIcc_of_le ht₀, Set.uIcc_of_le hle]
        exact hsub))
      (fun s hs => hw_nonneg s (hsub hs)) ha_t
      (by filter_upwards [hb_nonneg] with s hs hst; exact hs (hsub hst))
      (by filter_upwards [hineq] with s hs hst; exact hs (hsub hst)) hε
    have haII : IntervalIntegrable a MeasureTheory.volume t₀ t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht₀).mpr ha_t
    have hbII : IntervalIntegrable b MeasureTheory.volume t₀ t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht₀).mpr hb_t
    obtain ⟨hEAC, _⟩ := ac_exp_neg_intervalIntegral t₀ t a ht₀ ha_t
    have hforce : MeasureTheory.IntegrableOn
        (fun s => b s * Real.exp (-∫ r in t₀..s, a r)) (Set.Icc t₀ t)
        MeasureTheory.volume := by
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le ht₀]
      simpa [mul_comm] using hbII.mul_continuousOn hEAC.continuousOn
    have hG := linear_gronwall_interval (z := fun s =>
        (Real.exp (-(∫ r in t₀..s, a r) / (1 - α)) * w s + ε) ^ (1 - α))
      (a := fun _ : ℝ => 0) (c := fun s => b s * Real.exp (-∫ r in t₀..s, a r))
      ht₀ hzac (by simp) hforce (by simpa using hzderiv)
    simpa using hG
  let q : ℝ := 1 - α
  let A : ℝ → ℝ := fun s => ∫ r in t₀..s, a r
  let R : ℝ → ℝ := fun s => Real.exp (-A s / q)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0))
  have htend_left : Filter.Tendsto (fun n => (R t * w t + ε n) ^ q) Filter.atTop
      (nhds ((R t * w t) ^ q)) := by
    have hsum : Filter.Tendsto (fun n : ℕ => R t * w t + ε n) Filter.atTop
        (nhds (R t * w t)) := by
      simpa using ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => R t * w t) Filter.atTop
        (nhds (R t * w t))).add hεlim)
    exact (Real.continuousAt_rpow_const (R t * w t) q (Or.inr hq0)).tendsto.comp hsum
  have htend_zero : Filter.Tendsto (fun n => (w t₀ + ε n) ^ q) Filter.atTop
      (nhds (w t₀ ^ q)) := by
    have hsum : Filter.Tendsto (fun n : ℕ => w t₀ + ε n) Filter.atTop
        (nhds (w t₀)) := by
      simpa using ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => w t₀) Filter.atTop
        (nhds (w t₀))).add hεlim)
    exact (Real.continuousAt_rpow_const (w t₀) q (Or.inr hq0)).tendsto.comp hsum
  let J : ℝ := ∫ s in t₀..t, b s * Real.exp (-A s)
  have hconj : (R t * w t) ^ q ≤ w t₀ ^ q + J := by
    refine le_of_tendsto_of_tendsto htend_left
      (htend_zero.add (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => J) Filter.atTop (nhds J))) ?_
    filter_upwards with n
    simpa [q, A, R, ε, J] using hregularized (ε n) (by positivity)
  have hRq (s : ℝ) : R s ^ q = Real.exp (-A s) := by
    dsimp [R]
    exact exp_neg_div_rpow (by simpa [q] using hq)
  have hRpow_t : (R t * w t) ^ q = Real.exp (-A t) * w t ^ q := by
    rw [Real.mul_rpow (Real.exp_pos _).le hw_t, hRq]
  have hleftcancel : Real.exp (A t) * (R t * w t) ^ q = w t ^ q := by
    rw [hRpow_t, ← mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  have hscaled := mul_le_mul_of_nonneg_left hconj (Real.exp_pos (A t)).le
  have haII : IntervalIntegrable a MeasureTheory.volume t₀ t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht₀).mpr ha_t
  have hkernel : Real.exp (A t) * J =
      ∫ s in t₀..t, Real.exp (∫ r in s..t, a r) * b s := by
    dsimp [J]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    have hsI : s ∈ Set.Ioc t₀ t := Set.uIoc_of_le ht₀ ▸ hs
    have hsl : t₀ ≤ s := hsI.1.le
    have hst : s ≤ t := hsI.2
    have hlsII : IntervalIntegrable a MeasureTheory.volume t₀ s :=
      haII.mono_set (by
        rw [Set.uIcc_of_le hsl, Set.uIcc_of_le ht₀]
        exact Set.Icc_subset_Icc le_rfl hst)
    have hstII : IntervalIntegrable a MeasureTheory.volume s t :=
      haII.mono_set (by
        rw [Set.uIcc_of_le hst, Set.uIcc_of_le ht₀]
        exact Set.Icc_subset_Icc hsl le_rfl)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hlsII hstII
    dsimp [A]
    rw [← hsplit]
    change Real.exp ((∫ x in t₀..s, a x) + ∫ x in s..t, a x) *
      (b s * Real.exp (-∫ x in t₀..s, a x)) =
      Real.exp (∫ x in s..t, a x) * b s
    have hcancelE : Real.exp (∫ x in t₀..s, a x) *
        Real.exp (-∫ x in t₀..s, a x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [Real.exp_add]
    calc
      (Real.exp (∫ x in t₀..s, a x) * Real.exp (∫ x in s..t, a x)) *
          (b s * Real.exp (-∫ x in t₀..s, a x)) =
          Real.exp (∫ x in s..t, a x) *
            (Real.exp (∫ x in t₀..s, a x) * Real.exp (-∫ x in t₀..s, a x)) * b s := by ring
      _ = Real.exp (∫ x in s..t, a x) * b s := by rw [hcancelE]; ring
  simpa [q] using (calc
    w t ^ q = Real.exp (A t) * ((R t * w t) ^ q) := hleftcancel.symm
    _ ≤ Real.exp (A t) * (w t₀ ^ q + J) := hscaled
    _ = w t₀ ^ q * Real.exp (∫ τ in t₀..t, a τ) +
        ∫ s in t₀..t, Real.exp (∫ τ in s..t, a τ) * b s := by
      rw [show A t = ∫ τ in t₀..t, a τ by rfl, mul_add, hkernel]
      ring)

/-! ### Global Cauchy--Lipschitz solutions
Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/ext_thm_5 -/

/-- Global autonomous Cauchy--Lipschitz existence, isolated from the regularity
translation used in `exists_unique_global_solution_of_lipschitz`. -/
private theorem ext_thm_5_local_autonomous_solution_of_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (F : E → E)
    {K : NNReal} (hK : LipschitzWith K F) (t0 : ℝ) (x : E) :
    ∃ d : ℝ, 0 < d ∧ ∃ alpha : ℝ → E, alpha t0 = x ∧
      ∀ t ∈ Set.Ioo (t0 - d) (t0 + d), HasDerivAt alpha (F (alpha t)) t := by
  let M : ℝ := ‖F x‖ + (K : ℝ)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  let L : NNReal := Real.toNNReal M
  let d : ℝ := 1 / ((L : ℝ) + 1)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hbound : ∀ y ∈ Metric.closedBall x (1 : ℝ), ‖F y‖ ≤ L := by
    intro y hy
    have hy' : ‖y - x‖ ≤ (1 : ℝ) := by
      simpa [dist_eq_norm, norm_sub_rev] using Metric.mem_closedBall.mp hy
    rw [Real.coe_toNNReal M hM0]
    calc
      ‖F y‖ ≤ ‖F y - F x‖ + ‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * ‖y - x‖ + ‖F x‖ := by
        gcongr
        simpa [dist_eq_norm] using hK.dist_le_mul y x
      _ ≤ (K : ℝ) + ‖F x‖ := by
        gcongr
        exact mul_le_of_le_one_right NNReal.zero_le_coe hy'
      _ = M := by simp [M, add_comm]
  have htime : (L : ℝ) * max ((t0 + d) - t0) (t0 - (t0 - d)) ≤ (1 : ℝ) := by
    rw [show (t0 + d) - t0 = d by ring, show t0 - (t0 - d) = d by ring, max_self]
    dsimp [d]
    have hL : 0 ≤ (L : ℝ) := NNReal.zero_le_coe
    calc
      (L : ℝ) * (1 / ((L : ℝ) + 1)) = (L : ℝ) / ((L : ℝ) + 1) := by ring
      _ ≤ 1 := by
        rw [div_le_one (by positivity : 0 < (L : ℝ) + 1)]
        linarith
  let hPL : IsPicardLindelof (fun _ : ℝ => F)
      (tmin := t0 - d) (tmax := t0 + d)
      ⟨t0, by constructor <;> linarith⟩ x 1 0 L K :=
    IsPicardLindelof.of_time_independent hbound hK.lipschitzOnWith (by simpa using htime)
  obtain ⟨alpha, halpha0, halpha⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨d, hd, alpha, halpha0, ?_⟩
  intro t ht
  exact (halpha t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- A global Lipschitz bound implies the affine growth estimate used in the
continuation argument. -/
private theorem ext_thm_5_autonomous_affine_growth {E : Type*} [NormedAddCommGroup E]
    (F : E → E) {K : NNReal} (hK : LipschitzWith K F) (z : E) :
    ‖F z‖ ≤ ‖F 0‖ + (K : ℝ) * ‖z‖ := by
  calc
    ‖F z‖ ≤ ‖F z - F 0‖ + ‖F 0‖ := norm_le_norm_sub_add _ _
    _ ≤ (K : ℝ) * ‖z - 0‖ + ‖F 0‖ := by
      gcongr
      simpa [dist_eq_norm] using hK.dist_le_mul z 0
    _ = ‖F 0‖ + (K : ℝ) * ‖z‖ := by simp [add_comm]

/-- Grönwall's estimate for a partial autonomous right solution. -/
private theorem ext_thm_5_autonomous_partial_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → E) {K : NNReal} (hK : LipschitzWith K F)
    (T s : ℝ) (Z0 : E) (_hsT : s ∈ Set.Icc 0 T) {α : ℝ → E}
    (hα0 : α 0 = Z0) (hα : ContinuousOn α (Set.Icc 0 s))
    (hα' : ∀ q ∈ Set.Ico 0 s, HasDerivWithinAt α (F (α q)) (Set.Ici q) q) :
    ∀ q ∈ Set.Icc 0 s,
      ‖α q‖ ≤ gronwallBound ‖Z0‖ (K : ℝ) ‖F 0‖ q := by
  have hbound := norm_le_gronwallBound_of_norm_deriv_right_le hα hα'
    (δ := ‖Z0‖) (K := (K : ℝ)) (ε := ‖F 0‖) (by simp [hα0])
    (fun q _ => by simpa [add_comm] using ext_thm_5_autonomous_affine_growth F hK (α q))
  simpa using hbound

/-- A uniformly bounded state admits one Picard step of a prescribed length. -/
private theorem ext_thm_5_autonomous_fixed_step {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : E → E) {K : NNReal}
    (hK : LipschitzWith K F) (T R A s δ : ℝ) (hs : s ∈ Set.Icc 0 T)
    (hA : 0 ≤ A) (hAdef : A = max 1 (‖F 0‖ + (K : ℝ) * (R + 1)))
    (hδ : 0 < δ) (hAδ : A * δ ≤ 1) (x : E) (hxR : ‖x‖ ≤ R) :
    ∃ γ : ℝ → E, γ s = x ∧ ∀ q ∈ Set.Icc s (min T (s + δ)),
      HasDerivWithinAt γ (F (γ q)) (Set.Icc s (min T (s + δ))) q := by
  have hse : s ≤ min T (s + δ) := le_min hs.2 (by linarith)
  let hPL : IsPicardLindelof (fun _ : ℝ => F) (tmin := s)
      (tmax := min T (s + δ)) ⟨s, le_rfl, hse⟩ x 1 0
      (Real.toNNReal A) K := by
    apply IsPicardLindelof.of_time_independent
    · intro z hz
      have hzx : ‖z - x‖ ≤ 1 := by
        simpa [dist_eq_norm, norm_sub_rev] using Metric.mem_closedBall.mp hz
      have hnz : ‖z‖ ≤ R + 1 := by
        calc
          ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ R + 1 := by linarith
      rw [Real.coe_toNNReal A hA]
      calc
        ‖F z‖ ≤ ‖F 0‖ + (K : ℝ) * ‖z‖ := ext_thm_5_autonomous_affine_growth F hK z
        _ ≤ ‖F 0‖ + (K : ℝ) * (R + 1) := by gcongr
        _ ≤ A := by rw [hAdef]; exact le_max_right _ _
    · exact hK.lipschitzOnWith
    · rw [show s - s = 0 by ring, max_eq_left (sub_nonneg.mpr hse)]
      rw [Real.coe_toNNReal A hA]
      norm_num
      have htop : min T (s + δ) - s ≤ δ := by
        linarith [min_le_right T (s + δ)]
      exact (mul_le_mul_of_nonneg_left htop hA).trans (by simpa using hAδ)
  obtain ⟨γ, hγ0, hγ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨γ, hγ0, hγ⟩

private theorem ext_thm_5_autonomous_Icc_deriv_to_Ici {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b q : ℝ} {f' : E}
    (hq : q ∈ Set.Ico a b) (h : HasDerivWithinAt f f' (Set.Icc a b) q) :
    HasDerivWithinAt f f' (Set.Ici q) q := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Set.Iio b, Iio_mem_nhds hq.2, ?_⟩
  intro x hx
  exact ⟨hq.1.trans hx.2, hx.1.le⟩

private theorem ext_thm_5_autonomous_paste_continuousOn {E : Type*} [TopologicalSpace E]
    {a s b : ℝ} (_has : a ≤ s) (_hsb : s ≤ b) {f g : ℝ → E}
    (hf : ContinuousOn f (Set.Icc a s)) (hg : ContinuousOn g (Set.Icc s b))
    (hfg : f s = g s) :
    ContinuousOn (Set.piecewise (Set.Iic s) f g) (Set.Icc a b) := by
  apply ContinuousOn.piecewise (s := Set.Icc a b)
  · intro x hx
    rw [frontier_Iic] at hx
    have : x = s := by simpa using hx.2
    subst x
    exact hfg
  · rw [closure_Iic]
    apply hf.mono
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  · have hclosure : closure (Set.Iic s)ᶜ = Set.Ici s := by
      rw [closure_compl, interior_Iic]
      ext x
      simp
    rw [hclosure]
    apply hg.mono
    intro x hx
    exact ⟨hx.2, hx.1.2⟩

private theorem ext_thm_5_autonomous_paste_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → E) {a s b : ℝ} (has : a ≤ s) (hsb : s < b)
    {f g : ℝ → E} (hf : ContinuousOn f (Set.Icc a s))
    (hf' : ∀ q ∈ Set.Ico a s, HasDerivWithinAt f (F (f q)) (Set.Ici q) q)
    (hg : ContinuousOn g (Set.Icc s b))
    (hg' : ∀ q ∈ Set.Ico s b, HasDerivWithinAt g (F (g q)) (Set.Ici q) q)
    (hfg : f s = g s) : ∃ u : ℝ → E, u a = f a ∧
      ContinuousOn u (Set.Icc a b) ∧
      ∀ q ∈ Set.Ico a b, HasDerivWithinAt u (F (u q)) (Set.Ici q) q := by
  let u : ℝ → E := Set.piecewise (Set.Iic s) f g
  have hu : ContinuousOn u (Set.Icc a b) :=
    ext_thm_5_autonomous_paste_continuousOn has hsb.le hf hg hfg
  refine ⟨u, by simp [u, has], hu, ?_⟩
  intro q hq
  rcases lt_trichotomy q s with hqs | hqs | hsq
  · have heq : u =ᶠ[nhdsWithin q (Set.Ici q)] f := by
      filter_upwards [show Set.Iio s ∈ nhdsWithin q (Set.Ici q) from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hqs)] with x hx
      change x < s at hx
      simp [u, hx.le]
    have hval : u q = f q := by simp [u, hqs.le]
    simpa [hval] using (hf' q ⟨hq.1, hqs⟩).congr_of_eventuallyEq heq
  · subst q
    have heq : u =ᶠ[nhdsWithin s (Set.Ici s)] g := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      change s ≤ x at hx
      rcases hx.eq_or_lt with rfl | hlt
      · simp [u, hfg]
      · simp [u, not_le_of_gt hlt]
    have hval : u s = g s := by simp [u, hfg]
    simpa [hval] using (hg' s ⟨le_rfl, hsb⟩).congr_of_eventuallyEq heq
  · have heq : u =ᶠ[nhdsWithin q (Set.Ici q)] g := by
      filter_upwards [show Set.Ioi s ∈ nhdsWithin q (Set.Ici q) from
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hsq)] with x hx
      change s < x at hx
      simp [u, not_le_of_gt hx]
    have hval : u q = g q := by simp [u, not_le_of_gt hsq]
    simpa [hval] using (hg' q ⟨hsq.le, hq.2⟩).congr_of_eventuallyEq heq

/-- One mesh step, preserving the common Grönwall bound. -/
private theorem ext_thm_5_autonomous_mesh_extend {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : E → E) {K : NNReal}
    (hK : LipschitzWith K F) (T R A s δ : ℝ) (Z0 : E)
    (hs : s ∈ Set.Icc 0 T) (hA0 : 0 ≤ A)
    (hAdef : A = max 1 (‖F 0‖ + (K : ℝ) * (R + 1)))
    (hδ : 0 < δ) (hAδ : A * δ ≤ 1)
    (hR : R = gronwallBound ‖Z0‖ (K : ℝ) ‖F 0‖ T)
    {α : ℝ → E} (hα0 : α 0 = Z0) (hα : ContinuousOn α (Set.Icc 0 s))
    (hα' : ∀ q ∈ Set.Ico 0 s, HasDerivWithinAt α (F (α q)) (Set.Ici q) q)
    (hαR : ∀ q ∈ Set.Icc 0 s, ‖α q‖ ≤ R) :
    ∃ β : ℝ → E, β 0 = Z0 ∧ ContinuousOn β (Set.Icc 0 (min T (s + δ))) ∧
      (∀ q ∈ Set.Ico 0 (min T (s + δ)),
        HasDerivWithinAt β (F (β q)) (Set.Ici q) q) ∧
      ∀ q ∈ Set.Icc 0 (min T (s + δ)), ‖β q‖ ≤ R := by
  by_cases hsT : s = T
  · subst s
    have he : min T (T + δ) = T := min_eq_left (by linarith)
    refine ⟨α, hα0, ?_, ?_, ?_⟩
    · simpa [he] using hα
    · simpa [he] using hα'
    · simpa [he] using hαR
  · have hslt : s < T := lt_of_le_of_ne hs.2 hsT
    have hse : s < min T (s + δ) := lt_min hslt (by linarith)
    obtain ⟨γ, hγs, hγ⟩ := ext_thm_5_autonomous_fixed_step F hK T R A s δ hs hA0 hAdef hδ hAδ
      (α s) (hαR s ⟨hs.1, le_rfl⟩)
    have hγcont : ContinuousOn γ (Set.Icc s (min T (s + δ))) :=
      HasDerivWithinAt.continuousOn hγ
    have hγright : ∀ q ∈ Set.Ico s (min T (s + δ)),
        HasDerivWithinAt γ (F (γ q)) (Set.Ici q) q := by
      intro q hq
      exact ext_thm_5_autonomous_Icc_deriv_to_Ici hq (hγ q ⟨hq.1, hq.2.le⟩)
    obtain ⟨β, hβ0, hβ, hβ'⟩ :=
      ext_thm_5_autonomous_paste_right F hs.1 hse hα hα' hγcont hγright hγs.symm
    refine ⟨β, hβ0.trans hα0, hβ, hβ', ?_⟩
    intro q hq
    have hbound := ext_thm_5_autonomous_partial_bound F hK T (min T (s + δ)) Z0
      ⟨hs.1.trans hse.le, min_le_left _ _⟩ (by simpa using hβ0.trans hα0) hβ hβ' q hq
    rw [hR]
    refine hbound.trans ?_
    apply gronwallBound_mono (norm_nonneg Z0) (norm_nonneg (F 0)) NNReal.zero_le_coe
    linarith [hq.2, min_le_left T (s + δ)]

/-- The mesh construction produces an autonomous solution on every compact
forward interval. -/
private theorem ext_thm_5_autonomous_exists_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : E → E) {K : NNReal}
    (hK : LipschitzWith K F) (T : ℝ) (hT : 0 ≤ T) (Z0 : E) :
    ∃ α : ℝ → E, α 0 = Z0 ∧ ContinuousOn α (Set.Icc 0 T) ∧
      ∀ q ∈ Set.Ico 0 T, HasDerivWithinAt α (F (α q)) (Set.Ici q) q := by
  let R : ℝ := gronwallBound ‖Z0‖ (K : ℝ) ‖F 0‖ T
  have hR0 : ‖Z0‖ ≤ R := by
    calc
      ‖Z0‖ = gronwallBound ‖Z0‖ (K : ℝ) ‖F 0‖ 0 := (gronwallBound_x0 _ _ _).symm
      _ ≤ gronwallBound ‖Z0‖ (K : ℝ) ‖F 0‖ T :=
        gronwallBound_mono (norm_nonneg _) (norm_nonneg _) NNReal.zero_le_coe hT
  let A : ℝ := max 1 (‖F 0‖ + (K : ℝ) * (R + 1))
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hA0 : 0 ≤ A := hApos.le
  let δ : ℝ := min 1 (1 / A)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (one_div_pos.mpr hApos)
  have hAδ : A * δ ≤ 1 := by
    calc
      A * δ ≤ A * (1 / A) := mul_le_mul_of_nonneg_left (min_le_right _ _) hA0
      _ = 1 := by field_simp [ne_of_gt hApos]
  let s : ℕ → ℝ := fun n => min T ((n : ℝ) * δ)
  have hs_mem (n : ℕ) : s n ∈ Set.Icc 0 T := by
    dsimp [s]
    constructor
    · apply le_min hT
      positivity
    · exact min_le_left _ _
  have hs_zero : s 0 = 0 := by simp [s, min_eq_right hT]
  have hs_succ (n : ℕ) : min T (s n + δ) = s (n + 1) := by
    dsimp [s]
    rcases le_total T ((n : ℝ) * δ) with h | h
    · have hnext : T ≤ ((n + 1 : ℕ) : ℝ) * δ := by
        have : (n : ℝ) * δ ≤ ((n + 1 : ℕ) : ℝ) * δ := by
          norm_num [Nat.cast_add]
          nlinarith [hδ.le]
        linarith
      rw [min_eq_left h, min_eq_left (by linarith), min_eq_left hnext]
    · rw [min_eq_right h]
      congr 1
      push_cast
      ring
  have hpackages : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = Z0 ∧ ContinuousOn α (Set.Icc 0 (s n)) ∧
      (∀ q ∈ Set.Ico 0 (s n), HasDerivWithinAt α (F (α q)) (Set.Ici q) q) ∧
      ∀ q ∈ Set.Icc 0 (s n), ‖α q‖ ≤ R := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => Z0, rfl, continuous_const.continuousOn, ?_, ?_⟩
      · simp [hs_zero]
      · intro q hq
        simpa using hR0
    | succ n ih =>
      obtain ⟨α, hα0, hα, hα', hαR⟩ := ih
      obtain ⟨β, hβ0, hβ, hβ', hβR⟩ := ext_thm_5_autonomous_mesh_extend F hK T R A (s n) δ Z0
        (hs_mem n) hA0 rfl hδ hAδ rfl hα0 hα hα' hαR
      rw [hs_succ n] at hβ hβ' hβR
      exact ⟨β, hβ0, hβ, hβ', hβR⟩
  let N : ℕ := ⌈T / δ⌉₊
  have hN : T ≤ (N : ℝ) * δ := by
    exact (div_le_iff₀ hδ).mp (Nat.le_ceil _)
  have hsN : s N = T := by
    dsimp [s]
    exact min_eq_left hN
  obtain ⟨α, hα0, hα, hα', _⟩ := hpackages N
  refine ⟨α, hα0, ?_, ?_⟩
  · simpa [hsN] using hα
  · simpa [hsN] using hα'

private theorem ext_thm_5_autonomous_eqOn_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) {K : NNReal} (hK : LipschitzWith K F) {T : ℝ} {α β : ℝ → E}
    (hα : ContinuousOn α (Set.Icc 0 T))
    (hα' : ∀ q ∈ Set.Ico 0 T, HasDerivWithinAt α (F (α q)) (Set.Ici q) q)
    (hβ : ContinuousOn β (Set.Icc 0 T))
    (hβ' : ∀ q ∈ Set.Ico 0 T, HasDerivWithinAt β (F (β q)) (Set.Ici q) q)
    (h0 : α 0 = β 0) : Set.EqOn α β (Set.Icc 0 T) := by
  apply ODE_solution_unique_of_mem_Icc_right (fun _ _ => hK.lipschitzOnWith)
    hα hα' (fun _ _ => Set.mem_univ _) hβ hβ' (fun _ _ => Set.mem_univ _) h0

private theorem ext_thm_5_autonomous_ceil_cover (q : ℝ) : q < ((⌈q⌉₊ + 1 : ℕ) : ℝ) := by
  have hceil : q ≤ (⌈q⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : (⌈q⌉₊ : ℝ) < ((⌈q⌉₊ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self ⌈q⌉₊
  linarith

private theorem ext_thm_5_autonomous_global_local_agreement {E : Type*} (α : ℕ → ℝ → E)
    (hcompat : ∀ {m n : ℕ}, m ≤ n → Set.EqOn (α m) (α n) (Set.Icc 0 (m : ℝ)))
    (B : ℝ) (N : ℕ) (hBN : B + 1 ≤ (N : ℝ)) :
    Set.EqOn (fun q : ℝ => α (⌈q⌉₊ + 1) q) (α N) (Set.Icc 0 B) := by
  intro q hq
  let m : ℕ := ⌈q⌉₊ + 1
  have hm : q < (m : ℝ) := ext_thm_5_autonomous_ceil_cover q
  have hN : q < (N : ℝ) := by linarith [hq.2, hBN, lt_add_one B]
  rcases le_total m N with hmn | hNm
  · exact hcompat hmn ⟨hq.1, hm.le⟩
  · exact (hcompat hNm ⟨hq.1, hN.le⟩).symm

private theorem ext_thm_5_autonomous_hasDerivWithinAt_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} {α g : ℝ → E} (_hab : a ≤ b)
    (hα : ContinuousOn α (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt α (g x) (Set.Ici x) x) :
    ∀ x ∈ Set.Icc a b, HasDerivWithinAt α (g x) (Set.Icc a b) x := by
  intro x hx
  have heq (y : ℝ) (hy : y ∈ Set.Icc a b) : α y = α a + ∫ z in a..y, g z := by
    have hInt : ∫ z in a..y, g z = α y - α a := by
      apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hy.1
      · exact hα.mono fun z hz => ⟨hz.1, hz.2.trans hy.2⟩
      · intro z hz
        have hz' : z ∈ Set.Ioo a y := by simpa [min_eq_left hy.1, max_eq_right hy.1] using hz
        exact (hderiv z ⟨hz'.1.le, lt_of_lt_of_le hz'.2 hy.2⟩).Ioi_of_Ici
      · have hgy : ContinuousOn g (Set.Icc a y) := hg.mono fun z hz => ⟨hz.1, hz.2.trans hy.2⟩
        have hgy' : ContinuousOn g (Set.uIcc a y) := by simpa [Set.uIcc_of_le hy.1] using hgy
        exact hgy'.intervalIntegrable
    rw [hInt]
    abel
  have hP : HasDerivWithinAt (fun y : ℝ => α a + ∫ z in a..y, g z) (g x) (Set.Icc a b) x := by
    apply HasDerivWithinAt.const_add
    letI : Fact (x ∈ Set.Icc a b) := ⟨hx⟩
    apply intervalIntegral.integral_hasDerivWithinAt_right
    · have hgx : ContinuousOn g (Set.Icc a x) := hg.mono fun z hz => ⟨hz.1, hz.2.trans hx.2⟩
      have hgx' : ContinuousOn g (Set.uIcc a x) := by simpa [Set.uIcc_of_le hx.1] using hgx
      exact hgx'.intervalIntegrable
    · exact hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x
    · exact hg x hx
  apply hP.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact heq y hy
  · exact heq x hx

private theorem ext_thm_5_autonomous_forward_global {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : E → E) {K : NNReal}
    (hK : LipschitzWith K F) (Z0 : E) {d : ℝ} (hd : 0 < d) (a : ℝ → E)
    (ha0 : a 0 = Z0) (ha : ∀ t ∈ Set.Ioo (-d) d, HasDerivAt a (F (a t)) t) :
    ∃ U : ℝ → E, U 0 = Z0 ∧ ContinuousOn U (Set.Ici 0) ∧
      (∀ t ∈ Set.Ioi 0, HasDerivAt U (F (U t)) t) ∧ ∀ t ∈ Set.Ico 0 d, U t = a t := by
  classical
  have hfinite : ∀ N : ℕ, ∃ α : ℝ → E, α 0 = Z0 ∧ ContinuousOn α (Set.Icc 0 (N : ℝ)) ∧
      ∀ q ∈ Set.Ico 0 (N : ℝ), HasDerivWithinAt α (F (α q)) (Set.Ici q) q := by
    intro N
    exact ext_thm_5_autonomous_exists_Icc F hK (N : ℝ) (Nat.cast_nonneg N) Z0
  choose α hα0 hαcont hαderiv using hfinite
  have hcompat : ∀ {m n : ℕ}, m ≤ n → Set.EqOn (α m) (α n) (Set.Icc 0 (m : ℝ)) := by
    intro m n hmn
    apply ext_thm_5_autonomous_eqOn_Icc F hK (hαcont m) (hαderiv m)
    · apply (hαcont n).mono
      intro q hq
      have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      exact ⟨hq.1, hq.2.trans hmn'⟩
    · intro q hq
      have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      exact hαderiv n q ⟨hq.1, lt_of_lt_of_le hq.2 hmn'⟩
    · exact (hα0 m).trans (hα0 n).symm
  let U : ℝ → E := fun q => α (⌈q⌉₊ + 1) q
  have hlocal (B : ℝ) (N : ℕ) (hBN : B + 1 ≤ (N : ℝ)) : Set.EqOn U (α N) (Set.Icc 0 B) :=
    ext_thm_5_autonomous_global_local_agreement α hcompat B N hBN
  have hU0 : U 0 = Z0 := by simpa [U] using hα0 (⌈(0 : ℝ)⌉₊ + 1)
  have hαfull (N : ℕ) : ∀ q ∈ Set.Icc 0 (N : ℝ),
      HasDerivWithinAt (α N) (F (α N q)) (Set.Icc 0 (N : ℝ)) q := by
    apply ext_thm_5_autonomous_hasDerivWithinAt_Icc (Nat.cast_nonneg N) (hαcont N)
    · exact hK.continuous.continuousOn.comp (hαcont N) fun _ _ => Set.mem_univ _
    · exact hαderiv N
  have hUcont : ContinuousOn U (Set.Ici 0) := by
    intro q hq
    let N : ℕ := ⌈q + 2⌉₊ + 1
    have hN : q + 2 < (N : ℝ) := ext_thm_5_autonomous_ceil_cover (q + 2)
    have hBN : (q + 1) + 1 ≤ (N : ℝ) := by linarith
    have hmem : q ∈ Set.Icc 0 (N : ℝ) := ⟨hq, by linarith⟩
    have hcont : ContinuousWithinAt (α N) (Set.Ici 0) q := by
      apply (hαcont N q hmem).mono_of_mem_nhdsWithin
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio (q + 1), Iio_mem_nhds (lt_add_one q), ?_⟩
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      have hx1' : x < q + 1 := hx1
      have hx2' : 0 ≤ x := hx2
      exact ⟨hx2', by linarith⟩
    have heq : U =ᶠ[nhdsWithin q (Set.Ici 0)] α N := by
      filter_upwards [self_mem_nhdsWithin,
        show Set.Iio (q + 1) ∈ nhdsWithin q (Set.Ici 0) from mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_one q))] with x hxt hx
      exact hlocal (q + 1) N hBN ⟨hxt, hx.le⟩
    exact hcont.congr_of_eventuallyEq heq (hlocal (q + 1) N hBN ⟨hq, by linarith⟩)
  refine ⟨U, hU0, hUcont, ?_, ?_⟩
  intro t ht
  change 0 < t at ht
  let N : ℕ := ⌈t + 2⌉₊ + 1
  have hN : t + 2 < (N : ℝ) := ext_thm_5_autonomous_ceil_cover (t + 2)
  have hBN : (t + 1) + 1 ≤ (N : ℝ) := by linarith
  have hmem : t ∈ Set.Icc 0 (N : ℝ) := ⟨ht.le, by linarith⟩
  have hfin : HasDerivAt (α N) (F (α N t)) t :=
    (hαfull N t hmem).hasDerivAt (Icc_mem_nhds ht (by linarith))
  have heq : U =ᶠ[nhds t] α N := by
    filter_upwards [show Set.Ioo (t / 2) (t + 1) ∈ nhds t from Ioo_mem_nhds (by linarith) (by linarith)] with x hx
    rcases hx with ⟨hx1, hx2⟩
    exact hlocal (t + 1) N hBN ⟨by linarith, hx2.le⟩
  have hval : U t = α N t := hlocal (t + 1) N hBN ⟨ht.le, by linarith⟩
  simpa only [hval] using hfin.congr_of_eventuallyEq heq
  · intro t ht
    let N : ℕ := ⌈t + 1⌉₊ + 1
    have hN : t + 1 < (N : ℝ) := ext_thm_5_autonomous_ceil_cover (t + 1)
    have hBN : t + 1 ≤ (N : ℝ) := by linarith
    have hαa : Set.EqOn (α N) a (Set.Icc 0 t) := by
      apply ext_thm_5_autonomous_eqOn_Icc (T := t) F hK
      · exact (hαcont N).mono fun q hq => ⟨hq.1, by linarith [hq.2, hN]⟩
      · intro q hq
        exact hαderiv N q ⟨hq.1, by linarith [hq.2, hN]⟩
      · intro q hq
        exact (ha q ⟨by linarith [hd, hq.1], by linarith [hq.2, ht.2]⟩).continuousAt.continuousWithinAt
      · intro q hq
        exact (ha q ⟨by linarith [hd, hq.1], by linarith [hq.2, ht.2]⟩).hasDerivWithinAt
      · exact (hα0 N).trans ha0.symm
    exact (hlocal t N hBN ⟨ht.1, le_rfl⟩).trans (hαa ⟨ht.1, le_rfl⟩)

private theorem ext_thm_5_autonomous_neg_comp_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W : ℝ → E} {w : E} {t : ℝ}
    (hW : HasDerivAt W w (-t)) : HasDerivAt (fun s : ℝ => W (-s)) (-w) t := by
  let negTime : ℝ → ℝ := fun s => -s
  have hneg : HasDerivAt negTime (-1) t := by
    simpa [negTime] using hasDerivAt_neg t
  simpa [Function.comp_def, negTime] using hW.scomp_of_eq t hneg rfl

/-- The continuation step for a globally Lipschitz autonomous vector field. -/
theorem exists_global_solution_of_lipschitz {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (F : X → X)
    {K : NNReal} (hK : LipschitzWith K F) (Z0 : X) :
    ∃ Z : ℝ → X, Z 0 = Z0 ∧ ∀ t, HasDerivAt Z (F (Z t)) t := by
  obtain ⟨d, hd, alpha, halpha0, halpha⟩ :=
    ext_thm_5_local_autonomous_solution_of_lipschitz F hK 0 Z0
  obtain ⟨U, hU0, hUcont, hUderiv, hUalpha⟩ :=
    ext_thm_5_autonomous_forward_global F hK Z0 hd alpha halpha0 (by simpa only [zero_sub, zero_add] using halpha)
  let G : X → X := fun z => -F z
  have hG : LipschitzWith K G := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [G] using hK.dist_le_mul x y
  let arev : ℝ → X := fun t => alpha (-t)
  have harev0 : arev 0 = Z0 := by simpa [arev] using halpha0
  have harev : ∀ t ∈ Set.Ioo (-d) d, HasDerivAt arev (G (arev t)) t := by
    intro t ht
    rcases ht with ⟨ht1, ht2⟩
    have h := ext_thm_5_autonomous_neg_comp_deriv (halpha (-t) ⟨by linarith, by linarith⟩)
    simpa [arev, G] using h
  obtain ⟨W, hW0, hWcont, hWderiv, hWalpha⟩ :=
    ext_thm_5_autonomous_forward_global G hG Z0 hd arev harev0 harev
  let V : ℝ → X := fun t => W (-t)
  have hVderiv (t : ℝ) (ht : t < 0) : HasDerivAt V (F (V t)) t := by
    simpa [V, G] using ext_thm_5_autonomous_neg_comp_deriv
      (hWderiv (-t) (by simpa using neg_pos.mpr ht))
  let Z : ℝ → X := fun t => if 0 ≤ t then U t else V t
  have hZ0 : Z 0 = Z0 := by simp [Z, hU0]
  refine ⟨Z, hZ0, ?_⟩
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := (hVderiv t ht).congr_of_eventuallyEq (by
      filter_upwards [Iio_mem_nhds ht] with x hx
      change Z x = V x
      simp only [Z, if_neg (not_le_of_gt (show x < 0 from hx))])
    simpa [Z, not_le_of_gt ht] using h
  · have heq : Z =ᶠ[nhds 0] alpha := by
      filter_upwards [show Set.Ioo (-d) d ∈ nhds 0 from Ioo_mem_nhds (by linarith) hd] with x hx
      by_cases hx0 : 0 ≤ x
      · rw [show Z x = U x by simp only [Z, if_pos hx0]]
        exact hUalpha x ⟨hx0, hx.2⟩
      · rw [show Z x = V x by simp only [Z, if_neg hx0]]
        have hw := hWalpha (-x) ⟨by linarith, by linarith [hx.1]⟩
        simpa [V, arev] using hw
    simpa [hZ0, halpha0] using
      (halpha 0 ⟨by linarith, by linarith⟩).congr_of_eventuallyEq heq
  · have h := (hUderiv t ht).congr_of_eventuallyEq (by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      change Z x = U x
      simp only [Z, if_pos (show 0 ≤ x from (show 0 < x from hx).le)])
    simpa [Z, ht.le] using h

/-- Cauchy--Lipschitz--Picard theorem: a globally Lipschitz vector field on a
  Banach space has a unique global classical (C¹) solution for each initial
  value.  The paper applies this to the first-order system on `H × H`. -/
theorem exists_unique_global_solution_of_lipschitz {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X) (L : ℝ) (hL : 0 < L) (hlip : ∀ x y : X, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (x₀ : X) :
    ∃! x : ℝ → X, (Differentiable ℝ x ∧ Continuous (deriv x) ∧
      ∀ t : ℝ, deriv x t = F (x t) ∧ x 0 = x₀) := by
  have hF : LipschitzWith (Real.toNNReal L) F := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.coe_toNNReal L (le_of_lt hL)]
    simpa only [dist_eq_norm] using hlip x y
  obtain ⟨x, hx0, hxderiv⟩ := exists_global_solution_of_lipschitz F hF x₀
  have hxdiff : Differentiable ℝ x := fun t => (hxderiv t).differentiableAt
  have hxderiv_eq : deriv x = fun t => F (x t) := by
    funext t
    exact (hxderiv t).deriv
  have hxcontderiv : Continuous (deriv x) := by
    rw [hxderiv_eq]
    exact hF.continuous.comp hxdiff.continuous
  refine ⟨x, ⟨hxdiff, hxcontderiv, ?_⟩, ?_⟩
  · intro t
    rw [hxderiv_eq]
    exact ⟨rfl, hx0⟩
  · intro y hy
    rcases hy with ⟨hydiff, _, hyEq⟩
    apply ODE_solution_unique_univ (v := fun _ : ℝ => F) (s := fun _ => Set.univ)
      (fun _ => hF.lipschitzOnWith)
    · intro t
      refine ⟨?_, Set.mem_univ _⟩
      have hyderiv : deriv y t = F (y t) := (hyEq t).1
      simpa [hyderiv] using (hydiff t).hasDerivAt
    · intro t
      exact ⟨hxderiv t, Set.mem_univ _⟩
    · exact ((hyEq 0).2).trans hx0.symm

/-! ### Stability of equilibria of parametrized trajectory families
Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/def_9 -/

/-- Lyapunov stability of the equilibrium `xbar` of the parameter-`μbar`
  trajectory family: nearby initial data stay within `ε` of `xbar` forever. -/
def IsLyapunovStable {H M : Type*} [NormedAddCommGroup H] [NormedAddCommGroup M]
    (xbar : H) (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u₀, ‖u₀ - xbar‖ < δ →
    ∀ t : ℝ, 0 ≤ t → ‖trajectory μbar u₀ t - xbar‖ < ε

/-- Asymptotic stability: nearby initial data converge to the equilibrium. -/
def IsAsymptoticallyStable {H M : Type*} [NormedAddCommGroup H] [NormedAddCommGroup M]
    (xbar : H) (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ u₀, ‖u₀ - xbar‖ < δ →
    Filter.Tendsto (fun t : ℝ => ‖trajectory μbar u₀ t - xbar‖) Filter.atTop (nhds 0)

/-- Uniform (in the parameter `μ`) Lyapunov stability: the stability radius
  `δ` works for every `μ` in a `δ`-neighbourhood of `μbar`. -/
def IsUniformlyStable {H M : Type*} [NormedAddCommGroup H] [NormedAddCommGroup M]
    (xbar : H) (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ μ u₀,
    ‖μ - μbar‖ < δ → ‖u₀ - xbar‖ < δ → ∀ t : ℝ, 0 ≤ t →
      ‖trajectory μ u₀ t - xbar‖ < ε

/-- Uniform (in the parameter) asymptotic stability. -/
def IsUniformlyAsymptoticallyStable {H M : Type*} [NormedAddCommGroup H]
    [NormedAddCommGroup M] (xbar : H) (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ μ u₀,
    ‖μ - μbar‖ < δ → ‖u₀ - xbar‖ < δ →
      Filter.Tendsto (fun t : ℝ => ‖trajectory μ u₀ t - xbar‖) Filter.atTop (nhds 0)

/-! ### Time-dependent viscosity machinery

The tail kernel `Γ(t) = p(t) ∫_[t,∞) 1/p(s) ds` of the time-dependent
viscosity framework, local Cauchy--Lipschitz existence with the
`LocallyLipschitz` API, and the integral Gronwall--Bellman (sqrt) estimate.

Promoted from
`Attouch_Asymptotic_stabilization_of_inertial_gradient_dynamics_with_time_dependent_viscosity_2017`
(def_2, ext_thm_1, ext_lem_2).
-/

/-- The tail kernel `Γ(t) = p(t) ∫_[t,∞) 1/p(s) ds` of the time-dependent
  viscosity framework, represented using `volume`. -/
noncomputable def Gamma (t₀ : ℝ) (p : ℝ → ℝ)
    (hp : ∀ s ≥ t₀, 0 < p s)
    (h₀ : MeasureTheory.IntegrableOn (fun s => (p s)⁻¹) (Set.Ici t₀)) : Set.Ici t₀ → ℝ :=
  fun t ↦ p t * ∫ s, if (t : ℝ) ≤ s then (p s)⁻¹ else 0

/-- Local Cauchy--Lipschitz existence for an autonomous locally Lipschitz
  vector field: a classical solution on `(-ε, ε)` with `x 0 = x₀`. -/
theorem exists_local_solution_of_locally_lipschitz (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (f : X → X) (x₀ : X) (hf : LocallyLipschitz f) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x : ℝ → X, x 0 = x₀ ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt x (f (x t)) t := by
  obtain ⟨K, s, hs, hLip⟩ := hf x₀
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hs
  let L := K * a + ‖f x₀‖ + 1
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hBound : ∀ z ∈ Metric.closedBall x₀ (a / 2), ‖f z‖ ≤ L := by
    intro z hz
    calc
      ‖f z‖ ≤ ‖f z - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖z - x₀‖ + ‖f x₀‖ := by
        gcongr
        exact hLip.norm_sub_le (hball (Metric.mem_ball'.mpr
          (lt_of_le_of_lt (Metric.mem_closedBall'.mp hz) (half_lt_self ha))))
          (hball (Metric.mem_ball_self ha))
      _ ≤ K * a + ‖f x₀‖ := by
        gcongr
        have hz' : ‖z - x₀‖ ≤ a / 2 := by
          simpa only [dist_eq_norm, norm_sub_rev] using Metric.mem_closedBall'.mp hz
        exact hz'.trans (half_le_self ha.le)
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε : ℝ := a / L / 2 / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hPL : IsPicardLindelof (fun _ : ℝ => f)
      (tmin := -ε) (tmax := ε) ⟨0, by constructor <;> linarith⟩ x₀
      ⟨a / 2, (half_pos ha).le⟩ 0 ⟨L, hL.le⟩ K := by
    apply IsPicardLindelof.of_time_independent hBound
    · exact hLip.mono (fun z hz => hball (Metric.mem_ball'.mpr
        (lt_of_le_of_lt (Metric.mem_closedBall'.mp hz) (half_lt_self ha))))
    · simp only [sub_zero, zero_sub, neg_neg, max_self]
      simp only [NNReal.coe_zero, sub_zero]
      change L * ε ≤ a / 2
      rw [show ε = a / L / 4 by
        dsimp [ε]
        ring]
      calc
        L * (a / L / 4) = a / 4 := by field_simp
        _ ≤ a / 2 := by linarith
  obtain ⟨x, hx0, hxDeriv⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨ε, hε, x, hx0, fun t ht => ?_⟩
  exact (hxDeriv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Sqrt-energy companion of the integral Gronwall--Bellman estimate: from the
  pointwise squared bound one controls the sqrt of the accumulated energy by a
  relaxed constant plus the accumulated coefficient. -/
theorem integral_gronwall_sqrt_energy_le {a b c : ℝ} {m w : ℝ → ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hm : ContinuousOn m (Set.Icc a b)) (hw : ContinuousOn w (Set.Icc a b))
    (hmnonneg : ∀ s ∈ Set.Icc a b, 0 ≤ m s)
    (hsq : ∀ s ∈ Set.Icc a b,
      |w s| ^ 2 ≤ c ^ 2 + 2 * ∫ u in a..s, m u * |w u|)
    (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt (c ^ 2 + 2 * (∫ u in a..b, m u * |w u|) + ε) ≤
      Real.sqrt (c ^ 2 + ε) + ∫ u in a..b, m u := by
  let q : ℝ → ℝ := fun u => m u * |w u|
  have hq : ContinuousOn q (Set.Icc a b) := hm.mul hw.abs
  let qE : C(Set.Icc a b, ℝ) := ⟨fun x => q x, hq.restrict⟩
  let mE : C(Set.Icc a b, ℝ) := ⟨fun x => m x, hm.restrict⟩
  let qe : ℝ → ℝ := qE.IccExtend hab
  let me : ℝ → ℝ := mE.IccExtend hab
  have hqe : Continuous qe := (qE.IccExtend hab).continuous
  have hme : Continuous me := (mE.IccExtend hab).continuous
  have hqe_eq : ∀ s ∈ Set.Icc a b, qe s = q s := by
    intro s hs
    change Set.IccExtend hab (fun x : Set.Icc a b => q x) s = q s
    rw [Set.IccExtend_of_mem hab _ hs]
  have hme_eq : ∀ s ∈ Set.Icc a b, me s = m s := by
    intro s hs
    change Set.IccExtend hab (fun x : Set.Icc a b => m x) s = m s
    rw [Set.IccExtend_of_mem hab _ hs]
  have hq_int_eq : ∀ s ∈ Set.Icc a b, (∫ u in a..s, qe u) = ∫ u in a..s, q u := by
    intro s hs
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc a s := by simpa [Set.uIcc_of_le hs.1] using hu
    exact hqe_eq u ⟨hu'.1, hu'.2.trans hs.2⟩
  have hm_int_eq : (∫ u in a..b, me u) = ∫ u in a..b, m u := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact hme_eq u (by simpa [Set.uIcc_of_le hab] using hu)
  let A : ℝ → ℝ := fun s => c ^ 2 + 2 * ∫ u in a..s, qe u
  let B : ℝ → ℝ := fun s => Real.sqrt (A s + ε)
  have hA_cont : Continuous A := by
    dsimp [A]
    exact continuous_const.add
      (continuous_const.mul (intervalIntegral.differentiable_integral_of_continuous hqe).continuous)
  have hA_nonneg : ∀ s ∈ Set.Icc a b, 0 ≤ A s := by
    intro s hs
    have hq_nonneg : ∀ u ∈ Set.Icc a s, 0 ≤ q u := by
      intro u hu
      exact mul_nonneg (hmnonneg u ⟨hu.1, hu.2.trans hs.2⟩) (abs_nonneg _)
    have hint : 0 ≤ ∫ u in a..s, q u := intervalIntegral.integral_nonneg hs.1 hq_nonneg
    change 0 ≤ c ^ 2 + 2 * ∫ u in a..s, qe u
    rw [hq_int_eq s hs]
    nlinarith [sq_nonneg c]
  have hB_cont : ContinuousOn B (Set.Icc a b) := by
    exact (Real.continuous_sqrt.comp (hA_cont.add continuous_const)).continuousOn
  have hB_deriv : ∀ s ∈ Set.Ioo a b,
      HasDerivAt B (q s / Real.sqrt (A s + ε)) s := by
    intro s hs
    have hsI : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2.le⟩
    have hA' : HasDerivAt A (2 * qe s) s := by
      dsimp [A]
      convert (hasDerivAt_const s (c ^ 2)).add
        ((hasDerivAt_const s 2).mul (intervalIntegral.integral_hasDerivAt_right
          (hqe.intervalIntegrable a s) hqe.aestronglyMeasurable.stronglyMeasurableAtFilter
          hqe.continuousAt)) using 1 <;> simp [qe]
    have hpos : 0 < A s + ε := by linarith [hA_nonneg s hsI]
    have hroot : Real.sqrt (A s + ε) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
    convert (hA'.add_const ε).sqrt (ne_of_gt hpos) using 1
    rw [show qe s = q s from hqe_eq s hsI]
    field_simp
  have hderiv_bound : ∀ s ∈ Set.Ioo a b, q s / Real.sqrt (A s + ε) ≤ m s := by
    intro s hs
    have hsI : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2.le⟩
    have hsq' : |w s| ^ 2 ≤ A s := by simpa [A, q, hq_int_eq s hsI] using hsq s hsI
    have habs : |w s| ≤ Real.sqrt (A s + ε) := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [sq_abs, Real.sq_sqrt]
      · nlinarith [hsq', sq_abs (w s)]
      · linarith [hA_nonneg s hsI, le_of_lt hε]
    have hden : 0 < Real.sqrt (A s + ε) := Real.sqrt_pos.2 (by linarith [hA_nonneg s hsI])
    rw [← hqe_eq s hsI, ← hme_eq s hsI]
    change qe s / Real.sqrt (A s + ε) ≤ me s
    rw [hqe_eq s hsI, hme_eq s hsI]
    dsimp [q]
    exact (div_le_iff₀ hden).2 (by nlinarith [mul_le_mul_of_nonneg_left habs (hmnonneg s hsI)])
  let F : ℝ → ℝ := fun s => (∫ u in a..s, me u) - B s
  have hmono : MonotoneOn F (Set.Icc a b) := by
    change MonotoneOn (fun s => (∫ u in a..s, me u) - B s) (Set.Icc a b)
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact ((intervalIntegral.differentiable_integral_of_continuous hme).continuous.continuousOn.sub hB_cont)
    · intro s hs
      have hsi : s ∈ Set.Ioo a b := by simpa only [interior_Icc] using hs
      exact ((intervalIntegral.differentiable_integral_of_continuous hme).differentiableAt.sub
        (hB_deriv s hsi).differentiableAt).differentiableWithinAt
    · intro s hs
      have hsi : s ∈ Set.Ioo a b := by simpa only [interior_Icc] using hs
      have hd : HasDerivAt (fun z => (∫ u in a..z, me u) - B z)
          (me s - q s / Real.sqrt (A s + ε)) s :=
        (intervalIntegral.integral_hasDerivAt_right (hme.intervalIntegrable a s)
          hme.aestronglyMeasurable.stronglyMeasurableAtFilter hme.continuousAt).sub (hB_deriv s hsi)
      rw [hd.deriv]
      rw [hme_eq s ⟨hsi.1.le, hsi.2.le⟩]
      exact sub_nonneg.mpr (hderiv_bound s hsi)
  have hmain := hmono (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab) hab
  change (∫ u in a..a, me u) - B a ≤ (∫ u in a..b, me u) - B b at hmain
  simp only [intervalIntegral.integral_same] at hmain
  rw [hm_int_eq] at hmain
  have hA_b : A b = c ^ 2 + 2 * ∫ u in a..b, q u := by simp [A, hq_int_eq b (Set.right_mem_Icc.2 hab)]
  have hA_a : A a = c ^ 2 := by simp [A]
  dsimp [B] at hmain
  simp only [zero_sub] at hmain
  rw [hA_b, hA_a] at hmain
  have hfinal : Real.sqrt (c ^ 2 + 2 * (∫ u in a..b, q u) + ε) ≤
      Real.sqrt (c ^ 2 + ε) + ∫ u in a..b, m u := by
    linarith
  simpa [q] using hfinal

/-- Integral Gronwall--Bellman (sqrt) estimate: from the energy bound
  `w(t)²/2 ≤ c²/2 + ∫_δ^t m(s)·w(s) ds` on `[δ,T]` one gets the pointwise bound
  `|w(t)| ≤ c + ∫_δ^t m(s) ds`.  Distinct from `integral_gronwall_inequality`
  (linear form, different constants). -/
theorem integral_gronwall_sqrt_inequality (δ T c : ℝ) (m w : ℝ → ℝ) (hc : 0 ≤ c)
    (hm : ContinuousOn m (Set.Icc δ T)) (hw : ContinuousOn w (Set.Icc δ T))
    (hmnonneg : ∀ t ∈ Set.Icc δ T, 0 ≤ m t)
    (h : ∀ t, t ∈ Set.Icc δ T → w t ^ 2 / 2 ≤ c ^ 2 / 2 + ∫ τ in δ..t, m τ * w τ) :
    ∀ t, t ∈ Set.Icc δ T → |w t| ≤ c + ∫ τ in δ..t, m τ := by
  intro t ht
  have hδt : δ ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hsub : Set.Icc δ t ⊆ Set.Icc δ T := by
    intro x hx
    exact ⟨hx.1, hx.2.trans htT⟩
  have hm' : ContinuousOn m (Set.Icc δ t) := hm.mono hsub
  have hw' : ContinuousOn w (Set.Icc δ t) := hw.mono hsub
  have hmw_int : IntervalIntegrable (fun x => m x * w x) MeasureTheory.volume δ t :=
    (hm'.mul hw').intervalIntegrable_of_Icc hδt
  have hq_int : IntervalIntegrable (fun x => m x * |w x|) MeasureTheory.volume δ t :=
    (hm'.mul hw'.abs).intervalIntegrable_of_Icc hδt
  have h_int : (∫ x in δ..t, m x * w x) ≤ ∫ x in δ..t, m x * |w x| := by
    apply intervalIntegral.integral_mono_on hδt hmw_int hq_int
    intro x hx
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (hmnonneg x (hsub hx))
  have hsq : ∀ s ∈ Set.Icc δ t,
      |w s| ^ 2 ≤ c ^ 2 + 2 * ∫ x in δ..s, m x * |w x| := by
    intro s hs
    have hsT : s ≤ T := hs.2.trans htT
    have hsubs : Set.Icc δ s ⊆ Set.Icc δ T := by
      intro x hx
      exact ⟨hx.1, hx.2.trans hsT⟩
    have hm_s : ContinuousOn m (Set.Icc δ s) := hm.mono hsubs
    have hw_s : ContinuousOn w (Set.Icc δ s) := hw.mono hsubs
    have hcomp : (∫ x in δ..s, m x * w x) ≤ ∫ x in δ..s, m x * |w x| := by
      apply intervalIntegral.integral_mono_on hs.1
        ((hm_s.mul hw_s).intervalIntegrable_of_Icc hs.1)
        ((hm_s.mul hw_s.abs).intervalIntegrable_of_Icc hs.1)
      intro x hx
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (hmnonneg x (hsubs hx))
    have hh := h s (hsubs ⟨hs.1, le_rfl⟩)
    rw [sq_abs]
    nlinarith
  have hA_nonneg : 0 ≤ c ^ 2 + 2 * ∫ x in δ..t, m x * |w x| := by
    have hnonneg : ∀ x ∈ Set.Icc δ t, 0 ≤ m x * |w x| := by
      intro x hx
      exact mul_nonneg (hmnonneg x (hsub hx)) (abs_nonneg _)
    have hint := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hδt hnonneg
    nlinarith [sq_nonneg c]
  have habs_sqrt : |w t| ≤ Real.sqrt (c ^ 2 + 2 * ∫ x in δ..t, m x * |w x|) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt]
    · simpa only [sq_abs] using hsq t (Set.right_mem_Icc.2 hδt)
    · exact hA_nonneg
  apply le_of_forall_pos_le_add
  intro r hr
  have heps := integral_gronwall_sqrt_energy_le hδt hc hm' hw'
    (fun s hs => hmnonneg s (hsub hs)) hsq (r ^ 2) (sq_pos_of_pos hr)
  have hroot : Real.sqrt (c ^ 2 + r ^ 2) ≤ c + r := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by linarith)).mp
    rw [Real.sq_sqrt]
    · nlinarith [mul_nonneg hc (le_of_lt hr)]
    · positivity
  have henergy : Real.sqrt (c ^ 2 + 2 * (∫ x in δ..t, m x * |w x|)) ≤
      Real.sqrt (c ^ 2 + 2 * (∫ x in δ..t, m x * |w x|) + r ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r])
  linarith
