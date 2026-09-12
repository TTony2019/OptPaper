import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_1

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set Filter

/-- Select the first point of a strict-radius orbit from a fixed point of the
  comparison map. -/
private theorem exists_initial_orbit_point {X : Type*} [PseudoMetricSpace X]
    (S U : X → Set X) (D R : ENNReal)
    (hSU : ∀ x : X, Metric.hausdorffEDist (S x) (U x) ≤ D) (hDR : D < R)
    (p : X) (hp : p ∈ fixedPoints S) :
    ∃ u ∈ U p, edist p u < R := by
  change p ∈ S p at hp
  refine Metric.exists_edist_lt_of_hausdorffEDist_lt hp ?_
  calc
    Metric.hausdorffEDist (S p) (U p) ≤ D := hSU p
    _ < R := hDR

/-- Given two consecutive points of a multivalued contraction orbit, choose
the next point with a prescribed geometric ratio strictly larger than the
contraction constant. -/
private theorem exists_contractive_orbit_step {X : Type*} [MetricSpace X]
    (U : X → Set X) (K Q : ENNReal) (hKQ : K < Q)
    (hU : ∀ x y : X,
      Metric.hausdorffEDist (U x) (U y) ≤ K * edist x y)
    {a b : X} (hb : b ∈ U a) :
    ∃ c ∈ U b, edist b c ≤ Q * edist a b := by
  by_cases hab : a = b
  · subst b
    exact ⟨a, hb, by simp⟩
  · have hdpos : 0 < edist a b := edist_pos.mpr hab
    have hmul : K * edist a b < Q * edist a b := by
      exact ENNReal.mul_lt_mul_left hdpos.ne' (edist_ne_top _ _) hKQ
    have hhaus : Metric.hausdorffEDist (U a) (U b) < Q * edist a b :=
      (hU a b).trans_lt hmul
    obtain ⟨c, hc, hbc⟩ :=
      Metric.exists_edist_lt_of_hausdorffEDist_lt hb hhaus
    exact ⟨c, hc, hbc.le⟩

/-- Construct an orbit starting with `p,u₁` whose successive distances decay
geometrically with ratio `Q`. -/
private theorem exists_geometric_selection_orbit {X : Type*} [MetricSpace X]
    (U : X → Set X) (K Q : ENNReal) (hKQ : K < Q)
    (hU : ∀ x y : X,
      Metric.hausdorffEDist (U x) (U y) ≤ K * edist x y)
    (p u₁ : X) (hu₁ : u₁ ∈ U p) :
    ∃ u : ℕ → X, u 0 = p ∧ u 1 = u₁ ∧ ∀ n,
      u (n + 1) ∈ U (u n) ∧
      edist (u (n + 1)) (u (n + 2)) ≤
        Q * edist (u n) (u (n + 1)) := by
  classical
  let nextPoint : ∀ (a b : X), b ∈ U a → X := fun a b hb =>
    Classical.choose (exists_contractive_orbit_step U K Q hKQ hU hb)
  have hnextPoint : ∀ (a b : X) (hb : b ∈ U a),
      nextPoint a b hb ∈ U b ∧
        edist b (nextPoint a b hb) ≤ Q * edist a b := by
    intro a b hb
    simpa [nextPoint] using
      (Classical.choose_spec
        (exists_contractive_orbit_step U K Q hKQ hU hb))
  let State := {z : X × X // z.2 ∈ U z.1}
  let next : State → State := fun z =>
    ⟨(z.1.2, nextPoint z.1.1 z.1.2 z.2),
      (hnextPoint z.1.1 z.1.2 z.2).1⟩
  let v : ℕ → State := fun n =>
    Nat.rec ⟨(p, u₁), hu₁⟩ (fun _ z => next z) n
  let u : ℕ → X := fun n => match n with
    | 0 => p
    | n + 1 => (v n).1.2
  have hv_succ (n : ℕ) : v (n + 1) = next (v n) := by
    simp [v]
  have hv_pair (n : ℕ) : (v n).1 = (u n, u (n + 1)) := by
    cases n with
    | zero => simp [v, u]
    | succ n =>
        rw [hv_succ]
  refine ⟨u, by simp [u], by simp [u, v], ?_⟩
  intro n
  have hmem : (v n).1.2 ∈ U (v n).1.1 := (v n).2
  have hbound := hnextPoint (v n).1.1 (v n).1.2 (v n).2
  constructor
  · simpa [hv_pair n] using hmem
  · have hnextSecond :
        (v (n + 1)).1.2 = nextPoint (v n).1.1 (v n).1.2 (v n).2 := by
      rw [hv_succ]
    have hvnFst : (v n).1.1 = u n :=
      by rw [hv_pair n]
    have hvnSnd : (v n).1.2 = u (n + 1) :=
      by rw [hv_pair n]
    have hvnSuccSnd : (v (n + 1)).1.2 = u (n + 2) := by
      rw [hv_pair (n + 1)]
    rw [← hvnSnd, ← hvnSuccSnd, hnextSecond, ← hvnFst]
    exact hbound.2

/-- A geometrically controlled multivalued orbit converges to a fixed point,
with the expected geometric-series distance estimate. -/
private theorem exists_fixedPoint_edist_le_of_geometric_start
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (U : X → Set X) (K Q R : ENNReal) (hKQ : K < Q) (hQ : Q < 1)
    (hRtop : R ≠ ⊤) (hUclosed : ∀ x : X, IsClosed (U x))
    (hU : ∀ x y : X,
      Metric.hausdorffEDist (U x) (U y) ≤ K * edist x y)
    (p u₁ : X) (hu₁ : u₁ ∈ U p) (hpu₁ : edist p u₁ < R) :
    ∃ q ∈ fixedPoints U, edist p q ≤ (1 - Q)⁻¹ * R := by
  obtain ⟨u, hu0, hu1, hu⟩ :=
    exists_geometric_selection_orbit U K Q hKQ hU p u₁ hu₁
  have hstep : ∀ n : ℕ,
      edist (u n) (u (n + 1)) ≤ Q ^ n * R := by
    intro n
    induction n with
    | zero => simpa [hu0, hu1] using hpu₁.le
    | succ n ih =>
        calc
          edist (u (n + 1)) (u (n + 1 + 1)) ≤
              Q * edist (u n) (u (n + 1)) := by
            simpa [Nat.add_assoc] using (hu n).2
          _ ≤ Q * (Q ^ n * R) := mul_le_mul_left' ih Q
          _ = Q ^ (n + 1) * R := by rw [pow_succ]; ac_rfl
  have hsub : 0 < 1 - Q := tsub_pos_iff_lt.2 hQ
  have hgeomTop : (1 - Q)⁻¹ * R ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [hsub.ne']) hRtop
  have hsumTop : (∑' n : ℕ, Q ^ n * R) ≠ ⊤ := by
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    exact hgeomTop
  have hcauchy : CauchySeq u :=
    cauchySeq_of_edist_le_of_tsum_ne_top (fun n : ℕ => Q ^ n * R)
      (by simpa [Nat.succ_eq_add_one] using hstep) hsumTop
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hqShift : Tendsto (fun n : ℕ => u (n + 1)) Filter.atTop (nhds q) :=
    hq.comp (tendsto_add_atTop_nat 1)
  have hqConst : Tendsto (fun _ : ℕ => q) Filter.atTop (nhds q) :=
    tendsto_const_nhds
  have hright : Tendsto
      (fun n : ℕ => edist q (u (n + 1)) + edist (u n) q)
      Filter.atTop (nhds 0) := by
    simpa using (hqConst.edist hqShift).add (hq.edist hqConst)
  have hinfZero : Metric.infEDist q (U q) = 0 := by
    apply nonpos_iff_eq_zero.mp
    apply ge_of_tendsto hright
    filter_upwards [] with n
    calc
      Metric.infEDist q (U q) ≤
          Metric.infEDist q (U (u n)) +
            Metric.hausdorffEDist (U (u n)) (U q) :=
        Metric.infEDist_le_infEDist_add_hausdorffEDist
      _ ≤ edist q (u (n + 1)) + edist (u n) q := by
        apply add_le_add
        · exact Metric.infEDist_le_edist_of_mem (hu n).1
        · calc
            Metric.hausdorffEDist (U (u n)) (U q) ≤
                K * edist (u n) q := hU _ _
            _ ≤ 1 * edist (u n) q :=
              mul_le_mul_right' (hKQ.trans hQ).le _
            _ = edist (u n) q := one_mul _
  have hqFixed : q ∈ fixedPoints U := by
    change q ∈ U q
    exact (Metric.mem_iff_infEDist_zero_of_closed (hUclosed q)).2 hinfZero
  refine ⟨q, hqFixed, ?_⟩
  calc
    edist p q = edist (u 0) q := by rw [hu0]
    _ ≤ ∑' n : ℕ, Q ^ n * R :=
      edist_le_tsum_of_edist_le_of_tendsto₀
        (fun n : ℕ => Q ^ n * R)
        (by simpa [Nat.succ_eq_add_one] using hstep) hq
    _ = (1 - Q)⁻¹ * R := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

/-- Choose one positive slack controlling a finite product budget. -/
private theorem exists_small_product_slack (C eta : ENNReal)
    (hC : 0 < C) (hCtop : C ≠ ⊤) (heta : 0 < eta) :
    ∃ sigma : ENNReal, 0 < sigma ∧ sigma ≤ 1 ∧ sigma * C ≤ eta := by
  let sigma : ENNReal := min 1 (eta / C)
  have hetaC : 0 < eta / C := ENNReal.div_pos heta.ne' hCtop
  have hsigma : 0 < sigma := lt_min (by norm_num) hetaC
  refine ⟨sigma, hsigma, min_le_left _ _, ?_⟩
  have hle : sigma ≤ eta / C := min_le_right _ _
  exact (ENNReal.le_div_iff_mul_le (Or.inl hC.ne') (Or.inl hCtop)).mp hle

/-- The one-sided form of Lim's multivalued contraction estimate.  The
  strict-radius selection above is the first step of the geometric orbit used
  to prove this bound. -/
private theorem one_sided_lims_bound {X : Type*} [MetricSpace X] [CompleteSpace X]
    (S U : X → Set X) (K D : ENNReal) (hK : K < 1) (hD : D ≠ ⊤)
    (hSclosed : ∀ x : X, IsClosed (S x)) (hSne : ∀ x : X, (S x).Nonempty)
    (hUclosed : ∀ x : X, IsClosed (U x)) (hUne : ∀ x : X, (U x).Nonempty)
    (hS : ∀ x y : X, Metric.hausdorffEDist (S x) (S y) ≤ K * edist x y)
    (hU : ∀ x y : X, Metric.hausdorffEDist (U x) (U y) ≤ K * edist x y)
    (hSU : ∀ x : X, Metric.hausdorffEDist (S x) (U x) ≤ D)
    (p : X) (hp : p ∈ fixedPoints S) :
    Metric.infEDist p (fixedPoints U) ≤ (1 - K)⁻¹ * D := by
  -- For every strict radius above `D`, the first orbit point is available.
  have hfirst : ∀ R : ENNReal, D < R → ∃ u ∈ U p, edist p u < R := by
    intro R hDR
    exact exists_initial_orbit_point S U D R hSU hDR p hp
  let G : ENNReal := (1 - K)⁻¹
  have hsub : 0 < 1 - K := tsub_pos_iff_lt.2 hK
  have hGtop : G ≠ ⊤ := by simp [G, hsub.ne']
  have hG : 0 < G := by simp [G]
  apply ENNReal.le_of_forall_pos_le_add
  intro eta heta
  intro _
  let C : ENNReal := G + D + 1
  have hC : 0 < C := by positivity
  have hCtop : C ≠ ⊤ := by
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2 ⟨hGtop, hD⟩, by norm_num⟩
  obtain ⟨sigma, hsigma, hsigma1, hsigmaC⟩ :=
    exists_small_product_slack C (eta : ENNReal) hC hCtop (by exact_mod_cast heta)
  have hsigmaTop : sigma ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hsigma1
  let A : ENNReal := G + sigma
  have hAtop : A ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hGtop, hsigmaTop⟩
  have hA : 0 < A := hG.trans_le (le_add_right le_rfl)
  have hGA : G < A := ENNReal.lt_add_right hGtop hsigma.ne'
  have hAinvlt : A⁻¹ < 1 - K := by
    simpa [A, G] using ENNReal.inv_lt_inv' hGA
  have hAinvpos : 0 < A⁻¹ := by simp [hAtop]
  have hAinvle : A⁻¹ ≤ 1 :=
    hAinvlt.le.trans (tsub_le_self : 1 - K ≤ 1)
  let Q : ENNReal := 1 - A⁻¹
  have hKQ : K < Q := by
    apply (ENNReal.toReal_lt_toReal (ne_top_of_lt hK)
      (ENNReal.sub_ne_top (by norm_num))).mp
    rw [ENNReal.toReal_sub_of_le hAinvle (by norm_num)]
    have hreal := (ENNReal.toReal_lt_toReal
      (ENNReal.inv_ne_top.2 hA.ne') (ENNReal.sub_ne_top (by norm_num))).2 hAinvlt
    rw [ENNReal.toReal_sub_of_le hK.le (by norm_num)] at hreal
    norm_num at hreal ⊢
    linarith
  have hQ : Q < 1 := by
    dsimp [Q]
    exact ENNReal.sub_lt_self (by norm_num) (by norm_num) hAinvpos.ne'
  have hQcoef : (1 - Q)⁻¹ = A := by
    dsimp [Q]
    rw [ENNReal.sub_sub_cancel (by norm_num) hAinvle, inv_inv]
  let R : ENNReal := D + sigma
  have hRtop : R ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hD, hsigmaTop⟩
  have hDR : D < R := ENNReal.lt_add_right hD hsigma.ne'
  obtain ⟨u₁, hu₁, hpu₁⟩ := hfirst R hDR
  obtain ⟨q, hqFixed, hpq⟩ :=
    exists_fixedPoint_edist_le_of_geometric_start U K Q R hKQ hQ hRtop
      hUclosed hU p u₁ hu₁ hpu₁
  have hinner : G + D + sigma ≤ C := by
    dsimp [C]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hsigma1 (G + D)
  have hproduct : A * R ≤ G * D + (eta : ENNReal) := by
    calc
      A * R = G * D + sigma * (G + D + sigma) := by
        dsimp [A, R]
        ring
      _ ≤ G * D + sigma * C := by
        gcongr
      _ ≤ G * D + (eta : ENNReal) := by gcongr
  exact (Metric.infEDist_le_edist_of_mem hqFixed).trans
    (hpq.trans (by rw [hQcoef]; exact hproduct))

/-- Theorem 2.5 (Lim's Lemma): Let X be a complete metric space and T₁,T₂:X→{nonempty
  closed subsets of X} be Lipschitz continuous with the same λ∈[0,1). Then
  h(Fix(T₁),Fix(T₂)) ≤ (1/(1-λ)) sup_{x∈X} h(T₁(x),T₂(x)). -/
theorem ext_thm_2 {X : Type*} [MetricSpace X] [CompleteSpace X]
    (T₁ T₂ : X → Set X) (lam : ℝ) (hlam₁ : 0 ≤ lam) (hlam₂ : lam < 1)
    (hclosed₁ : ∀ x : X, IsClosed (T₁ x)) (hnonempty₁ : ∀ x : X, (T₁ x).Nonempty)
    (hclosed₂ : ∀ x : X, IsClosed (T₂ x)) (hnonempty₂ : ∀ x : X, (T₂ x).Nonempty)
    (hlip : ∀ x y : X,
      Metric.hausdorffEDist (T₁ x) (T₁ y) ≤ ENNReal.ofReal lam * edist x y ∧
      Metric.hausdorffEDist (T₂ x) (T₂ y) ≤ ENNReal.ofReal lam * edist x y) :
    Metric.hausdorffEDist (fixedPoints T₁) (fixedPoints T₂) ≤
      (1 - ENNReal.ofReal lam)⁻¹ *
        ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x) := by
  let K : ENNReal := ENNReal.ofReal lam
  let D : ENNReal := ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x)
  have hK : K < 1 := by
    simpa [K] using ENNReal.ofReal_lt_one.2 hlam₂
  by_cases hD : D = ⊤
  · have hsub : 1 - K ≠ 0 := ne_of_gt (tsub_pos_iff_lt.2 hK)
    have hRHS : (1 - K)⁻¹ * D = ⊤ := by
      rw [hD, ENNReal.mul_top]
      exact ENNReal.inv_ne_zero.2 (by simp)
    rw [show (1 - ENNReal.ofReal lam)⁻¹ *
        ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x) = (1 - K)⁻¹ * D by rfl, hRHS]
    exact le_top
  · have hDle (x : X) : Metric.hausdorffEDist (T₁ x) (T₂ x) ≤ D := by
      simpa [D] using le_iSup (fun z : X => Metric.hausdorffEDist (T₁ z) (T₂ z)) x
    suffices hside : ∀ (S U : X → Set X),
        (∀ x : X, IsClosed (S x)) → (∀ x : X, (S x).Nonempty) →
        (∀ x : X, IsClosed (U x)) → (∀ x : X, (U x).Nonempty) →
        (∀ x y : X, Metric.hausdorffEDist (S x) (S y) ≤ K * edist x y) →
        (∀ x y : X, Metric.hausdorffEDist (U x) (U y) ≤ K * edist x y) →
        (∀ x : X, Metric.hausdorffEDist (S x) (U x) ≤ D) →
        ∀ p : X, p ∈ fixedPoints S →
          Metric.infEDist p (fixedPoints U) ≤ (1 - K)⁻¹ * D by
      apply Metric.hausdorffEDist_le_of_infEDist
      · intro p hp
        exact hside T₁ T₂ hclosed₁ hnonempty₁ hclosed₂ hnonempty₂
          (fun x y => (hlip x y).1) (fun x y => (hlip x y).2) hDle p hp
      · intro p hp
        have hDle' (x : X) : Metric.hausdorffEDist (T₂ x) (T₁ x) ≤ D := by
          simpa only [Metric.hausdorffEDist_comm] using hDle x
        exact hside T₂ T₁ hclosed₂ hnonempty₂ hclosed₁ hnonempty₁
          (fun x y => (hlip x y).2) (fun x y => (hlip x y).1) hDle' p hp
    intro S U hSclosed hSne hUclosed hUne hS hU hSU p hp
    exact one_sided_lims_bound S U K D hK hD hSclosed hSne hUclosed hUne hS hU hSU p hp

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
