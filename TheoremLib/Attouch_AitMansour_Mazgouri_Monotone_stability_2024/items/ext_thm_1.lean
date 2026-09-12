import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_1

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set

/-- A strict approximate selection whose next residual is controlled by the
Hausdorff Lipschitz estimate. -/
private theorem exists_selection_step {X : Type*} [PseudoMetricSpace X]
    (T : X → Set X) (K σ : ENNReal) (hnonempty : ∀ x : X, (T x).Nonempty)
    (hlip : ∀ x y : X,
      Metric.hausdorffEDist (T x) (T y) ≤ K * edist x y)
    (hσ : 0 < σ) (x : X) :
    ∃ y, y ∈ T x ∧
      edist x y ≤ Metric.infEDist x (T x) + σ ∧
      Metric.infEDist y (T y) ≤ K * (Metric.infEDist x (T x) + σ) := by
  have hfin : Metric.infEDist x (T x) ≠ ⊤ :=
    Metric.infEDist_ne_top (hnonempty x)
  have hlt : Metric.infEDist x (T x) < Metric.infEDist x (T x) + σ :=
    ENNReal.lt_add_right hfin hσ.ne'
  obtain ⟨y, hy, hxy⟩ := Metric.infEDist_lt_iff.mp hlt
  refine ⟨y, hy, hxy.le, ?_⟩
  calc
    Metric.infEDist y (T y) ≤
        Metric.infEDist y (T x) + Metric.hausdorffEDist (T x) (T y) :=
      Metric.infEDist_le_infEDist_add_hausdorffEDist
    _ ≤ 0 + K * edist x y := by
      gcongr
      · exact (Metric.infEDist_zero_of_mem hy).le
      · exact hlip x y
    _ ≤ K * (Metric.infEDist x (T x) + σ) := by
      simpa using mul_le_mul_left' hxy.le K

/-- A recursively selected orbit with the one-step estimates needed for the
geometric contraction argument. -/
private theorem selection_orbit {X : Type*} [PseudoMetricSpace X]
    (T : X → Set X) (K σ : ENNReal) (hnonempty : ∀ x : X, (T x).Nonempty)
    (hlip : ∀ x y : X,
      Metric.hausdorffEDist (T x) (T y) ≤ K * edist x y)
    (hσ : 0 < σ) (x0 : X) :
    ∃ u : ℕ → X, u 0 = x0 ∧ ∀ n,
      u (n + 1) ∈ T (u n) ∧
      edist (u n) (u (n + 1)) ≤ Metric.infEDist (u n) (T (u n)) + σ ∧
      Metric.infEDist (u (n + 1)) (T (u (n + 1))) ≤
        K * (Metric.infEDist (u n) (T (u n)) + σ) := by
  classical
  choose step hstep using fun x =>
    exists_selection_step T K σ hnonempty hlip hσ x
  let u : ℕ → X := fun n => Nat.rec x0 (fun _ x => step x) n
  refine ⟨u, by simp [u], ?_⟩
  intro n
  simpa [u] using hstep (u n)

/-- The finite geometric contribution in the orientation induced by the
residual recurrence. -/
private noncomputable def reverseGeom (K : ENNReal) (n : Nat) : ENNReal :=
  (Finset.range n).sum (fun j => K ^ (n - j))

private theorem reverseGeom_zero (K : ENNReal) : reverseGeom K 0 = 0 := by
  simp [reverseGeom]

private theorem reverseGeom_succ (K : ENNReal) (n : Nat) :
    reverseGeom K (n + 1) = K * reverseGeom K n + K := by
  rw [reverseGeom, Finset.sum_range_succ]
  have hterm : ∀ j ∈ Finset.range n,
      K ^ (n + 1 - j) = K * K ^ (n - j) := by
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ, mul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  simp
  ac_rfl

private theorem reverseGeom_le_tsum_geometric (K : ENNReal) (n : Nat) :
    reverseGeom K n ≤ (1 - K)⁻¹ := by
  have hreindex : reverseGeom K n = (Finset.Icc 1 n).sum (fun m => K ^ m) := by
    unfold reverseGeom
    refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
    · intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      simp only [Finset.mem_Icc]
      constructor <;> omega
    · intro j₁ hj₁ j₂ hj₂ heq
      have hj₁' : j₁ < n := Finset.mem_range.mp hj₁
      have hj₂' : j₂ < n := Finset.mem_range.mp hj₂
      change n - j₁ = n - j₂ at heq
      omega
    · intro m hm
      have hm' : 1 ≤ m ∧ m ≤ n := Finset.mem_Icc.mp hm
      refine ⟨n - m, ?_, ?_⟩
      · apply Finset.mem_range.mpr
        omega
      · simpa using Nat.sub_sub_self hm'.2
    · intro j hj
      rfl
  rw [hreindex]
  calc
    (Finset.Icc 1 n).sum (fun m => K ^ m) ≤ ∑' m : Nat, K ^ m :=
      ENNReal.sum_le_tsum _
    _ = (1 - K)⁻¹ := ENNReal.tsum_geometric K

private theorem forwardGeom_le_tsum_geometric (K : ENNReal) (n : Nat) :
    (Finset.range n).sum (fun j => K ^ j) ≤ (1 - K)⁻¹ := by
  calc
    (Finset.range n).sum (fun j => K ^ j) ≤ ∑' j : Nat, K ^ j :=
      ENNReal.sum_le_tsum _
    _ = (1 - K)⁻¹ := ENNReal.tsum_geometric K

private theorem reverseGeom_sum_le (K : ENNReal) (n : Nat) :
    (Finset.range n).sum (fun j => reverseGeom K j) ≤
      (n : ENNReal) * (1 - K)⁻¹ := by
  calc
    (Finset.range n).sum (fun j => reverseGeom K j) ≤
        (Finset.range n).sum (fun _ => (1 - K)⁻¹) := by
          exact Finset.sum_le_sum (fun j _ => reverseGeom_le_tsum_geometric K j)
    _ = (n : ENNReal) * (1 - K)⁻¹ := by simp

/-- The residual along a selected orbit is controlled by the recurrence's
finite geometric contribution. -/
private theorem selection_orbit_residual_bound {X : Type*} [PseudoMetricSpace X]
    (T : X → Set X) (K σ : ENNReal) (hnonempty : ∀ x : X, (T x).Nonempty)
    (hlip : ∀ x y : X,
      Metric.hausdorffEDist (T x) (T y) ≤ K * edist x y)
    (hσ : 0 < σ) (x0 : X) :
    ∃ u : ℕ → X, u 0 = x0 ∧ ∀ n,
      u (n + 1) ∈ T (u n) ∧
      edist (u n) (u (n + 1)) ≤ Metric.infEDist (u n) (T (u n)) + σ ∧
      Metric.infEDist (u n) (T (u n)) ≤
        K ^ n * Metric.infEDist (u 0) (T (u 0)) + σ * reverseGeom K n := by
  obtain ⟨u, hu0, hu⟩ := selection_orbit T K σ hnonempty hlip hσ x0
  refine ⟨u, hu0, ?_⟩
  intro n
  refine ⟨(hu n).1, (hu n).2.1, ?_⟩
  induction n with
  | zero => simp [reverseGeom]
  | succ n ihn =>
      calc
        Metric.infEDist (u (n + 1)) (T (u (n + 1))) ≤
            K * (Metric.infEDist (u n) (T (u n)) + σ) := (hu n).2.2
        _ ≤ K * ((K ^ n * Metric.infEDist (u 0) (T (u 0)) +
            σ * reverseGeom K n) + σ) :=
          by
            simpa only [add_comm, add_left_comm, add_assoc] using
              mul_le_mul_left' (add_le_add_right ihn σ) K
        _ = K ^ (n + 1) * Metric.infEDist (u 0) (T (u 0)) +
            σ * reverseGeom K (n + 1) := by
          rw [reverseGeom_succ, pow_succ]
          simp only [mul_add]
          ac_rfl

private theorem selection_orbit_with_bounds {X : Type*} [PseudoMetricSpace X]
    (S : X → Set X) (K sigma : ENNReal) (hS : ∀ x : X, (S x).Nonempty)
    (hLip : ∀ x y : X,
      Metric.hausdorffEDist (S x) (S y) ≤ K * edist x y)
    (hsigma : 0 < sigma) (z : X) :
    ∃ u : ℕ → X, u 0 = z ∧ ∀ n,
      u (n + 1) ∈ S (u n) ∧
      edist (u n) (u (n + 1)) ≤ Metric.infEDist (u n) (S (u n)) + sigma ∧
      Metric.infEDist (u n) (S (u n)) ≤
        K ^ n * Metric.infEDist z (S z) + sigma * reverseGeom K n ∧
      edist z (u n) ≤ (Finset.range n).sum (fun j =>
        K ^ j * Metric.infEDist z (S z) + sigma * reverseGeom K j + sigma) := by
  obtain ⟨u, hu0, hu⟩ := selection_orbit S K sigma hS hLip hsigma z
  have hres : ∀ n, Metric.infEDist (u n) (S (u n)) ≤
      K ^ n * Metric.infEDist z (S z) + sigma * reverseGeom K n := by
    intro n
    induction n with
    | zero => simpa [hu0, reverseGeom]
    | succ n ihn =>
      calc
        Metric.infEDist (u (n + 1)) (S (u (n + 1))) ≤
            K * (Metric.infEDist (u n) (S (u n)) + sigma) := (hu n).2.2
        _ ≤ K * ((K ^ n * Metric.infEDist z (S z) + sigma * reverseGeom K n) + sigma) := by
          simpa only [add_comm] using mul_le_mul_left' (add_le_add_right ihn sigma) K
        _ = K ^ (n + 1) * Metric.infEDist z (S z) + sigma * reverseGeom K (n + 1) := by
          rw [reverseGeom_succ, pow_succ]
          simp only [mul_add]
          ac_rfl
  refine ⟨u, hu0, ?_⟩
  intro n
  refine ⟨(hu n).1, (hu n).2.1, hres n, ?_⟩
  induction n with
  | zero => simp [hu0]
  | succ n ihn =>
    calc
      edist z (u (n + 1)) ≤ edist z (u n) + edist (u n) (u (n + 1)) :=
        edist_triangle _ _ _
      _ ≤ (Finset.range n).sum (fun j =>
          K ^ j * Metric.infEDist z (S z) + sigma * reverseGeom K j + sigma) +
          (K ^ n * Metric.infEDist z (S z) + sigma * reverseGeom K n + sigma) := by
            gcongr
            exact (hu n).2.1.trans (by simpa only [add_comm] using add_le_add_right (hres n) sigma)
      _ = (Finset.range (n + 1)).sum (fun j =>
          K ^ j * Metric.infEDist z (S z) + sigma * reverseGeom K j + sigma) := by
            rw [Finset.sum_range_succ]

/-- A strict Hausdorff contraction with nonempty values has approximate fixed
points, without requiring completeness of the ambient space. -/
private theorem approximateFixedPoints_nonempty_of_hausdorff_contractive
    {X : Type*} [PseudoMetricSpace X] [Nonempty X]
    (T : X → Set X) (lam epsilon : Real) (hlam0 : 0 <= lam) (hlam1 : lam < 1)
    (hepsilon : 0 < epsilon) (hnonempty : forall x : X, (T x).Nonempty)
    (hlip : forall x y : X,
      Metric.hausdorffEDist (T x) (T y) <= ENNReal.ofReal lam * edist x y) :
    (approximateFixedPoints T epsilon).Nonempty := by
  let K : ENNReal := ENNReal.ofReal lam
  let E : ENNReal := ENNReal.ofReal epsilon
  have hK : K < 1 := by simpa [K] using ENNReal.ofReal_lt_one.2 hlam1
  have hE : 0 < E := by simpa [E] using ENNReal.ofReal_pos.mpr hepsilon
  have hsub : 0 < 1 - K := tsub_pos_iff_lt.2 hK
  have hsub_top : 1 - K ≠ ⊤ := ENNReal.sub_ne_top (by simp)
  let sigma : ENNReal := (E / 4) * (1 - K)
  have hsigma : 0 < sigma := by
    exact ENNReal.mul_pos (ENNReal.div_pos hE.ne' ENNReal.ofNat_ne_top).ne' hsub.ne'
  have hsigma_geom : sigma * (1 - K)⁻¹ = E / 4 := by
    dsimp [sigma]
    rw [mul_assoc, ENNReal.mul_inv_cancel (ne_of_gt hsub) hsub_top, mul_one]
  let x0 : X := Classical.choice inferInstance
  obtain ⟨u, hu0, hu⟩ :=
    selection_orbit_residual_bound T K sigma hnonempty (by simpa [K] using hlip) hsigma x0
  let r0 : ENNReal := Metric.infEDist (u 0) (T (u 0))
  have hres (n : Nat) :
      Metric.infEDist (u n) (T (u n)) <= K ^ n * r0 + E / 4 := by
    calc
      Metric.infEDist (u n) (T (u n))
          <= K ^ n * r0 + sigma * reverseGeom K n := by simpa [r0] using (hu n).2.2
      _ <= K ^ n * r0 + sigma * (1 - K)⁻¹ :=
        add_le_add_right (mul_le_mul_left' (reverseGeom_le_tsum_geometric K n) sigma) _
      _ = K ^ n * r0 + E / 4 := by rw [hsigma_geom]
  have hquarter : E / 4 + E / 4 <= E := by
    rw [ENNReal.div_add_div_same]
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
    calc
      E + E = E * 2 := (mul_two E).symm
      _ <= E * 4 := mul_le_mul_left' (by norm_num) E
  have hexists : exists N : Nat, K ^ N * r0 < E / 4 := by
    by_cases hr0 : r0 = 0
    · refine ⟨0, ?_⟩
      simpa [hr0] using
        (ENNReal.div_pos hE.ne' (show (4 : ENNReal) ≠ ⊤ by norm_num))
    · have hpow : Filter.Tendsto (fun n : Nat => K ^ n * r0)
          Filter.atTop (nhds 0) := by
        simpa using ENNReal.Tendsto.mul_const
          (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hK) (Or.inr (Metric.infEDist_ne_top (hnonempty (u 0))))
      have hNevent : ∀ᶠ n : Nat in Filter.atTop, K ^ n * r0 < E / 4 :=
        hpow.eventually (Iio_mem_nhds (ENNReal.div_pos hE.ne' ENNReal.ofNat_ne_top))
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hNevent
      exact ⟨N, hN N le_rfl⟩
  obtain ⟨N, hN⟩ := hexists
  refine ⟨u N, le_of_lt hepsilon, ?_⟩
  have hfinal : Metric.infEDist (u N) (T (u N)) <= E :=
    (calc
      Metric.infEDist (u N) (T (u N)) <= K ^ N * r0 + E / 4 := hres N
      _ < E / 4 + E / 4 :=
        ENNReal.add_lt_add_right (ENNReal.div_ne_top (by simp [E]) (by norm_num)) hN
      _ <= E := hquarter).le
  simpa [E] using hfinal

/-- A strict ENNReal contraction makes any finite error term smaller than a
prescribed positive budget after finitely many steps. -/
private theorem exists_contraction_horizon (K B E : ENNReal)
    (hK : K < 1) (hBtop : B ≠ ⊤) (hE : 0 < E) :
    ∃ N : Nat, K ^ N * B < E / 2 := by
  have hpow : Filter.Tendsto (fun n : Nat => K ^ n * B)
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hK) (Or.inr hBtop)
  have hevent : ∀ᶠ n : Nat in Filter.atTop, K ^ n * B < E / 2 :=
    hpow.eventually (Iio_mem_nhds (ENNReal.div_pos hE.ne' ENNReal.ofNat_ne_top))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  exact ⟨N, hN N le_rfl⟩

/-- A positive slack can be chosen below two prescribed finite ENNReal
budgets.  The formulation avoids cancellation through infinity. -/
private theorem exists_small_slack (E G C eta : ENNReal)
    (hE : 0 < E) (hG : 0 < G) (hGtop : G ≠ ⊤)
    (hC : 0 < C) (hCtop : C ≠ ⊤) (heta : 0 < eta) :
    ∃ sigma : ENNReal, 0 < sigma ∧ sigma ≤ 1 ∧
      sigma * G ≤ E / 2 ∧ sigma * C ≤ eta := by
  let sigma : ENNReal := min 1 (min ((E / 2) / G) (eta / C))
  have hhalf : 0 < E / 2 := ENNReal.div_pos hE.ne' ENNReal.ofNat_ne_top
  have hEG : 0 < (E / 2) / G := ENNReal.div_pos hhalf.ne' hGtop
  have hetaC : 0 < eta / C := ENNReal.div_pos heta.ne' hCtop
  have hsigma : 0 < sigma := lt_min (by norm_num) (lt_min hEG hetaC)
  refine ⟨sigma, hsigma, min_le_left _ _, ?_, ?_⟩
  · have hle : sigma ≤ (E / 2) / G :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    exact (ENNReal.le_div_iff_mul_le (Or.inl hG.ne') (Or.inl hGtop)).mp hle
  · have hle : sigma ≤ eta / C := le_trans (min_le_right _ _) (min_le_right _ _)
    exact (ENNReal.le_div_iff_mul_le (Or.inl hC.ne') (Or.inl hCtop)).mp hle

private theorem initial_and_shifted_geometric_le (K Q : ENNReal) (n : Nat) :
    Q + (Finset.range n).sum (fun j => K ^ j * (K * Q)) ≤
      Q * (1 - K)⁻¹ := by
  have hshift : Q + (Finset.range n).sum (fun j => K ^ j * (K * Q)) =
      Q * (Finset.range (n + 1)).sum (fun j => K ^ j) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        rw [show K ^ n * (K * Q) = Q * K ^ (n + 1) by
          rw [pow_succ]
          ac_rfl]
        calc
          Q + ((Finset.range n).sum (fun j => K ^ j * (K * Q)) +
              Q * K ^ (n + 1)) =
              (Q + (Finset.range n).sum (fun j => K ^ j * (K * Q))) +
                Q * K ^ (n + 1) := by ac_rfl
          _ = Q * (Finset.range (n + 1)).sum (fun j => K ^ j) +
                Q * K ^ (n + 1) := by rw [ih]
          _ = Q * ((Finset.range (n + 1)).sum (fun j => K ^ j) +
                K ^ (n + 1)) := by rw [mul_add]
  rw [hshift]
  exact mul_le_mul_left' (forwardGeom_le_tsum_geometric K (n + 1)) Q

private theorem slack_orbit_sum_le (K sigma : ENNReal) (n : Nat) :
    (Finset.range n).sum (fun j => sigma * reverseGeom K j + sigma) ≤
      sigma * ((n : ENNReal) * ((1 - K)⁻¹ + 1)) := by
  calc
    (Finset.range n).sum (fun j => sigma * reverseGeom K j + sigma) =
        sigma * (Finset.range n).sum (fun j => reverseGeom K j) + (n : ENNReal) * sigma := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [mul_comm]
    _ ≤ sigma * ((n : ENNReal) * (1 - K)⁻¹) + (n : ENNReal) * sigma := by
      gcongr
      exact reverseGeom_sum_le K n
    _ = sigma * ((n : ENNReal) * ((1 - K)⁻¹ + 1)) := by
      ring

private theorem approximateFixedPoint_infEDist_le
    {X : Type*} [PseudoMetricSpace X] [Nonempty X]
    (T S : X → Set X) (lam epsilon : Real)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hepsilon : 0 < epsilon)
    (hT : ∀ x : X, (T x).Nonempty) (hS : ∀ x : X, (S x).Nonempty)
    (hSlip : ∀ x y : X,
      Metric.hausdorffEDist (S x) (S y) ≤ ENNReal.ofReal lam * edist x y)
    (D : ENNReal) (hDtop : D ≠ ⊤)
    (hD : ∀ x : X, Metric.hausdorffEDist (T x) (S x) ≤ D)
    {x : X} (hx : x ∈ approximateFixedPoints T epsilon) :
    Metric.infEDist x (approximateFixedPoints S epsilon) ≤
      ENNReal.ofReal (epsilon / (1 - lam)) +
        (1 - ENNReal.ofReal lam)⁻¹ * D := by
  let A : ENNReal := Metric.infEDist x (T x) + D
  have hdistS : Metric.infEDist x (S x) ≤ A := by
    calc
      Metric.infEDist x (S x) ≤ Metric.infEDist x (T x) +
          Metric.hausdorffEDist (T x) (S x) :=
        Metric.infEDist_le_infEDist_add_hausdorffEDist
      _ ≤ A := by simpa [A, add_comm] using add_le_add_right (hD x) (Metric.infEDist x (T x))
  have hA_top : A ≠ ⊤ := by
    exact ENNReal.add_ne_top.2 ⟨Metric.infEDist_ne_top (hT x), hDtop⟩
  have hK : ENNReal.ofReal lam < 1 := by
    simpa using ENNReal.ofReal_lt_one.2 hlam1
  have hE : 0 < ENNReal.ofReal epsilon := by
    simpa using ENNReal.ofReal_pos.mpr hepsilon
  have hBtop : ENNReal.ofReal lam * (ENNReal.ofReal epsilon + D + 1) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hDtop⟩, by norm_num⟩)
  obtain ⟨N, hN⟩ := exists_contraction_horizon
    (ENNReal.ofReal lam)
    (ENNReal.ofReal lam * (ENNReal.ofReal epsilon + D + 1))
    (ENNReal.ofReal epsilon) hK hBtop hE
  let K : ENNReal := ENNReal.ofReal lam
  let E : ENNReal := ENNReal.ofReal epsilon
  let G : ENNReal := (1 - K)⁻¹
  have hsub : 0 < 1 - K := tsub_pos_iff_lt.2 hK
  have hGtop : G ≠ ⊤ := by simp [G, hsub.ne']
  have hG : 0 < G := by simp [G, hsub.ne']
  apply ENNReal.le_of_forall_pos_le_add
  intro eta heta
  intro hRtop
  let C : ENNReal := G + (N : ENNReal) * (G + 1)
  have hC : 0 < C := by positivity
  have hCtop : C ≠ ⊤ := by
    apply ENNReal.add_ne_top.2
    exact ⟨hGtop, ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp [hGtop])⟩
  obtain ⟨sigma, hsigma, hsigma1, hsigmaG, hsigmaC⟩ :=
    exists_small_slack E G C (eta : ENNReal) hE hG hGtop hC hCtop (by exact_mod_cast heta)
  have hdistS' : Metric.infEDist x (S x) < Metric.infEDist x (S x) + sigma := by
    exact ENNReal.lt_add_right (Metric.infEDist_ne_top (hS x)) hsigma.ne'
  obtain ⟨z, hz, hzx⟩ := Metric.infEDist_lt_iff.mp hdistS'
  have hzx' : edist x z ≤ A + sigma := by
    calc
      edist x z ≤ Metric.infEDist x (S x) + sigma := hzx.le
      _ ≤ A + sigma := by simpa [add_comm] using add_le_add_right hdistS sigma
  have hr0 : Metric.infEDist z (S z) ≤ K * (A + sigma) := by
    calc
      Metric.infEDist z (S z) ≤ Metric.infEDist z (S x) + Metric.hausdorffEDist (S x) (S z) :=
        Metric.infEDist_le_infEDist_add_hausdorffEDist
      _ ≤ K * edist x z := by
        calc
          Metric.infEDist z (S x) + Metric.hausdorffEDist (S x) (S z)
              ≤ 0 + Metric.hausdorffEDist (S x) (S z) := by
                gcongr
                simp [Metric.infEDist_zero_of_mem hz]
          _ ≤ 0 + K * edist x z := by simpa [K] using hSlip x z
          _ = K * edist x z := by simp
      _ ≤ K * (A + sigma) := mul_le_mul_left' hzx' K
  have hr0B : Metric.infEDist z (S z) ≤ K * (E + D + 1) := by
    calc
      Metric.infEDist z (S z) ≤ K * (A + sigma) := hr0
      _ ≤ K * (E + D + 1) := by
        gcongr
        have hxE : Metric.infEDist x (T x) ≤ E := by simpa [approximateFixedPoints, E] using hx.2
        dsimp [A]
        simpa [add_assoc, add_left_comm, add_comm] using
          (add_le_add_right hxE D)
  obtain ⟨u, hu0, hu⟩ := selection_orbit_with_bounds S K sigma hS
    (by simpa [K] using hSlip) hsigma z
  have hresN : Metric.infEDist (u N) (S (u N)) ≤ E := by
    calc
      Metric.infEDist (u N) (S (u N)) ≤ K ^ N * Metric.infEDist z (S z) + sigma * reverseGeom K N := (hu N).2.2.1
      _ ≤ K ^ N * (K * (E + D + 1)) + sigma * G := by
        exact add_le_add
          (mul_le_mul_left' hr0B (K ^ N))
          (mul_le_mul_left' (reverseGeom_le_tsum_geometric K N) sigma)
      _ ≤ E := by
        have hpow : K ^ N * (K * (E + D + 1)) < E / 2 := by simpa [mul_assoc] using hN
        exact (add_le_add hpow.le hsigmaG).trans (by
          rw [ENNReal.div_add_div_same]
          rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
          rw [← mul_two E]
          )
  have hu_mem : u N ∈ approximateFixedPoints S epsilon := by
    refine ⟨le_of_lt hepsilon, ?_⟩
    simpa [E] using hresN
  have hpath : edist x (u N) ≤ A * G + sigma * C := by
    have hsum :
        (Finset.range N).sum (fun j =>
          K ^ j * Metric.infEDist z (S z) + sigma * reverseGeom K j + sigma) ≤
        (Finset.range N).sum (fun j =>
          K ^ j * (K * (A + sigma)) + (sigma * reverseGeom K j + sigma)) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        K ^ j * Metric.infEDist z (S z) + sigma * reverseGeom K j + sigma =
            K ^ j * Metric.infEDist z (S z) +
              (sigma * reverseGeom K j + sigma) := by ac_rfl
        _ ≤ K ^ j * (K * (A + sigma)) +
              (sigma * reverseGeom K j + sigma) := by
          gcongr
    calc
      edist x (u N) ≤ edist x z + edist z (u N) := edist_triangle _ _ _
      _ ≤ (A + sigma) +
          (Finset.range N).sum (fun j =>
            K ^ j * Metric.infEDist z (S z) + sigma * reverseGeom K j + sigma) :=
        add_le_add hzx' (hu N).2.2.2
      _ ≤ (A + sigma) +
          (Finset.range N).sum (fun j =>
            K ^ j * (K * (A + sigma)) + (sigma * reverseGeom K j + sigma)) :=
        by gcongr
      _ = ((A + sigma) +
          (Finset.range N).sum (fun j => K ^ j * (K * (A + sigma)))) +
          (Finset.range N).sum (fun j => sigma * reverseGeom K j + sigma) := by
        rw [Finset.sum_add_distrib]
        ac_rfl
      _ ≤ (A + sigma) * G +
          sigma * ((N : ENNReal) * (G + 1)) := by
        exact add_le_add
          (initial_and_shifted_geometric_le K (A + sigma) N)
          (slack_orbit_sum_le K sigma N)
      _ = A * G + sigma * (G + (N : ENNReal) * (G + 1)) := by
        ring
      _ = A * G + sigma * C := by
        dsimp [C]
  have hdist : Metric.infEDist x (approximateFixedPoints S epsilon) ≤ A * G + (eta : ENNReal) := by
    exact (Metric.infEDist_le_edist_of_mem hu_mem).trans
      (hpath.trans (by simpa [add_comm] using add_le_add_left hsigmaC (A * G)))
  have hAG : A * G ≤ ENNReal.ofReal (epsilon / (1 - lam)) + G * D := by
    have hxE : Metric.infEDist x (T x) ≤ E := by simpa [approximateFixedPoints, E] using hx.2
    calc
      A * G ≤ (E + D) * G := by
        apply mul_le_mul_right' _ G
        simpa [A, add_comm] using add_le_add_right hxE D
      _ = E * G + G * D := by rw [add_mul, mul_comm D G]
      _ = ENNReal.ofReal (epsilon / (1 - lam)) + G * D := by
        congr 1
        dsimp [E, G, K]
        rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hlam1)]
        rw [ENNReal.ofReal_sub (p := (1 : ℝ)) (q := lam) hlam0]
        norm_num
        rw [ENNReal.div_eq_inv_mul]
        ac_rfl
  have hG' : G = (1 - ENNReal.ofReal lam)⁻¹ := by rfl
  rw [hG'] at hAG hdist
  exact (hdist.trans (add_le_add_left hAG (eta : ENNReal))).trans (by
    exact le_rfl)

/-- Theorem 2.4: Let X be a metric space and T₁,T₂:X⇉X be Lipschitz continuous
  with the same λ∈[0,1). Then for every ε>0, ε-Fix(T_i)≠∅ (i=1,2) and
  h(ε-Fix(T₁),ε-Fix(T₂)) ≤ ε/(1-λ) + (1/(1-λ)) sup_{x∈X} h(T₁(x),T₂(x)). -/
theorem ext_thm_1 {X : Type*} [PseudoMetricSpace X] [Nonempty X]
    (T₁ T₂ : X → Set X) (lam ε : ℝ)
    (hlam₁ : 0 ≤ lam) (hlam₂ : lam < 1) (hε : 0 < ε)
    (hnonempty₁ : ∀ x : X, (T₁ x).Nonempty)
    (hnonempty₂ : ∀ x : X, (T₂ x).Nonempty)
    (hlip : ∀ x y : X,
      Metric.hausdorffEDist (T₁ x) (T₁ y) ≤ ENNReal.ofReal lam * edist x y ∧
      Metric.hausdorffEDist (T₂ x) (T₂ y) ≤ ENNReal.ofReal lam * edist x y) :
    (approximateFixedPoints T₁ ε).Nonempty ∧ (approximateFixedPoints T₂ ε).Nonempty ∧
    Metric.hausdorffEDist (approximateFixedPoints T₁ ε) (approximateFixedPoints T₂ ε) ≤
      ENNReal.ofReal (ε / (1 - lam)) + (1 - ENNReal.ofReal lam)⁻¹ *
        ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x) := by
  have happrox₁ : (approximateFixedPoints T₁ ε).Nonempty :=
    approximateFixedPoints_nonempty_of_hausdorff_contractive T₁ lam ε hlam₁ hlam₂ hε
      hnonempty₁ (fun x y => (hlip x y).1)
  have happrox₂ : (approximateFixedPoints T₂ ε).Nonempty :=
    approximateFixedPoints_nonempty_of_hausdorff_contractive T₂ lam ε hlam₁ hlam₂ hε
      hnonempty₂ (fun x y => (hlip x y).2)
  refine ⟨happrox₁, happrox₂, ?_⟩
  let D : ENNReal := ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x)
  by_cases hDtop : D = ⊤
  · have hsubtop : 1 - ENNReal.ofReal lam ≠ ⊤ := ENNReal.sub_ne_top (by simp)
    rw [show (⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x)) = D by rfl, hDtop,
      ENNReal.mul_top (ENNReal.inv_ne_zero.2 hsubtop)]
    exact le_top
  · have hDle : ∀ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x) ≤ D := fun x =>
      le_iSup (fun z : X => Metric.hausdorffEDist (T₁ z) (T₂ z)) x
    apply Metric.hausdorffEDist_le_of_infEDist
    · intro x hx
      exact approximateFixedPoint_infEDist_le T₁ T₂ lam ε hlam₁ hlam₂ hε hnonempty₁
        hnonempty₂ (fun x y => (hlip x y).2) D hDtop hDle hx
    · intro x hx
      exact approximateFixedPoint_infEDist_le T₂ T₁ lam ε hlam₁ hlam₂ hε hnonempty₂
        hnonempty₁ (fun x y => (hlip x y).1) D hDtop
        (fun y => by simpa only [Metric.hausdorffEDist_comm] using hDle y) hx

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
