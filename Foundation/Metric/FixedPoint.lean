import Mathlib

/-!
# Metric FixedPoint

Metric Lipschitz locality, distance-to-set continuity, cluster continua, and contraction fixed-point principles.
-/

open scoped Topology
open Filter
open Function
open Filter Function

/-! Source item: Chap01/Definition_1_47 -/

universe u v

/-- Definition 1.47(2): `T` is locally Lipschitz continuous near `x` iff it is Lipschitz on
some positive-radius ball centered at `x`. The neighborhood formulation on the left is the one
used by the canonical predicate `LocallyLipschitz`. -/
theorem locallyLipschitzNear_iff_exists_lipschitzOnWith_ball {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] {T : X → Y} {x : X} :
    (∃ β : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith β T s) ↔
      ∃ ρ > 0, ∃ β : NNReal, LipschitzOnWith β T (Metric.ball x ρ) := by
  constructor
  · rintro ⟨β, s, hs, hT⟩
    rcases Metric.mem_nhds_iff.mp hs with ⟨ρ, hρ, hball⟩
    exact ⟨ρ, hρ, β, hT.mono hball⟩
  · rintro ⟨ρ, hρ, β, hT⟩
    exact ⟨β, Metric.ball x ρ, Metric.ball_mem_nhds x hρ, hT⟩

/-- Definition 1.47(3): `T` is locally Lipschitz continuous on `C` iff every point of `C`
admits a positive-radius ambient ball on which `T` is Lipschitz. -/
theorem locallyLipschitzOnSet_iff_forall_mem_exists_lipschitzOnWith_ball {X : Type u}
    {Y : Type v} [MetricSpace X] [MetricSpace Y] {C : Set X} {T : X → Y} :
    (∀ x ∈ C, ∃ β : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith β T s) ↔
      ∀ x ∈ C, ∃ ρ > 0, ∃ β : NNReal, LipschitzOnWith β T (Metric.ball x ρ) := by
  constructor
  · intro h x hx
    exact locallyLipschitzNear_iff_exists_lipschitzOnWith_ball.mp (h x hx)
  · intro h x hx
    exact locallyLipschitzNear_iff_exists_lipschitzOnWith_ball.mpr (h x hx)

/-- In metric spaces, a map is locally Lipschitz iff each point has a positive-radius ball on
which the map is Lipschitz with some constant. -/
theorem locallyLipschitz_iff_forall_exists_lipschitzOnWith_ball {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] {T : X → Y} :
    LocallyLipschitz T ↔
      ∀ x, ∃ ρ > 0, ∃ β : NNReal, LipschitzOnWith β T (Metric.ball x ρ) := by
  simp [LocallyLipschitz, locallyLipschitzNear_iff_exists_lipschitzOnWith_ball]

/-! Source item: Chap01/Example_1_48 -/

/-- Example 1.48: the textbook estimate (1.67) is the pointwise form of the canonical
`1`-Lipschitz estimate for `x ↦ Metric.infDist x C`; the book's nonemptiness hypothesis is
unnecessary for this inequality. -/
theorem abs_infDist_sub_infDist_le_dist {α : Type u} [PseudoMetricSpace α] {C : Set α} (x y : α) :
    |Metric.infDist x C - Metric.infDist y C| ≤ dist x y := by
  simpa [Real.dist_eq, one_mul] using (Metric.lipschitz_infDist_pt C).dist_le_mul x y

/-! Source item: Chap01/Theorem_1_49 -/

variable {X : Type u} [MetricSpace X]

/-- Helper for Theorem 1.49: disjoint compact and closed sets have a positive `infDist` gap. -/
private lemma exists_positive_infDist_lower_bound_of_disjoint {A B : Set X} (hA : IsCompact A)
    (hBclosed : IsClosed B) (hBne : B.Nonempty) (hAB : Disjoint A B) :
    ∃ δ > 0, ∀ a ∈ A, δ ≤ Metric.infDist a B := by
  rw [Set.disjoint_left] at hAB
  -- Every point of `A` stays at positive distance from the closed set `B`.
  have hpos : ∀ a ∈ A, 0 < Metric.infDist a B := by
    intro a ha
    have hnotmem : a ∉ B := fun hb ↦ hAB ha hb
    have hnotclosure : a ∉ closure B := by
      simpa [hBclosed.closure_eq] using hnotmem
    exact (Metric.infDist_pos_iff_notMem_closure hBne).mp hnotclosure
  -- Compactness upgrades pointwise positivity to a uniform positive lower bound.
  obtain ⟨δ, hδ, hδlower⟩ :=
    hA.exists_forall_le' ((Metric.continuous_infDist_pt B).continuousOn) hpos
  exact ⟨δ, hδ, hδlower⟩

/-- Helper for Theorem 1.49: a cluster point in `A` forces arbitrarily late visits arbitrarily
close to `A`. -/
private lemma exists_ge_infDist_lt_of_mem_mapClusterPt {A : Set X} {a : X} {u : ℕ → X}
    (haA : a ∈ A)
    (ha : MapClusterPt a atTop u) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n ≥ N, Metric.infDist (u n) A < ε := by
  -- The cluster-point condition gives arbitrarily late terms inside every ball around `a`.
  have hfreq : ∃ᶠ n in atTop, u n ∈ Metric.ball a ε :=
    (mapClusterPt_iff_frequently.mp ha) (Metric.ball a ε) (Metric.ball_mem_nhds a hε)
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨n, hnN, hnball⟩ := hfreq N
  refine ⟨n, hnN, lt_of_le_of_lt (Metric.infDist_le_dist_of_mem haA) ?_⟩
  simpa [Metric.mem_ball, dist_comm] using hnball

/-- Helper for Theorem 1.49: being within `δ / 3` of the left piece forces distance greater than
`2 * δ / 3` from the right piece. -/
private lemma two_thirds_gap_of_one_third_near_left {A B : Set X} (hAne : A.Nonempty) {δ : ℝ}
    (hlower : ∀ a ∈ A, δ ≤ Metric.infDist a B) {x : X} (hx : Metric.infDist x A < δ / 3) :
    2 * δ / 3 < Metric.infDist x B := by
  -- Pick a point of `A` close to `x` and compare distances through the Lipschitz control of `infDist`.
  obtain ⟨a, haA, hxa⟩ := (Metric.infDist_lt_iff hAne).mp hx
  have hδle : δ ≤ Metric.infDist x B + dist x a := by
    calc
      δ ≤ Metric.infDist a B := hlower a haA
      _ ≤ Metric.infDist x B + dist a x :=
        by
          simpa using
            (show Metric.infDist a B ≤ Metric.infDist x B + dist a x from
              Metric.infDist_le_infDist_add_dist)
      _ = Metric.infDist x B + dist x a := by rw [dist_comm]
  linarith

/- Proof sketch: argue by contradiction, separating the cluster-point set into two disjoint closed
pieces with positive distance; then use `dist (u n) (u (n + 1)) → 0` and compactness to extract
a new cluster point whose distance to one piece lies strictly between `δ / 3` and `2 * δ / 3`,
contradicting the separation. -/
/-- Theorem 1.49: (Ostrowski) in a metric space, if `C` is compact, a sequence `u` takes values in
`C`, and `dist (u n) (u (n + 1)) → 0`, then the cluster-point set of `u` is connected. Under the
hypothesis `u n ∈ C`, every cluster point already lies in `C`, so this is equivalent to the
textbook formulation with `C ∩ {x | MapClusterPt x atTop u}`. -/
theorem isConnected_clusterPoints_of_tendsto_dist_succ_eq_zero
    {C : Set X} {u : ℕ → X} (hC : IsCompact C) (huC : ∀ n, u n ∈ C)
    (hstep : Tendsto (fun n ↦ dist (u n) (u (n + 1))) atTop (𝓝 0)) :
    IsConnected {x | MapClusterPt x atTop u} := by
  classical
  let S : Set X := {x | MapClusterPt x atTop u}
  -- Compactness of `C` supplies at least one cluster point.
  have hSnonempty : S.Nonempty := by
    obtain ⟨x, -, hxcluster⟩ :=
      hC.isCountablyCompact.seq_clusterPt u (Filter.Eventually.of_forall huC)
    exact ⟨x, hxcluster⟩
  -- The cluster-point set is closed, hence compact inside `C`.
  have hSclosed : IsClosed S := by
    simpa [S, MapClusterPt] using
      (isClosed_setOf_clusterPt : IsClosed {x | ClusterPt x (map u atTop)})
  have hSsubsetC : S ⊆ C := by
    intro x hx
    exact IsClosed.mem_of_mapClusterPt hC.isClosed hx (Filter.Eventually.of_forall huC)
  have hScompact : IsCompact S := hC.of_isClosed_subset hSclosed hSsubsetC
  change IsConnected S
  refine ⟨hSnonempty, ?_⟩
  by_contra hSnotpre
  -- A failure of preconnectedness yields a separation by closed sets.
  have hsep : ∃ U V, IsClosed U ∧ IsClosed V ∧ S ⊆ U ∪ V ∧ Disjoint U V ∧ ¬ S ⊆ U ∧ ¬ S ⊆ V := by
    rw [isPreconnected_iff_subset_of_fully_disjoint_closed hSclosed] at hSnotpre
    push Not at hSnotpre
    exact hSnotpre
  obtain ⟨U, V, hUclosed, hVclosed, hSUV, hUV, hSnotU, hSnotV⟩ := hsep
  let A : Set X := S ∩ U
  let B : Set X := S ∩ V
  have hUV' : ∀ ⦃x⦄, x ∈ U → x ∈ V → False := by
    rw [Set.disjoint_left] at hUV
    exact hUV
  have hAclosed : IsClosed A := hSclosed.inter hUclosed
  have hBclosed : IsClosed B := hSclosed.inter hVclosed
  have hAne : A.Nonempty := by
    obtain ⟨a, haS, haVnot⟩ := Set.not_subset.1 hSnotV
    have haU : a ∈ U := by
      rcases hSUV haS with haU | haV
      · exact haU
      · exact (haVnot haV).elim
    exact ⟨a, ⟨haS, haU⟩⟩
  have hBne : B.Nonempty := by
    obtain ⟨b, hbS, hbUnot⟩ := Set.not_subset.1 hSnotU
    have hbV : b ∈ V := by
      rcases hSUV hbS with hbU | hbV
      · exact (hbUnot hbU).elim
      · exact hbV
    exact ⟨b, ⟨hbS, hbV⟩⟩
  have hAdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hUV' hxA.2 hxB.2
  have hAcompact : IsCompact A := hScompact.of_isClosed_subset hAclosed (by
    intro x hx
    exact hx.1)
  have hAne_keep : A.Nonempty := hAne
  have hBne_keep : B.Nonempty := hBne
  obtain ⟨a₀, ha₀A⟩ := hAne
  obtain ⟨b₀, hb₀B⟩ := hBne
  have ha₀cluster : MapClusterPt a₀ atTop u := ha₀A.1
  have hb₀cluster : MapClusterPt b₀ atTop u := hb₀B.1
  -- The two closed pieces are separated by a uniform positive gap in `infDist`.
  obtain ⟨δ, hδpos, hδlower⟩ :=
    exists_positive_infDist_lower_bound_of_disjoint hAcompact hBclosed hBne_keep hAdisjoint
  have hδthird : 0 < δ / 3 := by linarith
  have hδtwo : δ / 3 < 2 * δ / 3 := by linarith
  -- For every late threshold `N`, one can find a first crossing index into the `2δ / 3`-neighborhood
  -- of `B`, while still staying outside the `δ / 3`-neighborhood of `B`.
  have hcross :
      ∀ N, ∃ n ≥ N, δ / 3 < Metric.infDist (u n) B ∧ Metric.infDist (u n) B < 2 * δ / 3 := by
    intro N
    obtain ⟨M, hMraw⟩ := Metric.tendsto_atTop.1 hstep (δ / 3) hδthird
    have hM : ∀ n ≥ M, dist (u n) (u (n + 1)) < δ / 3 := by
      intro n hn
      have hsmall := hMraw n hn
      simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg : 0 ≤ dist (u n) (u (n + 1)))] using hsmall
    obtain ⟨k, hk_ge, hkAnear⟩ :=
      exists_ge_infDist_lt_of_mem_mapClusterPt ha₀A ha₀cluster hδthird (max N M)
    have hkN : k ≥ N := le_trans (le_max_left N M) hk_ge
    have hkM : k ≥ M := le_trans (le_max_right N M) hk_ge
    have hkBfar : 2 * δ / 3 < Metric.infDist (u k) B :=
      two_thirds_gap_of_one_third_near_left hAne_keep hδlower hkAnear
    obtain ⟨j, hj_ge, hjBnear⟩ :=
      exists_ge_infDist_lt_of_mem_mapClusterPt hb₀B hb₀cluster hδthird (max (k + 1) M)
    have hjk : k < j := by
      exact lt_of_lt_of_le (Nat.lt_succ_self k) (le_trans (le_max_left (k + 1) M) hj_ge)
    let Q : ℕ → Prop := fun n ↦ k < n ∧ n ≤ j ∧ Metric.infDist (u n) B < 2 * δ / 3
    have hQj : Q j := by
      refine ⟨hjk, le_rfl, lt_trans hjBnear hδtwo⟩
    let l : ℕ := Nat.find ⟨j, hQj⟩
    have hlQ : Q l := Nat.find_spec ⟨j, hQj⟩
    have hkl : k < l := hlQ.1
    have hlj : l ≤ j := hlQ.2.1
    have hlupper : Metric.infDist (u l) B < 2 * δ / 3 := hlQ.2.2
    have hlpos : 0 < l := lt_of_le_of_lt (Nat.zero_le k) hkl
    have hpred_ge_M : l - 1 ≥ M := by
      omega
    have hstep_small : dist (u (l - 1)) (u l) < δ / 3 := by
      have hstep_small' := hM (l - 1) hpred_ge_M
      have hlpred : l - 1 + 1 = l := Nat.sub_add_cancel (Nat.succ_le_of_lt hlpos)
      simpa [hlpred] using hstep_small'
    have hpred_far : 2 * δ / 3 ≤ Metric.infDist (u (l - 1)) B := by
      by_cases hl_eq : l = k + 1
      · have hl_sub : l - 1 = k := by
          omega
        simpa [hl_sub] using hkBfar.le
      · have hk_pred : k < l - 1 := by
          omega
        have hpred_lt : l - 1 < l := Nat.pred_lt hlpos.ne'
        have hnotQpred : ¬ Q (l - 1) := Nat.find_min ⟨j, hQj⟩ hpred_lt
        have hpred_le_j : l - 1 ≤ j := by
          omega
        have hpred_not_lt : ¬ Metric.infDist (u (l - 1)) B < 2 * δ / 3 := by
          intro hlt
          exact hnotQpred ⟨hk_pred, hpred_le_j, hlt⟩
        exact le_of_not_gt hpred_not_lt
    have hllower : δ / 3 < Metric.infDist (u l) B := by
      have hcompare : 2 * δ / 3 ≤ Metric.infDist (u l) B + dist (u (l - 1)) (u l) := by
        calc
          2 * δ / 3 ≤ Metric.infDist (u (l - 1)) B := hpred_far
          _ ≤ Metric.infDist (u l) B + dist (u (l - 1)) (u l) :=
            by
              simpa using
                (show
                  Metric.infDist (u (l - 1)) B ≤
                    Metric.infDist (u l) B + dist (u (l - 1)) (u l) from
                  Metric.infDist_le_infDist_add_dist)
      linarith
    exact ⟨l, le_trans hkN hkl.le, hllower, hlupper⟩
  -- These intermediate-distance indices produce a cluster point inside the closed middle band.
  have hfreq :
      ∃ᶠ n in atTop,
        δ / 3 < Metric.infDist (u n) B ∧ Metric.infDist (u n) B < 2 * δ / 3 := by
    rw [Filter.frequently_atTop]
    exact hcross
  let D : Set X := {x | x ∈ C ∧ δ / 3 ≤ Metric.infDist x B ∧ Metric.infDist x B ≤ 2 * δ / 3}
  have hDclosed : IsClosed D := by
    refine hC.isClosed.inter ?_
    exact (isClosed_le continuous_const (Metric.continuous_infDist_pt B)).inter
      (isClosed_le (Metric.continuous_infDist_pt B) continuous_const)
  have hDcompact : IsCompact D := hC.of_isClosed_subset hDclosed (by
    intro x hx
    exact hx.1)
  have hfreqD : ∃ᶠ n in atTop, u n ∈ D := by
    refine hfreq.mono ?_
    intro n hn
    exact ⟨huC n, le_of_lt hn.1, le_of_lt hn.2⟩
  obtain ⟨z, hzD, hzcluster⟩ := hDcompact.exists_mapClusterPt_of_frequently hfreqD
  have hzS : z ∈ S := hzcluster
  have hznotV : z ∉ V := by
    intro hzV
    have hznotB : z ∉ B := by
      have hposB : 0 < Metric.infDist z B := by
        linarith [hzD.2.1]
      exact ((hBclosed.notMem_iff_infDist_pos hBne_keep).2 hposB)
    exact hznotB ⟨hzS, hzV⟩
  have hzA : z ∈ A := by
    have hzU : z ∈ U := by
      rcases hSUV hzS with hzU | hzV
      · exact hzU
      · exact (hznotV hzV).elim
    exact ⟨hzS, hzU⟩
  have hz_gap : δ ≤ Metric.infDist z B := hδlower z hzA
  have hz_upper : Metric.infDist z B ≤ 2 * δ / 3 := hzD.2.2
  linarith

/-- Theorem 1.49 in textbook form: under the same hypotheses, the cluster points of `u` lying in
`C` form a connected set. This is a one-step restatement of
`isConnected_clusterPoints_of_tendsto_dist_succ_eq_zero`. -/
theorem isConnected_clusterPointsIn_compact_of_tendsto_dist_succ_eq_zero
    {C : Set X} {u : ℕ → X} (hC : IsCompact C) (huC : ∀ n, u n ∈ C)
    (hstep : Tendsto (fun n ↦ dist (u n) (u (n + 1))) atTop (𝓝 0)) :
    IsConnected {x | x ∈ C ∧ MapClusterPt x atTop u} := by
  have hcluster :
      {x | x ∈ C ∧ MapClusterPt x atTop u} = {x | MapClusterPt x atTop u} := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨IsClosed.mem_of_mapClusterPt hC.isClosed hx (Filter.Eventually.of_forall huC), hx⟩
  simpa [hcluster] using isConnected_clusterPoints_of_tendsto_dist_succ_eq_zero hC huC hstep

/-! Source item: Chap01/Theorem_1_50 -/


variable {X : Type u} [MetricSpace X] [Nonempty X] [CompleteSpace X]
variable {β : NNReal} {T : X → X}

private theorem fixedPoints_eq_singleton_fixedPoint (hT : ContractingWith β T) :
    fixedPoints T = {hT.fixedPoint T} := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_singleton_iff]
    exact hT.fixedPoint_unique hy
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hT.fixedPoint_isFixedPt

private theorem dist_iterate_succ_fixedPoint_le (hT : ContractingWith β T) (x₀ : X) :
    ∀ n : ℕ,
      dist (T^[n + 1] x₀) (hT.fixedPoint T) ≤ β * dist (T^[n] x₀) (hT.fixedPoint T) := by
  intro n
  simpa [iterate_succ_apply', hT.fixedPoint_isFixedPt.eq] using
    hT.dist_le_mul (T^[n] x₀) (hT.fixedPoint T)

private theorem dist_iterate_fixedPoint_le_geometric (hT : ContractingWith β T) (x₀ : X) :
    ∀ n : ℕ,
      dist (T^[n] x₀) (hT.fixedPoint T) ≤ β ^ n * dist x₀ (hT.fixedPoint T) := by
  intro n
  simpa [(hT.fixedPoint_isFixedPt.iterate n).eq] using
    (hT.toLipschitzWith.iterate n).dist_le_mul x₀ (hT.fixedPoint T)

private theorem initial_error_bounds (hT : ContractingWith β T) (x₀ : X) :
    dist x₀ (T x₀) / (1 + β) ≤ dist x₀ (hT.fixedPoint T) ∧
      dist x₀ (hT.fixedPoint T) ≤ dist x₀ (T x₀) / (1 - β) := by
  constructor
  · have hstep :
        dist (hT.fixedPoint T) (T x₀) ≤ β * dist x₀ (hT.fixedPoint T) := by
      simpa [iterate_zero, iterate_succ_apply', dist_comm] using
        dist_iterate_succ_fixedPoint_le hT x₀ 0
    have hsum :
        dist x₀ (T x₀) ≤ (1 + β) * dist x₀ (hT.fixedPoint T) := by
      calc
        dist x₀ (T x₀) ≤ dist x₀ (hT.fixedPoint T) + dist (hT.fixedPoint T) (T x₀) :=
          dist_triangle _ _ _
        _ ≤ dist x₀ (hT.fixedPoint T) + β * dist x₀ (hT.fixedPoint T) := by
          gcongr
        _ = (1 + β) * dist x₀ (hT.fixedPoint T) := by
          ring
    have hpos : (0 : ℝ) < 1 + β := by
      positivity
    exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using hsum)
  · simpa using hT.apriori_dist_iterate_fixedPoint_le x₀ 0

/-- Theorem 1.50 (Banach-Picard): a contraction on a nonempty complete metric space has a unique
fixed point, expressed canonically as `fixedPoints T = {x}`, and this point satisfies the
textbook one-step, geometric, a priori, a posteriori, and initial two-sided bounds for every
starting point `x₀`. -/
-- Proof sketch: take the canonical fixed point supplied by `ContractingWith.fixedPoint`; the
-- singleton fixed-point set follows from `fixedPoint_unique`. The one-step and geometric bounds
-- come from the contraction inequality and the Lipschitz control of iterates, the a priori and
-- a posteriori estimates are the corresponding mathlib theorems, and the initial two-sided bound
-- combines the one-step estimate at `n = 0` with the a priori estimate at `n = 0`.
theorem exists_fixedPoint_with_banach_picard_estimates (hT : ContractingWith β T) :
    ∃ x : X,
      fixedPoints T = {x} ∧
      (∀ x₀ : X, ∀ n : ℕ, dist (T^[n + 1] x₀) x ≤ β * dist (T^[n] x₀) x) ∧
      (∀ x₀ : X, ∀ n : ℕ, dist (T^[n] x₀) x ≤ β ^ n * dist x₀ x) ∧
      (∀ x₀ : X, ∀ n : ℕ,
        dist (T^[n] x₀) x ≤ dist x₀ (T x₀) * (β : ℝ) ^ n / (1 - β)) ∧
      (∀ x₀ : X, ∀ n : ℕ,
        dist (T^[n] x₀) x ≤ dist (T^[n] x₀) (T^[n + 1] x₀) / (1 - β)) ∧
      ∀ x₀ : X,
        dist x₀ (T x₀) / (1 + β) ≤ dist x₀ x ∧
          dist x₀ x ≤ dist x₀ (T x₀) / (1 - β) := by
  refine ⟨hT.fixedPoint T, fixedPoints_eq_singleton_fixedPoint hT, ?_, ?_, ?_, ?_, ?_⟩
  · intro x₀ n
    exact dist_iterate_succ_fixedPoint_le hT x₀ n
  · intro x₀ n
    exact dist_iterate_fixedPoint_le_geometric hT x₀ n
  · intro x₀ n
    simpa using hT.apriori_dist_iterate_fixedPoint_le x₀ n
  · intro x₀ n
    simpa using hT.aposteriori_dist_iterate_fixedPoint_le x₀ n
  · intro x₀
    exact initial_error_bounds hT x₀

/-! Source item: Chap01/Theorem_1_51 -/

/-- The tail sum of the nonnegative coefficient sequence controlling the iterate distances. -/
noncomputable abbrev summable_iterate_bound_tail (β : ℕ → NNReal) (n : ℕ) : NNReal :=
  ∑' m, β (n + m)

/-- The zeroth tail of the iterate-bound coefficients is the full sum of the series. -/
-- Proof sketch: unfold `summable_iterate_bound_tail`; for `n = 0` the shifted series is exactly
-- the original series.
theorem summable_iterate_bound_tail_zero (β : ℕ → NNReal) :
    summable_iterate_bound_tail β 0 = ∑' n, β n := by
  -- Unfold the tail definition and simplify the zero shift.
  simp [summable_iterate_bound_tail]

/-- Helper for Theorem 1.51: the iterate-distance hypothesis bounds the successive increments of
the orbit of `x₀`. -/
private lemma iterate_successive_dist_le {X : Type u} [MetricSpace X] {T : X → X}
    {β : ℕ → NNReal}
    (hiterate : ∀ n : ℕ, ∀ x y : X,
      dist (T^[n] x) (T^[n] y) ≤ (β n : ℝ) * dist x y) (x₀ : X) :
    ∀ n : ℕ, dist (T^[n] x₀) (T^[n + 1] x₀) ≤ (β n : ℝ) * dist x₀ (T x₀) := by
  intro n
  -- Rewrite the next iterate so the given `n`-step estimate applies directly to `x₀` and `T x₀`.
  simpa [Nat.succ_eq_add_one, Function.iterate_succ_apply] using hiterate n x₀ (T x₀)

/-- Helper for Theorem 1.51: applying the iterate bound to two fixed points yields the textbook
estimate used for uniqueness. -/
private lemma fixed_point_dist_le_mul_beta {X : Type u} [MetricSpace X] {T : X → X}
    {β : ℕ → NNReal}
    (hiterate : ∀ n : ℕ, ∀ x y : X,
      dist (T^[n] x) (T^[n] y) ≤ (β n : ℝ) * dist x y) {x y : X}
    (hx : IsFixedPt T x) (hy : IsFixedPt T y) :
    ∀ n : ℕ, dist x y ≤ (β n : ℝ) * dist x y := by
  intro n
  -- Each iterate fixes both points, so the iterate-distance bound collapses back to `dist x y`.
  simpa [(hx.iterate n).eq, (hy.iterate n).eq] using hiterate n x y

/-- Helper for Theorem 1.51: the real tail sum of the weighted coefficients is the coefficient
tail multiplied by the fixed scalar. -/
private lemma iterate_tail_sum_as_bound (β : ℕ → NNReal) (n : ℕ) (c : ℝ) :
    (∑' m, ((β (n + m) : ℝ) * c)) = (summable_iterate_bound_tail β n : ℝ) * c := by
  -- Pull the scalar out of the series, then identify the remaining tail sum with the NNReal tail.
  rw [tsum_mul_right, summable_iterate_bound_tail, ← NNReal.coe_tsum]

/-- Theorem 1.51: if a self-map of a complete metric space has iterates whose pairwise distances
are bounded by a summable nonnegative sequence, then every orbit converges to the unique fixed
point, with the quantitative tail estimate given by the coefficient series. -/
-- Proof sketch: apply the iterate-distance estimate with `y = T x₀` to show that the orbit
-- `(fun n ↦ T^[n] x₀)` has summable successive distances, hence is Cauchy; completeness gives a
-- limit `x`. Then use the `n = 1` bound and continuity of the limit along the orbit to prove
-- `T x = x`, apply the bound to two fixed points and choose `n` with `β n < 1` to get uniqueness,
-- and finally bound `dist (T^[n] x₀) x` by the tail sum of the successive-distance estimate.
theorem exists_fixed_point_of_summable_iterate_bound {X : Type u} [MetricSpace X]
    [CompleteSpace X] {T : X → X} {β : ℕ → NNReal} (hβ : Summable β)
    (hiterate : ∀ n : ℕ, ∀ x y : X, dist (T^[n] x) (T^[n] y) ≤ (β n : ℝ) * dist x y) (x₀ : X) :
    ∃ x : X,
      IsFixedPt T x ∧
      (∀ ⦃y : X⦄, IsFixedPt T y → y = x) ∧
      Tendsto (fun n ↦ T^[n] x₀) atTop (nhds x) ∧
      ∀ n : ℕ, dist (T^[n] x₀) x ≤ (summable_iterate_bound_tail β n : ℝ) * dist x₀ (T x₀) := by
  -- The orbit increments are controlled by the summable coefficient sequence times the first step.
  have hstep :
      ∀ n : ℕ, dist (T^[n] x₀) (T^[n + 1] x₀) ≤ (β n : ℝ) * dist x₀ (T x₀) :=
    iterate_successive_dist_le hiterate x₀
  have hsummable_dist : Summable (fun n ↦ (β n : ℝ) * dist x₀ (T x₀)) := by
    -- Coercing the NNReal series to `ℝ` preserves summability, and scalar multiplication preserves
    -- it as well.
    exact ((NNReal.summable_coe).2 hβ).mul_right (dist x₀ (T x₀))
  have hcauchy : CauchySeq (fun n ↦ T^[n] x₀) :=
    cauchySeq_of_dist_le_of_summable (fun n ↦ (β n : ℝ) * dist x₀ (T x₀)) hstep hsummable_dist
  obtain ⟨x, hx_tendsto⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hT_lipschitz : LipschitzWith (β 1) T := by
    -- The case `n = 1` of the hypothesis says exactly that `T` is Lipschitz.
    refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    simpa using hiterate 1 y z
  have hx_fixed : IsFixedPt T x :=
    isFixedPt_of_tendsto_iterate hx_tendsto hT_lipschitz.continuous.continuousAt
  refine ⟨x, ?_⟩
  refine ⟨hx_fixed, ?_, hx_tendsto, ?_⟩
  · intro y hy_fixed
    -- Choose an iterate with coefficient strictly below `1`; then the fixed-point distance
    -- estimate forces the distance to vanish.
    have hβ_lt_one : ∀ᶠ n in atTop, β n < 1 := by
      have hmem : Set.Iio (1 : NNReal) ∈ nhds (0 : NNReal) := by
        exact Iio_mem_nhds (by simp)
      exact (NNReal.tendsto_atTop_zero_of_summable hβ) hmem
    rcases (eventually_atTop.1 hβ_lt_one) with ⟨n, hn⟩
    have hdist_le : dist x y ≤ (β n : ℝ) * dist x y :=
      fixed_point_dist_le_mul_beta hiterate hx_fixed hy_fixed n
    have hβn_lt : (β n : ℝ) < 1 := by
      exact_mod_cast hn n le_rfl
    have hxy : x = y := by
      by_contra hxy
      have hdist_pos : 0 < dist x y := dist_pos.mpr hxy
      nlinarith
    simpa [eq_comm] using hxy
  · intro n
    -- Apply the standard distance-to-limit estimate to the orbit and rewrite the tail series into
    -- the textbook coefficient tail.
    calc
      dist (T^[n] x₀) x ≤ ∑' m, ((β (n + m) : ℝ) * dist x₀ (T x₀)) := by
        exact dist_le_tsum_of_dist_le_of_tendsto
          (fun m ↦ (β m : ℝ) * dist x₀ (T x₀)) hstep hsummable_dist hx_tendsto n
      _ = (summable_iterate_bound_tail β n : ℝ) * dist x₀ (T x₀) := by
        simpa using iterate_tail_sum_as_bound β n (dist x₀ (T x₀))

/-! Source item: Chap01/Text_1_0_66 -/


variable {X : Type u} [MetricSpace X]

/-- In a metric space, a sequence converges to `x` exactly when its distances to `x` tend to `0`.
-/
-- Proof sketch: specialize `tendsto_iff_dist_tendsto_zero` to the filter `atTop` on `ℕ`.
theorem sequence_tendsto_iff_dist_tendsto_zero {u : ℕ → X} {x : X} :
    Tendsto u atTop (nhds x) ↔ Tendsto (fun n ↦ dist (u n) x) atTop (nhds 0) := by
  simpa using
    (tendsto_iff_dist_tendsto_zero :
      Tendsto u atTop (nhds x) ↔ Tendsto (fun n ↦ dist (u n) x) atTop (nhds 0))

/-! Source item: Chap01/Text_1_0_67 -/


variable {X : Type u} [MetricSpace X]

/-- Text 1.0.67: a metric space is complete exactly when every Cauchy sequence converges to a
point of the space. -/
-- Proof sketch: use `cauchySeq_tendsto_of_complete` for the forward implication and
-- `Metric.complete_of_cauchySeq_tendsto` for the converse implication.
theorem completeSpace_iff_cauchySeq_tendsto :
    CompleteSpace X ↔ ∀ u : ℕ → X, CauchySeq u → ∃ x : X, Tendsto u atTop (nhds x) := by
  constructor
  · intro hX u hu
    letI : CompleteSpace X := hX
    exact cauchySeq_tendsto_of_complete hu
  · intro h
    exact Metric.complete_of_cauchySeq_tendsto h

/-! ### Distances to sets, excess, and approximate fixed points
Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/ext_def_1 -/

/-- The point-to-set distance `d(x,C) = inf_{y ∈ C} d(x,y)`, including the
  convention `d(x, ∅) = +∞`. -/
recall Metric.infEDist

/-- The excess `e(C,D) = sup_{x ∈ C} d(x,D)`.  Consequently it is infinite
  when `C` is nonempty and `D` is empty. -/
noncomputable def excess {X : Type*} [PseudoMetricSpace X] (C D : Set X) : ENNReal :=
  ⨆ x ∈ C, Metric.infEDist x D

/-- The Hausdorff distance `h(C,D) = max {e(C,D), e(D,C)}`, including the
  paper's empty-set conventions. -/
recall Metric.hausdorffEDist

/-- `ε`-approximate fixed points, for `ε ≥ 0`. -/
def approximateFixedPoints {X : Type*} [PseudoMetricSpace X]
    (T : X → Set X) (ε : ℝ) : Set X :=
  {x | 0 ≤ ε ∧ Metric.infEDist x (T x) ≤ ENNReal.ofReal ε}

/-- Exact fixed points: `Fix(T) = {x ∈ X | x ∈ T(x)}`. -/
def fixedPoints {X : Type*} (T : X → Set X) : Set X := {x | x ∈ T x}

/-! Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/ext_thm_6 -/

/-- Convergence of ε-approximate fixed points to the exact contraction fixed
  point (cf. [4, Proposition 4(g)]). For the contractive fixed-point setting
  used in Section 7: if T is a λ-contraction (λ∈[0,1)) with unique fixed
  point x*, then ε-Fix(T) converges in the Painlevé–Kuratowski sense to
  {x*} as ε→0. -/
theorem epsilon_approximate_fixedPoint_bound {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (c : ℝ) (xstar : X)
    (hc : 0 ≤ c) (hc_lt_one : c < 1)
    (hcontr : ∀ x y : X, dist (T x) (T y) ≤ c * dist x y)
    (hfix : T xstar = xstar) (huniq : ∀ x : X, T x = x → x = xstar) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧
      ∀ y : X, dist y (T y) ≤ ε → dist y xstar < η := by
  intro η hη
  have hgap : 0 < 1 - c := sub_pos.mpr hc_lt_one
  refine ⟨η * (1 - c) / 2, div_pos (mul_pos hη hgap) (by norm_num), ?_⟩
  intro y hy
  have hdist : dist y xstar ≤ η * (1 - c) / 2 + c * dist y xstar := by
    calc
      dist y xstar ≤ dist y (T y) + dist (T y) xstar := dist_triangle _ _ _
      _ = dist y (T y) + dist (T y) (T xstar) := by rw [hfix]
      _ ≤ η * (1 - c) / 2 + c * dist y xstar := add_le_add hy (hcontr y xstar)
  nlinarith [show 0 ≤ dist y xstar from dist_nonneg]
