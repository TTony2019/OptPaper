import Mathlib
import Mathlib.Data.List.TFAE
import Foundation.Hilbert.WeakTopology
import Foundation.Topology.Sequences
import Foundation.Hilbert.WeakConvergence

/-!
# Convex WeakClosed

Weak closedness and weak compactness of convex sets, convex hull convergence, and Minkowski-sum closedness.
-/

open Filter
open scoped InnerProductSpace
open scoped BigOperators Topology
open scoped Pointwise
open scoped Topology InnerProductSpace
open scoped Topology

/-! Source item: Chap03/Theorem_3_34 -/
universe u


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Theorem 3.34: weak sequential closedness of the weak-space image pulls back to
strong sequential closedness of the original set. -/
-- Proof sketch: a strongly convergent sequence becomes weakly convergent after applying the
-- canonical continuous map `toWeakSpace`, so sequential closedness of the weak image descends
-- along the injective preimage.
private lemma isSeqClosed_of_weak_image_isSeqClosed {C : Set 𝓗}
    (hC : IsSeqClosed ((toWeakSpace ℝ 𝓗) '' C)) :
    IsSeqClosed C := by
  -- Pull back sequential closedness along the sequentially continuous map to the weak space.
  have hcont : Continuous (toWeakSpace ℝ 𝓗 : 𝓗 → WeakSpace ℝ 𝓗) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using (toWeakSpaceCLM ℝ 𝓗).continuous
  simpa [Set.preimage_image_eq _ (toWeakSpace ℝ 𝓗).injective] using hC.preimage hcont.seqContinuous

/-- Helper for Theorem 3.34: a closed convex set has weakly closed image in the weak space. -/
-- Proof sketch: `Convex.toWeakSpace_closure` identifies the weak closure of the image with the
-- image of the strong closure, and closedness makes the latter equal to the original image.
private lemma weak_image_isClosed_of_isClosed_convex {C : Set 𝓗}
    (hC_convex : Convex ℝ C) (hC_closed : IsClosed C) :
    IsClosed ((toWeakSpace ℝ 𝓗) '' C) := by
  -- Rewrite the weak closure of the image as the image of the strong closure.
  rw [← closure_eq_iff_isClosed]
  calc
    closure ((toWeakSpace ℝ 𝓗) '' C) = (toWeakSpace ℝ 𝓗) '' closure C := by
      simpa using (hC_convex.toWeakSpace_closure ℝ).symm
    _ = (toWeakSpace ℝ 𝓗) '' C := by
      rw [hC_closed.closure_eq]

/-- Helper for Theorem 3.34: weak closedness of the weak-space image forces strong closedness of
the original convex set. -/
-- Proof sketch: if `x ∈ closure C`, then `toWeakSpace x` lies in the weak closure of the image;
-- weak closedness returns a witness from `C`, and injectivity of `toWeakSpace` identifies it
-- with `x`.
private lemma isClosed_of_weak_image_isClosed_convex {C : Set 𝓗}
    (hC_convex : Convex ℝ C) (hC_weakClosed : IsClosed ((toWeakSpace ℝ 𝓗) '' C)) :
    IsClosed C := by
  -- It suffices to prove that every point in `closure C` already lies in `C`.
  rw [← closure_eq_iff_isClosed]
  refine le_antisymm ?_ subset_closure
  intro x hx
  -- Transport the closure membership to the weak space using the convex closure identity.
  have hxWeak : toWeakSpace ℝ 𝓗 x ∈ closure ((toWeakSpace ℝ 𝓗) '' C) := by
    rw [← hC_convex.toWeakSpace_closure ℝ]
    exact ⟨x, hx, rfl⟩
  -- Weak closedness yields a witness in the image of `C`.
  rw [hC_weakClosed.closure_eq] at hxWeak
  rcases hxWeak with ⟨y, hyC, hyx⟩
  -- Injectivity of `toWeakSpace` pulls the witness back to the original space.
  exact (toWeakSpace ℝ 𝓗).injective hyx ▸ hyC

/-- Theorem 3.34, weak-closedness form: for a convex subset `C` of a real inner-product space,
`C` is closed exactly when its image in `WeakSpace ℝ 𝓗` is weakly closed. -/
theorem isClosed_iff_weak_image_isClosed_of_convex {C : Set 𝓗} (hC_convex : Convex ℝ C) :
    IsClosed C ↔ IsClosed ((toWeakSpace ℝ 𝓗) '' C) := by
  refine ⟨weak_image_isClosed_of_isClosed_convex hC_convex,
    isClosed_of_weak_image_isClosed_convex hC_convex⟩

/-- Theorem 3.34, weak-sequential form: for a convex subset `C` of a real inner-product space,
`C` is sequentially closed exactly when its image in `WeakSpace ℝ 𝓗` is weakly sequentially
closed. -/
theorem isSeqClosed_iff_weak_image_isSeqClosed_of_convex {C : Set 𝓗} (hC_convex : Convex ℝ C) :
    IsSeqClosed C ↔ IsSeqClosed ((toWeakSpace ℝ 𝓗) '' C) := by
  refine ⟨?_, isSeqClosed_of_weak_image_isSeqClosed⟩
  intro hC_seqClosed
  have hC_closed : IsClosed C :=
    (isSeqClosed_iff_isClosed : IsSeqClosed C ↔ IsClosed C).1 hC_seqClosed
  exact ((isClosed_iff_weak_image_isClosed_of_convex hC_convex).1 hC_closed).isSeqClosed

/-- Theorem 3.34: for a convex subset `C` of a real inner-product space, weak sequential closedness,
strong sequential closedness, strong closedness, and weak closedness are equivalent. The weak
conditions are expressed on the image of `C` in `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: `(i) → (ii)` because norm convergence implies weak convergence. `(ii) ↔ (iii)`
-- because the norm topology is metrizable, hence sequential. `(iii) → (iv)` by the Hilbert-space
-- projection argument for closed convex sets, which shows weak limits of points of `C` remain in
-- `C`. `(iv) → (i)` because every weakly closed set is weakly sequentially closed.
theorem convex_weaklySeqClosed_sequentiallyClosed_closed_weaklyClosed_tfae
    {C : Set 𝓗} (hC_convex : Convex ℝ C) :
    List.TFAE
      [IsSeqClosed ((toWeakSpace ℝ 𝓗) '' C),
        IsSeqClosed C,
        IsClosed C,
        IsClosed ((toWeakSpace ℝ 𝓗) '' C)] := by
  -- The sequentially closed strong and weak-space formulations are equivalent for convex sets.
  tfae_have 1 ↔ 2 := by
    simpa [iff_comm] using isSeqClosed_iff_weak_image_isSeqClosed_of_convex hC_convex
  -- In a Hilbert space, the norm topology is metric, so closedness and sequential closedness agree.
  tfae_have 2 ↔ 3 := by
    simpa using (isSeqClosed_iff_isClosed : IsSeqClosed C ↔ IsClosed C)
  -- Convexity identifies strong closedness with weak closedness after transport to `WeakSpace`.
  tfae_have 3 ↔ 4 := by
    exact isClosed_iff_weak_image_isClosed_of_convex hC_convex
  tfae_finish

/-! Source item: Chap03/Corollary_3_35 -/

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Corollary 3.35: a weak limit of points in a closed convex set of a real inner-product space
belongs to the set. -/
-- Proof sketch: `Theorem_3_34` already identifies norm-closed convex sets with weakly closed
-- subsets after transport to `WeakSpace`. Once the weak image of `C` is closed, the limit point
-- lies in that image by closure, and injectivity of `toWeakSpace` pulls the conclusion back to `C`.
theorem mem_of_tendsto_weakly_of_isClosed_convex {C : Set 𝓗}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {xₙ : ℕ → 𝓗} {x : 𝓗} (hxₙ : ∀ n, xₙ n ∈ C)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) atTop
      (nhds (toWeakSpace ℝ 𝓗 x))) :
    x ∈ C := by
  have hC_weakClosed : IsClosed ((toWeakSpace ℝ 𝓗) '' C) :=
    (isClosed_iff_weak_image_isClosed_of_convex hC_convex).1 hC_closed
  have hxWeak :
      toWeakSpace ℝ 𝓗 x ∈ closure ((toWeakSpace ℝ 𝓗) '' C) := by
    exact mem_closure_of_tendsto hweak <|
      Filter.Eventually.of_forall fun n ↦ ⟨xₙ n, hxₙ n, rfl⟩
  rw [hC_weakClosed.closure_eq] at hxWeak
  rcases hxWeak with ⟨y, hyC, hyx⟩
  exact (toWeakSpace ℝ 𝓗).injective hyx ▸ hyC

/-! Source item: Chap03/Corollary_3_36 -/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Corollary 3.36: weak convergence places the limit in the norm closure of the convex
hull of the sequence range. -/
private lemma mem_closure_convexHull_of_tendsto_weakly
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x))) :
    x ∈ closure (convexHull ℝ (Set.range xₙ)) := by
  let s : Set E := convexHull ℝ (Set.range xₙ)
  have hs_convex : Convex ℝ s := by
    -- The weak/strong closure comparison applies to the convex hull itself.
    simpa [s] using convex_convexHull ℝ (Set.range xₙ)
  have hmem : ∀ n, (xₙ n : WeakSpace ℝ E) ∈ (toWeakSpace ℝ E) '' s := by
    intro n
    -- Each sequence term already lies in the convex hull through the singleton inclusion.
    refine ⟨xₙ n, ?_, rfl⟩
    exact subset_convexHull ℝ (Set.range xₙ) (show xₙ n ∈ Set.range xₙ from ⟨n, rfl⟩)
  have hxWeak : toWeakSpace ℝ E x ∈ closure ((toWeakSpace ℝ E) '' s) := by
    -- Closedness of the weak closure gives the limit point in the weak closure.
    exact mem_closure_of_tendsto hx (Filter.Eventually.of_forall hmem)
  rw [← hs_convex.toWeakSpace_closure (𝕜 := ℝ)] at hxWeak
  rcases hxWeak with ⟨y, hy, hyx⟩
  have hxy : y = x := (toWeakSpace ℝ E).injective hyx
  simpa [hxy] using hy

section

variable {X : Type u}

/-- Helper for Corollary 3.36: a finite subset of the sequence range is already contained in some
finite initial segment. -/
private lemma finite_subset_range_subset_initialSegment
    (xₙ : ℕ → X) (s : Finset X)
    (hs : (↑s : Set X) ⊆ Set.range xₙ) :
    ∃ N : ℕ, (↑s : Set X) ⊆ Set.range (fun k : Fin (N + 1) ↦ xₙ k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro y hy
      simp at hy
  | @insert a s ha ih =>
      have ha_range : a ∈ Set.range xₙ := hs (by simp)
      rcases ha_range with ⟨na, rfl⟩
      have hs_tail : ((↑s : Set X) ⊆ Set.range xₙ) := by
        -- Remove the head point and recurse on the remaining finite subset.
        intro y hy
        exact hs (by simp [hy])
      rcases ih hs_tail with ⟨N, hN⟩
      refine ⟨max na N, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · -- The newly inserted point is represented by its original sequence index.
        refine ⟨⟨na, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩, rfl⟩
      · -- Points from the tail keep their witnesses after enlarging the initial segment.
        rcases hN hy with ⟨k, hk⟩
        refine ⟨⟨k.1, Nat.lt_succ_of_le ?_⟩, hk⟩
        exact Nat.le_trans (Nat.le_of_lt_succ k.2) (Nat.le_max_right _ _)

end

/-- Helper for Corollary 3.36: every norm-neighborhood of the weak limit meets some finite
initial-segment convex hull. -/
private lemma exists_point_initialSegment_convexHull_dist_lt
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N z,
      z ∈ convexHull ℝ (Set.range fun k : Fin (N + 1) ↦ xₙ k) ∧
      dist x z < ε := by
  have hxmem : x ∈ closure (convexHull ℝ (Set.range xₙ)) :=
    mem_closure_convexHull_of_tendsto_weakly xₙ x hx
  rcases Metric.mem_closure_iff.mp hxmem ε hε with ⟨z, hz, hdist⟩
  rw [convexHull_eq_union_convexHull_finite_subsets] at hz
  rcases Set.mem_iUnion.mp hz with ⟨s, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hs, hzs⟩
  rcases finite_subset_range_subset_initialSegment xₙ s hs with ⟨N, hN⟩
  refine ⟨N, z, convexHull_mono hN hzs, hdist⟩

/-- Helper for Corollary 3.36: the distances from `x` to the convex hulls of the initial segments
of the sequence tend to `0`. -/
private lemma tendsto_infDist_initialSegment_convexHull
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x))) :
    Tendsto
      (fun n ↦ Metric.infDist x (convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)))
      atTop (𝓝 0) := by
  let C : ℕ → Set E := fun n ↦ convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)
  have hC_mono : ∀ {m n : ℕ}, m ≤ n → C m ⊆ C n := by
    intro m n hmn
    -- Enlarging the initial segment enlarges its convex hull.
    refine convexHull_mono ?_
    intro y hy
    rcases hy with ⟨k, rfl⟩
    refine ⟨⟨k.1, Nat.lt_of_lt_of_le k.2 (Nat.succ_le_succ hmn)⟩, rfl⟩
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    -- Distances are always nonnegative, so lower neighborhoods of `0` are automatic.
    exact Filter.Eventually.of_forall fun n ↦ lt_of_lt_of_le ha Metric.infDist_nonneg
  · intro ε hε
    rcases exists_point_initialSegment_convexHull_dist_lt xₙ x hx hε with ⟨N, z, hzC, hdist⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hzCn : z ∈ C n := hC_mono hn hzC
    exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hzCn) hdist

-- Proof sketch: let `C := convexHull ℝ (Set.range xₙ)`. Weak convergence of `xₙ` to `x` implies
-- that `x` belongs to the weak closure of `C`; apply the preceding closed-convex weak/strong
-- closure equivalence to identify this with the norm closure of `C`. Then approximate `x` in norm
-- by points of `C`, pass to convex combinations supported on finitely many initial segments, and
-- choose for each `n` a convex combination of `xₙ 0, …, xₙ n` whose distance to `x` is within
-- `1 / (n + 1)` of the infimum over that finite convex hull.
/-- Corollary 3.36: (Mazur's lemma) if a sequence in a real normed space converges weakly to
`x`, then one can choose a sequence of convex combinations of the initial segments
`xₙ 0, …, xₙ n` that converges strongly to `x`. -/
theorem exists_stronglyConvergent_convex_combinations_of_tendsto_weakly
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x))) :
    ∃ y : ℕ → E,
      (∀ n, y n ∈ convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)) ∧
      Tendsto y atTop (𝓝 x) := by
  classical
  let C : ℕ → Set E := fun n ↦ convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)
  have hC_nonempty : ∀ n, (C n).Nonempty := by
    intro n
    refine ⟨xₙ 0, ?_⟩
    -- Each initial-segment convex hull contains its first point.
    exact subset_convexHull ℝ _ ⟨0, rfl⟩
  have hd :
      Tendsto (fun n ↦ Metric.infDist x (C n)) atTop (𝓝 0) :=
    tendsto_infDist_initialSegment_convexHull xₙ x hx
  have hy_exists :
      ∀ n, ∃ z ∈ C n, dist x z < Metric.infDist x (C n) + 1 / ((n : ℝ) + 1) := by
    intro n
    have hlt :
        Metric.infDist x (C n) <
          Metric.infDist x (C n) + 1 / ((n : ℝ) + 1) := by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    -- Pick an almost-minimizer for the distance to the `n`th finite convex hull.
    exact (Metric.infDist_lt_iff (hC_nonempty n)).mp hlt
  choose y hy_mem hy_dist using hy_exists
  refine ⟨y, hy_mem, ?_⟩
  have hy_dist_le :
      ∀ n, dist (y n) x ≤ Metric.infDist x (C n) + 1 / ((n : ℝ) + 1) := by
    intro n
    simpa [dist_comm] using le_of_lt (hy_dist n)
  have hbound :
      Tendsto
        (fun n ↦ Metric.infDist x (C n) + 1 / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    -- The quantitative error is the sum of the hull-distance and the auxiliary `1 / (n + 1)`.
    simpa using hd.add (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
      (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hdist :
      Tendsto (fun n ↦ dist (y n) x) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ dist_nonneg) hy_dist_le hbound
  -- Strong convergence is exactly convergence of the distances to `x`.
  exact tendsto_iff_dist_tendsto_zero.2 hdist

/-- Helper for Corollary 3.36: membership in an initial-segment convex hull yields explicit convex
coefficients on that initial segment. -/
private lemma exists_coefficients_of_mem_initialSegment_convexHull
    (xₙ : ℕ → E) {n : ℕ} {y : E}
    (hy : y ∈ convexHull ℝ (Set.range fun k : Fin (n + 1) ↦ xₙ k)) :
    ∃ α : Fin (n + 1) → ℝ,
      (∀ k, α k ∈ Set.Icc (0 : ℝ) 1) ∧
      (∑ k, α k = 1) ∧
      (y = ∑ k, α k • xₙ k) := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hy
  rcases hy with ⟨s, w, hw₀, hw₁, rfl⟩
  let α : Fin (n + 1) → ℝ := fun k ↦ if k ∈ s then w k else 0
  have hy_linear :
      s.affineCombination ℝ (fun k : Fin (n + 1) ↦ xₙ k) w =
        Finset.sum s (fun k : Fin (n + 1) ↦ w k • xₙ k) := by
    -- In a vector space, affine combinations are just linear combinations when the weights sum to
    -- `1`.
    simpa using
      (Finset.affineCombination_eq_linear_combination s
        (fun k : Fin (n + 1) ↦ xₙ k) w hw₁)
  have hy_univ :
      Finset.sum s (fun k : Fin (n + 1) ↦ w k • xₙ k) =
        Finset.univ.sum (fun k : Fin (n + 1) ↦ α k • xₙ k) := by
    -- Extending the finite support by zero does not change the resulting sum.
    calc
      Finset.sum s (fun k : Fin (n + 1) ↦ w k • xₙ k) =
          Finset.univ.sum (fun k : Fin (n + 1) ↦ if k ∈ s then w k • xₙ k else 0) := by
        symm
        exact Finset.sum_ite_mem_eq s (fun k : Fin (n + 1) ↦ w k • xₙ k)
      _ = Finset.univ.sum (fun k : Fin (n + 1) ↦ α k • xₙ k) := by
        simp [α]
  have hαsum : Finset.univ.sum α = 1 := by
    -- The zero extension preserves the total mass of the coefficients.
    simpa [α] using (Finset.sum_ite_mem_eq s w).trans hw₁
  refine ⟨α, ?_, ?_, ?_⟩
  · intro k
    constructor
    · by_cases hk : k ∈ s
      · simpa [α, hk] using hw₀ k hk
      · simp [α, hk]
    · by_cases hk : k ∈ s
      · have hk_le : w k ≤ ∑ j ∈ s, w j := by
          -- A nonnegative coefficient is bounded above by the total sum of all coefficients.
          simpa [Finset.sum_erase_add _ _ hk] using
            (Finset.single_le_sum (fun j hj ↦ hw₀ j hj) hk : w k ≤ ∑ j ∈ s, w j)
        simpa [hw₁, α, hk] using hk_le
      · simp [α, hk]
  · simp [hαsum]
  · simp [hy_linear.trans hy_univ]

/-- A coefficient-form companion to Mazur's lemma: the approximating sequence may be written using
explicit convex-combination coefficients on each initial segment. -/
-- Proof sketch: apply the convex-hull formulation above to obtain `y n ∈ convexHull ℝ
-- (Set.range fun k : Fin (n + 1) ↦ xₙ k)` for every `n`, then use the finite-dimensional
-- characterization of membership in a convex hull of a finite set to choose coefficients
-- `α n k ∈ [0, 1]` summing to `1` with `y n = ∑ k, α n k • xₙ k`.
theorem exists_stronglyConvergent_initialSegment_coefficients_of_tendsto_weakly
    (xₙ : ℕ → E) (x : E)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop (𝓝 (toWeakSpace ℝ E x))) :
    ∃ α : (n : ℕ) → Fin (n + 1) → ℝ,
      (∀ n k, α n k ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, ∑ k, α n k = 1) ∧
      Tendsto (fun n ↦ ∑ k, α n k • xₙ k) atTop (𝓝 x) := by
  rcases exists_stronglyConvergent_convex_combinations_of_tendsto_weakly xₙ x hx with
    ⟨y, hy_mem, hy_tendsto⟩
  have hα :
      ∀ n, ∃ α : Fin (n + 1) → ℝ,
        (∀ k, α k ∈ Set.Icc (0 : ℝ) 1) ∧
        (∑ k, α k = 1) ∧
        (y n = ∑ k, α k • xₙ k) := by
    intro n
    -- Convert each convex-hull membership statement into explicit coefficients.
    exact exists_coefficients_of_mem_initialSegment_convexHull xₙ (hy_mem n)
  choose α hα_mem hα_sum hα_eq using hα
  have hy_def : y = fun n ↦ ∑ k, α n k • xₙ k := by
    funext n
    exact hα_eq n
  exact ⟨α, hα_mem, hα_sum, hy_def ▸ hy_tendsto⟩

/-! Source item: Chap03/Theorem_3_37 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: a Hilbert space is reflexive, so closed bounded sets are weakly compact after
-- passing to the weak topology. A norm-closed convex subset is weakly closed, hence a weakly
-- closed subset of a weakly compact closed ball and therefore weakly compact.
/-- Canonical weak compactness form of Theorem 3.37. The weak topology is expressed by viewing the
set inside `WeakSpace ℝ H`. -/
theorem weaklyCompact_of_bounded_closed_convex
    {C : Set H} (hCbdd : Bornology.IsBounded C) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    IsCompact (toWeakSpace ℝ H '' C) := by
  -- Reuse the earlier canonical closed-convex weak-closedness criterion.
  have hweakClosed : IsClosed ((toWeakSpace ℝ H) '' C) :=
    (isClosed_iff_weak_image_isClosed_of_convex hCconv).1 hCclosed
  -- The Hilbert-space weak compactness criterion finishes once weak closedness and boundedness
  -- are available.
  exact
    (weaklyCompact_iff_weaklyClosed_and_bounded :
      IsCompact ((toWeakSpace ℝ H) '' C) ↔
        IsClosed ((toWeakSpace ℝ H) '' C) ∧ Bornology.IsBounded C).2
      ⟨hweakClosed, hCbdd⟩

/-- Theorem 3.37: a nonempty bounded closed convex subset of a real Hilbert space is weakly
compact. The weak topology is expressed by viewing the set inside `WeakSpace ℝ H`. -/
theorem weaklyCompact_of_nonempty_bounded_closed_convex
    {C : Set H} (_hCne : C.Nonempty) (hCbdd : Bornology.IsBounded C) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    IsCompact (toWeakSpace ℝ H '' C) :=
  weaklyCompact_of_bounded_closed_convex hCbdd hCclosed hCconv

-- Proof sketch: apply weak compactness from the previous theorem, then use the Hilbert-space
-- form of the Eberlein-Smulian theorem to identify weak compactness with weak sequential
-- compactness on subsets of `H`.
/-- Weak sequential compactness companion in canonical bounded/closed/convex form. -/
theorem weaklySeqCompact_of_bounded_closed_convex
    {C : Set H} (hCbdd : Bornology.IsBounded C) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    IsSeqCompact (toWeakSpace ℝ H '' C) := by
  -- First obtain weak compactness from the closed-convex bounded criterion.
  have hcompact : IsCompact (toWeakSpace ℝ H '' C) :=
    weaklyCompact_of_bounded_closed_convex hCbdd hCclosed hCconv
  -- Then apply the Hilbert-space Eberlein-Smulian equivalence on the same weak image.
  exact (weaklyCompact_iff_weaklySeqCompact C).1 hcompact

/-- Weak sequential compactness companion for a nonempty bounded closed convex subset of a real
Hilbert space. -/
theorem weaklySeqCompact_of_nonempty_bounded_closed_convex
    {C : Set H} (_hCne : C.Nonempty) (hCbdd : Bornology.IsBounded C) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    IsSeqCompact (toWeakSpace ℝ H '' C) :=
  weaklySeqCompact_of_bounded_closed_convex hCbdd hCclosed hCconv

/-! Source item: Chap03/Corollary_3_38 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Every weak sequential cluster point of a sequence in a closed convex subset of a real Hilbert
space belongs to that set. -/
-- Proof sketch: weak closedness of a closed convex set identifies the weak limit of any weakly
-- convergent subsequence with a point in the weak image of the set; injectivity of `toWeakSpace`
-- then returns the corresponding point of `C`.
private theorem mem_of_weakSequentialClusterPt_of_isClosed_convex {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {u : ℕ → H} (hu : ∀ n, u n ∈ C)
    {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H x)) :
    x ∈ C := by
  have hweakClosed : IsClosed ((toWeakSpace ℝ H) '' C) :=
    (isClosed_iff_weak_image_isClosed_of_convex hC_convex).1 hC_closed
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  have hsubseq_mem :
      ∀ n, toWeakSpace ℝ H (u (φ n)) ∈ (toWeakSpace ℝ H) '' C := by
    intro n
    exact ⟨u (φ n), hu (φ n), rfl⟩
  have hx_mem : toWeakSpace ℝ H x ∈ closure ((toWeakSpace ℝ H) '' C) :=
    mem_closure_of_tendsto hφx (Filter.Eventually.of_forall hsubseq_mem)
  rw [hweakClosed.closure_eq] at hx_mem
  rcases hx_mem with ⟨y, hyC, hyx⟩
  exact (toWeakSpace ℝ H).injective hyx ▸ hyC

/-- Corollary 3.38: every sequence with values in a bounded closed convex subset of a real Hilbert
space admits a weakly convergent subsequence whose weak limit belongs to the set. -/
-- Proof sketch: weak sequential compactness of the weak image of `C` produces a weakly
-- convergent subsequence in `WeakSpace`; pulling the limit back along `toWeakSpace` gives the
-- desired `x ∈ C`.
theorem exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex {C : Set H}
    (hC_bounded : Bornology.IsBounded C) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (u : ℕ → H) (hu : ∀ n, u n ∈ C) :
    ∃ x ∈ C, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (u (φ n))) atTop (nhds (toWeakSpace ℝ H x)) := by
  have hseqCompact : IsSeqCompact ((toWeakSpace ℝ H) '' C) :=
    weaklySeqCompact_of_bounded_closed_convex hC_bounded hC_closed hC_convex
  have hu_mem : ∀ n, toWeakSpace ℝ H (u n) ∈ (toWeakSpace ℝ H) '' C := by
    intro n
    exact ⟨u n, hu n, rfl⟩
  obtain ⟨w, hw, φ, hφ, hφw⟩ := hseqCompact hu_mem
  rcases hw with ⟨x, hxC, hwx⟩
  refine ⟨x, hxC, φ, hφ, ?_⟩
  simpa [hwx] using hφw

/-! Source item: Chap03/Example_3_40 -/

/-- The horizontal axis in `ℝ²`, viewed as the set `ℝ × {0}`. -/
def minkowskiCounterexample_horizontalAxis : Set (ℝ × ℝ) :=
  (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)

/-- The first-quadrant region on or above the hyperbola `x₁ x₂ = 1`. -/
def minkowskiCounterexample_positiveProductRegion : Set (ℝ × ℝ) :=
  (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) ∩ {x | 1 ≤ x.1 * x.2}

-- Proof sketch: unfold `minkowskiCounterexample_horizontalAxis`; membership is definitionally the
-- vanishing of the second coordinate.
/-- Membership in the horizontal-axis set is equivalent to having second coordinate `0`. -/
theorem mem_minkowskiCounterexample_horizontalAxis_iff (x : ℝ × ℝ) :
    x ∈ minkowskiCounterexample_horizontalAxis ↔ x.2 = 0 := by
  -- Unfolding the product-set definition reduces membership to the second-coordinate condition.
  simp [minkowskiCounterexample_horizontalAxis]

-- Proof sketch: unfold `minkowskiCounterexample_positiveProductRegion`; membership is exactly the
-- conjunction of first-quadrant inequalities and the product lower bound.
/-- Membership in the positive-product region means lying in the first quadrant with product at
least `1`. -/
theorem mem_minkowskiCounterexample_positiveProductRegion_iff (x : ℝ × ℝ) :
    x ∈ minkowskiCounterexample_positiveProductRegion ↔
      0 ≤ x.1 ∧ 0 ≤ x.2 ∧ 1 ≤ x.1 * x.2 := by
  -- This is the product-set description of the first quadrant plus the product lower bound.
  rw [minkowskiCounterexample_positiveProductRegion, Set.mem_inter_iff, Set.mem_prod]
  simp [and_assoc]

-- Proof sketch: identify the set as the zero-level set of the continuous map
-- `x ↦ x.2`.
/-- The horizontal axis is a closed subset of `ℝ²`. -/
theorem minkowskiCounterexample_horizontalAxis_isClosed :
    IsClosed minkowskiCounterexample_horizontalAxis := by
  -- `ℝ × {0}` is the product of two closed sets.
  simpa [minkowskiCounterexample_horizontalAxis] using
    (isClosed_univ : IsClosed (Set.univ : Set ℝ)).prod isClosed_singleton

-- Proof sketch: this set is a linear subspace, hence convex.
/-- The horizontal axis is convex. -/
theorem minkowskiCounterexample_horizontalAxis_convex :
    Convex ℝ minkowskiCounterexample_horizontalAxis := by
  -- `ℝ × {0}` is the product of two convex sets.
  simpa [minkowskiCounterexample_horizontalAxis] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).prod (convex_singleton (0 : ℝ))

-- Proof sketch: write the region as the intersection of the closed first quadrant with the closed
-- superlevel set of the continuous map `x ↦ x.1 * x.2`.
/-- The positive-product region is closed in `ℝ²`. -/
theorem minkowskiCounterexample_positiveProductRegion_isClosed :
    IsClosed minkowskiCounterexample_positiveProductRegion := by
  have hquadrant : IsClosed ((Set.Ici (0 : ℝ) : Set ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
    exact isClosed_Ici.prod isClosed_Ici
  have hprod :
      IsClosed {x : ℝ × ℝ | 1 ≤ x.1 * x.2} := by
    simpa using isClosed_le continuous_const (continuous_fst.mul continuous_snd)
  -- The region is the intersection of the closed first quadrant with a closed superlevel set.
  simpa [minkowskiCounterexample_positiveProductRegion] using hquadrant.inter hprod

/-- Helper for Example 3.40: every point in the positive-product region has strictly positive
second coordinate. -/
private lemma minkowskiCounterexample_positiveProductRegion_snd_pos (x : ℝ × ℝ)
    (hx : x ∈ minkowskiCounterexample_positiveProductRegion) :
    0 < x.2 := by
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff x).1 hx with
    ⟨hx1, hx2, hxprod⟩
  -- The product bound rules out `x.2 = 0`, while first-quadrant membership gives `x.2 ≥ 0`.
  by_contra h_not_pos
  have hx2eq : x.2 = 0 := by
    linarith
  nlinarith [hxprod, hx1, hx2eq]

/-- Helper for Example 3.40: the mixed cross term in the convexity computation is at least `2`. -/
private lemma minkowskiCounterexample_positiveProductRegion_cross_term_two_le
    (x y : ℝ × ℝ)
    (hx : x ∈ minkowskiCounterexample_positiveProductRegion)
    (hy : y ∈ minkowskiCounterexample_positiveProductRegion) :
    2 ≤ x.1 * y.2 + y.1 * x.2 := by
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff x).1 hx with
    ⟨hx1, hx2, hxprod⟩
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff y).1 hy with
    ⟨hy1, hy2, hyprod⟩
  have hcross_prod : 1 ≤ (x.1 * y.2) * (y.1 * x.2) := by
    nlinarith [hxprod, hyprod]
  have hleft_nonneg : 0 ≤ x.1 * y.2 := mul_nonneg hx1 hy2
  have hright_nonneg : 0 ≤ y.1 * x.2 := mul_nonneg hy1 hx2
  have hsquare : 0 ≤ (x.1 * y.2 - (y.1 * x.2)) ^ 2 := sq_nonneg _
  -- Apply AM-GM in polynomial form to the two nonnegative mixed terms.
  nlinarith

-- Proof sketch: use the standard convexity argument for the epigraph of `x ↦ 1 / x` on the
-- positive ray, equivalently the arithmetic-geometric-mean estimate in the textbook proof.
/-- The positive-product region is convex. -/
theorem minkowskiCounterexample_positiveProductRegion_convex :
    Convex ℝ minkowskiCounterexample_positiveProductRegion := by
  intro x hx y hy a b ha hb hab
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff x).1 hx with
    ⟨hx1, hx2, hxprod⟩
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff y).1 hy with
    ⟨hy1, hy2, hyprod⟩
  rw [mem_minkowskiCounterexample_positiveProductRegion_iff]
  refine ⟨add_nonneg (mul_nonneg ha hx1) (mul_nonneg hb hy1),
    add_nonneg (mul_nonneg ha hx2) (mul_nonneg hb hy2), ?_⟩
  have hcross :
      2 ≤ x.1 * y.2 + y.1 * x.2 :=
    minkowskiCounterexample_positiveProductRegion_cross_term_two_le x y hx hy
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
  have ha_sq_nonneg : 0 ≤ a ^ 2 := sq_nonneg a
  have hb_sq_nonneg : 0 ≤ b ^ 2 := sq_nonneg b
  -- Expand the product of the convex-combination coordinates and bound each summand below.
  calc
    1 = a ^ 2 * 1 + (a * b) * 2 + b ^ 2 * 1 := by
      nlinarith [hab]
    _ ≤ a ^ 2 * (x.1 * x.2)
          + (a * b) * (x.1 * y.2 + y.1 * x.2)
          + b ^ 2 * (y.1 * y.2) := by
      nlinarith [hxprod, hyprod, hcross, hab_nonneg, ha_sq_nonneg, hb_sq_nonneg]
    _ = (a * x.1 + b * y.1) * (a * x.2 + b * y.2) := by
      ring

/-- Helper for Example 3.40: every point in the open upper half-plane splits as a point on the
horizontal axis plus a point in the positive-product region. -/
private lemma upperHalfPlane_subset_minkowskiCounterexample_sum (p : ℝ × ℝ)
    (hp : p ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ)) :
    p ∈ minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion := by
  rcases p with ⟨a, b⟩
  rcases Set.mem_prod.mp hp with ⟨_, hb_mem⟩
  rw [Set.mem_Ioi] at hb_mem
  rw [Set.mem_add]
  have hb_ne : b ≠ 0 := ne_of_gt hb_mem
  have hrecip_mul : b⁻¹ * b = 1 := by
    simpa [one_div] using one_div_mul_cancel hb_ne
  have haxis : (a - 1 / b, 0) ∈ minkowskiCounterexample_horizontalAxis := by
    -- The first summand lies on the horizontal axis by construction.
    simp [mem_minkowskiCounterexample_horizontalAxis_iff]
  have hregion : (1 / b, b) ∈ minkowskiCounterexample_positiveProductRegion := by
    -- The second summand lies in the region because `b > 0` and `(1 / b) * b = 1`.
    rw [mem_minkowskiCounterexample_positiveProductRegion_iff]
    refine ⟨le_of_lt (one_div_pos.mpr hb_mem), le_of_lt hb_mem, ?_⟩
    simp [one_div, hrecip_mul]
  have hsum : (a - 1 / b, 0) + (1 / b, b) = (a, b) := by
    -- This is the explicit decomposition used in the textbook proof.
    simp
  exact ⟨(a - 1 / b, 0), haxis, (1 / b, b), hregion, hsum⟩

/-- Helper for Example 3.40: every point in the Minkowski sum has strictly positive second
coordinate. -/
private lemma minkowskiCounterexample_sum_subset_upperHalfPlane (p : ℝ × ℝ)
    (hp : p ∈ minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion) :
    p ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
  rcases Set.mem_add.mp hp with ⟨c, hc, d, hd, rfl⟩
  rw [Set.mem_prod, Set.mem_Ioi]
  constructor
  · simp
  · have hd2 : 0 < d.2 :=
      minkowskiCounterexample_positiveProductRegion_snd_pos d hd
    rw [mem_minkowskiCounterexample_horizontalAxis_iff] at hc
    -- Adding a horizontal-axis point leaves the second coordinate unchanged.
    simpa [hc] using hd2

-- Proof sketch: for `b > 0`, decompose `(a, b)` as `(a - 1 / b, 0) + (1 / b, b)`, and conversely
-- observe that every point of the Minkowski sum has strictly positive second coordinate because
-- every point of the positive-product region does, yielding exactly `Set.univ ×ˢ Set.Ioi 0`.
/-- Example 3.40: for `C = ℝ × {0}` and
`D = {(ξ₁, ξ₂) ∈ ℝ² | 0 ≤ ξ₁ ∧ 0 ≤ ξ₂ ∧ 1 ≤ ξ₁ * ξ₂}`, the Minkowski sum is the open upper
half-plane `ℝ × ℝ_{++}`, i.e. `Set.univ ×ˢ Set.Ioi (0 : ℝ)`. -/
theorem minkowskiCounterexample_sum_eq_upperHalfPlane :
    minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion =
      Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
  -- Route correction: compute the sum by explicit two-sided inclusion, not by topological
  -- properties of the sum itself.
  ext p
  constructor
  · exact minkowskiCounterexample_sum_subset_upperHalfPlane p
  · exact upperHalfPlane_subset_minkowskiCounterexample_sum p

-- Proof sketch: rewrite the sum using `minkowskiCounterexample_sum_eq_upperHalfPlane` and use that
-- `Set.univ ×ˢ Set.Ioi (0 : ℝ)` is open as the product of the open sets `Set.univ` and `Set.Ioi 0`.
/-- The Minkowski sum in Example 3.40 is an open subset of `ℝ²`. -/
theorem minkowskiCounterexample_sum_isOpen :
    IsOpen
      (minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion) :=
  by
  -- Rewrite the sum as the open upper half-plane.
  rw [minkowskiCounterexample_sum_eq_upperHalfPlane]
  simpa using isOpen_univ.prod isOpen_Ioi

-- Proof sketch: combine `minkowskiCounterexample_sum_eq_upperHalfPlane` with the fact that the
-- open upper half-plane is not closed in `ℝ²`.
/-- The Minkowski sum in Example 3.40 is not closed. -/
theorem minkowskiCounterexample_sum_not_isClosed :
    ¬ IsClosed
      (minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion) :=
  by
  intro hClosed
  have hclosure :
      closure
          (minkowskiCounterexample_horizontalAxis
            + minkowskiCounterexample_positiveProductRegion) =
        (Set.univ : Set ℝ) ×ˢ Set.Ici (0 : ℝ) := by
    -- The closure of the open upper half-plane is the closed upper half-plane.
    rw [minkowskiCounterexample_sum_eq_upperHalfPlane, closure_prod_eq, closure_univ, closure_Ioi]
  have horigin_closure :
      ((0 : ℝ), (0 : ℝ)) ∈
        closure
          (minkowskiCounterexample_horizontalAxis
            + minkowskiCounterexample_positiveProductRegion) := by
    rw [hclosure]
    simp
  have horigin :
      ((0 : ℝ), (0 : ℝ)) ∈
        minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion := by
    rw [← hClosed.closure_eq]
    exact horigin_closure
  have horigin_not :
      ((0 : ℝ), (0 : ℝ)) ∉
        minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion := by
    rw [minkowskiCounterexample_sum_eq_upperHalfPlane]
    simp
  exact horigin_not horigin

/-! Source item: Chap03/Example_3_41 -/

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

noncomputable section

/-- The closed linear span of the even-indexed vectors of a sequence in a real Hilbert space. -/
def even_indexed_closed_span (e : ℕ → 𝓗) : Submodule ℝ 𝓗 :=
  (Submodule.span ℝ (Set.range fun n : ℕ ↦ e (2 * n))).topologicalClosure

/-- The rotated even-odd vector `cos (θ n) • e (2n) + sin (θ n) • e (2n + 1)`. -/
def rotated_even_odd_vector (e : ℕ → 𝓗) (θ : ℕ → ℝ) (n : ℕ) : 𝓗 :=
  Real.cos (θ n) • e (2 * n) + Real.sin (θ n) • e (2 * n + 1)

/-- The closed linear span of the rotated even-odd vectors from Example 3.41. -/
def rotated_even_odd_closed_span (e : ℕ → 𝓗) (θ : ℕ → ℝ) : Submodule ℝ 𝓗 :=
  (Submodule.span ℝ (Set.range (rotated_even_odd_vector e θ))).topologicalClosure

-- Proof sketch: the generator `e (2 * n)` belongs to the algebraic span of the even-indexed
-- range, and every point of that span belongs to its topological closure.
/-- Each even-indexed vector of the sequence belongs to its associated closed span. -/
private theorem even_mem_even_indexed_closed_span (e : ℕ → 𝓗) (n : ℕ) :
    e (2 * n) ∈ even_indexed_closed_span e := by
  -- The generator already lies in the algebraic span, hence also in its closure.
  exact (Submodule.span ℝ (Set.range fun n : ℕ ↦ e (2 * n))).le_topologicalClosure
    (Submodule.subset_span (by exact ⟨n, rfl⟩))

-- Proof sketch: the vector `rotated_even_odd_vector e θ n` is one of the generators of the span
-- whose closure defines `rotated_even_odd_closed_span e θ`.
/-- Each rotated even-odd generator belongs to its associated closed span. -/
private theorem rotated_even_odd_vector_mem_rotated_even_odd_closed_span
    (e : ℕ → 𝓗) (θ : ℕ → ℝ) (n : ℕ) :
    rotated_even_odd_vector e θ n ∈ rotated_even_odd_closed_span e θ := by
  -- The rotated vector is one of the generators of the defining span.
  exact (Submodule.span ℝ (Set.range (rotated_even_odd_vector e θ))).le_topologicalClosure
    (Submodule.subset_span (by exact ⟨n, rfl⟩))

-- Proof sketch: `even_indexed_closed_span e` is defined as the topological closure of a
-- submodule, and closures of submodules are closed subsets of the ambient Hilbert space.
/-- Example 3.41 (1): the closed span of the even-indexed vectors is a closed linear subspace. -/
theorem isClosed_even_indexed_closed_span (e : ℕ → 𝓗) :
    IsClosed ((even_indexed_closed_span e : Submodule ℝ 𝓗) : Set 𝓗) := by
  -- This subspace is defined as a topological closure.
  exact Submodule.isClosed_topologicalClosure _

-- Proof sketch: `rotated_even_odd_closed_span e θ` is likewise a topological closure of a
-- submodule, so its underlying subset is closed.
/-- Example 3.41 (2): the closed span of the rotated even-odd vectors is a closed linear
subspace. -/
theorem isClosed_rotated_even_odd_closed_span (e : ℕ → 𝓗) (θ : ℕ → ℝ) :
    IsClosed ((rotated_even_odd_closed_span e θ : Submodule ℝ 𝓗) : Set 𝓗) := by
  -- This subspace is also defined as a topological closure.
  exact Submodule.isClosed_topologicalClosure _

section

variable (e : ℕ → 𝓗)

private lemma even_index_orthonormal (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun n : ℕ ↦ e (2 * n)) := by
  -- Reindex the original orthonormal family along the injective even map.
  exact Orthonormal.comp he (fun n : ℕ ↦ 2 * n) (by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by decide) hmn)

private lemma odd_index_orthonormal (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun n : ℕ ↦ e (2 * n + 1)) := by
  -- Reindex the original orthonormal family along the injective odd map.
  exact Orthonormal.comp he (fun n : ℕ ↦ 2 * n + 1) (by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel hmn))

variable (θ : ℕ → ℝ)

private lemma rotated_even_odd_inner_kronecker (he : Orthonormal ℝ e) (m n : ℕ) :
    ⟪rotated_even_odd_vector e θ m, rotated_even_odd_vector e θ n⟫_ℝ =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst n
    -- On the diagonal, the two summands are orthogonal, so the norm square splits.
    have hcross :
        ⟪Real.cos (θ m) • e (2 * m), Real.sin (θ m) • e (2 * m + 1)⟫_ℝ = 0 := by
      have hneq : 2 * m ≠ 2 * m + 1 := by
        omega
      simp [real_inner_smul_left, real_inner_smul_right, he.2 hneq]
    calc
      ⟪rotated_even_odd_vector e θ m, rotated_even_odd_vector e θ m⟫_ℝ
          = ‖rotated_even_odd_vector e θ m‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
      _ = ‖Real.cos (θ m) • e (2 * m)‖ ^ 2 + ‖Real.sin (θ m) • e (2 * m + 1)‖ ^ 2 := by
            simpa [pow_two, rotated_even_odd_vector] using
              norm_add_sq_eq_norm_sq_add_norm_sq_real hcross
      _ = Real.cos (θ m) ^ 2 + Real.sin (θ m) ^ 2 := by
            simp [norm_smul, he.1]
      _ = 1 := by
            have htrig := Real.sin_sq_add_cos_sq (θ m)
            linarith
    simp
  · -- Off the diagonal, every inner-product term vanishes by parity and orthonormality.
    have h_even : 2 * m ≠ 2 * n := by
      omega
    have h_even_odd : 2 * m ≠ 2 * n + 1 := by
      omega
    have h_odd_even : 2 * m + 1 ≠ 2 * n := by
      omega
    have h_odd : 2 * m + 1 ≠ 2 * n + 1 := by
      omega
    rw [rotated_even_odd_vector, rotated_even_odd_vector]
    rw [inner_add_left, inner_add_right, inner_add_right]
    simp [hmn, real_inner_smul_left, real_inner_smul_right, he.2 h_even, he.2 h_even_odd,
      he.2 h_odd_even, he.2 h_odd]

/-- Helper for Example 3.41: the even and odd coordinate functionals agree with the rotated
coordinate functional on each rotated generator. -/
private lemma rotated_coordinate_functional_eq_on_generators (he : Orthonormal ℝ e) (n m : ℕ) :
    (⟪e (2 * n), rotated_even_odd_vector e θ m⟫_ℝ =
        Real.cos (θ n) *
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ) ∧
      (⟪e (2 * n + 1), rotated_even_odd_vector e θ m⟫_ℝ =
        Real.sin (θ n) *
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ) := by
  by_cases hnm : n = m
  · subst m
    -- On the diagonal, both coordinates are read directly from the rotated vector.
    have hneq : 2 * n ≠ 2 * n + 1 := by
      omega
    have hself : ‖rotated_even_odd_vector e θ n‖ ^ 2 = 1 := by
      have hinner :
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ = 1 := by
        simpa using rotated_even_odd_inner_kronecker e θ he n n
      simpa [real_inner_self_eq_norm_sq] using hinner
    constructor
    · calc
        ⟪e (2 * n), rotated_even_odd_vector e θ n⟫_ℝ = Real.cos (θ n) := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 hneq, he.1 (2 * n)]
        _ = Real.cos (θ n) * ‖rotated_even_odd_vector e θ n‖ ^ 2 := by
          rw [hself]
          ring
        _ = Real.cos (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq]
    · have hneq' : 2 * n + 1 ≠ 2 * n := by
        omega
      calc
        ⟪e (2 * n + 1), rotated_even_odd_vector e θ n⟫_ℝ = Real.sin (θ n) := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 hneq', he.1 (2 * n + 1)]
        _ = Real.sin (θ n) * ‖rotated_even_odd_vector e θ n‖ ^ 2 := by
          rw [hself]
          ring
        _ = Real.sin (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq]
  · -- Off the diagonal, both coordinates vanish and the rotated Kronecker term is zero.
    have h_even : 2 * n ≠ 2 * m := by
      omega
    have h_even_odd : 2 * n ≠ 2 * m + 1 := by
      omega
    have h_odd_even : 2 * n + 1 ≠ 2 * m := by
      omega
    have h_odd : 2 * n + 1 ≠ 2 * m + 1 := by
      omega
    constructor
    · calc
        ⟪e (2 * n), rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 h_even, he.2 h_even_odd]
        _ = Real.cos (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ := by
              have hrot :
                  ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
                simpa [hnm] using rotated_even_odd_inner_kronecker e θ he n m
              rw [hrot]
              ring
    · calc
        ⟪e (2 * n + 1), rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 h_odd_even, he.2 h_odd]
        _ = Real.sin (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ := by
              have hrot :
                  ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
                simpa [hnm] using rotated_even_odd_inner_kronecker e θ he n m
              rw [hrot]
              ring

private lemma inner_odd_eq_zero_of_mem_even_indexed_closed_span (he : Orthonormal ℝ e)
    {x : 𝓗} {n : ℕ}
    (hx : x ∈ even_indexed_closed_span e) :
    ⟪e (2 * n + 1), x⟫_ℝ = 0 := by
  -- Compare the odd-coordinate functional with the zero map on the even generators.
  let F : 𝓗 →L[ℝ] ℝ := innerSL ℝ (e (2 * n + 1))
  let G : 𝓗 →L[ℝ] ℝ := 0
  have hEq : Set.EqOn F G (Set.range fun m : ℕ ↦ e (2 * m)) := by
    intro y hy
    rcases hy with ⟨m, rfl⟩
    have hneq : 2 * n + 1 ≠ 2 * m := by
      omega
    simp [F, G, innerSL_apply_apply, he.2 hneq]
  have hEqClosure := ContinuousLinearMap.eqOn_closure_span hEq
  -- The closure-extension step transports the generator identity to the whole closed span.
  simpa [even_indexed_closed_span, F, G, innerSL_apply_apply] using
    hEqClosure (by simpa [even_indexed_closed_span] using hx)

private lemma inner_even_odd_eq_scaled_inner_rotated_of_mem_rotated_even_odd_closed_span
    (he : Orthonormal ℝ e)
    {x : 𝓗} {n : ℕ} (hx : x ∈ rotated_even_odd_closed_span e θ) :
    (⟪e (2 * n), x⟫_ℝ =
        Real.cos (θ n) * ⟪rotated_even_odd_vector e θ n, x⟫_ℝ) ∧
      (⟪e (2 * n + 1), x⟫_ℝ =
        Real.sin (θ n) * ⟪rotated_even_odd_vector e θ n, x⟫_ℝ) := by
  -- Compare the coordinate functionals on the rotated generators before extending by closure.
  let F_even : 𝓗 →L[ℝ] ℝ := innerSL ℝ (e (2 * n))
  let G_even : 𝓗 →L[ℝ] ℝ := Real.cos (θ n) • innerSL ℝ (rotated_even_odd_vector e θ n)
  let F_odd : 𝓗 →L[ℝ] ℝ := innerSL ℝ (e (2 * n + 1))
  let G_odd : 𝓗 →L[ℝ] ℝ := Real.sin (θ n) • innerSL ℝ (rotated_even_odd_vector e θ n)
  have hEqEven : Set.EqOn F_even G_even (Set.range (rotated_even_odd_vector e θ)) := by
    intro y hy
    rcases hy with ⟨m, rfl⟩
    simpa [F_even, G_even, innerSL_apply_apply] using
      (rotated_coordinate_functional_eq_on_generators e θ he n m).1
  have hEqOdd : Set.EqOn F_odd G_odd (Set.range (rotated_even_odd_vector e θ)) := by
    intro y hy
    rcases hy with ⟨m, rfl⟩
    simpa [F_odd, G_odd, innerSL_apply_apply] using
      (rotated_coordinate_functional_eq_on_generators e θ he n m).2
  have hEqEvenClosure := ContinuousLinearMap.eqOn_closure_span hEqEven
  have hEqOddClosure := ContinuousLinearMap.eqOn_closure_span hEqOdd
  -- The same identities now hold on every vector in the closed rotated span.
  constructor
  · simpa [F_even, G_even, innerSL_apply_apply] using
      hEqEvenClosure (by simpa [rotated_even_odd_closed_span] using hx)
  · simpa [F_odd, G_odd, innerSL_apply_apply] using
      hEqOddClosure (by simpa [rotated_even_odd_closed_span] using hx)

private lemma eq_zero_of_mem_rotated_even_odd_closed_span_of_inner_rotated_eq_zero {x : 𝓗}
    (hx : x ∈ rotated_even_odd_closed_span e θ)
    (hinner : ∀ n : ℕ, ⟪rotated_even_odd_vector e θ n, x⟫_ℝ = 0) :
    x = 0 := by
  -- Compare the functional `innerSL ℝ x` with zero on the rotated generators.
  let F : 𝓗 →L[ℝ] ℝ := innerSL ℝ x
  let G : 𝓗 →L[ℝ] ℝ := 0
  have hEq : Set.EqOn F G (Set.range (rotated_even_odd_vector e θ)) := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    simpa [F, G, innerSL_apply_apply, real_inner_comm] using hinner n
  have hEqClosure := ContinuousLinearMap.eqOn_closure_span hEq
  have hxx : ⟪x, x⟫_ℝ = 0 := by
    have hxx' := hEqClosure (by simpa [rotated_even_odd_closed_span] using hx)
    simpa [rotated_even_odd_closed_span, F, G, innerSL_apply_apply] using hxx'
  exact inner_self_eq_zero.mp hxx

-- Proof sketch: expand an element of the intersection in the orthonormal family `e`; comparison
-- of the coefficients of `e (2 * n)` and `e (2 * n + 1)` gives `b n * sin (θ n) = 0`, and the
-- positivity of `θ n` implies `sin (θ n) > 0`, so all coefficients vanish.
/-- Example 3.41 (3): the even-index closed span and the rotated closed span intersect trivially. -/
theorem disjoint_even_indexed_closed_span_rotated_even_odd_closed_span
    (he : Orthonormal ℝ e)
    (hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    Disjoint (even_indexed_closed_span e) (rotated_even_odd_closed_span e θ) := by
  -- A vector in the intersection has zero odd coordinates, hence zero rotated coordinates.
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  have hx_even : x ∈ even_indexed_closed_span e := hx.1
  have hx_rot : x ∈ rotated_even_odd_closed_span e θ := hx.2
  have hrot_zero : ∀ n : ℕ, ⟪rotated_even_odd_vector e θ n, x⟫_ℝ = 0 := by
    intro n
    rcases inner_even_odd_eq_scaled_inner_rotated_of_mem_rotated_even_odd_closed_span
        e θ he hx_rot with ⟨_, hodd⟩
    have hprod : Real.sin (θ n) * ⟪rotated_even_odd_vector e θ n, x⟫_ℝ = 0 := by
      rw [← hodd, inner_odd_eq_zero_of_mem_even_indexed_closed_span e he hx_even]
    have hθn_lt_pi : θ n < Real.pi := by
      linarith [Real.pi_pos, (hθ n).2]
    have hsin_pos : 0 < Real.sin (θ n) := by
      exact Real.sin_pos_of_pos_of_lt_pi (hθ n).1 hθn_lt_pi
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hsin_pos)
  -- The vanishing of all rotated coordinates forces the vector itself to vanish.
  exact eq_zero_of_mem_rotated_even_odd_closed_span_of_inner_rotated_eq_zero
    e θ hx_rot hrot_zero

end

private lemma not_summable_cos_sq_of_summable_sin_sq (θ : ℕ → ℝ)
    (hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2)) :
    ¬ Summable (fun n : ℕ ↦ Real.cos (θ n) ^ 2) := by
  intro hcos
  -- Summability forces the sine-square sequence to converge to zero.
  have hsin_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.sin (θ n) ^ 2) Filter.atTop (nhds 0) :=
    hθ_square_summable.tendsto_atTop_zero
  have hsinevent :
      ∀ᶠ n : ℕ in Filter.atTop, Real.sin (θ n) ^ 2 < (1 / 2 : ℝ) := by
    exact hsin_tendsto.eventually_lt_const (by norm_num)
  have hcos_event :
      ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ) < Real.cos (θ n) ^ 2 := by
    filter_upwards [hsinevent] with n hsin
    have htrig := Real.sin_sq_add_cos_sq (θ n)
    linarith
  -- A summable real sequence must converge to zero, which conflicts with the uniform lower bound.
  have hcos_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.cos (θ n) ^ 2) Filter.atTop (nhds 0) :=
    hcos.tendsto_atTop_zero
  have hcos_small :
      ∀ᶠ n : ℕ in Filter.atTop, Real.cos (θ n) ^ 2 < (1 / 2 : ℝ) := by
    exact hcos_tendsto.eventually_lt_const (by norm_num)
  rw [Filter.eventually_atTop] at hcos_event hcos_small
  rcases hcos_event with ⟨N₁, hN₁⟩
  rcases hcos_small with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  have hn_gt : (1 / 2 : ℝ) < Real.cos (θ N) ^ 2 := hN₁ N (le_max_left _ _)
  have hn_lt : Real.cos (θ N) ^ 2 < (1 / 2 : ℝ) := hN₂ N (le_max_right _ _)
  linarith

section

variable [CompleteSpace 𝓗]
variable (e : ℕ → 𝓗) (θ : ℕ → ℝ)
variable (he : Orthonormal ℝ e)
variable (hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2))
variable (hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2))

-- Proof sketch: form `x = ∑ sin (θ n) • e (2 * n + 1)`, which belongs to the Hilbert space by the
-- square-summability hypothesis. Finite partial sums show `x` lies in the closure of the submodule
-- sum, while coefficient comparison in a hypothetical decomposition `x = c + d` forces the even
-- coefficients to be `-cos (θ n)`, contradicting square summability because `θ n ∈ (0, π / 2]`
-- and `sin (θ n) → 0` imply `cos (θ n) → 1`.
/-- Example 3.41 (4): the sum of the even-index closed span and the rotated closed span is not a
closed linear subspace. -/
theorem not_isClosed_sup_even_indexed_closed_span_rotated_even_odd_closed_span
    (he : Orthonormal ℝ e)
    (hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2))
    (hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2)) :
    ¬ IsClosed
      (((even_indexed_closed_span e ⊔ rotated_even_odd_closed_span e θ : Submodule ℝ 𝓗) :
        Set 𝓗)) := by
  -- The witness is the odd series with coefficients `sin (θ n)`.
  let f : ℕ → 𝓗 := fun n ↦ Real.sin (θ n) • e (2 * n + 1)
  let S : Submodule ℝ 𝓗 := even_indexed_closed_span e ⊔ rotated_even_odd_closed_span e θ
  have hodd := odd_index_orthonormal e he
  have hf : Summable f := by
    refine ((hodd.orthogonalFamily).summable_iff_norm_sq_summable
      (fun n ↦ Real.sin (θ n))).2 ?_
    simpa [f, Real.norm_eq_abs] using hθ_square_summable
  let x : 𝓗 := ∑' n, f n
  have hx_odd : ∀ n : ℕ, ⟪e (2 * n + 1), x⟫_ℝ = Real.sin (θ n) := by
    intro n
    have hmap := (hf.hasSum.mapL (innerSL ℝ (e (2 * n + 1)))).tsum_eq
    have hsingle : (∑' b : ℕ, if n = b then Real.sin (θ b) else 0) = Real.sin (θ n) := by
      refine (tsum_eq_single n ?_).trans ?_
      · intro b hb
        have hnb : ¬ n = b := by
          exact fun h ↦ hb h.symm
        simp [hnb]
      · simp
    dsimp [x, f] at hmap
    -- Mapping the convergent series through the odd-coordinate functional recovers the coefficient.
    simpa [hsingle, innerSL_apply_apply, real_inner_smul_right, orthonormal_iff_ite.mp he] using
      hmap.symm
  have hx_even : ∀ n : ℕ, ⟪e (2 * n), x⟫_ℝ = 0 := by
    intro n
    have hmap := (hf.hasSum.mapL (innerSL ℝ (e (2 * n)))).tsum_eq
    have hparity : ∀ b : ℕ, 2 * n ≠ 2 * b + 1 := by
      intro b
      omega
    dsimp [x, f] at hmap
    -- The even coordinates vanish because the series uses only odd basis vectors.
    simpa [innerSL_apply_apply, real_inner_smul_right, orthonormal_iff_ite.mp he, hparity] using
      hmap.symm
  have hpartial_mem :
      ∀ N : ℕ, Finset.sum (Finset.range N) f ∈ S := by
    intro N
    refine Submodule.sum_mem S fun n hn ↦ ?_
    -- Each summand is the sum of one vector in `C` and one vector in `D`.
    refine Submodule.mem_sup.2 ?_
    refine ⟨(-Real.cos (θ n)) • e (2 * n), ?_, rotated_even_odd_vector e θ n, ?_, ?_⟩
    · exact (even_indexed_closed_span e).smul_mem _ (even_mem_even_indexed_closed_span e n)
    · exact rotated_even_odd_vector_mem_rotated_even_odd_closed_span e θ n
    · simp [rotated_even_odd_vector, add_comm, add_left_comm]
  intro hclosed
  have hx_mem_S : x ∈ S := by
    -- Closedness of the sum forces it to contain the limit of its partial sums.
    exact hclosed.mem_of_tendsto hf.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hpartial_mem)
  have hx_mem_sup :
      x ∈ even_indexed_closed_span e ⊔ rotated_even_odd_closed_span e θ := by
    simpa [S] using hx_mem_S
  rcases Submodule.mem_sup.1 hx_mem_sup with ⟨c, hc, d, hd, hxcd⟩
  have hd_coords :
      ∀ n : ℕ,
        (⟪e (2 * n), d⟫_ℝ =
            Real.cos (θ n) * ⟪rotated_even_odd_vector e θ n, d⟫_ℝ) ∧
          (⟪e (2 * n + 1), d⟫_ℝ =
            Real.sin (θ n) * ⟪rotated_even_odd_vector e θ n, d⟫_ℝ) := by
    intro n
    exact inner_even_odd_eq_scaled_inner_rotated_of_mem_rotated_even_odd_closed_span
      e θ he hd
  have hrot_one : ∀ n : ℕ, ⟪rotated_even_odd_vector e θ n, d⟫_ℝ = 1 := by
    intro n
    have hθn_lt_pi : θ n < Real.pi := by
      linarith [Real.pi_pos, (hθ n).2]
    have hsin_pos : 0 < Real.sin (θ n) := by
      exact Real.sin_pos_of_pos_of_lt_pi (hθ n).1 hθn_lt_pi
    have hprod :
        Real.sin (θ n) * ⟪rotated_even_odd_vector e θ n, d⟫_ℝ = Real.sin (θ n) := by
      have hsum_odd :
          ⟪e (2 * n + 1), x⟫_ℝ = ⟪e (2 * n + 1), c⟫_ℝ + ⟪e (2 * n + 1), d⟫_ℝ := by
        rw [← hxcd]
        simp [inner_add_right]
      rw [hx_odd n, inner_odd_eq_zero_of_mem_even_indexed_closed_span e he hc,
        (hd_coords n).2] at hsum_odd
      simpa [add_comm] using hsum_odd.symm
    have hsin_ne : Real.sin (θ n) ≠ 0 := ne_of_gt hsin_pos
    have hprod' :
        ⟪rotated_even_odd_vector e θ n, d⟫_ℝ * Real.sin (θ n) = 1 * Real.sin (θ n) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
    exact mul_right_cancel₀ hsin_ne hprod'
  have hc_even : ∀ n : ℕ, ⟪e (2 * n), c⟫_ℝ = -Real.cos (θ n) := by
    intro n
    have hsum_even :
        ⟪e (2 * n), x⟫_ℝ = ⟪e (2 * n), c⟫_ℝ + ⟪e (2 * n), d⟫_ℝ := by
      rw [← hxcd]
      simp [inner_add_right]
    rw [hx_even n, (hd_coords n).1, hrot_one n] at hsum_even
    linarith
  have hcos_summable : Summable (fun n : ℕ ↦ Real.cos (θ n) ^ 2) := by
    have hsummable_inner :=
      (even_index_orthonormal e he).inner_products_summable c
    convert hsummable_inner using 1
    ext n
    rw [hc_even n]
    simp [Real.norm_eq_abs]
  exact not_summable_cos_sq_of_summable_sin_sq θ hθ_square_summable hcos_summable

end

end

/-! Source item: Chap03/Proposition_3_42 -/

variable {E : Type u} [NormedAddCommGroup E]

/- Helper for Proposition 3.42: a sequence taking values in a Minkowski sum admits termwise
decompositions into sequences in the two summands. -/
-- Proof sketch: unpack `z n ∈ C + D` for each index and choose compatible witnesses.
private lemma exists_component_sequences_of_mem_add {C D : Set E} {z : ℕ → E}
    (hz : ∀ n, z n ∈ C + D) :
    ∃ x y : ℕ → E, (∀ n, x n ∈ C) ∧ (∀ n, y n ∈ D) ∧ (∀ n, z n = x n + y n) := by
  have hdecomp : ∀ n, ∃ x ∈ C, ∃ y ∈ D, z n = x + y := by
    intro n
    simpa [Set.mem_add, eq_comm] using hz n
  choose x hx y hy hxy using hdecomp
  exact ⟨x, y, hx, hy, hxy⟩

section Hilbert

variable [InnerProductSpace ℝ E]

section Complete

variable [CompleteSpace E]

/- Helper for Proposition 3.42: a weak limit of a sequence in a nonempty closed convex set of a
real Hilbert space still belongs to that set. -/
-- Proof sketch: project the weak limit onto the closed convex set, use the variational inequality
-- for the projection on every sequence term, and pass to the limit in the corresponding
-- inner-product coordinates.
private lemma weak_limit_mem_of_nonempty_isClosed_convex {C : Set E} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {xₙ : ℕ → E} {x : E}
    (hxₙ : ∀ n, xₙ n ∈ C)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ E (xₙ n)) atTop
      (nhds (toWeakSpace ℝ E x))) :
    x ∈ C := by
  obtain ⟨p, hp_mem, hp_best⟩ :=
    exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex x
  have hvariational : ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
    -- The projection theorem turns the minimizing point `p` into a variational inequality.
    have hinner_nonpos : ∀ y ∈ C, ⟪x - p, y - p⟫_ℝ ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp_mem).mp hp_best
    intro y hy
    simpa [real_inner_comm] using hinner_nonpos y hy
  have hnonpos : ∀ n, ⟪xₙ n - p, x - p⟫_ℝ ≤ 0 := by
    -- Apply the variational inequality to each point of the sequence.
    intro n
    exact hvariational (xₙ n) (hxₙ n)
  have hinner_raw :
      Tendsto (fun n ↦ ⟪xₙ n, x - p⟫_ℝ) atTop (nhds (⟪x, x - p⟫_ℝ)) := by
    -- Weak convergence is tested against the fixed vector `x - p`.
    have hEval :=
      ((WeakBilin.eval_continuous ((topDualPairing ℝ E).flip)
        (InnerProductSpace.toDual ℝ E (x - p))).tendsto (toWeakSpace ℝ E x)).comp hweak
    have hEval' :
        Tendsto (fun n ↦ ⟪x - p, xₙ n⟫_ℝ) atTop (nhds (⟪x - p, x⟫_ℝ)) := by
      simpa only [toWeakSpace, LinearEquiv.refl_apply, LinearMap.flip_apply,
        topDualPairing_apply, InnerProductSpace.toDual_apply_apply] using hEval
    simpa [real_inner_comm] using hEval'
  have hinner :
      Tendsto (fun n ↦ ⟪xₙ n - p, x - p⟫_ℝ) atTop (nhds (‖x - p‖ ^ 2)) := by
    -- Subtract the constant projection term to reveal the squared norm of `x - p`.
    have hsub :
        Tendsto (fun n ↦ ⟪xₙ n, x - p⟫_ℝ - ⟪p, x - p⟫_ℝ) atTop
          (nhds (⟪x, x - p⟫_ℝ - ⟪p, x - p⟫_ℝ)) := by
      exact hinner_raw.sub tendsto_const_nhds
    convert hsub using 1
    · ext n
      rw [inner_sub_left]
    · rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hnorm_sq_nonpos : ‖x - p‖ ^ 2 ≤ 0 := by
    -- The closed half-line `(-∞, 0]` captures the sign inequality in the limit.
    exact le_of_tendsto hinner (Filter.Eventually.of_forall hnonpos)
  have hnorm_sq_zero : ‖x - p‖ ^ 2 = 0 := by
    exact le_antisymm hnorm_sq_nonpos (sq_nonneg ‖x - p‖)
  have hxp : x = p := by
    -- A vanishing squared norm forces the weak limit to coincide with its projection.
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact eq_zero_of_pow_eq_zero hnorm_sq_zero
  exact hxp ▸ hp_mem

/-- Proposition 3.42 (3): If `C` and `D` are closed convex subsets of a Hilbert space and `D` is
bounded, then their Minkowski sum is closed. -/
-- Proof sketch: Take a convergent sequence in `C + D`, decompose it as `xₙ + yₙ` with `xₙ ∈ C`
-- and `yₙ ∈ D`, extract a weakly convergent subsequence from the bounded sequence `(yₙ)`, use
-- weak closedness of closed convex sets to keep the weak limits in `D` and `C`, and conclude that
-- the strong limit belongs to `C + D`.
theorem isClosed_minkowski_sum_of_isBounded {C D : Set E} (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hD_bounded : Bornology.IsBounded D) : IsClosed (C + D) := by
  rw [← isSeqClosed_iff_isClosed]
  intro z w hz hw
  rcases exists_component_sequences_of_mem_add hz with ⟨x, y, hxC, hyD, hz_eq⟩
  have hy_bounded_range : Bornology.IsBounded (Set.range y) := by
    -- The right-hand component sequence stays in the bounded set `D`.
    refine hD_bounded.subset ?_
    rintro _ ⟨n, rfl⟩
    exact hyD n
  obtain ⟨y_lim, φ, hφ, hy_lim⟩ :=
    bounded_sequence_has_weakly_convergent_subsequence y hy_bounded_range
  have hD_nonempty : D.Nonempty := ⟨y (φ 0), hyD (φ 0)⟩
  have hy_lim_mem : y_lim ∈ D := by
    -- Weak closedness of the closed convex set `D` keeps the weak subsequential limit in `D`.
    exact
      weak_limit_mem_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex
        (fun n ↦ hyD (φ n)) hy_lim
  have hz_subseq : Tendsto (fun n ↦ z (φ n)) atTop (nhds w) := hw.comp hφ.tendsto_atTop
  have hw_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ E (z (φ n))) atTop (nhds (toWeakSpace ℝ E w)) := by
    -- Strong convergence implies weak convergence after passing to the extracted subsequence.
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ E).continuous.tendsto w).comp hz_subseq
  have hx_sub : ∀ n, x n = z n - y n := by
    intro n
    -- Rearranging the decomposition `z n = x n + y n` isolates the left-hand component.
    calc
      x n = x n + y n - y n := by abel
      _ = z n - y n := by rw [hz_eq n]
  have hx_lim_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ E (x (φ n))) atTop
        (nhds (toWeakSpace ℝ E (w - y_lim))) := by
    -- Subtract the weakly convergent `y`-subsequence from the weak limit of the `z`-subsequence.
    have hsub :
        Tendsto
          (fun n ↦ toWeakSpace ℝ E (z (φ n)) - toWeakSpace ℝ E (y (φ n)))
          atTop (nhds (toWeakSpace ℝ E w - toWeakSpace ℝ E y_lim)) := by
      exact hw_weak.sub hy_lim
    have hx_eq :
        (fun n ↦ toWeakSpace ℝ E (x (φ n))) =
          (fun n ↦ toWeakSpace ℝ E (z (φ n)) - toWeakSpace ℝ E (y (φ n))) := by
      funext n
      rw [hx_sub (φ n)]
      simp
    rw [hx_eq]
    simpa using hsub
  have hC_nonempty : C.Nonempty := ⟨x (φ 0), hxC (φ 0)⟩
  have hw_sub_mem : w - y_lim ∈ C := by
    -- Weak closedness of `C` captures the weak limit of the left-hand subsequence.
    exact
      weak_limit_mem_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
        (fun n ↦ hxC (φ n)) hx_lim_weak
  -- Reassemble the limit as a sum of the two weak limits.
  exact
    by
      simpa [Set.mem_add] using
        ⟨w - y_lim, hw_sub_mem, y_lim, hy_lim_mem, by simp [sub_eq_add_neg, add_assoc]⟩

end Complete
end Hilbert
