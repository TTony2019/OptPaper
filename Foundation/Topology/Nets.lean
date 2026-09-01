import Mathlib
import Foundation.Analysis.Semicontinuity

/-!
# Topology Nets

Directed sets, nets, subnets, cluster points, and convergence through filters.
-/

open Filter
open Filter ERealFunction

/-! Source item: Chap01/Text_1_0_22 -/
universe u

/-- Text 1.0.22: the textbook notion of a directed set is exactly a nonempty type equipped with a
reflexive, transitive, and directed relation, equivalently a nonempty type with a directed
preorder relation. -/
theorem isDirectedSet_iff {α : Type u} {r : α → α → Prop} :
    (Nonempty α ∧ Std.Refl r ∧ IsTrans α r ∧ IsDirected α r) ↔
      Nonempty α ∧ IsPreorder α r ∧ IsDirected α r := by
  constructor
  · rintro ⟨hα, hrefl, htrans, hdir⟩
    exact ⟨hα, @IsPreorder.mk α r hrefl htrans, hdir⟩
  · rintro ⟨hα, hpre, hdir⟩
    exact ⟨hα, hpre.toRefl, hpre.toIsTrans, hdir⟩

/-- The textbook converse relation satisfies `Function.swap r a b` exactly when `r b a` holds. -/
theorem converseRelation_iff {α : Type u} {r : α → α → Prop} {a b : α} :
    Function.swap r a b ↔ r b a :=
  Iff.rfl

/-- Text 1.0.22: in a partial order, the textbook strict-order relation `a ≤ b ∧ a ≠ b` is the
canonical relation `<`. -/
theorem strictOrder {α : Type u} [PartialOrder α] :
    (fun a b : α ↦ a ≤ b ∧ a ≠ b) = (· < ·) := by
  funext a b
  exact propext lt_iff_le_and_ne.symm

/-- Companion bridge: the textbook strict-order condition is equivalent to the canonical relation
`a < b`. -/
theorem strictOrder_iff {α : Type u} [PartialOrder α] {a b : α} :
    (a ≤ b ∧ a ≠ b) ↔ a < b :=
  lt_iff_le_and_ne.symm

/-! Source item: Chap01/Text_1_0_24 -/
universe v

namespace Net

variable {A : Type u} {X : Type v} [Preorder A] [IsDirectedOrder A] [Nonempty A]

/-- A net is eventually in `Y` exactly when all sufficiently large indices map into `Y`. -/
theorem eventuallyIn_iff_exists_forall_ge_mem (x : A → X) (Y : Set X) :
    (∀ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∃ a : A, ∀ b ≥ a, x b ∈ Y := by
  exact
    (Filter.eventually_atTop : (∀ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∃ a : A, ∀ b ≥ a, x b ∈ Y)

/-- A net is frequently in `Y` exactly when every tail contains an index whose value lies in
`Y`. -/
theorem frequentlyIn_iff_forall_exists_ge_mem (x : A → X) (Y : Set X) :
    (∃ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∀ a : A, ∃ b ≥ a, x b ∈ Y := by
  exact
    (Filter.frequently_atTop : (∃ᶠ a in Filter.atTop, x a ∈ Y) ↔ ∀ a : A, ∃ b ≥ a, x b ∈ Y)

end Net

/-! Source item: Chap01/Text_1_0_25 -/

universe w

namespace Net

variable {X : Type u} {A : Type v} {B : Type w}

/-- Text 1.0.25: a net `y` is a subnet of a net `x` via `k` exactly when the textbook
reindexing-and-cofinality condition holds, equivalently when `y = x ∘ k` and `k` tends to
`atTop`. -/
theorem isSubnetOfVia_iff [Preorder A] [Preorder B] [IsDirectedOrder A] [IsDirectedOrder B]
    [Nonempty B] {x : A → X} {y : B → X} {k : B → A} :
    (y = x ∘ k ∧ ∀ a : A, ∃ d : B, ∀ b : B, d ≤ b → a ≤ k b) ↔
      y = x ∘ k ∧ Tendsto k atTop atTop := by
  rw [tendsto_atTop_atTop]

end Net

/-! Source item: Chap01/Text_1_0_44 -/


variable {A : Type u} [Preorder A] [IsDirectedOrder A] [Nonempty A]
variable {X : Type v} [TopologicalSpace X]

/-- Text 1.0.44: a net `ξ` converges to `x` exactly when it is eventually contained in every
neighborhood of `x`; in mathlib this convergence is expressed by `Tendsto ξ atTop (nhds x)`. -/
-- Proof sketch: this is the canonical specialization of `tendsto_iff_forall_eventually_mem`
-- to the target filter `nhds x`, together with the tail characterization of `atTop`.
theorem tendsto_atTop_nhds_iff_forall_exists_forall_ge_mem (ξ : A → X) (x : X) :
    Tendsto ξ atTop (nhds x) ↔
      ∀ V ∈ nhds x, ∃ b, ∀ a ≥ b, ξ a ∈ V := by
  rw [tendsto_iff_forall_eventually_mem]
  constructor
  · intro h V hV
    exact eventually_atTop.mp (h V hV)
  · intro h V hV
    exact eventually_atTop.mpr (h V hV)

/-! Source item: Chap01/Text_1_0_45 -/

variable {A : Type u} [Nonempty A] [Preorder A] [IsDirectedOrder A]
variable {X : Type v} [TopologicalSpace X]

/-- Text 1.0.45: for a net `ξ : A → X`, the canonical predicate `MapClusterPt x Filter.atTop ξ`
means that every neighborhood of `x` is visited arbitrarily far out in the directed index set. -/
-- Proof sketch: unfold `MapClusterPt`, rewrite cluster points using
-- `mapClusterPt_iff_frequently`, and then rewrite frequent membership in `Filter.atTop`
-- as the textbook tail condition.
theorem mapClusterPt_atTop_iff_forall_forall_exists_ge_mem_nhds (ξ : A → X) (x : X) :
    MapClusterPt x Filter.atTop ξ ↔
      ∀ V : Set X, V ∈ nhds x → ∀ b : A, ∃ a : A, b ≤ a ∧ ξ a ∈ V := by
  rw [mapClusterPt_iff_frequently]
  constructor
  · intro h V hV b
    exact (Filter.frequently_atTop.mp (h V hV)) b
  · intro h V hV
    exact Filter.frequently_atTop.mpr (h V hV)

/-! Source item: Chap01/Text_1_0_47 -/


private structure ClusterHitPair {X : Type u} [TopologicalSpace X] {A : Type v}
    (u : A → X) (x : X) where
  index : A
  neighborhood : Set X
  neighborhood_mem : neighborhood ∈ nhds x
  hit_mem : u index ∈ neighborhood

private instance clusterHitPairPreorder {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] {u : A → X} {x : X} : Preorder (ClusterHitPair u x) where
  le p q := p.index ≤ q.index ∧ q.neighborhood ⊆ p.neighborhood
  le_refl p := ⟨le_rfl, Set.Subset.rfl⟩
  le_trans p q r hpq hqr := ⟨hpq.1.trans hqr.1, Set.Subset.trans hqr.2 hpq.2⟩

private lemma clusterHitPair_nonempty {X : Type u} [TopologicalSpace X] {A : Type v}
    [Nonempty A] [Preorder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Nonempty (ClusterHitPair u x) := by
  classical
  let a₀ : A := Classical.choice ‹Nonempty A›
  obtain ⟨a, _, ha_mem⟩ := hcluster Set.univ Filter.univ_mem a₀
  exact ⟨⟨a, Set.univ, Filter.univ_mem, ha_mem⟩⟩

private lemma clusterHitPair_directed {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    IsDirectedOrder (ClusterHitPair u x) := by
  refine ⟨?_⟩
  intro p q
  obtain ⟨a₀, hpa₀, hqa₀⟩ := exists_ge_ge p.index q.index
  have hpq_mem : p.neighborhood ∩ q.neighborhood ∈ nhds x :=
    Filter.inter_mem p.neighborhood_mem q.neighborhood_mem
  obtain ⟨a, ha₀a, ha_mem⟩ := hcluster (p.neighborhood ∩ q.neighborhood) hpq_mem a₀
  refine ⟨⟨a, p.neighborhood ∩ q.neighborhood, hpq_mem, ha_mem⟩, ?_, ?_⟩
  · exact ⟨hpa₀.trans ha₀a, Set.inter_subset_left⟩
  · exact ⟨hqa₀.trans ha₀a, Set.inter_subset_right⟩

private lemma clusterHitPair_index_monotone {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] {u : A → X} {x : X} :
    Monotone (ClusterHitPair.index : ClusterHitPair u x → A) := by
  intro p q hpq
  exact hpq.1

private lemma clusterHitPair_index_tendsto_atTop {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Tendsto (ClusterHitPair.index : ClusterHitPair u x → A) atTop atTop := by
  refine Monotone.tendsto_atTop_atTop clusterHitPair_index_monotone ?_
  intro a₀
  obtain ⟨a, ha₀a, ha_mem⟩ := hcluster Set.univ Filter.univ_mem a₀
  exact ⟨⟨a, Set.univ, Filter.univ_mem, ha_mem⟩, ha₀a⟩

private lemma clusterHitPair_tendsto_nhds {X : Type u} [TopologicalSpace X] {A : Type v}
    [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Tendsto (u ∘ (ClusterHitPair.index : ClusterHitPair u x → A)) atTop (nhds x) := by
  classical
  let a₀ : A := Classical.choice ‹Nonempty A›
  let _ : Nonempty (ClusterHitPair u x) := clusterHitPair_nonempty hcluster
  let _ : IsDirectedOrder (ClusterHitPair u x) := clusterHitPair_directed hcluster
  rw [tendsto_atTop']
  intro V hV
  obtain ⟨a, _, ha_mem⟩ := hcluster V hV a₀
  refine ⟨⟨a, V, hV, ha_mem⟩, ?_⟩
  intro b hb
  exact hb.2 b.hit_mem

private lemma subnet_tendsto_implies_mapClusterPt_atTop {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    {B : Type w} [Nonempty B] [Preorder B] [IsDirectedOrder B] {φ : B → A}
    (hφ : Tendsto φ atTop atTop) (hconv : Tendsto (u ∘ φ) atTop (nhds x)) :
    MapClusterPt x atTop u := by
  exact MapClusterPt.of_comp hφ (Filter.Tendsto.mapClusterPt hconv)

/-- Text 1.0.47: a point `x` is a cluster point of a net `u` iff there is a subnet, given by a
monotone cofinal reindexing map, whose reindexed net converges to `x`. -/
-- Proof sketch: for the forward implication, take the directed set of pairs `(a, U)` consisting
-- of an index and a neighborhood of `x` hit by the net, ordered by tail refinement and reverse
-- inclusion of neighborhoods; the projection to `A` is monotone and cofinal, and the reindexed
-- net converges to `x`. For the reverse implication, combine convergence of the subnet with
-- cofinality of the reindexing map to show every neighborhood of `x` is met on every tail of the
-- original net.
theorem mapClusterPt_atTop_iff_exists_subnet_tendsto {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X} :
    MapClusterPt x atTop u ↔
      ∃ (B : Type (max u v)) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B)
        (φ : B → A),
        Monotone φ ∧ Tendsto φ atTop atTop ∧ Tendsto (u ∘ φ) atTop (nhds x) := by
  constructor
  · intro hx
    have hx' : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V := by
      rw [mapClusterPt_iff_frequently] at hx
      intro V hV a₀
      have hfreq : ∃ᶠ a in atTop, u a ∈ V := hx V hV
      rw [frequently_atTop] at hfreq
      exact hfreq a₀
    let B : Type (max u v) := ClusterHitPair u x
    let _ : Nonempty B := clusterHitPair_nonempty hx'
    let _ : IsDirectedOrder B := clusterHitPair_directed hx'
    refine ⟨B, inferInstance, inferInstance, inferInstance, ClusterHitPair.index, ?_⟩
    exact ⟨clusterHitPair_index_monotone, clusterHitPair_index_tendsto_atTop hx',
      clusterHitPair_tendsto_nhds hx'⟩
  · rintro ⟨B, _, _, _, φ, _, hφ, hconv⟩
    exact subnet_tendsto_implies_mapClusterPt_atTop hφ hconv

/-! Source item: Chap01/Fact_1_9 -/

section

variable {A : Type u} {B : Type v} {X : Type w}
variable [Preorder A] [Preorder B] [TopologicalSpace X]
variable {x : A → X} {k : B → A} {x₀ : X}

/-- Fact 1.9 in textbook subnet form: a monotone cofinal reindexing preserves the limit of a
convergent net. -/
theorem subnet_tendsto_same_limit_of_monotone_cofinal
    (hx : Tendsto x atTop (nhds x₀)) (hk_mono : Monotone k)
    (hk_cofinal : ∀ a₀ : A, ∃ b₀ : B, ∀ b : B, b₀ ≤ b → a₀ ≤ k b) :
    Tendsto (x ∘ k) atTop (nhds x₀) := by
  simpa [Function.comp] using hx.comp <|
    hk_mono.tendsto_atTop_atTop fun a₀ ↦ by
      rcases hk_cofinal a₀ with ⟨b₀, hb₀⟩
      exact ⟨b₀, hb₀ b₀ le_rfl⟩

end

/-! Source item: Chap01/Lemma_1_10 -/


private lemma nhds_reverse_inclusion_directed {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirected {U : Set X // U ∈ nhds x} (fun U V => (V : Set X) ⊆ U) := by
  refine ⟨?_⟩
  intro U V
  -- Intersections provide a common smaller neighborhood, which is an upper bound
  -- for the reverse-inclusion order.
  refine ⟨⟨(U : Set X) ∩ V, inter_mem U.2 V.2⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private theorem exists_tendsto_subtype_of_mem_closure {X : Type u} [TopologicalSpace X]
    {C : Set X}
    {x : X} (h : x ∈ closure C) :
    ∃ (A : Type u) (_ : Preorder A) (_ : IsDirectedOrder A) (_ : Nonempty A)
      (ξ : A → C), Tendsto (fun a ↦ (ξ a : X)) atTop (nhds x) := by
  classical
  let A := {U : Set X // U ∈ nhds x}
  letI : LE A := ⟨fun U V => (V : Set X) ⊆ U⟩
  letI : LT A := ⟨fun U V => (V : Set X) ⊆ U ∧ ¬ (U : Set X) ⊆ V⟩
  letI : Preorder A :=
    { le_refl := fun U => Set.Subset.rfl
      le_trans := fun U V W hUV hVW => Set.Subset.trans hVW hUV
      lt_iff_le_not_ge := fun U V => Iff.rfl }
  letI : IsDirectedOrder A := nhds_reverse_inclusion_directed
  letI : Nonempty A := ⟨⟨Set.univ, univ_mem⟩⟩
  have hclosure : ∀ t ∈ nhds x, ∃ y : C, (y : X) ∈ t := (mem_closure_iff_nhds').1 h
  let ξ : A → C := fun U ↦ Classical.choose (hclosure U U.2)
  refine ⟨A, inferInstance, inferInstance, inferInstance, ξ, ?_⟩
  rw [Filter.tendsto_def]
  intro W hW
  rw [Filter.mem_atTop_sets]
  -- Once the index neighborhood lies inside `W`, the chosen point is also in `W`.
  refine ⟨⟨W, hW⟩, ?_⟩
  intro U hU
  have hξU : (ξ U : X) ∈ (U : Set X) := Classical.choose_spec (hclosure U U.2)
  exact hU hξU

/-- Lemma 1.10: a point belongs to the closure of a subset `C` exactly when there exists a
nonempty directed net with values in `C` that converges to that point. -/
-- Proof sketch: for the forward direction, index by the neighborhoods of `x` ordered by reverse
-- inclusion and choose one point of `C` in each neighborhood using closure membership; for the
-- reverse direction, a convergent net is eventually contained in every neighborhood of `x`, so
-- each neighborhood meets `C`.
theorem mem_closure_iff_exists_net_tendsto {X : Type u} [TopologicalSpace X] {C : Set X} {x : X} :
    x ∈ closure C ↔
      ∃ (A : Type u) (_ : Preorder A) (_ : IsDirectedOrder A) (_ : Nonempty A)
        (ξ : A → C), Tendsto (fun a ↦ (ξ a : X)) atTop (nhds x) := by
  constructor
  · intro hx
    -- Build the net by choosing one point of `C` in each neighborhood of `x`.
    exact exists_tendsto_subtype_of_mem_closure hx
  · rintro ⟨A, _, _, _, ξ, hξ⟩
    -- A convergent net whose values lie in `C` has limit in `closure C`.
    exact mem_closure_of_tendsto hξ <|
      Filter.Eventually.of_forall fun a ↦ (ξ a).2

/-! Source item: Chap01/Lemma_1_14 -/


/-- Lemma 1.14: if a net in a compact subset of a Hausdorff space has `x` as its unique cluster
point, then the net converges to `x`. -/
-- Proof sketch: apply `IsCompact.tendsto_nhds_of_unique_mapClusterPt` to the compact set `C`.
-- The hypothesis `hξC` gives eventual membership in `C`, and uniqueness of cluster points in `X`
-- restricts to uniqueness among points of `C`.
theorem tendsto_of_unique_cluster_point_on_compact {X : Type u} [TopologicalSpace X] [T2Space X]
    {A : Type v} [Preorder A] [IsDirectedOrder A] {C : Set X} (hC : IsCompact C) {ξ : A → X}
    (hξC : ∀ a, ξ a ∈ C) {x : X} (_hx : MapClusterPt x atTop ξ)
    (hunique : ∀ y : X, MapClusterPt y atTop ξ → y = x) :
    Tendsto ξ atTop (nhds x) := by
  exact hC.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hξC) fun y _ hy ↦
    hunique y hy

/-! Source item: Chap01/Lemma_1_23 -/

private structure NhdsPoint (X : Type u) [TopologicalSpace X] (x : X) where
  value : X
  carrier : Set X
  value_mem : value ∈ carrier
  carrier_mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NhdsPoint X x) :=
  ⟨⟨x, Set.univ, by simp, by simp⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NhdsPoint X x) :=
  ⟨fun p q ↦ q.carrier ⊆ p.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NhdsPoint X x) where
  le := (· ≤ ·)
  le_refl p := by
    intro y hy
    exact hy
  le_trans p q r hpq hqr := by
    intro y hy
    exact hpq (hqr hy)

private instance {X : Type u} [TopologicalSpace X] {x : X} : IsDirectedOrder (NhdsPoint X x) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.carrier ∩ q.carrier ∈ nhds x :=
    inter_mem p.carrier_mem_nhds q.carrier_mem_nhds
  refine ⟨⟨x, p.carrier ∩ q.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{v} (NhdsPoint X x)) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.down.carrier ∩ q.down.carrier ∈ nhds x :=
    inter_mem p.down.carrier_mem_nhds q.down.carrier_mem_nhds
  refine ⟨ULift.up ⟨x, p.down.carrier ∩ q.down.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩,
    ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private theorem map_nhdsPoint_eq_nhds {X : Type u} [TopologicalSpace X] {x : X} :
    map (fun p : ULift.{v} (NhdsPoint X x) ↦ p.down.value) atTop = nhds x := by
  refine Filter.ext fun s ↦ ?_
  rw [mem_map]
  constructor
  · intro hs
    rcases mem_atTop_sets.mp hs with ⟨p, hp⟩
    refine mem_of_superset p.down.carrier_mem_nhds ?_
    intro y hy
    exact hp (ULift.up ⟨y, p.down.carrier, hy, p.down.carrier_mem_nhds⟩) (by
      intro z hz
      exact hz)
  · intro hs
    rw [mem_atTop_sets]
    refine ⟨ULift.up ⟨x, s, mem_of_mem_nhds hs, hs⟩, ?_⟩
    intro p hp
    exact hp p.down.value_mem

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The set of limit inferior values of `f` along nets converging to `x`. -/
def netLiminfValuesAt (f : X → EReal) (x : X) : Set EReal :=
  {r | ∃ (A : Type (max u v)) (_ : Preorder A) (_ : IsDirectedOrder A) (_ : Nonempty A)
      (ξ : A → X), Tendsto ξ atTop (nhds x) ∧ liminf (f ∘ ξ) atTop = r}

/-- Any net converging to `x` has limit inferior at least the pointwise limit inferior of `f`
at `x`. -/
private theorem liminfAt_le_liminf_net_of_tendsto (f : X → EReal) {A : Type v} [Preorder A]
    [IsDirectedOrder A] [Nonempty A] (ξ : A → X) (hξ : Tendsto ξ atTop (nhds x)) :
    liminfAt f x ≤ liminf (f ∘ ξ) atTop := by
  simpa [liminfAt, Filter.liminf_comp] using
    (liminf_le_liminf_of_le hξ : liminf f (nhds x) ≤ liminf f (map ξ atTop))

/-- Lemma 1.23: the limit inferior of `f` at `x` is the minimum of the limit inferiors of `f`
along all nets converging to `x`. -/
-- Proof sketch: every convergent net `ξ` satisfies `map ξ atTop ≤ nhds x`, so monotonicity of
-- `Filter.liminf` gives `liminfAt f x ≤ liminf (f ∘ ξ) atTop`. Equality is attained by the
-- canonical neighborhood-point net at `x`, whose pushed-forward filter is exactly `nhds x`.
theorem liminfAt_isLeast_netLiminfValues {X : Type u} [TopologicalSpace X]
    (f : X → EReal) (x : X) :
    IsLeast (netLiminfValuesAt.{u, v} f x) (liminfAt f x) := by
  refine ⟨?_, ?_⟩
  · let ξ : ULift.{v} (NhdsPoint X x) → X := fun p ↦ p.down.value
    have hMap : map ξ atTop = nhds x := map_nhdsPoint_eq_nhds
    have hξ : Tendsto ξ atTop (nhds x) := hMap.le
    have hLiminf : liminf (f ∘ ξ) atTop = liminfAt f x := by
      simpa [liminfAt, Filter.liminf_comp] using congrArg (liminf f) hMap
    exact ⟨ULift.{v} (NhdsPoint X x), inferInstance, inferInstance, inferInstance, ξ, hξ,
      hLiminf⟩
  · intro r hr
    rcases hr with ⟨A, _, _, _, ξ, hξ, rfl⟩
    exact liminfAt_le_liminf_net_of_tendsto f ξ hξ

/-! Source item: Chap01/Fact_1_19 -/


private structure NhdsPoint19 (X : Type u) [TopologicalSpace X] (x : X) where
  value : X
  carrier : Set X
  value_mem : value ∈ carrier
  carrier_mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NhdsPoint19 X x) :=
  ⟨⟨x, Set.univ, by simp, by simp⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NhdsPoint19 X x) :=
  ⟨fun p q ↦ q.carrier ⊆ p.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NhdsPoint19 X x) where
  le := (· ≤ ·)
  le_refl p := by
    intro y hy
    exact hy
  le_trans p q r hpq hqr := by
    intro y hy
    exact hpq (hqr hy)

private instance {X : Type u} [TopologicalSpace X] {x : X} : IsDirectedOrder (NhdsPoint19 X x) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.carrier ∩ q.carrier ∈ nhds x :=
    inter_mem p.carrier_mem_nhds q.carrier_mem_nhds
  refine ⟨⟨x, p.carrier ∩ q.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{w} (NhdsPoint19 X x)) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.down.carrier ∩ q.down.carrier ∈ nhds x :=
    inter_mem p.down.carrier_mem_nhds q.down.carrier_mem_nhds
  refine ⟨ULift.up ⟨x, p.down.carrier ∩ q.down.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩,
    ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private theorem tendsto_ulift_nhdsPoint {X : Type u} [TopologicalSpace X] {x : X} :
    Tendsto (fun p : ULift.{w} (NhdsPoint19 X x) ↦ p.down.value) atTop (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  refine ⟨ULift.up ⟨x, U, mem_of_mem_nhds hU, hU⟩, ?_⟩
  intro p hp
  exact hp p.down.value_mem

private lemma continuousAt_of_tendsto_liftedNhdsPoint {X : Type u} {Y : Type v}
    [TopologicalSpace X]
    [TopologicalSpace Y] {T : X → Y} {x : X}
    (h : Tendsto (fun p : ULift.{w} (NhdsPoint19 X x) ↦ T p.down.value) atTop
      (nhds (T x))) :
    ContinuousAt T x := by
  rw [Filter.tendsto_def] at h
  rw [ContinuousAt, Filter.tendsto_def]
  intro V hV
  rcases Filter.mem_atTop_sets.mp (h V hV) with ⟨p, hp⟩
  refine Filter.mem_of_superset p.down.carrier_mem_nhds ?_
  intro y hy
  have hyV := hp (ULift.up ⟨y, p.down.carrier, hy, p.down.carrier_mem_nhds⟩) (by
    intro z hz
    exact hz)
  simpa using hyV

/-- Fact 1.19: a map `T : X → Y` is continuous at `x` exactly when it sends every net
converging to `x` to a net converging to `T x`. -/
-- Proof sketch: the forward implication is the canonical filter-composition law for
-- `ContinuousAt`. For the reverse implication, apply the assumed net-preservation property to the
-- neighborhood-point net at `x`, whose convergence is canonical and whose image convergence
-- recovers the neighborhood definition of `ContinuousAt`.
theorem continuousAt_iff_tendsto_nets {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {T : X → Y} {x : X} :
    ContinuousAt T x ↔
      ∀ {A : Type (max u w)} [Preorder A] [IsDirectedOrder A] (ξ : A → X),
        Tendsto ξ atTop (nhds x) → Tendsto (T ∘ ξ) atTop (nhds (T x)) := by
  constructor
  · intro hCont A _ _ ξ hξ
    simpa [Function.comp] using hCont.tendsto.comp hξ
  · intro hNets
    exact continuousAt_of_tendsto_liftedNhdsPoint <|
      hNets (fun p : ULift.{w} (NhdsPoint19 X x) ↦ p.down.value) tendsto_ulift_nhdsPoint
