import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_3

/-!
# Normal cone stability for convex polyhedra
Let $C \subset H$ be a convex polyhedron and $\overline{x} \in C$.
Then there exists a neighbourhood $V$ of $\overline{x}$ such that for all $x \in V$,
$N_C(x) \subset N_C(\overline{x})$.
Cited from: known property of convex polyhedra
(see e.g. R.T. Rockafellar and R. Wets, Variational Analysis, Springer, 1998).

The paper's own Proposition 5.1 cites this external result, so this item must not
import `prop_4`.  "Convex polyhedron" is therefore spelled out here as the same
finite intersection of closed half-spaces used by the rest of the paper.
-/
open Set
open Filter
open scoped Topology
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- If every feasible direction from `x` towards `xbar` remains feasible for some
positive step, then the normal cone at `x` is contained in the normal cone at
`xbar`. This is the elementary variational step used to prove normal-cone
stability. -/
private lemma normal_subset_of_local_feasible_segments (C : Set H) (xbar x : H)
    (hxbar : xbar ∈ C) (_hx : x ∈ C)
    (hfeas : ∀ y ∈ C, ∃ t : ℝ, 0 < t ∧ x + t • (y - xbar) ∈ C) :
    normalCone C x ⊆ normalCone C xbar := by
  intro u hu
  rw [Set.mem_normalCone_iff_forall] at hu ⊢
  rcases hu with ⟨-, hu⟩
  refine ⟨hxbar, ?_⟩
  intro y hy
  rcases hfeas y hy with ⟨t, htpos, htC⟩
  have hzle : inner ℝ (y - xbar) u ≤ 0 := by
    have h := hu (x + t • (y - xbar)) htC
    have hz : x + t • (y - xbar) - x = t • (y - xbar) := by abel
    rw [hz, inner_smul_left] at h
    by_contra hnot
    have h' : t * inner ℝ (y - xbar) u ≤ 0 := h
    linarith [mul_pos htpos (lt_of_not_ge hnot)]
  exact hzle

/-- For a finite half-space representation `C = {x | ∀ i, ⟪a i, x⟫ ≤ b i}`,
all constraints that are inactive at `xbar` remain inactive in a neighbourhood
of `xbar`. -/
private lemma inactive_constraints_stay_inactive_near_xbar (C : Set H) (m : ℕ)
    (a : Fin m → H) (b : Fin m → ℝ)
    (_hC : C = {x | ∀ i, inner ℝ (a i) x ≤ b i})
    (xbar : H) (_hxbar : xbar ∈ C) :
    ∃ V : Set H, V ∈ 𝓝 xbar ∧
      ∀ x ∈ V, ∀ i, inner ℝ (a i) xbar < b i → inner ℝ (a i) x < b i := by
  let V : Set H :=
    {x | ∀ i : Fin m, inner ℝ (a i) xbar < b i → inner ℝ (a i) x < b i}
  refine ⟨V, ?_, ?_⟩
  · rw [← Filter.eventually_iff, Filter.eventually_all]
    intro i
    by_cases hlt : inner ℝ (a i) xbar < b i
    · filter_upwards
        [((continuous_const.inner continuous_id).tendsto xbar).eventually_lt_const hlt]
        with x hx _
      exact hx
    · filter_upwards [] with x hx
      exact (hlt hx).elim
  · exact fun x hx i => hx i

/-- Under the finite half-space representation and the inactive-constraint
neighbourhood `V`, every direction from `x` towards a point `y ∈ C` remains
feasible for some positive step. -/
private lemma local_feasible_segment_for_polyhedron (C : Set H) (m : ℕ)
    (a : Fin m → H) (b : Fin m → ℝ)
    (hC : C = {x | ∀ i, inner ℝ (a i) x ≤ b i})
    (xbar : H) (hxbar : xbar ∈ C)
    (V : Set H) (_hV : V ∈ 𝓝 xbar)
    (hV_inactive : ∀ x ∈ V, ∀ i,
      inner ℝ (a i) xbar < b i → inner ℝ (a i) x < b i)
    (x : H) (hxV : x ∈ V) (hxC : x ∈ C) (y : H) (hyC : y ∈ C) :
    ∃ t : ℝ, 0 < t ∧ x + t • (y - xbar) ∈ C := by
  classical
  have hx_constraints : ∀ i : Fin m, inner ℝ (a i) x ≤ b i := by
    simpa [hC] using hxC
  have hxbar_constraints : ∀ i : Fin m, inner ℝ (a i) xbar ≤ b i := by
    simpa [hC] using hxbar
  have hy_constraints : ∀ i : Fin m, inner ℝ (a i) y ≤ b i := by
    simpa [hC] using hyC
  have hstep_event :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ∀ i : Fin m, inner ℝ (a i) (x + t • (y - xbar)) ≤ b i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hxlt : inner ℝ (a i) x < b i
    · have htend :
          Tendsto (fun t : ℝ => inner ℝ (a i) (x + t • (y - xbar)))
            (𝓝 (0 : ℝ)) (𝓝 (inner ℝ (a i) x)) := by
        have hcont : Continuous (fun t : ℝ => inner ℝ (a i) (x + t • (y - xbar))) := by
          exact continuous_const.inner
            (continuous_const.add (continuous_id.smul continuous_const))
        simpa using hcont.tendsto 0
      filter_upwards [htend.eventually_lt_const hxlt |>.filter_mono nhdsWithin_le_nhds]
        with t ht
      exact le_of_lt ht
    · have hxeq : inner ℝ (a i) x = b i :=
        le_antisymm (hx_constraints i) (le_of_not_gt hxlt)
      have hxbar_not_lt : ¬ inner ℝ (a i) xbar < b i := by
        intro hbarlt
        exact (lt_irrefl (b i)) (hxeq ▸ hV_inactive x hxV i hbarlt)
      have hxbareq : inner ℝ (a i) xbar = b i :=
        le_antisymm (hxbar_constraints i) (le_of_not_gt hxbar_not_lt)
      have hdir : inner ℝ (a i) (y - xbar) ≤ 0 := by
        rw [inner_sub_right]
        linarith [hy_constraints i, hxbareq]
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht_nonneg : 0 ≤ t := le_of_lt ht
      calc
        inner ℝ (a i) (x + t • (y - xbar))
            = inner ℝ (a i) x + t * inner ℝ (a i) (y - xbar) := by
              rw [inner_add_right, inner_smul_right]
        _ ≤ b i := by nlinarith
  rcases (hstep_event.and self_mem_nhdsWithin).exists with ⟨t, ht_constraints, ht_pos⟩
  refine ⟨t, ht_pos, ?_⟩
  rw [hC]
  exact ht_constraints

/-- For a convex polyhedron `C` and `xbar ∈ C`, there exists a neighbourhood `V` of `xbar`
such that for all `x ∈ V`, `N_C(x) ⊆ N_C(xbar)`. -/
theorem normalCone_stability_convexPolyhedron (C : Set H)
    (hC : ∃ (m : ℕ) (a : Fin m → H) (b : Fin m → ℝ),
      C = {x | ∀ i, inner ℝ (a i) x ≤ b i})
    (xbar : H) (hxbar : xbar ∈ C) :
    ∃ (V : Set H), V ∈ 𝓝 xbar ∧ ∀ x ∈ V, normalCone C x ⊆ normalCone C xbar := by
  rcases hC with ⟨m, a, b, hC⟩
  rcases inactive_constraints_stay_inactive_near_xbar C m a b hC xbar hxbar with
    ⟨V, hV, hV_inactive⟩
  refine ⟨V, hV, ?_⟩
  intro x hxV
  by_cases hxC : x ∈ C
  · apply normal_subset_of_local_feasible_segments C xbar x hxbar hxC
    intro y hyC
    exact local_feasible_segment_for_polyhedron C m a b hC xbar hxbar V hV hV_inactive
      x hxV hxC y hyC
  · rw [Set.normalCone_of_not_mem hxC]
    exact Set.empty_subset _
