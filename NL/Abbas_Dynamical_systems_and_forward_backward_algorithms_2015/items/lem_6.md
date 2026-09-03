## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_6.lean`

## Lean statement
```lean
theorem opial_trajectory_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : Set H) (x : ℝ → H) (hS : S.Nonempty)
    (hdist : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds l))
    (hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop (nhds (toWeakSpace ℝ H z))) → z ∈ S) :
    ∃ z ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The theorem is named `opial_trajectory_lemma` and is stated in a context where `H` is an arbitrary type equipped with the structure of a real normed inner-product space: `H` has a normed additive commutative group structure, an inner product over `ℝ`, and is complete, so it is a real Hilbert space. The additional objects are a set `S : Set H` and a trajectory `x : ℝ → H`, i.e. a function assigning to each real time `t` a point `x t` in `H`. There are three hypotheses. First, `hS : S.Nonempty` says that `S` contains at least one point. Second, `hdist` says that for every point `z ∈ S`, the distance from the moving point `x t` to the fixed point `z` has a limit as `t → ∞`: for each such `z`, there exists a real number `l` such that `‖x t - z‖ → l` in the filter sense as `t → ∞`. Third, `hcluster` says that every weak sequential cluster point at infinity of the trajectory belongs to `S`: if for some point `z` there is a sequence `u : ℕ → ℝ` tending to `∞` such that the weak-topology images `toWeakSpace ℝ H (x (u n))` converge to `toWeakSpace ℝ H z`, then `z ∈ S`. The notation `Tendsto` is convergence with respect to the filters `atTop` and `nhds`; `atTop` expresses the parameter tending to infinity, and `nhds` expresses the usual neighborhood filter in the target space. The conclusion is that there exists a point `z ∈ S` such that the whole trajectory converges weakly to `z` as the real parameter `t` tends to infinity, i.e. `toWeakSpace ℝ H (x t) → toWeakSpace ℝ H z` in the weak topology.

## Lean proof
```lean
by
  have hcluster' : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n ↦ f (x (u n))) atTop (nhds (f z))) → z ∈ S := by
    rintro z ⟨u, hu, hfun⟩
    exact hcluster z ⟨u, hu, by
      rw [weakConvergence_iff_forall_tendsto_inner_right]
      intro v
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        hfun (InnerProductSpace.toDual ℝ H v)⟩
  obtain ⟨z, hz, hf⟩ := opial_lemma_continuous_weak x S hS hdist hcluster'
  exact ⟨z, hz, by
    rw [weakConvergence_iff_forall_tendsto_inner_right]
    intro u
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hf (InnerProductSpace.toDual ℝ H u)⟩
```

## Proof explanation
The proof first restates the weak-cluster hypothesis in terms of continuous linear functionals rather than the weak topology. It creates a new statement `hcluster'`: for any `z`, if there exists a sequence `u` tending to infinity and if, for every continuous linear functional `f : H →L[ℝ] ℝ`, the real numbers `f (x (u n))` converge to `f z`, then `z ∈ S`. To prove `hcluster'`, the proof assumes such a `z`, `u`, and functional-convergence property, and then applies the original hypothesis `hcluster`. The command `rintro z ⟨u, hu, hfun⟩` unpacks the existential sequence and its two properties. The goal is to show that `x (u n)` converges weakly to `z`. This is done by rewriting with the lemma `weakConvergence_iff_forall_tendsto_inner_right`, which states that in a real Hilbert space, weak convergence is equivalent to convergence of all inner products with a fixed vector on the right. After this rewrite, `intro v` introduces an arbitrary vector `v`. Then the functional convergence assumption `hfun` is used with the continuous linear functional `InnerProductSpace.toDual ℝ H v`, which represents the inner product against `v`. The command `simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm]` simplifies the resulting expression, converting the continuous-linear-functional notation to inner products and using commutativity of the real inner product. Thus the required inner-product limit follows, and the original weak-cluster hypothesis applies.

The proof then invokes an existing lemma `opial_lemma_continuous_weak` with the same trajectory `x`, set `S`, and hypotheses `hS`, `hdist`, and the newly constructed `hcluster'`. This lemma supplies a witness `z` together with proofs that `z ∈ S` and that, for every continuous linear functional `f`, one has `f (x t) → f z` as `t → ∞`; this convergence is assigned to `hf`.

Finally, the proof proves the original conclusion for this witness. The final goal is rewritten using `weakConvergence_iff_forall_tendsto_inner_right`, turning the desired weak convergence into inner-product convergence against an arbitrary vector `u`. Then `intro u` fixes such a vector. The proof applies `hf` to the continuous linear functional `InnerProductSpace.toDual ℝ H u`, and uses `simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm]` to rewrite the applied functional as the appropriate inner product with a commuted real inner product. This gives exactly the inner-product limit needed for weak convergence. The command `exact ⟨z, hz, ...⟩` assembles the witness `z`, the membership proof `hz`, and the convergence proof into the existential conclusion of the theorem. No `linarith` or numerical inequality reasoning is used; the argument is built from the earlier lemma and from rewriting weak convergence into inner-product convergence.

