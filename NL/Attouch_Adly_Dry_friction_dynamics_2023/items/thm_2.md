## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_2.lean`

## Lean statement
```lean
theorem theorem_3_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (z dz : ℝ → H)
    (hf : ContDiff ℝ 1 f)
    (_hconvex : ConvexOn ℝ Set.univ f)
    (hsol : IsDrygradTrajectory r hr f (hf.differentiable (by norm_num)) z dz t₀)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hgradient_lip : LocallyLipschitz (gradient f))
    (hinitial : r < ‖gradient f (z t₀)‖)
    (hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (gradient f (z t)) (dz t)) t)
    (hcomp_cont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀))
    (V : H → H) (hV_lip : LocallyLipschitz V)
    (hV_zero : ∀ x, V x = 0 ↔ ‖gradient f x‖ ≤ r)
    (hvelocity : ∀ t ∈ Set.Ici t₀, dz t = V (z t))
    (hvelocity_limit : Filter.Tendsto dz Filter.atTop (nhds 0))
    (hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 →
      ∀ t ∈ Set.Ici S, z t = z S)
    (ddz : ℝ → H) (A : ℝ → H → H)
    (hdz_deriv : ∀ t ∈ Set.Ici t₀, HasDerivAt dz (ddz t) t)
    (hgrad_deriv : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => gradient f (z s)) (A t (dz t)) t)
    (hA_nonneg : ∀ t ∈ Set.Ici t₀, 0 ≤ inner ℝ (A t (dz t)) (dz t)) :
    AntitoneOn (fun t => ‖dz t‖) (Set.Ici t₀) ∧
      Filter.Tendsto (fun t : ℝ => t * ‖dz t‖) Filter.atTop (nhds 0)
```

## Statement explanation
The theorem named `theorem_3_1` takes as background a type `H` which is a real inner-product space, complete as a normed additive commutative group, so effectively a real Hilbert space. The real numbers `t₀` and `r` are given with `hr : 0 < r`, so `r` is a positive radius. There is a real-valued function `f` on `H`, and two curves `z` and `dz` from `ℝ` to `H`; conceptually `z t` is position and `dz t` is velocity. The hypothesis `hf` says `f` is continuously differentiable of order one over the reals, and `_hconvex` says `f` is convex on all of `H`. The hypothesis `hsol` states that `(z, dz)` is a drygrad trajectory with radius `r`, starting at `t₀`, for the differentiable function `f`; this is a formal project-specific predicate used to encode the dry-friction gradient dynamics. The hypothesis `hf_lower` says `f` is bounded below, and `hgradient_lip` says the gradient vector field `∇f` is locally Lipschitz. The hypothesis `hinitial` says the initial gradient magnitude exceeds `r`: `r < ‖∇f (z t₀)‖`. For every `t ≥ t₀`, `hchain` gives the derivative of the composition `s ↦ f (z s)` as `⟨∇f (z t), dz t⟩`, and `hcomp_cont` says this composition is continuous on `[t₀, ∞)`. Next, `V : H → H` is a locally Lipschitz vector field whose zero set is exactly where `‖∇f x‖ ≤ r`, as expressed by `hV_zero`. The relation `hvelocity` says that for all `t ≥ t₀`, `dz t = V (z t)`. The condition `hvelocity_limit` says `dz t → 0` as `t → ∞`. The hypothesis `hstationary` says that if at some time `S ≥ t₀` the velocity vector vanishes, so `V (z S) = 0`, then the curve remains constant forever after: `z t = z S` for all `t ≥ S`. Finally, the theorem assumes extra differentiability: `ddz : ℝ → H` is the derivative of `dz`, and `A : ℝ → H → H` gives the derivative of the gradient along the trajectory, so for each `t ≥ t₀`, the derivative of `s ↦ gradient f (z s)` at `t` is `A t (dz t)`. The nonnegativity condition `hA_nonneg` states that for every `t ≥ t₀`, `0 ≤ ⟨A t (dz t), dz t⟩`.

The conclusion is the conjunction of two asymptotic and monotonicity facts. First, the speed function `t ↦ ‖dz t‖` is antitone on `[t₀, ∞)`, meaning that for `t₀ ≤ s ≤ t` one has `‖dz t‖ ≤ ‖dz s‖`. Second, `t ↦ t * ‖dz t‖` tends to `0` as `t → ∞`.

## Lean proof
```lean
by
  have hL1 : MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ici t₀) := by
    rcases theorem_2_1 hr f z dz hf hf_lower hgradient_lip hinitial hchain
      hcomp_cont hsol V hV_lip hV_zero hvelocity hvelocity_limit hstationary with
      ⟨_, _, hL1, _⟩
    exact hL1
  have hradial : ∀ t ∈ Set.Ici t₀, dz t ≠ 0 →
      dz t + (r / ‖dz t‖) • dz t + gradient f (z t) = 0 := by
    intro t ht hv
    rcases hsol t ht with ⟨_, u, hu, hsum⟩
    rw [drygrad_subgradient_eq_radial hr hv hu] at hsum
    exact hsum
  have hacc : ∀ t ∈ interior (Set.Ici t₀), inner ℝ (ddz t) (dz t) ≤ 0 := by
    intro t ht
    have ht₀ : t ∈ Set.Ici t₀ := interior_subset ht
    by_cases hv : dz t = 0
    · simp [hv]
    · have hvnorm : ‖dz t‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hn : HasDerivAt (fun s => ‖dz s‖)
          (inner ℝ (ddz t) (dz t) / ‖dz t‖) t := by
        have hs := (hdz_deriv t ht₀).norm_sq.sqrt (pow_ne_zero 2 hvnorm)
        convert hs using 1
        all_goals simp [real_inner_comm, norm_nonneg]
        all_goals field_simp
      have hc : HasDerivAt (fun s : ℝ => r / ‖dz s‖)
          (-(r * (inner ℝ (ddz t) (dz t) / ‖dz t‖)) / ‖dz t‖ ^ 2) t := by
        convert (hasDerivAt_const t r).div hn hvnorm using 1
        all_goals ring
      have hd : HasDerivAt (fun s =>
          dz s + (r / ‖dz s‖) • dz s + gradient f (z s))
          (ddz t + ((r / ‖dz t‖) • ddz t +
            (-(r * (inner ℝ (ddz t) (dz t) / ‖dz t‖)) / ‖dz t‖ ^ 2) • dz t) +
            A t (dz t)) t :=
        ((hdz_deriv t ht₀).add (hc.smul (hdz_deriv t ht₀))).add (hgrad_deriv t ht₀)
      have hneigh : ∀ᶠ s in nhds t, dz s ≠ 0 :=
        (hdz_deriv t ht₀).continuousAt.eventually_ne hv
      have hEq : (fun _ : ℝ => (0 : H)) =ᶠ[nhds t]
          fun s => dz s + (r / ‖dz s‖) • dz s + gradient f (z s) := by
        filter_upwards [mem_interior_iff_mem_nhds.mp ht, hneigh] with s hs hsnz
        exact (hradial s hs hsnz).symm
      have hDzero : ddz t + ((r / ‖dz t‖) • ddz t +
          (-(r * (inner ℝ (ddz t) (dz t) / ‖dz t‖)) / ‖dz t‖ ^ 2) • dz t) +
          A t (dz t) = 0 := by
        exact (hd.congr_of_eventuallyEq hEq).unique (hasDerivAt_const t 0)
      have hinner := congrArg (fun w => inner ℝ w (dz t)) hDzero
      simp only [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
        inner_zero_left] at hinner
      simp at hinner
      field_simp [hvnorm] at hinner
      nlinarith [hA_nonneg t ht₀, norm_pos_iff.mpr hv]
  have hsq_anti : AntitoneOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
      (fun t ht => ((hdz_deriv t ht).continuousAt.norm).continuousWithinAt.pow 2)
    · intro t ht
      exact ((hdz_deriv t (interior_subset ht)).norm_sq).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [((hdz_deriv t (interior_subset ht)).norm_sq).deriv]
      rw [real_inner_comm]
      nlinarith [hacc t ht]
  have hspeed : AntitoneOn (fun t => ‖dz t‖) (Set.Ici t₀) := by
    intro s hs t ht hst
    nlinarith [hsq_anti hs ht hst, norm_nonneg (dz s), norm_nonneg (dz t)]
  exact ⟨hspeed, lemma_3_1 (fun t => ‖dz t‖) (fun _ _ => norm_nonneg _) hspeed hL1⟩
```

## Proof explanation
The proof first invokes the earlier theorem `theorem_2_1`, using many of the stated hypotheses, to obtain integrability of the speed function. The command `rcases theorem_2_1 hr f z dz hf hf_lower hgradient_lip hinitial hchain hcomp_cont hsol V hV_lip hV_zero hvelocity hvelocity_limit hstationary with ⟨_, _, hL1, _⟩` destructs the conclusion of that theorem and names the third component `hL1`; then `exact hL1` establishes that `‖dz t‖` is integrable on `[t₀, ∞)`. This integrability is used at the very end for the decay of `t * ‖dz t‖`.

Next, the proof establishes a pointwise radial equation. It introduces arbitrary `t` in `Ici t₀` and assumes `dz t ≠ 0`. From the drygrad trajectory assumption `hsol t ht`, it extracts the actual subgradient-like information and rewrites it using the lemma `drygrad_subgradient_eq_radial hr hv hu`. The resulting equation `hz` or `hradial` is:
`dz t + (r / ‖dz t‖) • dz t + gradient f (z t) = 0`.
This is the active dry-friction balance in the nonzero-velocity case.

The central estimate is the claim called `hacc`: for every `t` in the interior of `Set.Ici t₀`, one has `inner ℝ (ddz t) (dz t) ≤ 0`. To prove this, the proof first notes that such a `t` also lies in `Ici t₀`. It splits into cases with `by_cases hv : dz t = 0`. If the velocity is zero, then `simp [hv]` reduces the inner product to zero, so the inequality is trivial. Otherwise, `dz t ≠ 0`, so `‖dz t‖ ≠ 0`. The proof then differentiates the norm function: from `hdz_deriv`, it obtains the derivative of `s ↦ ‖dz s‖` at `t` as `inner ℝ (ddz t) (dz t) / ‖dz t‖`; this is done by taking the derivative of the squared norm and then the square root, using the derivative of `norm_sq` and `sqrt`. It then derives the derivative of the scalar function `s ↦ r / ‖dz s‖`, which is `-(r * (inner ℝ (ddz t) (dz t) / ‖dz t‖)) / ‖dz t‖ ^ 2`, by differentiating a constant divided by the norm. Combining these derivatives with `(hdz_deriv t ht₀).add` and `.smul`, plus the gradient-derivative assumption `hgrad_deriv`, the proof forms the derivative of the whole expression
`dz s + (r / ‖dz s‖) • dz s + gradient f (z s)`
at `t`.

The next steps show that this whole expression is identically zero in a neighborhood of `t`, so its derivative must be zero. The neighborhood condition is established in two parts. Since `t` is interior to `Ici t₀`, nearby points `s` are still in `Ici t₀`. Also, because `dz` is differentiable at `t` and `dz t ≠ 0`, the derivative is continuous at `t`, so `dz s ≠ 0` for all `s` sufficiently close to `t`; this is `hneigh`, obtained using `(hdz_deriv t ht₀).continuousAt.eventually_ne hv`. The proof then uses `filter_upwards` to combine these two neighborhoods and applies the radial equation `hradial` to conclude that, on a neighborhood of `t`,
`dz s + (r / ‖dz s‖) • dz s + gradient f (z s) = 0`.
Thus the function is eventually equal to the constant zero function. Since its derivative was already computed, the derivative at `t` is zero, yielding the equality called `hDzero`:
`ddz t + ((r / ‖dz t‖) • ddz t + (-(r * (inner ℝ (ddz t) (dz t) / ‖dz t‖)) / ‖dz t‖ ^ 2) • dz t) + A t (dz t) = 0`.

To get the sign condition, the proof applies the linear map `w ↦ inner ℝ w (dz t)` to both sides using `congrArg`. The simplifier expands inner products of sums and scalar multiples, using laws such as `inner_add_left`, `inner_smul_left`, and `inner_zero_left`, and replaces `inner ℝ (dz t) (dz t)` by `‖dz t‖^2`. After simplification and clearing denominators with `field_simp [hvnorm]`, the equation reduces to an equality relating `inner ℝ (ddz t) (dz t)`, `inner ℝ (A t (dz t)) (dz t)`, and terms that cancel algebraically. The command `nlinarith [hA_nonneg t ht₀, norm_pos_iff.mpr hv]` then finishes the argument: because the `A`-term is nonnegative by `hA_nonneg` and the norm is positive, it follows that `inner ℝ (ddz t) (dz t) ≤ 0`.

Using this estimate, the proof proves monotonicity of the squared speed. It invokes a standard interval monotonicity theorem, `antitoneOn_of_deriv_nonpos`, with the convex set `Ici t₀`. For that theorem one must provide continuity and differentiability of `Q t = ‖dz t‖^2` on the appropriate sets; these follow from `hdz_deriv` and its consequences. For each interior point, the derivative of `Q` is computed from the derivative of `norm_sq` as `2 * inner ℝ (ddz t) (dz t)`. Rewriting and using `hacc`, the derivative is nonpositive. Thus `Q` is antitone on `[t₀, ∞)`: for `t₀ ≤ s ≤ t`, one has `‖dz t‖^2 ≤ ‖dz s‖^2`.

The proof then derives that the unsquared norm itself is antitone. It introduces arbitrary `s`, `t` with `s ≥ t₀`, `t ≥ t₀`, and `s ≤ t`, and uses `nlinarith` with the square-monotonicity inequality and the nonnegativity of the two norms. From `‖dz t‖^2 ≤ ‖dz s‖^2` and `‖dz s‖ ≥ 0`, `‖dz t‖ ≥ 0`, the nonlinear arithmetic tactic concludes `‖dz t‖ ≤ ‖dz s‖`. This proves `hspeed : AntitoneOn (fun t => ‖dz t‖) (Set.Ici t₀)`.

Finally, the proof combines this monotonicity with the earlier integrability statement using an auxiliary lemma `lemma_3_1`. It supplies to that lemma the nonnegative function `fun t => ‖dz t‖`, the trivial proof that its values are nonnegative, the monotonicity `hspeed`, and the integrability `hL1`. The lemma gives exactly the last needed conclusion: `Filter.Tendsto (fun t : ℝ => t * ‖dz t‖) Filter.atTop (nhds 0)`. Therefore the proof finishes with `exact ⟨hspeed, lemma_3_1 ...⟩`, combining the two parts of the desired conjunction.

