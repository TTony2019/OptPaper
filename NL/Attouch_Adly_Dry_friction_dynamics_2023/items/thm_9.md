## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_9.lean`

## Lean statement
```lean
theorem theorem_A_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {t₀ r : ℝ}
    (hr : 0 < r) (f : H → ℝ) (z dz : ℝ → H) (hf : ContDiff ℝ 1 f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hgradient_lip : LocallyLipschitz (gradient f))
    (hinitial : r < ‖gradient f (z t₀)‖)
    (hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (gradient f (z t)) (dz t)) t)
    (hcomp_cont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀))
    (hsolution : IsDrygradTrajectory r hr f (hf.differentiable (by norm_num)) z dz t₀)
    (V : H → H) (hV_lip : LocallyLipschitz V)
    (hV_zero : ∀ x, V x = 0 ↔ ‖gradient f x‖ ≤ r)
    (hvelocity : ∀ t ∈ Set.Ici t₀, dz t = V (z t))
    (hvelocity_limit : Filter.Tendsto dz Filter.atTop (nhds 0))
    (hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 →
      ∀ t ∈ Set.Ici S, z t = z S) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀)
```

## Statement explanation
The theorem is stated in a real Hilbert space setting. The type `H` is arbitrary but is assumed to be a normed additive commutative group, a real inner product space over `ℝ`, and complete, so it is a real Hilbert space. The parameters `t₀` and `r` are real numbers, with the explicit hypothesis `hr : 0 < r`. The symbols `f`, `z`, and `dz` denote functions: `f : H → ℝ` is a real-valued function on the space, while `z : ℝ → H` and `dz : ℝ → H` are curves in `H`, generally interpreted as a position and a velocity.

The hypotheses are as follows:
- `hf : ContDiff ℝ 1 f` means that `f` is continuously differentiable of order one.
- `hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x` says that `f` is bounded below.
- `hgradient_lip : LocallyLipschitz (gradient f)` says that the gradient vector field of `f` is locally Lipschitz.
- `hinitial : r < ‖gradient f (z t₀)‖` says that at the initial time `t₀`, the norm of the gradient of `f` at `z t₀` is strictly larger than `r`.
- `hchain : ∀ t ∈ Set.Ici t₀, HasDerivAt (fun s => f (z s)) (inner ℝ (gradient f (z t)) (dz t)) t` means that for every time `t ≥ t₀`, the function `s ↦ f(z s)` is differentiable at `t`, and its derivative equals the real inner product of `gradient f (z t)` with `dz t`.
- `hcomp_cont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀)` says that the composition `f ∘ z` is continuous on the half-line `[t₀, +∞)`.
- `hsolution : IsDrygradTrajectory r hr f (hf.differentiable (by norm_num)) z dz t₀` asserts that the pair `(z, dz)` is a dry-friction gradient trajectory for `f`, with threshold `r > 0`, starting at `t₀`, using the differentiability of `f` supplied by `hf`.
- Then `V : H → H` is another map, with `hV_lip : LocallyLipschitz V` saying that `V` is locally Lipschitz.
- `hV_zero : ∀ x, V x = 0 ↔ ‖gradient f x‖ ≤ r` says that the zeros of `V` are exactly the points where the gradient norm is no more than `r`.
- `hvelocity : ∀ t ∈ Set.Ici t₀, dz t = V (z t)` says that the velocity curve `dz` equals `V` evaluated along `z`.
- `hvelocity_limit : Filter.Tendsto dz Filter.atTop (nhds 0)` says that `dz t` tends to `0` as `t → +∞`.
- `hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 → ∀ t ∈ Set.Ici S, z t = z S` says that if at some time `S ≥ t₀` the vector `V(z S)` is zero, then the curve `z` remains constantly equal to `z S` for all later times `t ≥ S`.

The conclusion is `AntitoneOn (fun t => f (z t)) (Set.Ici t₀)`. This means that the composed function `t ↦ f(z t)` is nonincreasing on the entire half-line `[t₀, +∞)`: for any times `a, b ≥ t₀` with `a ≤ b`, one has `f(z b) ≤ f(z a)`.

## Lean proof
```lean
(theorem_2_1 hr f z dz hf hf_lower hgradient_lip hinitial hchain hcomp_cont hsolution V
    hV_lip hV_zero hvelocity hvelocity_limit hstationary).1
```

## Proof explanation
The proof consists of a single direct appeal to a previously established theorem named `theorem_2_1`. The proof term is:

`(theorem_2_1 hr f z dz hf hf_lower hgradient_lip hinitial hchain hcomp_cont hsolution V hV_lip hV_zero hvelocity hvelocity_limit hstationary).1`

In words, all of the hypotheses of the present theorem are passed, in order, to `theorem_2_1`. Thus `theorem_2_1` is applied to the same objects:
- the positive threshold `hr`,
- the function `f`,
- the curves `z` and `dz`,
- the smoothness hypothesis `hf`,
- the lower-bound hypothesis `hf_lower`,
- the local-Lipschitz gradient hypothesis `hgradient_lip`,
- the initial gradient condition `hinitial`,
- the chain-rule hypothesis `hchain`,
- the continuity hypothesis `hcomp_cont`,
- the dry-gradient trajectory hypothesis `hsolution`,
- the map `V`,
- the local-Lipschitz condition `hV_lip`,
- the zero characterisation `hV_zero`,
- the velocity relation `hvelocity`,
- the vanishing-at-infinity condition `hvelocity_limit`,
- and the stationarity condition `hstationary`.

The result of this application is some object whose first component, selected by `.1`, has exactly the type of the desired conclusion `AntitoneOn (fun t => f (z t)) (Set.Ici t₀)`. Therefore the current theorem is an immediate consequence of `theorem_2_1`, with no additional reasoning, case analysis, or algebraic manipulation. No Lean tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` appear in the proof; the only operation is the use of projection `.1` on the result supplied by `theorem_2_1` to extract its first assertion.

