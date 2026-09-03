## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/rem_8.lean`

## Lean statement
```lean
theorem restrictive_parameter_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B T : H → H) (S : Set H) (x : ℝ → H) (mu beta : ℝ)
    (hmu : 0 < mu ∧ mu < 2 * beta) (hS : S.Nonempty)
    (_hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (_hB_maximal_monotone : Maximal SetValuedOperator.IsMonotone B.toSetValuedOperator)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (hT : ∀ q, T q = ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
      (q - mu • B q))
    (hcontraction : LipschitzWith (1 / 2 : NNReal) T)
    (hclassical : ∀ t : ℝ, HasDerivAt x (T (x t) - x t) t)
    (_hdynamics : ∀ t, deriv x t = T (x t) - x t) :
    ∃ z ∈ S, Filter.Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) Filter.atTop
      (nhds (toWeakSpace ℝ H z))
```

## Statement explanation


## Lean proof
```lean
by
  obtain ⟨z, hzS⟩ := hS
  have hzsub : -B z ∈ ERealFunction.subdifferential Phi z := (hsolution z).mp hzS
  have hfix : T z = z := by
    rw [hT z]
    let gamma : ERealFunction.PosReal := ⟨mu, hmu.1⟩
    have hg : gamma • Phi ∈ ERealFunction.gammaZero H :=
      ERealFunction.smul_mem_gammaZero Phi hPhi gamma
    have hsub : (z - mu • B z) - z ∈ ERealFunction.subdifferential (gamma • Phi) z := by
      rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
      refine Set.mem_smul_set.2 ⟨-B z, hzsub, ?_⟩
      simp [gamma]
    change ERealFunction.proximityOperator (gamma • Phi) _ (z - mu • B z) = z
    exact (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential hg
      (z - mu • B z) z).mpr hsub |>.symm
  have henergy : ∀ t : ℝ,
      2 * inner ℝ (x t - z) (T (x t) - x t) ≤ -‖x t - z‖ ^ 2 := by
    intro t
    have hLip : ‖T (x t) - T z‖ ≤ (1 / 2 : ℝ) * ‖x t - z‖ := by
      simpa using hcontraction.norm_sub_le (x t) z
    have hinner : inner ℝ (x t - z) (T (x t) - T z) ≤
        (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 := by
      calc
        inner ℝ (x t - z) (T (x t) - T z) ≤
            ‖x t - z‖ * ‖T (x t) - T z‖ := real_inner_le_norm _ _
        _ ≤ ‖x t - z‖ * ((1 / 2 : ℝ) * ‖x t - z‖) :=
            mul_le_mul_of_nonneg_left hLip (norm_nonneg _)
        _ = (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 := by ring
    rw [show T (x t) - x t = (T (x t) - T z) - (x t - z) by rw [hfix]; abel]
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    nlinarith
  let p : ℝ → ℝ := fun t ↦ Real.exp t * ‖x t - z‖ ^ 2
  have hp : ∀ t : ℝ, HasDerivAt p
      (Real.exp t * ‖x t - z‖ ^ 2 +
        Real.exp t * (2 * inner ℝ (x t - z) (T (x t) - x t))) t := by
    intro t
    simpa [p] using
      (Real.hasDerivAt_exp t).mul ((hclassical t).sub_const z).norm_sq
  have hp_nonpos : ∀ t : ℝ, deriv p t ≤ 0 := by
    intro t
    rw [(hp t).deriv]
    have hscaled := mul_le_mul_of_nonneg_left (henergy t) (Real.exp_pos t).le
    nlinarith
  have hp_diff : Differentiable ℝ p := fun t ↦ (hp t).differentiableAt
  have hp_anti : Antitone p := antitone_of_deriv_nonpos hp_diff hp_nonpos
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖x t - z‖ ^ 2 ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
    intro t ht
    have hle := hp_anti ht
    have hscaled := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-t)).le
    have hexp : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      ‖x t - z‖ ^ 2 = Real.exp (-t) * (Real.exp t * ‖x t - z‖ ^ 2) := by
        rw [← mul_assoc, hexp, one_mul]
      _ ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
        simpa [p] using hscaled
  let q : ℝ → ℝ := fun t ↦ if 0 ≤ t then ‖x t - z‖ ^ 2 else 0
  have hq_nonneg : ∀ t : ℝ, 0 ≤ q t := by
    intro t
    by_cases ht : 0 ≤ t <;> simp [q, ht]
  have hq_le : ∀ t : ℝ, q t ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
    intro t
    by_cases ht : 0 ≤ t
    · simpa [q, ht] using hbound t ht
    · rw [show q t = 0 by simp [q, ht]]
      exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hexp_zero : Filter.Tendsto
      (fun t : ℝ ↦ Real.exp (-t) * ‖x 0 - z‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul tendsto_const_nhds
  have hq_zero : Filter.Tendsto q Filter.atTop (nhds 0) :=
    squeeze_zero hq_nonneg hq_le hexp_zero
  have hsq_zero : Filter.Tendsto (fun t : ℝ ↦ ‖x t - z‖ ^ 2) Filter.atTop (nhds 0) := by
    apply hq_zero.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simp [q, ht]
  have hsqrt_zero :
      Filter.Tendsto (fun t : ℝ ↦ √(‖x t - z‖ ^ 2)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq_zero
  have hnorm_zero : Filter.Tendsto (fun t : ℝ ↦ ‖x t - z‖) Filter.atTop (nhds 0) := by
    convert hsqrt_zero using 1
    funext t
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hstrong : Filter.Tendsto x Filter.atTop (nhds z) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm_zero
  exact ⟨z, hzS, by simpa using ((toWeakSpaceCLM ℝ H).continuous.tendsto z).comp hstrong⟩
```

## Proof explanation
The theorem is named `restrictive_parameter_remark`. It takes as assumptions:

- `H : Type*` is a real inner product space that is also a normed additive commutative group and complete (so a real Hilbert space). The inner product is denoted `inner ℝ` and the norm by `‖·‖`.
- `Phi : H → Set.Ioi (⊥ : EReal)` is a function on `H` whose value at each point lies in the set of extended real numbers strictly greater than bottom (`⊥`). This represents a proper extended-real-valued function with values in `(⊥, +∞]`.
- `hPhi : Phi ∈ ERealFunction.gammaZero H` says `Phi` belongs to the class `gammaZero`, meaning it is a proper, lower semicontinuous, convex function (the usual domain of Moreau–Yosida regularization).
- `B T : H → H` are two self-maps of `H`.
- `S : Set H` is a subset of `H`.
- `x : ℝ → H` is a path in `H` parametrized by real time.
- `mu beta : ℝ` are real parameters.
- `hmu : 0 < mu ∧ mu < 2 * beta` says `mu` is positive and less than twice `beta`.
- `hS : S.Nonempty` says the set `S` is nonempty.
- `_hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w)` says that `B`, viewed on the whole space, is `beta`-cocoercive: for all pairs of points, `inner (B x - B y) (x - y) ≥ beta * ‖B x - B y‖^2` in the appropriate convention.
- `_hB_maximal_monotone : Maximal SetValuedOperator.IsMonotone B.toSetValuedOperator` says the set-valued operator induced by `B` is maximal monotone.
- `hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z` characterizes `S` as the set of zeros of the sum operator `B + ∂Phi`: a point `z` lies in `S` exactly when `-B z` belongs to the subdifferential of `Phi` at `z`.
- `hT : ∀ q, T q = ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩ (q - mu • B q)` defines `T` as the forward–backward operator: at each point `q`, `T q` is the scaled proximity operator of `Phi` with parameter `mu`, applied to `q - mu B q`.
- `hcontraction : LipschitzWith (1 / 2 : NNReal) T` says `T` is Lipschitz continuous with constant `1/2`.
- `hclassical : ∀ t : ℝ, HasDerivAt x (T (x t) - x t) t` says at every time `t`, the function `x` has derivative `T (x t) - x t` in the classical sense.
- `_hdynamics : ∀ t, deriv x t = T (x t) - x t` repeats the same differential equation using the `deriv` notation.

The conclusion is:
`∃ z ∈ S, Filter.Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) Filter.atTop (nhds (toWeakSpace ℝ H z))`.
That is, there exists a point `z` belonging to the solution set `S` such that, as time `t` tends to `+∞`, the trajectory `x t` converges to `z` in the weak topology of the Hilbert space `H`.

===PROOF_EXPLANATION===
The proof starts by extracting a point from the nonempty set `S` using `obtain ⟨z, hzS⟩ := hS`. From `hsolution`, it obtains `hzsub : -B z ∈ ERealFunction.subdifferential Phi z`, which records that `z` is a critical point for `Phi + B`.

Next it proves `hfix : T z = z`, i.e. `z` is a fixed point of `T`. The proof writes `T z` using `hT`, then introduces the positive real parameter `gamma = ⟨mu, hmu.1⟩`. It uses `ERealFunction.smul_mem_gammaZero` to show that the scalar multiple `gamma • Phi` is again in the appropriate function class. It then proves that the vector `(z - mu • B z) - z` belongs to the subdifferential of `gamma • Phi` at `z`. This is done by rewriting with `ERealFunction.subdifferential_posReal_smul_eq_smul`, using `Set.mem_smul_set`, the existing subdifferential membership `hzsub`, and simplification with `simp`. The proof then changes the goal into the equality of the proximity operator of `gamma • Phi` at `z - mu • B z` with `z`. This follows from `ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential`, which characterizes the proximity operator: the prox point equals `z` iff `argument - z` lies in the scaled subdifferential. The result is reversed with `.symm` to match the direction `T z = z`.

The main energy estimate is the lemma `henergy`, which states for every time `t`:
`2 * inner ℝ (x t - z) (T (x t) - x t) ≤ -‖x t - z‖ ^ 2`.
To prove it, `intro t` fixes a time. The first step derives a Lipschitz bound `hLip`: by applying the global `1/2`-Lipschitz estimate to the pair `(x t, z)`, one obtains `‖T (x t) - T z‖ ≤ (1/2) * ‖x t - z‖`. Then an inner-product Cauchy–Schwarz estimate `hinner` is shown by a `calc` block:
`inner (x t - z) (T (x t) - T z) ≤ ‖x t - z‖ * ‖T (x t) - T z‖`, which is `real_inner_le_norm`; this is bounded by `‖x t - z‖ * ((1/2) * ‖x t - z‖)` using the Lipschitz bound and nonnegativity of the norm; finally this equals `(1/2) * ‖x t - z‖^2` by `ring`.
Because `z` is a fixed point, `hfix` is used to rewrite `T (x t) - x t` as `(T (x t) - T z) - (x t - z)`. The proof rewrites the inner product of a difference against two terms using `inner_sub_right`, rewrites `inner (x t - z) (x t - z)` as `‖x t - z‖^2` via `real_inner_self_eq_norm_sq`, and then uses `nlinarith` to convert the quadratic estimate into the desired energy inequality.

Next the proof introduces a weighted energy function `p : ℝ → ℝ` defined by `p t = exp t * ‖x t - z‖^2`. It proves `hp`, the derivative of `p` at every `t`: using the product rule and the chain rule for the norm-squared expression, it obtains
`p' t = exp t * ‖x t - z‖^2 + exp t * (2 * inner (x t - z) (T (x t) - x t))`.
The proof uses `Real.hasDerivAt_exp`, multiplies by the derivative of `(x t - z).norm_sq`, and simplifies with `simp`. The key Lyapunov inequality `hp_nonpos` says `deriv p t ≤ 0` for all `t`: from `henergy`, the bracketed expression is at most `-‖x t - z‖^2`, so after multiplying by the positive exponential factor and using `nlinarith`, the derivative is nonpositive. From `hp_diff`, which records differentiability of `p`, and `hp_nonpos`, the proof applies `antitone_of_deriv_nonpos` to obtain `hp_anti : Antitone p`, i.e. `p` is nonincreasing on the real line.

The nonincreasing property gives the explicit bound `hbound`: for all `t ≥ 0`,
`‖x t - z‖^2 ≤ exp (-t) * ‖x 0 - z‖^2`.
The argument multiplies the antitone inequality `p 0 ≤ p t` by `exp (-t)`, uses `Real.exp_add` to show `exp (-t) * exp t = 1`, and rewrites `p t` and `p 0`. This gives exponential decay of the squared distance.

To pass from decay along `t ≥ 0` to a full limit, the proof defines the function `q t = if 0 ≤ t then ‖x t - z‖^2 else 0`. Two auxiliary properties are proved. `hq_nonneg` says `q` is nonnegative, checked by splitting cases on whether `0 ≤ t`. `hq_le` says `q t ≤ exp (-t) * ‖x 0 - z‖^2` for all `t`: for `t ≥ 0` this is `hbound`; for `t < 0`, `q t = 0` and the right-hand side is nonnegative because the exponential is positive and the square is nonnegative. The bound `hexp_zero` establishes that the right-hand envelope tends to `0` as `t → +∞`, using the known limit `Real.tendsto_exp_neg_atTop_nhds_zero` multiplied by the constant `‖x 0 - z‖^2`. Then `squeeze_zero` applies to conclude `hq_zero`, i.e. `q t → 0`.

From convergence of the truncated function `q`, the proof obtains convergence of the full squared norm. `hsq_zero` says `‖x t - z‖^2 → 0`: it uses `hq_zero.congr'` and filters to large times where `t ≥ 0`, rewriting `q t` back to the square. Since square root is continuous at `0`, `hsqrt_zero` gives `√(‖x t - z‖^2) → 0`. Using the identity `√(a^2) = a` for `a ≥ 0`, the proof converts this to `hnorm_zero`, the convergence to zero of `‖x t - z‖`. This in turn yields `hstrong`, the strong convergence of `x t` to `z`, via `tendsto_iff_norm_sub_tendsto_zero`.

Finally, the proof combines the results. It returns the witness `z`, the membership `hzS`, and the weak convergence. Since the inclusion map from `H` into its weak topology, represented by `toWeakSpaceCLM ℝ H`, is continuous, composing the strongly convergent trajectory `x` with this continuous map yields convergence in the weak topology. The command `simpa` handles the details of this composition, proving
`Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))`. This is exactly the desired conclusion.

