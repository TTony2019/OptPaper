## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_9.lean`

## Lean statement
```lean
theorem derivative_inner_nonnegative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (x v : ℝ → H)
    (hsubgradient : ∀ t, 0 ≤ t →
      v t ∈ ERealFunction.subdifferential Phi (x t))
    (_hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (_hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), HasDerivAt v (deriv v t) t) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi 0), 0 ≤ inner ℝ (deriv x t) (deriv v t)
```

## Statement explanation
The statement is an implication. For an arbitrary type `H` equipped with a normed additive commutative group structure and an inner product space structure over `ℝ`, the theorem assumes:

- `Phi` is a function from `H` to the subtype `Set.Ioi (⊥ : EReal)`, i.e. to extended-real numbers strictly greater than the bottom element `⊥` of `EReal`.
- `hPhi : Phi ∈ ERealFunction.gammaZero H` is an assumption that `Phi` belongs to the library-defined set `gammaZero H`.
- `x` and `v` are functions `ℝ → H`, so they are curves in the real inner product space `H`.
- `hsubgradient` says that for every real `t ≥ 0`, the vector `v t` belongs to the subdifferential of `Phi` at `x t`: `v t ∈ ERealFunction.subdifferential Phi (x t)`.
- The assumptions `_hx_ac` and `_hv_ac` state that for every `b > 0`, `x` and `v` are absolutely continuous on the interval `[0, b]`.
- `hx_deriv` states that, for almost every `t` with respect to the default volume measure restricted to `Set.Ioi 0 = {t | 0 < t}`, the curve `x` has derivative at `t` equal to `deriv x t`: `HasDerivAt x (deriv x t) t`.
- Similarly, `hv_deriv` states that for almost every such `t`, `v` has derivative `deriv v t` at `t`.

The conclusion is also an almost-everywhere statement with respect to the same restricted measure: for almost every `t > 0`, the real inner product of the two derivatives is nonnegative:
`0 ≤ inner ℝ (deriv x t) (deriv v t)`.

## Lean proof
```lean
by
  have hmono : SetValuedOperator.IsMonotone
      (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
    ERealFunction.isMonotone_subdifferential
      (fun y : H => (Phi y : EReal))
      (ERealFunction.isProper_of_mem_gammaZero hPhi)
  filter_upwards [hx_deriv, hv_deriv,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t hxt hvt ht
  exact inner_deriv_nonneg_of_monotone hmono hsubgradient ht hxt hvt
```

## Proof explanation
The proof starts with a `have` step that constructs a monotonicity statement. Using the assumption `hPhi`, the proof first applies a library theorem `ERealFunction.isProper_of_mem_gammaZero` to conclude that the extended-real-valued function `y ↦ (Phi y : EReal)` is proper. Then it applies `ERealFunction.isMonotone_subdifferential` to conclude that the set-valued subdifferential operator of this proper function is monotone. This local result is named `hmono`.

Next, the goal is an almost-everywhere statement with respect to the measure `volume.restrict (Set.Ioi 0)`. The command `filter_upwards` combines the three almost-everywhere hypotheses:

- `hx_deriv`,
- `hv_deriv`,
- `MeasureTheory.ae_restrict_mem measurableSet_Ioi`, which says that almost every point under the restriction of the measure to `Set.Ioi 0` belongs to `Set.Ioi 0`.

Using the `with` clause, the proof obtains a generic point `t` and the corresponding pointwise hypotheses:
- `hxt : HasDerivAt x (deriv x t) t`,
- `hvt : HasDerivAt v (deriv v t) t`,
- `ht : t ∈ Set.Ioi 0`, equivalently `0 < t`.

At this stage it suffices to prove the pointwise inequality `0 ≤ inner ℝ (deriv x t) (deriv v t)`.

The proof finishes with `exact inner_deriv_nonneg_of_monotone hmono hsubgradient ht hxt hvt`. This applies an existing lemma which, from the monotonicity of the subdifferential operator, the subgradient inclusion for `v` along `x`, the positivity `0 < t`, and the differentiability of `x` and `v` at `t`, derives exactly the desired nonnegativity of the inner product of the derivatives. Since all its hypotheses are available, the goal is closed. The proof does not use `rw`, `simp`, or `linarith`; it relies on the earlier library lemma and on `filter_upwards` to handle the almost-everywhere quantification.

