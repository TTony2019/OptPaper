## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_1.lean`

## Lean statement
```lean
theorem cocoercive_lipschitz {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (beta : ℝ) (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x)) :
    LipschitzWith ⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩ B
```

## Statement explanation
The declaration is a theorem. It fixes a type `H` equipped with the typeclass assumptions `[NormedAddCommGroup H]` and `[InnerProductSpace ℝ H]`, so `H` is a real vector space with an inner product, norm, and additive group structure. The theorem also takes three explicit arguments:

- `B : H → H`, a self-map on `H`;
- `beta : ℝ`, a real number intended as a cocoercivity constant;
- `hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x)`, an assumption that `B` is `beta`-cocoercive on the whole space `H`. The expression `Set.univ` is the universal subset of `H`, and the elements `x : Set.univ` are coerced to elements of `H` before applying `B`, so this is the full map `B : H → H`.

The conclusion is `LipschitzWith ⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩ B`. Here `⟨1 / beta, ...⟩` constructs a nonnegative real number, i.e. an element of `ℝ≥0`, whose underlying value is `1 / beta` and whose second component is a proof that `1 / beta ≥ 0`. That nonnegativity proof is obtained from `hB.pos`, which expresses that the cocoercivity constant `beta` is positive. Therefore the conclusion says that `B` is Lipschitz continuous with Lipschitz constant `1 / beta`.

## Lean proof
```lean
by
  have heq : Real.toNNReal (1 / beta) =
      ⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩ :=
    NNReal.eq (Real.coe_toNNReal (1 / beta) (one_div_nonneg.mpr hB.pos.le))
  rw [← heq]
  exact cocoercive_implies_lipschitz B beta hB
```

## Proof explanation
The proof has no `intro` commands, because the hypotheses are already in the local context and the goal is not a universal implication that needs to be unpacked.

The first step creates a local equality named `heq`. It states that `Real.toNNReal (1 / beta)` equals the nonnegative-real-number expression `⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩`. In Lean, a real number can be converted to a nonnegative real via `Real.toNNReal`. When the input real number is already nonnegative, this conversion does not change its value. Here `1 / beta` is nonnegative because `hB.pos` says `beta > 0`, so `one_div_pos.mpr hB.pos` proves `1 / beta > 0`, and `le_of_lt` turns that strict inequality into a non-strict inequality `0 ≤ 1 / beta`. The equality `heq` is proved by `NNReal.eq`, which reduces equality of two nonnegative real numbers to equality of their underlying real values, together with `Real.coe_toNNReal`, which states that coercing `Real.toNNReal (1 / beta)` back to a real number gives `1 / beta` under the nonnegativity hypothesis.

The second step uses `rw [← heq]`. This rewrites the goal from right to left using `heq`: it replaces the expression `⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩` appearing in the stated Lipschitz constant by the equivalent expression `Real.toNNReal (1 / beta)`. After this rewriting, the goal is `LipschitzWith (Real.toNNReal (1 / beta)) B`.

The final step is `exact cocoercive_implies_lipschitz B beta hB`. This supplies an existing theorem that says, from the same cocoercivity hypothesis `hB`, the map `B` is Lipschitz with constant `Real.toNNReal (1 / beta)`. That term exactly matches the rewritten goal, so `exact` closes the proof.

