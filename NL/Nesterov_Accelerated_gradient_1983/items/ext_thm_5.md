## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_thm_5.lean`

## Lean statement
```lean
theorem backtracking_predecessor_reference {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) :
    ∃ S : EarlierOneDimensionalHalvingSearch,
      StartsKthSearchFromPreviousStep f M S
```

## Statement explanation
The theorem is stated for a type $E$ equipped with a normed additive commutative group structure, a real inner product space structure, and completeness; thus $E$ is a complete real inner product space, i.e. a real Hilbert space. The function $f : E \to \mathbb{R}$ is a real-valued objective function, and $M$ is an accelerated gradient method associated with $f$. The theorem asserts that there exists an object $S$ of type `EarlierOneDimensionalHalvingSearch` such that the predicate `StartsKthSearchFromPreviousStep f M S` holds.

The method $M$ supplies, in the proof, a sequence of steps $M.\text{step} : \mathbb{N} \to E$, an initial step $M.\text{initialStep} \in E$, and a search index $M.\text{searchIndex} : \mathbb{N} \to \mathbb{N}$. The predicate `StartsKthSearchFromPreviousStep f M S` is, after unfolding for the constructed $S$, the statement that for every natural number $k$,

$$
M.\text{step}(k)
=2^{-M.\text{searchIndex}(k)}
\cdot
\begin{cases}
M.\text{initialStep}, & k=0,\\
M.\text{step}(k-1), & k\neq 0.
\end{cases}
$$

Here the exponent $M.\text{searchIndex}(k)$ is coerced to an integer, and the multiplication is scalar multiplication of the vector $E$ by the real number $2^{-M.\text{searchIndex}(k)}$. The halving search $S$ constructed in the proof is the rule that assigns to a vector $\alpha \in E$ and a natural number $i$ the scaled vector

$$
(\alpha,i) \mapsto 2^{-i}\alpha.
$$

Thus the theorem says that the predecessor-reference relation needed for the backtracking search can be represented by a dyadic halving search: the $k$-th step is obtained from the previous step, or from the initial step when $k=0$, by multiplying by the factor $2^{-M.\text{searchIndex}(k)}$.

## Lean proof
```lean
by
  refine ⟨⟨fun α i => (2 : ℝ) ^ (-(i : ℤ)) * α, ?_⟩, ?_⟩
  · intro α i
    rfl
  · intro k
    change M.step k =
      (2 : ℝ) ^ (-(M.searchIndex k : ℤ)) *
        (if k = 0 then M.initialStep else M.step (k - 1))
    exact M.step_eq_dyadic_previous k
```

## Proof explanation
The proof is constructive. The tactic `refine ⟨⟨fun α i => (2 : ℝ) ^ (-(i : ℤ)) * α, ?_⟩, ?_⟩` applies the existential introduction rule. The outer pair supplies the witness $S$ and the proof of `StartsKthSearchFromPreviousStep f M S`. The inner pair constructs $S$: its factor function is defined by

$$
(\alpha,i) \mapsto 2^{-i}\alpha,
$$

where $\alpha \in E$ and $i \in \mathbb{N}$. The first subgoal is the structural condition required of an `EarlierOneDimensionalHalvingSearch`, namely that this factor function is exactly the dyadic halving rule. The command `intro α i` introduces arbitrary $\alpha \in E$ and $i \in \mathbb{N}$, and `rfl` closes the goal by reflexivity because the function was introduced literally as $2^{-i}\alpha$. No external mathematical fact is needed for this step; it simply verifies that the chosen search object has the intended definition.

The second subgoal is the proof of `StartsKthSearchFromPreviousStep f M S`. The command `intro k` introduces an arbitrary natural number $k$, since the predicate is a universal statement over $k$. The `change` command then replaces the goal by the definitionally equal equality

$$
M.\text{step}(k)
=2^{-M.\text{searchIndex}(k)}
\cdot
\begin{cases}
M.\text{initialStep}, & k=0,\\
M.\text{step}(k-1), & k\neq 0.
\end{cases}
$$

This reshaping is valid because the predicate, when unfolded using the chosen search object $S$, asks precisely that the $k$-th step equal the previous step—or the initial step when $k=0$—scaled by the dyadic factor $2^{-M.\text{searchIndex}(k)}$. In the branch $k\neq 0$, Lean’s natural-number subtraction $k-1$ is the usual predecessor, since $k$ is nonzero.

Finally, `exact M.step_eq_dyadic_previous k` closes the goal. The expression `M.step_eq_dyadic_previous` is the recurrence property carried by the accelerated gradient method $M$. Applied to $k$, it states exactly the displayed equality: the $k$-th step is the previous step, or the initial step at $k=0$, multiplied by $2^{-M.\text{searchIndex}(k)}$. This matches the goal precisely, so the proof is complete. Since $k$ was arbitrary, the universal condition `StartsKthSearchFromPreviousStep f M S` holds, and therefore the existential witness $S$ has been successfully constructed.

