## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/thm_1.lean`

## Lean statement
```lean
theorem hpe_main_theorem {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) (A : HPEIterates H T) :
    (∃ xStar, (0 : H) ∈ T xStar ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (A.x k)) atTop
        (nhds (toWeakSpace ℝ H xStar))) ∨
    (T.zeros = ∅ ∧ ¬ Bornology.IsBounded (Set.range A.x))
```

## Statement explanation
The declaration `hpe_main_theorem` concerns a complete real inner product space $H$, hence a real Hilbert space, and a set-valued operator $T:H\to 2^H$. It assumes that $T$ is maximal monotone and that $A$ is an `HPEIterates H T` object, whose sequence component is written $A.x=(A.x_k)_{k\in\mathbb N}$. The zero set of $T$ is the set of points $x$ for which $0$ belongs to the value $T(x)$:

```math
T.\mathrm{zeros}=\{x\in H:\ 0\in T(x)\}.
```

The conclusion is the following dichotomy:

$$
\left(\exists x^\star\in H,\ 0\in T(x^\star)\ \text{and}\
\iota(A.x_k)\to \iota(x^\star)\ \text{weakly as }k\to\infty\right)
$$

or

```math
\left(T.\mathrm{zeros}=\emptyset\ \text{and}\
\neg\mathrm{Bornology.IsBounded}\bigl(\{A.x_k:k\in\mathbb N\}\bigr)\right).
```

Here $\iota=\mathrm{toWeakSpace}_{\mathbb R,H}$ is the map to the weak space, so the convergence in the first alternative is convergence in the weak topology. Thus the theorem says that for a maximal monotone operator $T$ and an associated HPE iteration $A$, either there is a zero of $T$ and the HPE iterates converge weakly to some zero of $T$, or $T$ has no zero at all and the range of the HPE iterates is unbounded.

## Lean proof
```lean
by
  classical
  by_cases hzeros : T.zeros = ∅
  · exact Or.inr ⟨hzeros, hpe_unbounded_of_no_zero hT A hzeros⟩
  · rcases Set.nonempty_iff_ne_empty.mpr hzeros with ⟨xStar, hxStar⟩
    have hzero : ∃ xStar, (0 : H) ∈ T xStar :=
      ⟨xStar, SetValuedOperator.mem_zeros_iff T xStar |>.mp hxStar⟩
    exact Or.inl (hpe_weakly_converges_to_zero hT A hzero)
```

## Proof explanation
The proof is a case split on whether the zero set of $T$ is empty. It begins with `classical`, which makes classical logic and the needed decidability instances available. Then `by_cases hzeros : T.zeros = ∅` separates the proof into the case $T.\mathrm{zeros}=\emptyset$, where `hzeros` is the equality, and the case $\neg(T.\mathrm{zeros}=\emptyset)$, i.e. $T.\mathrm{zeros}\neq\emptyset$, where `hzeros` is the negation.

In the first case, `hzeros` says exactly that $T.\mathrm{zeros}=\emptyset$. The proof applies `hpe_unbounded_of_no_zero hT A hzeros`. The cited theorem states that if $T$ is maximal monotone, $A$ is an HPE iterates object for $T$, and $T.\mathrm{zeros}=\emptyset$, then the range of the iterates is not bounded:

$$
\neg\mathrm{Bornology.IsBounded}\bigl(\mathrm{Set.range}A.x\bigr).
$$

This supplies precisely the unboundedness part of the right disjunct. The proof then uses `exact Or.inr ⟨hzeros, hpe_unbounded_of_no_zero hT A hzeros⟩`. The constructor `Or.inr` chooses the right side of the disjunction, and the pair contains the two required facts: $T.\mathrm{zeros}=\emptyset$ and the non-boundedness of $\mathrm{Set.range}A.x$. This closes the first branch.

In the second case, `hzeros` says $\neg(T.\mathrm{zeros}=\emptyset)$, equivalently $T.\mathrm{zeros}\neq\emptyset$. The proof applies `Set.nonempty_iff_ne_empty.mpr hzeros`. The set lemma used here has the content that a set $s$ is nonempty if and only if $s\neq\emptyset$. Taking the forward direction from the negated equality gives that $T.\mathrm{zeros}$ is nonempty. The tactic `rcases ... with ⟨xStar, hxStar⟩` then extracts a witness $x^\star$ and a proof $hxStar$ that $x^\star\in T.\mathrm{zeros}$.

Next the proof uses `SetValuedOperator.mem_zeros_iff T xStar`. This lemma says that membership in the zero set is equivalent to zero belonging to the corresponding value:

$$
x\in T.\mathrm{zeros}\ \Longleftrightarrow\ (0:H)\in T(x).
$$

Applying its forward implication `.mp` to $hxStar:x^\star\in T.\mathrm{zeros}$ gives $(0:H)\in T(x^\star)$. The `have` declaration then packages this as

$$
\texttt{hzero}:\ \exists x^\star,\ (0:H)\in T(x^\star).
$$

Finally, the proof invokes `hpe_weakly_converges_to_zero hT A hzero`. The cited theorem states that, under the same maximal-monotonicity and HPE-iterates hypotheses, if there exists $x^\star$ with $0\in T(x^\star)$, then there exists $x^\star$ with $0\in T(x^\star)$ and

$$
\mathrm{toWeakSpace}_{\mathbb R,H}(A.x_k)
\longrightarrow
\mathrm{toWeakSpace}_{\mathbb R,H}(x^\star)
$$

in the weak topology as $k\to\infty$. This is exactly the left disjunct of the target conclusion. The constructor `Or.inl` selects that left side, so `exact Or.inl (hpe_weakly_converges_to_zero hT A hzero)` closes the second branch.

The proof does not use `intro`, `rw`, `simp`, or `linarith`; its essential logical moves are the classical case split, extraction of a nonempty-set witness, conversion between $x^\star\in T.\mathrm{zeros}$ and $0\in T(x^\star)$, and the final use of `Or.inr` or `Or.inl` to assemble the required disjunction.

