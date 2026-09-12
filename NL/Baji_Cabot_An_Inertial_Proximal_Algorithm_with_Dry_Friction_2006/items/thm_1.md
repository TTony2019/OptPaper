## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/thm_1.lean`

## Lean statement
```lean
theorem thm_3_1_iii [FiniteDimensional ℝ H] (A B : SetValuedOperator H H) (f : H → EReal)
    (lam : ℕ → ℝ) (x : ℕ → H)
    (h : Theorem31Assumptions A B f lam x)
    (xInf : H) (hxInf : Tendsto x atTop (𝓝 xInf)) :
    ((∃ N, ∀ n ≥ N, x n = x N) ∨
      normalizedIncrementLimitPoints x ⊆ normalConeSet (A (0 : H)) (-(B xInf))) ∧
    ((-(B xInf)) ⊆ interior (A (0 : H)) → ∃ N, ∀ n ≥ N, x n = x N)
```

## Statement explanation
The declaration is a theorem about a sequence of iterates in a finite-dimensional real space $H$. The explicit typeclass assumption is `FiniteDimensional ℝ H`, meaning $H$ is finite-dimensional over $\mathbb{R}$. The other data are two set-valued operators $A,B: H \rightrightarrows H$, an extended-real-valued function $f: H \to \overline{\mathbb{R}}$, a real parameter sequence $\lambda: \mathbb{N} \to \mathbb{R}$, and a sequence $x: \mathbb{N} \to H$. The hypothesis `h : Theorem31Assumptions A B f lam x` is a bundled package of the standing assumptions of Theorem 3.1 for these data; its internal fields are not expanded in the supplied source, so it is used as a black-box hypothesis. A point $x_\infty \in H$ is fixed, and the hypothesis `hxInf` says that $x_n \to x_\infty$ as $n \to \infty$.

The conclusion is a conjunction of two statements. Let us abbreviate

$$
P := \exists N,\ \forall n \ge N,\ x_n = x_N ,
$$

so $P$ says that the sequence $x$ is eventually constant, i.e. the algorithm terminates finitely. Let

```math
Q := \mathrm{normalizedIncrementLimitPoints}(x)
\subseteq
\mathrm{normalConeSet}\bigl(A(0),\, -B(x_\infty)\bigr),
```

and let

$$
R := -B(x_\infty) \subseteq \mathrm{interior}(A(0)).
$$

Then the theorem states

$$
(P \lor Q) \land (R \to P).
$$

Thus the first conjunct says: either the iterates are eventually constant, or every limit direction of normalized increments lies in the normal-cone set determined by $A(0)$ and the negative of $B(x_\infty)$. The second conjunct says: if every element of $-B(x_\infty)$ lies in the interior of $A(0)$, then the iterates are eventually constant.

The set $\mathrm{normalizedIncrementLimitPoints}(x)$ is defined by saying that $d$ belongs to it if and only if there exists a strictly increasing map $\varphi: \mathbb{N} \to \mathbb{N}$ such that every selected index $\varphi(n)$ is not a stationary index of $x$, and the normalized increment directions along the subsequence converge to $d$:

$$
d \in \mathrm{normalizedIncrementLimitPoints}(x)
\iff
\exists \varphi,\
\mathrm{StrictMono}(\varphi)
\land
\bigl(\forall n,\ \varphi(n) \notin \mathrm{stationaryIndices}(x)\bigr)
\land
\mathrm{normalizedIncrementDirection}(x,\varphi(n)) \to d.
$$

The exact definitions of `stationaryIndices` and `normalizedIncrementDirection` are not provided in the source, so only their role in this limit-point definition is used.

The set $\mathrm{normalConeSet}$ is defined by

$$
\mathrm{normalConeSet}(C,S)
=\bigcup_{\xi \in S} \mathrm{normalCone}(C,\xi).
$$

Hence $Q$ says that for every limit direction $d$ of normalized increments, there exists some $\xi \in -B(x_\infty)$ such that $d$ lies in the normal cone to $A(0)$ at $\xi$. Equivalently, since $\xi \in -B(x_\infty)$ means $\xi = -b$ for some $b \in B(x_\infty)$, every such limit direction lies in the normal cone to $A(0)$ at some point $-b$ with $b \in B(x_\infty)$. The interior condition $R$ says that every negative of an element of the set value $B(x_\infty)$ lies in the interior of the set value $A(0)$.

## Lean proof
```lean
by
  constructor
  · by_cases hFinite : ∃ N, ∀ n ≥ N, x n = x N
    · exact Or.inl hFinite
    · exact Or.inr (theorem31_limit_directions_normal_cone A B f lam x h xInf hxInf hFinite)
  · intro hInterior
    by_contra hnotFinite
    have hDirections :
        normalizedIncrementLimitPoints x ⊆ normalConeSet (A (0 : H)) (-(B xInf)) :=
      theorem31_limit_directions_normal_cone A B f lam x h xInf hxInf hnotFinite
    exact theorem31_interior_condition_forces_finite A B f lam x h xInf hxInf hInterior
      hDirections hnotFinite
```

## Proof explanation
The proof begins with `by`, entering tactic mode. The command `constructor` splits the top-level conjunction $(P \lor Q) \land (R \to P)$ into two goals: first prove $P \lor Q$, and then prove $R \to P$.

For the first goal, the proof uses `by_cases hFinite : \exists N,\ \forall n \ge N,\ x_n = x_N`, a case split on the proposition $P$. In the case where $P$ holds, the proof uses `exact Or.inl hFinite`. Mathematically, this is simply choosing the left disjunct of $P \lor Q$ and supplying the assumed proof of $P$. In the case where $P$ fails, `hFinite` has type $\neg P$, i.e.

$$
\neg \exists N,\ \forall n \ge N,\ x_n = x_N.
$$

The proof then uses

```math
\texttt{theorem31\_limit\_directions\_normal\_cone}
```

with the arguments $A,B,f,\lambda,x,h,x_\infty,hxInf,hFinite$. The cited theorem states that, under the finite-dimensionality assumption, the standing assumptions `Theorem31Assumptions A B f lam x`, the convergence $x_n \to x_\infty$, and the non-eventual-constancy hypothesis $\neg P$, one obtains exactly

```math
\mathrm{normalizedIncrementLimitPoints}(x)
\subseteq
\mathrm{normalConeSet}\bigl(A(0),\, -B(x_\infty)\bigr),
```

which is $Q$. The proof wraps this conclusion with `Or.inr`, thereby proving $P \lor Q$ by selecting the right disjunct. This completes the first conjunct.

For the second goal, the proof must show $R \to P$. The command `intro hInterior` introduces the hypothesis $R$, namely

$$
-B(x_\infty) \subseteq \mathrm{interior}(A(0)).
$$

The new goal is $P$. The proof then uses `by_contra hnotFinite`, which is proof by contradiction: it assumes $\neg P$, i.e.

$$
\neg \exists N,\ \forall n \ge N,\ x_n = x_N,
$$

and changes the goal to `False`.

Next, the proof introduces an intermediate fact `hDirections` by invoking again

```math
\texttt{theorem31\_limit\_directions\_normal\_cone}
```

with the same data and with `hnotFinite`. Since the hypotheses of that theorem are exactly the standing assumptions, convergence $x_n \to x_\infty$, and non-eventual constancy $\neg P$, the theorem yields the inclusion

```math
\mathrm{normalizedIncrementLimitPoints}(x)
\subseteq
\mathrm{normalConeSet}\bigl(A(0),\, -B(x_\infty)\bigr).
```

This is precisely the statement $Q$.

Finally, the proof applies

```math
\texttt{theorem31\_interior\_condition\_forces\_finite}
```

with the arguments $A,B,f,\lambda,x,h,x_\infty,hxInf,hInterior,hDirections,hnotFinite$. The cited theorem states that, under the same finite-dimensional setting and standing assumptions, if $x_n \to x_\infty$, the interior condition $R$ holds, the normal-cone inclusion $Q$ holds, and the sequence is not eventually constant $\neg P$, then the conclusion is `False`. The proof supplies exactly those hypotheses, and the resulting contradiction matches the current goal `False`. Thus the assumption $\neg P$ is impossible under $R$, so $P$ must hold, proving $R \to P$.

In summary, the proof is purely a reduction to the two cited theorems: the first branch of the disjunction is handled by the case $P$, while the case $\neg P$ invokes `theorem31_limit_directions_normal_cone` to obtain $Q$. The second conjunct assumes the interior condition $R$, argues by contradiction against eventual constancy, rederives $Q$ from $\neg P$ using the same theorem, and then invokes `theorem31_interior_condition_forces_finite` to obtain the required contradiction.

