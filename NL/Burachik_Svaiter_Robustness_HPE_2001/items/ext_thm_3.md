## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/ext_thm_3.lean`

## Lean statement
```lean
theorem rockafellar_sum_maximal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {T : SetValuedOperator H H} (hT : T.IsMaximalMonotone) (C : Set H)
    (hCnonempty : C.Nonempty) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (hint : (T.dom ∩ interior C).Nonempty) :
    (T + N[C]).IsMaximalMonotone
```

## Statement explanation
The declaration `rockafellar_sum_maximal` is stated in a complete real inner product space $H$, so $H$ is a real Hilbert space. It considers a set-valued operator $T:H\rightrightarrows H$, meaning that each $x\in H$ is assigned a subset $T(x)\subseteq H$, and assumes that $T$ is maximal monotone. It also fixes a subset $C\subseteq H$, assumed to be nonempty, closed, and convex over $\mathbb R$. The additional hypothesis is

$$
(T.\mathrm{dom}\cap \operatorname{int}C)\neq\emptyset,
$$

where $\operatorname{dom}T=\{x\in H:T(x)\neq\emptyset\}$ and $\operatorname{int}C$ is the topological interior of $C$. Thus there exists some point $x$ that lies both in the domain of $T$ and in the interior of $C$.

The conclusion is that the sum operator $T+N_C$ is maximal monotone, where $N_C$ is the normal-cone operator associated with $C$, written `N[C]` in Lean. The sum of two set-valued operators is defined pointwise by Minkowski addition:

$$
(A+B)(x)=A(x)+B(x)=\{a+b:a\in A(x),\, b\in B(x)\}.
$$

Maximal monotonicity, according to the cited definition, means that $A$ is monotone and its graph is maximal among monotone graphs: for every monotone operator $A'$ with $\operatorname{graph}A\subseteq \operatorname{graph}A'$, one also has $\operatorname{graph}A'\subseteq \operatorname{graph}A$. In ordinary mathematical terms, the theorem says that adding the normal cone of a nonempty closed convex set to a maximal monotone operator preserves maximal monotonicity, provided that the domain of the operator meets the interior of the convex set.

## Lean proof
```lean
by
  have hnormal_max : IsMaximalMonotone (N[C]) :=
    normalCone_maximal C hCnonempty hCclosed hCconvex
  rcases hint with ⟨x, hxT, hxC⟩
  have hqual : (interior (SetValuedOperator.dom (N[C])) ∩ T.dom).Nonempty := by
    refine ⟨x, ?_, hxT⟩
    rw [normalCone_dom]
    exact hxC
  have hsum : IsMaximalMonotone (N[C] + T) :=
    sum_maximal_monotone (N[C]) T hnormal_max hT hqual
  have hcomm : N[C] + T = T + N[C] := by
    ext x w
    change w ∈ N[C] x + T x ↔ w ∈ T x + N[C] x
    rw [Set.mem_add]
    constructor
    · rintro ⟨n, hn, t, ht, rfl⟩
      exact ⟨t, ht, n, hn, by exact add_comm t n⟩
    · rintro ⟨t, ht, n, hn, rfl⟩
      exact ⟨n, hn, t, ht, by exact add_comm n t⟩
  rwa [hcomm] at hsum
```

## Proof explanation
The proof proceeds as follows.

1. It first proves that the normal-cone operator $N_C$ is maximal monotone. This is obtained from the cited result `normalCone_maximal`. That result states that if $H$ is a complete real inner product space and $C\subseteq H$ is nonempty, closed, and convex, then the normal-cone operator $N_C$ is maximal monotone. In the proof, the three hypotheses $C\neq\emptyset$, $C$ closed, and $C$ convex are supplied by `hCnonempty`, `hCclosed`, and `hCconvex`. Hence Lean obtains

$$
\operatorname{IsMaximalMonotone}(N_C).
$$

This supplies one of the two maximal-monotonicity hypotheses needed for the later sum theorem.

2. The hypothesis

$$
(T.\mathrm{dom}\cap \operatorname{int}C)\neq\emptyset
$$

is destructed by `rcases hint with ⟨x, hxT, hxC⟩`. This extracts a point $x\in H$, together with the facts $hxT:x\in \operatorname{dom}T$ and $hxC:x\in \operatorname{int}C$. Thus $T(x)\neq\emptyset$ and $x$ lies in the interior of $C$.

3. The proof next establishes the qualification condition needed to apply the sum theorem. The cited theorem `sum_maximal_monotone` requires, for operators $A$ and $B$,

$$
\bigl(\operatorname{int}(\operatorname{dom}A)\cap \operatorname{dom}B\bigr)\neq\emptyset.
$$

The proof will apply this with $A=N_C$ and $B=T$, so it needs

$$
\bigl(\operatorname{int}(\operatorname{dom}N_C)\cap \operatorname{dom}T\bigr)\neq\emptyset.
$$

It constructs the same point $x$ as a witness. The remaining obligation is to show $x\in \operatorname{int}(\operatorname{dom}N_C)$. Here Lean uses the cited fact `normalCone_dom`, which states

$$
\operatorname{dom}(N_C)=C.
$$

Therefore $\operatorname{int}(\operatorname{dom}N_C)=\operatorname{int}C$, and rewriting with `normalCone_dom` turns the goal $x\in \operatorname{int}(\operatorname{dom}N_C)$ into $x\in \operatorname{int}C$, which is exactly `hxC`. Hence the qualification condition

$$
\bigl(\operatorname{int}(\operatorname{dom}N_C)\cap \operatorname{dom}T\bigr)\neq\emptyset
$$

is proved.

4. The proof now applies `sum_maximal_monotone` to the operators $N_C$ and $T$. That theorem says: if $A$ and $B$ are maximal monotone and

$$
\bigl(\operatorname{int}(\operatorname{dom}A)\cap \operatorname{dom}B\bigr)\neq\emptyset,
$$

then $A+B$ is maximal monotone. Here $A=N_C$, $B=T$. The two maximal-monotonicity assumptions are `hnormal_max` for $N_C$ and `hT` for $T$, and the qualification condition is the one just proved. Therefore Lean obtains

$$
\operatorname{IsMaximalMonotone}(N_C+T).
$$

5. The target conclusion concerns $T+N_C$, not $N_C+T$. Thus the proof establishes commutativity of the operator sum:

$$
N_C+T=T+N_C.
$$

It uses `ext x w` to reduce equality of set-valued operators to pointwise set equality, so it suffices to prove for each $x$ and $w$ that

$$
w\in (N_C+T)(x)\iff w\in (T+N_C)(x).
$$

After unfolding the sums, this becomes

$$
w\in N_C(x)+T(x)\iff w\in T(x)+N_C(x).
$$

The Lean command `rw [Set.mem_add]` rewrites membership in a Minkowski sum into the existence of summands. In the forward direction, if $w=n+t$ with $n\in N_C(x)$ and $t\in T(x)$, then the same point can be represented as $w=t+n$ with $t\in T(x)$ and $n\in N_C(x)$. The reverse direction is identical with the roles of $n$ and $t$ exchanged. Both directions use `add_comm`, the commutativity of addition in $H$, to identify $n+t$ with $t+n$. Thus the two operator sums are equal.

6. Finally, `rwa [hcomm] at hsum` rewrites the previously proved fact

$$
\operatorname{IsMaximalMonotone}(N_C+T)
$$

using the equality $N_C+T=T+N_C$, producing

$$
\operatorname{IsMaximalMonotone}(T+N_C),
$$

and then closes the goal by assumption. Hence $T+N_C$ is maximal monotone, as claimed.

