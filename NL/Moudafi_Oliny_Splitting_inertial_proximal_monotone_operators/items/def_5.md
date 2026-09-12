## Source file
`Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators/items/def_5.lean`

## Lean statement
```lean
def IsCocoerciveWRT (A : SetValuedOperator H H) (B : H → H) (β : ℝ) : Prop :=
  0 < β ∧ ∀ x, ∀ y ∈ ((A + svEmbed B).zeros), β * ‖B x - B y‖ ^ 2 ≤ ⟪B x - B y, x - y⟫_ℝ
```

## Statement explanation
The declaration defines a predicate `IsCocoerciveWRT`. It takes three explicit arguments: a set-valued operator $A$ on $H$, represented in Lean by `A : SetValuedOperator H H`; a single-valued map $B:H\to H$; and a real parameter $\beta:\mathbb R$. The result is a proposition, so the definition specifies a property that the pair $(A,B)$ and the scalar $\beta$ may or may not satisfy. The notation uses a norm and a real inner product, so in the ambient Lean context $H$ is equipped with the structures needed to interpret $\| \cdot \|$ and $\langle \cdot,\cdot\rangle_{\mathbb R}$.

The body of the definition is the conjunction

$$
0<\beta
\quad\wedge\quad
\forall x\in H,\ \forall y\in H,\ 
y\in (A+\operatorname{svEmbed}B).\mathrm{zeros}
\ \Longrightarrow\
\beta\,\lVert Bx-By\rVert^{2}
\le
\langle Bx-By,\,x-y\rangle_{\mathbb R}.
$$

Here `svEmbed B` converts the single-valued map $B$ into a set-valued operator, so that it can be added to the set-valued operator $A$. The sum $A+\operatorname{svEmbed}B$ is the set-valued operator whose value at a point $z$ is $A z+\{B z\}$, and `.zeros` denotes the set of zeros of a set-valued operator. Thus

$$
y\in (A+\operatorname{svEmbed}B).\mathrm{zeros}
$$

means that $0$ belongs to the value of the sum at $y$, i.e.

$$
0\in A y+B y.
$$

Equivalently, there exists $a\in A y$ such that $a+B y=0$, or $-B y\in A y$. So $y$ is a solution point of the inclusion $0\in A y+B y$.

The property therefore says: $\beta$ is positive, and for every $x\in H$ and every solution point $y$ of the inclusion $0\in A y+B y$, one has

$$
\beta\,\lVert Bx-By\rVert^{2}
\le
\langle Bx-By,\,x-y\rangle_{\mathbb R}.
$$

This is a cocoercivity-type inequality for $B$, but only with respect to the zero set of $A+\operatorname{svEmbed}B$. The variable $y$ is restricted to that zero set, while $x$ is arbitrary. The definition itself does not assert any separate monotonicity or continuity assumptions on $A$ or $B$; it only records this inequality together with $\beta>0$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part in the supplied Lean source. The declaration is a definition, not a theorem, and the Lean code contains only the definition body followed by the comment that there is no separate proof. Consequently there are no proof steps, no tactic invocations such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named local theorem or lemma is cited.

If the definition is unfolded in a later argument, its logical content is the conjunction described above. To prove `IsCocoerciveWRT A B β`, one would have to prove the two components: first, the positivity condition $0<\beta$; second, the universal implication saying that for every $x\in H$ and every $y\in H$ satisfying $y\in (A+\operatorname{svEmbed}B).\mathrm{zeros}$, the inequality

$$
\beta\,\lVert Bx-By\rVert^{2}
\le
\langle Bx-By,\,x-y\rangle_{\mathbb R}
$$

holds. Conversely, from a hypothesis of the form `h : IsCocoerciveWRT A B β`, one may extract the first component $0<\beta$ and the second component, namely the same universal statement over all $x$ and all zeros $y$ of $A+\operatorname{svEmbed}B$. These are the only mathematical contents supplied by the definition; no further conclusion is asserted or proved in this source.

