## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/def_4.lean`

## Lean statement
```lean
def IsStronglyMonotoneOn (beta : ℝ) (D : Set H) (A : D → H) : Prop :=
  0 < beta ∧ ∀ x y : D, beta * ‖(x : H) - y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (A x - A y)
```

## Statement explanation
The declaration introduces the predicate `IsStronglyMonotoneOn`, whose parameters are a real number $\beta$, a set $D$ of elements of the ambient space $H$, and a function $A : D \to H$. Here $H$ is used with a real inner product pairing `inner ℝ` and with a norm $\lVert\cdot\rVert$, so $D$ is a subset of the ambient real inner-product space and $A$ assigns to every $x \in D$ a vector $A x \in H$. The definition says that $A$ is strongly monotone on $D$ with modulus or coefficient $\beta$ precisely when:

$$
0<\beta
$$

and, for every $x,y\in D$,

$$
\beta\,\lVert (x:H)-y\rVert^{2}
\le
\left\langle (x:H)-y,\; A x-A y\right\rangle_{\mathbb R}.
$$

Because $D$ is a subtype of $H$, the notation $(x:H)$ is the coercion of $x\in D$ to the corresponding element of $H$. Thus $(x:H)-y$ is the ambient vector difference $x-y$, and $A x-A y$ is the difference of the two values of $A$ in $H$. The inner product is the real inner product on $H$. Mathematically, the definition requires the pairing of $x-y$ with $A x-A y$ to be bounded below by $\beta$ times the squared distance between $x$ and $y$. Since the real inner product is symmetric, this is the usual strong monotonicity inequality for $A$ on $D$ with constant $\beta$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. This declaration is a definition, not a theorem, so it does not prove a proposition; it introduces the proposition `IsStronglyMonotoneOn beta D A`. The body after the colon is a conjunction: the first conjunct is $0<\beta$, and the second conjunct is the universal statement that for all $x,y:D$,

$$
\beta\,\lVert (x:H)-y\rVert^{2}
\le
\left\langle (x:H)-y,\; A x-A y\right\rangle_{\mathbb R}.
$$

The binder over $x,y:D$ ranges over elements of the subtype determined by the set $D$, while `(x : H)` coerces such an element to its underlying vector in $H$. The operations of subtraction, norm, and inner product then take place in $H$. There are no tactic steps such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named theorem or lemma is invoked. The definition simply packages the stated positivity condition on $\beta$ together with the strong monotonicity inequality for $A$ on $D$.

