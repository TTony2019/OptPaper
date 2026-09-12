## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/algo_1.lean`

## Lean statement
```lean
noncomputable def inertialForwardBackwardNext (x z : ℕ → H) (inertia : ℕ → ℝ) (x0 : H)
    (n : ℕ) (h : IsChebyshev
      (inertialForwardBackwardC x z inertia n ∩ inertialForwardBackwardQ x x0 n)) : H :=
  projectionPoint (inertialForwardBackwardC x z inertia n ∩ inertialForwardBackwardQ x x0 n) h x0
```

## Statement explanation
The declaration `inertialForwardBackwardNext` is a noncomputable definition. It has an ambient type $H$, two sequences $x,z:\mathbb N\to H$, a real-valued sequence $\mathrm{inertia}:\mathbb N\to\mathbb R$, a point $x_0:H$, an index $n:\mathbb N$, and a proof term

$$
h:\mathrm{IsChebyshev}\Bigl(
  \mathrm{inertialForwardBackwardC}(x,z,\mathrm{inertia},n)
  \cap
  \mathrm{inertialForwardBackwardQ}(x,x_0,n)
\Bigr).
$$

The two named sets are subsets of $H$: the first is determined by $x$, $z$, $\mathrm{inertia}$, and $n$, while the second is determined by $x$, $x_0$, and $n$. The hypothesis $h$ is not an extra mathematical assumption of a theorem; it is an explicit certificate that the intersection

$$
S_n
=
\mathrm{inertialForwardBackwardC}(x,z,\mathrm{inertia},n)
\cap
\mathrm{inertialForwardBackwardQ}(x,x_0,n)
$$

has the Chebyshev property. The output of the definition is the element of $H$

$$
\mathrm{projectionPoint}(S_n,h,x_0).
$$

Mathematically, this defines the next point by projecting $x_0$ onto the intersection $S_n$, using the Chebyshev certificate $h$ to make the projection point well-defined. The parameter $x_0$ plays two roles: it appears in the definition of the set $\mathrm{inertialForwardBackwardQ}(x,x_0,n)$, and it is also the point whose projection onto the intersection is taken. The keyword `noncomputable` marks that the projection point is obtained nonconstructively, typically by extracting the unique nearest point from an existence-and-uniqueness statement. The source does not display the internal definitions of `inertialForwardBackwardC`, `inertialForwardBackwardQ`, `projectionPoint`, or `IsChebyshev`; the exact content visible here is that $h$ certifies the Chebyshev property of the intersection, and `projectionPoint` then consumes that set, that certificate, and the point $x_0$ to produce an element of $H$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a definition, and its body is the single term

$$
\mathrm{projectionPoint}\bigl(S_n,h,x_0\bigr),
$$

where

$$
S_n
=
\mathrm{inertialForwardBackwardC}(x,z,\mathrm{inertia},n)
\cap
\mathrm{inertialForwardBackwardQ}(x,x_0,n).
$$

No tactics such as `intro`, `rw`, `simp`, or `linarith` occur, and no local theorem or lemma is invoked. The proof argument $h$ is not discharged or used in a proof step; it is simply supplied as the second argument to `projectionPoint`, because that function requires a proof that the set is Chebyshev before it can return a projection point. Thus the definition constructs the next iterate by first forming the intersection of the two algorithmically determined sets and then taking the projection of $x_0$ onto that intersection.

