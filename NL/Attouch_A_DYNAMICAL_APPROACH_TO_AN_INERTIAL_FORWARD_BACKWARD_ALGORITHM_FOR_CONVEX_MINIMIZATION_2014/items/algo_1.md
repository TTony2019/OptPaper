## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_1.lean`

## Lean statement
```lean
structure IsIFBTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam : ℝ)
    (u y : ℕ → H) : Prop where
  a_pos : 0 < a
  b_pos : 0 < b
  lambda_pos : 0 < lam
  phi_proper : ERealFunction.IsProper phi
  first_update : ∀ k, ∃ g ∈ subdifferential phi (u (k + 1)),
    (1 / lam) • (u (k + 1) - u k) + g + a • u k - b • y k = 0
  second_update : ∀ k,
    (1 / lam) • (y (k + 1) - y k) + gradPsi (u (k + 1)) - a • u (k + 1) + b • y (k + 1) = 0
```

## Statement explanation
The declaration defines a proposition-valued structure `IsIFBTrajectory`. Its parameters are a real inner product space $H$, a function $\phi : H \to \overline{\mathbb R}$ into the extended real numbers, a finite-valued function $\psi : H \to \mathbb R$, a map $\mathrm{gradPsi} : H \to H$, real numbers $a,b,\lambda$, and two sequences $u : \mathbb N \to H$ and $y : \mathbb N \to H$. The typeclass assumptions on $H$ provide a normed additive group structure and a real inner product space structure, so expressions such as vector subtraction, addition, scalar multiplication by real numbers, and the zero vector are available.

A term of `IsIFBTrajectory phi psi gradPsi a b lam u y` is exactly a proof that all of the following conditions hold:

- The parameters are positive:

  $$
  a>0,\qquad b>0,\qquad \lambda>0.
  $$

- The extended-real-valued function $\phi$ is proper, in the sense of the Mathlib property `ERealFunction.IsProper phi`.

- For every $k\in\mathbb N$, there exists an element

  $$
  g\in \partial \phi(u_{k+1})
  $$

  in the subdifferential of $\phi$ at $u_{k+1}$, such that

  $$
  \frac{1}{\lambda}(u_{k+1}-u_k)+g+a\,u_k-b\,y_k=0.
  $$

  Here the equation is a vector equation in $H$, the scalar factor is the positive real number $1/\lambda$, and $g$ may depend on $k$. Equivalently, the first recurrence says that for each $k$, the vector

  $$
  \frac{1}{\lambda}(u_{k+1}-u_k)+a\,u_k-b\,y_k
  $$

  is the negative of some subgradient of $\phi$ at $u_{k+1}$.

- For every $k\in\mathbb N$,

  $$
  \frac{1}{\lambda}(y_{k+1}-y_k)+\mathrm{gradPsi}(u_{k+1})-a\,u_{k+1}+b\,y_{k+1}=0.
  $$

  This is also a vector equation in $H$. It relates $y_{k+1}$ to $y_k$, to the map $\mathrm{gradPsi}$ evaluated at $u_{k+1}$, and to $u_{k+1}$ and $y_{k+1}$ themselves.

Thus the predicate asserts that the coupled sequences $u$ and $y$ satisfy these two implicit difference relations, with positive parameters $a,b,\lambda$ and with $\phi$ proper. The declaration itself does not assert the existence of such sequences, nor does it assert convergence of any algorithm. It also does not state convexity of $\phi$ or $\psi$, differentiability of $\psi$, or that the map called `gradPsi` is actually the gradient of $\psi$; the second recurrence only uses `gradPsi` as a given map $H \to H$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source contains only the structure declaration, followed by the comment that there is no proof. Therefore no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named theorem or lemma is invoked.

Mathematically, the content is therefore entirely definitional: `IsIFBTrajectory` packages the conditions listed above as the fields of a proposition-valued structure. To prove `IsIFBTrajectory phi psi gradPsi a b lam u y`, one would have to supply exactly the fields of the structure: proofs of $a>0$, $b>0$, and $\lambda>0$; a proof that $\phi$ is proper; and for each $k\in\mathbb N$, a witness $g$ in the subdifferential of $\phi$ at $u_{k+1}$ satisfying the first vector recurrence; and a proof of the second vector recurrence. Conversely, if an instance of `IsIFBTrajectory` is assumed, these fields are precisely the facts that become available: positivity of the three parameters, properness of $\phi$, and the two universally quantified recurrence equations. No further mathematical conclusion is drawn in this declaration.

