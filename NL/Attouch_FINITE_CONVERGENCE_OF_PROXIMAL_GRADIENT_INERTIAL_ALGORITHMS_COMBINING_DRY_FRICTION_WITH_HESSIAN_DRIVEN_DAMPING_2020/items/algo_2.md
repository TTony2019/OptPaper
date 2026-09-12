## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/algo_2.lean`

## Lean statement
```lean
structure IPAHDDSoftThreshold {n : Type*} [Fintype n]
    (f : EuclideanSpace ℝ n → ℝ) (h gamma beta r : ℝ) where
  x : ℕ → EuclideanSpace ℝ n
  initial0 : EuclideanSpace ℝ n
  initial1 : EuclideanSpace ℝ n
  init0 : x 0 = initial0
  init1 : x 1 = initial1
  threshold_nonneg : 0 ≤ h * r / (1 + h * gamma)
  update (k : ℕ) : x (k + 2) = x (k + 1) + h • softThresholdVector (h * r / (1 + h * gamma)) threshold_nonneg
    ((1 / (h * (1 + h * gamma))) • (x (k + 1) - x k) -
      (beta / (1 + h * gamma)) • (gradient f (x (k + 1)) - gradient f (x k)) -
      (h / (1 + h * gamma)) • gradient f (x (k + 1)))
```

## Statement explanation
The declaration `IPAHDDSoftThreshold` introduces a structure, i.e. a bundled record type. It is parameterized by a finite index type $n$, a function

$$
f : \mathbb R^n \to \mathbb R,
$$

and real parameters $h,\gamma,\beta,r$. Mathematically, it packages a second-order iterative sequence $(x_k)_{k\in\mathbb N}$ in $\mathbb R^n$, together with two prescribed initial points, a nonnegativity proof for a threshold, and the recurrence relating each new term to the two preceding terms.

The fields of the structure are as follows.

- `x` is a sequence

  $$
  x : \mathbb N \to \mathbb R^n,
  $$

  so $x_k$ denotes the $k$-th iterate.

- `initial0` and `initial1` are prescribed vectors in $\mathbb R^n$, written here as $a_0$ and $a_1$.

- `init0` is the equality

  $$
  x_0 = a_0.
  $$

- `init1` is the equality

  $$
  x_1 = a_1.
  $$

- `threshold_nonneg` is a proof of the inequality

  $$
  0 \le \frac{h r}{1+h\gamma}.
  $$

  Thus the structure requires that this scalar threshold be nonnegative.

- `update` is a dependent function assigning to every natural number $k$ a proof of the recurrence

  $$
  x_{k+2}
  =x_{k+1}
  +h\,\mathrm{softThresholdVector}\!\left(
    \frac{h r}{1+h\gamma},\,
    \pi,\,
    z_k
  \right),
  $$

  where $\pi$ is the proof supplied by `threshold_nonneg`, and

  $$
  z_k
  =\frac{1}{h(1+h\gamma)}(x_{k+1}-x_k)
  -\frac{\beta}{1+h\gamma}\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
  -\frac{h}{1+h\gamma}\nabla f(x_{k+1}).
  $$

  Here $\nabla f$ denotes the gradient of $f$ in the Euclidean space, and `softThresholdVector` is the named vector-valued soft-thresholding operation appearing in the update. Its internal formula is not expanded in the provided source; only its role as a function taking the threshold $\frac{h r}{1+h\gamma}$, the proof that this threshold is nonnegative, and the vector $z_k$, and returning the vector that is added to $x_{k+1}$, is visible.

In ordinary mathematical language, an object of type `IPAHDDSoftThreshold f h gamma beta r` consists exactly of a sequence $(x_k)$ in $\mathbb R^n$, two initial points $a_0,a_1$ with $x_0=a_0$ and $x_1=a_1$, a proof that the threshold $\frac{h r}{1+h\gamma}$ is nonnegative, and, for every $k$, the displayed second-order recurrence. The recurrence uses a momentum-like term $x_{k+1}-x_k$, a term involving the difference of gradients $\nabla f(x_{k+1})-\nabla f(x_k)$, a gradient term $\nabla f(x_{k+1})$, and finally the soft-thresholding operation scaled by $h$. No convexity, differentiability, or positivity assumptions on $h,\gamma,\beta,r$ other than the threshold inequality are fields of the structure.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration. The declaration is a `structure`, so it does not prove a theorem and does not contain a tactic script. Its mathematical content is entirely the specification of the record fields.

The proof-like fields are required components rather than derived conclusions. The fields `init0` and `init1` are equalities that any instance must supply, namely $x_0=a_0$ and $x_1=a_1$. The field `threshold_nonneg` is a proof of

$$
0 \le \frac{h r}{1+h\gamma}.
$$

This proof is then passed as the second argument to `softThresholdVector` inside the update field, so the recurrence depends on it as a formal argument. The field `update` is a dependent function that, for each $k\in\mathbb N$, supplies a proof of

$$
x_{k+2}
=x_{k+1}
+h\,\mathrm{softThresholdVector}\!\left(
  \frac{h r}{1+h\gamma},\,
  \pi,\,
  z_k
\right),
$$

with $z_k$ as displayed above and $\pi$ the proof from `threshold_nonneg`.

No named theorem or lemma is invoked in this declaration, and no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur. To construct an instance of `IPAHDDSoftThreshold f h gamma beta r`, one must provide the sequence $x$, the initial points $a_0,a_1$, proofs of the two initial equalities, a proof of the threshold inequality, and for every $k$ a proof of the update recurrence.

