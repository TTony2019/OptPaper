## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/algo_1.lean`

## Lean statement
```lean
theorem algorithm_bregman_bounds {m : Nat} {P : ProblemData m} (A : AlgorithmData P) :
    ∀ x y : EuclideanSpace m,
      (A.sigma / 2) * ‖x - y‖ ^ 2 <= bregmanDistance A.u x y ∧
        bregmanDistance A.u x y <= (A.Lgrad_u / 2) * ‖x - y‖ ^ 2
```

## Statement explanation
The theorem `algorithm_bregman_bounds` is a statement about an algorithm-data object $A$ attached to problem data $P$ in dimension $m$. The dimension $m$ is a natural number, so the ambient space is `EuclideanSpace m`, which is $\mathbb{R}^m$ with its Euclidean norm. $P$ is problem data of dimension $m$, and $A$ is algorithm data for $P$. The theorem uses the following components of $A$: $A.u$ is a real-valued function on $\mathbb{R}^m$, $A.\sigma$ and $A.Lgrad_u$ are real numbers, $A.u_strongly_convex$ is the assertion that $A.u$ is strongly convex with modulus $A.\sigma$, and $A.u_lipschitz_gradient$ is the assertion that $A.u$ has $A.Lgrad_u$-Lipschitz continuous gradient. The conclusion is that for every $x,y\in\mathbb{R}^m$, the Bregman distance $D_{A.u}(x,y)$ associated with $A.u$ satisfies the two quadratic bounds

$$
\frac{A.\sigma}{2}\|x-y\|^2 \le D_{A.u}(x,y)
$$

and

$$
D_{A.u}(x,y) \le \frac{A.Lgrad_u}{2}\|x-y\|^2.
$$

Equivalently, writing $u_A=A.u$, $\sigma_A=A.\sigma$, and $L_A=A.Lgrad_u$, the theorem says that for all $x,y\in\mathbb{R}^m$,

$$
\frac{\sigma_A}{2}\|x-y\|^2 \le D_{u_A}(x,y) \le \frac{L_A}{2}\|x-y\|^2.
$$

The lower bound is the quadratic lower estimate coming from strong convexity, and the upper bound is the quadratic upper estimate coming from Lipschitz continuity of the gradient. The theorem statement explicitly quantifies only $A$, but the strong-convexity and Lipschitz-gradient hypotheses are carried as fields of $A$, so they are available for the proof without being separate arguments in the displayed statement.

## Lean proof
```lean
bregmanDistance_quadratic_bounds A.u A.sigma A.Lgrad_u A.u_strongly_convex
    A.u_lipschitz_gradient
```

## Proof explanation
The proof is a single term, namely an application of the previously established theorem `bregmanDistance_quadratic_bounds`. That cited theorem states that for any dimension $m$, any function $u:\mathbb{R}^m\to\mathbb{R}$, any real numbers $\sigma$ and $L$, if $u$ is strongly convex with modulus $\sigma$ and has $L$-Lipschitz continuous gradient, then for all $x,y\in\mathbb{R}^m$,

$$
\frac{\sigma}{2}\|x-y\|^2 \le D_u(x,y)
$$

and

$$
D_u(x,y) \le \frac{L}{2}\|x-y\|^2.
$$

In other words, it gives exactly the conjunction of the lower and upper quadratic bounds on the Bregman distance, uniformly in $x$ and $y$.

The present proof instantiates the cited theorem with $u=A.u$, $\sigma=A.\sigma$, and $L=A.Lgrad_u$. It supplies the required strong-convexity hypothesis using $A.u_strongly_convex$, whose type is `StronglyConvexWith A.sigma A.u`, and it supplies the required Lipschitz-gradient hypothesis using `A.u_lipschitz_gradient`, whose type is `HasLipschitzContinuousGradient A.u A.Lgrad_u`. The implicit dimension argument $m$ is inferred from the type of $A.u$, and the problem data $P$ is not passed to the cited theorem because it only determines the type of $A$.

After this instantiation, the conclusion of `bregmanDistance_quadratic_bounds` is precisely the goal of `algorithm_bregman_bounds`:

$$
\forall x,y\in\mathbb{R}^m,\quad
\frac{A.\sigma}{2}\|x-y\|^2 \le D_{A.u}(x,y)
\ \wedge\
D_{A.u}(x,y) \le \frac{A.Lgrad_u}{2}\|x-y\|^2.
$$

Because the cited theorem already returns the universal quantifier over $x$ and $y$, there is no need for `intro` to introduce $x$ and $y$. Because it already returns the conjunction of the two inequalities, there is no need to split the conjunction manually. No `rw`, `simp`, `exact`, or `linarith` tactic is used in the proof. The mathematical work is entirely contained in the cited theorem: strong convexity of $A.u$ gives the lower quadratic bound, and Lipschitz continuity of the gradient of $A.u$ gives the upper quadratic bound. Lean accepts the application directly because its type is definitionally the same as the goal after substituting the fields of $A$.

