## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_def_2.lean`

## Lean statement
```lean
def StronglyConvexWith {m : Nat} (sigma : Real) (u : EuclideanSpace m -> Real) : Prop :=
  0 < sigma ∧
    ConvexOn Real Set.univ (fun x : EuclideanSpace m => u x - (sigma / 2) * ‖x‖ ^ 2)
```

## Statement explanation
The declaration introduces a predicate named `StronglyConvexWith`. It is implicitly parameterized by a natural number $m$, and it takes two explicit arguments: a real scalar $\sigma$ (written `sigma` in Lean) and a function

$$
u : \mathbb{R}^m \to \mathbb{R},
$$

where the Euclidean space $\mathbb{R}^m$ is represented in Lean by `EuclideanSpace m`. The predicate returns a proposition, so `StronglyConvexWith sigma u` is a statement about $\sigma$ and $u$.

The proposition is the conjunction of two conditions:

$$
\sigma > 0
$$

and the function

$$
x \mapsto u(x) - \frac{\sigma}{2}\|x\|^2
$$

is convex on the whole space. Here `Set.univ` is the entire Euclidean space, and $\|x\|$ is the Euclidean norm. The Lean expression `ConvexOn Real Set.univ` is the standard convexity predicate over the real scalar field, restricted to the full domain. Unfolding the usual meaning of convexity, the second component says that for all $x,y \in \mathbb{R}^m$ and all $t \in [0,1]$,

$$
f\bigl((1-t)x+ty\bigr)\le (1-t)f(x)+t f(y),
$$

where

$$
f(x)=u(x)-\frac{\sigma}{2}\|x\|^2.
$$

Equivalently, writing this out in terms of $u$,

$$
u\bigl((1-t)x+ty\bigr)-\frac{\sigma}{2}\|(1-t)x+ty\|^2
\le
(1-t)\left(u(x)-\frac{\sigma}{2}\|x\|^2\right)
+t\left(u(y)-\frac{\sigma}{2}\|y\|^2\right).
$$

Thus the declaration formalizes the usual notion that $u$ is $\sigma$-strongly convex: it requires the strong-convexity parameter $\sigma$ to be positive, and it encodes strong convexity by requiring that subtracting the quadratic term $\frac{\sigma}{2}\|x\|^2$ leaves a convex function. No smoothness, differentiability, lower semicontinuity, or properness assumptions are included; the only hypotheses are those appearing in the proposition itself.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, not a theorem, so it introduces an abbreviation for a proposition rather than proving a result. The Lean source contains only the definition body and the comment that there is no separate proof. Consequently, no commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named local theorem or lemma is invoked.

Semantically, `StronglyConvexWith sigma u` simply unfolds to the conjunction of $\sigma>0$ and the convexity of the function $x \mapsto u(x)-\frac{\sigma}{2}\|x\|^2$ on the entire Euclidean space. If this predicate were used later, a proof of `StronglyConvexWith sigma u` would consist of a proof of $\sigma>0$ together with a proof of the stated convexity property; conversely, from a hypothesis of the form `StronglyConvexWith sigma u` one may extract those two components. But the declaration itself only defines the predicate and does not prove any mathematical claim.

