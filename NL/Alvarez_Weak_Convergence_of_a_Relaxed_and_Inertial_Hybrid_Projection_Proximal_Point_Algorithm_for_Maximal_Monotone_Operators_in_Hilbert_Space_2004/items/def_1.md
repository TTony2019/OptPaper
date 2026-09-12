## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/def_1.lean`

## Lean statement
```lean
theorem resolvent_selection_lipschitz
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    {lam : ℝ} (hlam : 0 < lam) (J : H → H)
    (hJ : ∀ x : H, J x ∈ J[(lam • A)] x) :
    LipschitzWith 1 J
```

## Statement explanation
The declaration `resolvent_selection_lipschitz` is stated in the ambient real inner-product space $H$. It involves a set-valued operator $A:H\to\mathcal P(H)$, a real scalar $\lambda$, and a single-valued map $J:H\to H$. The hypotheses are:

- $A$ is maximal monotone. In particular, its monotonicity part says that for $u\in A(p)$ and $v\in A(q)$, the monotonicity inequality

$$
\langle u-v,p-q\rangle\ge 0
$$

  holds, up to the usual convention for the order of the two inner-product arguments.
- $\lambda\gt 0$.
- For every $x\in H$, $Jx$ belongs to the resolvent of the scaled operator $\lambda A$ at $x$, written in the source as $J[(\lambda A)]x$. By the cited result `mem_resolvent_smul_iff` and the definition `identityAddScaled`, this means that for every $x$ there exists $a_x\in A(Jx)$ such that

$$
x=Jx+\lambda a_x,
$$

  equivalently $x-Jx\in \lambda A(Jx)$.

The conclusion is that $J$ is Lipschitz with constant $1$, i.e.

```math
d(Jx,Jy)\le 1\cdot d(x,y)=\|x-y\|
```

for all $x,y\in H$. Equivalently, $J$ is nonexpansive. The maximality part of $A$ is not used beyond its monotonicity component; the selection hypothesis already provides the resolvent points.

## Lean proof
```lean
by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hxres : x ∈ SetValuedOperator.identityAddScaled A lam (J x) :=
    (SetValuedOperator.mem_resolvent_smul_iff A lam x (J x)).mp (hJ x)
  have hyres : y ∈ SetValuedOperator.identityAddScaled A lam (J y) :=
    (SetValuedOperator.mem_resolvent_smul_iff A lam y (J y)).mp (hJ y)
  dsimp [SetValuedOperator.identityAddScaled] at hxres hyres
  rcases hxres with ⟨a, ha, hxeq'⟩
  rcases hyres with ⟨b, hb, hyeq'⟩
  have hxeq : x = J x + lam • a := hxeq'.symm
  have hyeq : y = J y + lam • b := hyeq'.symm
  have hdiff : x - y = (J x - J y) + lam • (a - b) := by
    calc
      x - y = (J x + lam • a) - y := congrArg (· - y) hxeq
      _ = (J x + lam • a) - (J y + lam • b) :=
        congrArg ((J x + lam • a) - ·) hyeq
      _ = (J x - J y) + (lam • a - lam • b) := by abel
      _ = (J x - J y) + lam • (a - b) := by rw [smul_sub]
  have hfirm : ‖J x - J y‖ ^ 2 ≤ inner ℝ (J x - J y) (x - y) := by
    rw [hdiff, inner_add_right, real_inner_smul_right]
    have hmono : 0 ≤ inner ℝ (J x - J y) (a - b) := by
      have h := hA.1 a ha b hb
      rwa [real_inner_comm] at h
    have hself : inner ℝ (J x - J y) (J x - J y) = ‖J x - J y‖ ^ 2 := by
      simp
    rw [hself]
    nlinarith [mul_nonneg (le_of_lt hlam) hmono]
  have hcauchy : inner ℝ (J x - J y) (x - y) ≤ ‖J x - J y‖ * ‖x - y‖ := by
    exact real_inner_le_norm (J x - J y) (x - y)
  have hsq_le : ‖J x - J y‖ ^ 2 ≤ ‖J x - J y‖ * ‖x - y‖ := le_trans hfirm hcauchy
  have hnorm : ‖J x - J y‖ ≤ ‖x - y‖ := by
    by_cases hzero : ‖J x - J y‖ = 0
    · rw [hzero]
      exact norm_nonneg _
    · have hpos : 0 < ‖J x - J y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      nlinarith
  simpa [dist_eq_norm, mul_comm] using hnorm
```

## Proof explanation
To prove that $J$ is Lipschitz with constant $1$, the proof uses `LipschitzWith.of_dist_le_mul`, reducing the goal to showing

$$
d(Jx,Jy)\le 1\cdot d(x,y)
$$

for arbitrary $x,y\in H$. The tactic `intro x y` fixes such arbitrary points.

First, the proof extracts the resolvent representations. From $`hJ\,x`$, we have$Jx\in \mathcal R_{\lambda A}(x)$. The theorem `mem_resolvent_smul_iff` says, for any $\rho$, $x$, and $y$,

$$
y\in \mathcal R_{\rho A}(x)
\iff
x\in (I+\rho A)(y),
$$

where

```math
(I+\rho A)(y)=\{y+\rho a:a\in A(y)\}.
```

Specializing to $\rho=\lambda$ and $y=Jx$, we get $x\in (I+\lambda A)(Jx)$, so there exists $a\in A(Jx)$ with

$$
x=Jx+\lambda a.
$$

Similarly, for $y$, there exists $b\in A(Jy)$ with

$$
y=Jy+\lambda b.
$$

The commands `dsimp` and `rcases` unfold `identityAddScaled` and extract the witnesses $a$ and $b$.

Subtracting the two equations gives

$$
x-y=(Jx-Jy)+\lambda(a-b).
$$

The proof obtains this by substituting the two equalities using `congrArg`, normalizing the additive expression using `abel`, and using `smul_sub`, which is the distributivity identity $\lambda(a-b)=\lambda a-\lambda b$.

Next, the proof establishes the firm inequality

```math
\|Jx-Jy\|^{2}\le \langle Jx-Jy,x-y\rangle.
```

Using the identity for $x-y$ and bilinearity of the real inner product, the right-hand side becomes

$$
\langle Jx-Jy,Jx-Jy\rangle
+\lambda\langle Jx-Jy,a-b\rangle.
$$

The first term is $`\|Jx-Jy\|^{2}`$, by the standard real inner-product identity$`\langle u,u\rangle=\|u\|^{2}`$, applied through `simp`. For the second term, monotonicity of $A$ applied to $a\in A(Jx)$ and $b\in A(Jy)$ gives the monotonicity inequality, and after using `real_inner_comm` the proof obtains

$$
0\le \langle Jx-Jy,a-b\rangle.
$$

Since $\lambda\gt 0$, the product $\lambda\langle Jx-Jy,a-b\rangle$ is nonnegative. Therefore

```math
\|Jx-Jy\|^{2}
\le
\|Jx-Jy\|^{2}
+\lambda\langle Jx-Jy,a-b\rangle,
```

which is exactly the firm inequality. The tactics `inner_add_right`, `real_inner_smul_right`, `mul_nonneg`, and `nlinarith` implement these algebraic and order-theoretic steps.

The proof then applies Cauchy–Schwarz in the form

```math
\langle Jx-Jy,x-y\rangle
\le
\|Jx-Jy\|\,\|x-y\|,
```

which is the content of `real_inner_le_norm`. Combining this with the firm inequality via `le_trans` gives

```math
\|Jx-Jy\|^{2}
\le
\|Jx-Jy\|\,\|x-y\|.
```

From this the desired norm inequality is deduced. Let

```math
u=\|Jx-Jy\|,\qquad v=\|x-y\|.
```

We know $u\ge 0$ and $u^{2}\le uv$. If $u=0$, then $u\le v$ because $v\ge 0$, using `norm_nonneg`. If $u\ne 0$, then $u\gt 0$ because $u\ge 0$, and dividing $u^{2}\le uv$ by the positive number $u$ yields $u\le v$. The tactic `nlinarith` performs this cancellation. Thus

```math
\|Jx-Jy\|\le \|x-y\|.
```

Finally, the command `simpa [dist_eq_norm, mul_comm] using hnorm` rewrites the distances as norms,

```math
d(Jx,Jy)=\|Jx-Jy\|,\qquad d(x,y)=\|x-y\|,
```

and handles the factor $1$, so that the previously proved inequality becomes exactly the Lipschitz inequality for $J$ with constant $1$. Since $x$ and $y$ were arbitrary, $J$ is Lipschitz with constant $1$.

