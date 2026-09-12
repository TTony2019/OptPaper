## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/ext_def_1.lean`

## Lean statement
```lean
theorem yosida_resolvent_equiv
    (A : SetValuedOperator H H) {lam : ℝ} (hlam : lam ≠ 0)
    {x y xi : H}
    (hy : y ∈ J[(lam • A)] x)
    (hxi : xi = x - y) :
    lam⁻¹ • xi ∈ A (x - xi)
```

## Statement explanation
The declaration establishes a standard algebraic form of the resolvent relation for a set-valued operator. Let $H$ be the ambient additive commutative group with real scalar multiplication used by the cited resolvent lemmas, let $A : H \rightrightarrows H$ be a set-valued operator, let $\lambda \in \mathbb{R}$ with $\lambda \neq 0$, and let $x,y,\xi \in H$. The notation $J_{\lambda A}(x)$, written in Lean as `J[(lam • A)] x`, denotes the value at $x$ of the resolvent of the scaled set-valued operator $\lambda \bullet A$.

The hypotheses are:

- $y \in J_{\lambda A}(x)$, meaning that $y$ lies in the resolvent of $\lambda A$ at $x$;
- $\xi = x-y$, so $\xi$ is the displacement from the resolvent point $y$ back to $x$.

The conclusion is:

$$
\lambda^{-1}\bullet \xi \in A(x-\xi).
$$

Since $\xi=x-y$, we have $x-\xi=y$. Thus the conclusion says

$$
\lambda^{-1}\bullet (x-y) \in A(y),
$$

or equivalently, after multiplying by the nonzero scalar $\lambda$,

$$
x-y \in \lambda \bullet A(y).
$$

So the theorem says that membership $y \in J_{\lambda A}(x)$ is equivalent to the statement that the displacement $x-y$, rescaled by $\lambda^{-1}$, belongs to $A(y)$. This is exactly the usual resolvent relation $x \in y+\lambda A(y)$ rearranged.

## Lean proof
```lean
by
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hy
  dsimp [SetValuedOperator.identityAddScaled] at hy
  rcases hy with ⟨a, ha, hx_eq⟩
  have hxi' : xi = lam • a := by
    rw [hxi, ← hx_eq]
    abel
  have ha_eq : lam⁻¹ • xi = a := by
    rw [hxi']
    calc
      lam⁻¹ • (lam • a) = (lam⁻¹ * lam) • a := by rw [mul_smul]
      _ = a := by
        simp [hlam]
  have hxy : x - xi = y := by
    rw [hxi]
    abel
  rw [hxy]
  rw [ha_eq]
  exact ha
```

## Proof explanation
The proof begins by applying the cited result `SetValuedOperator.mem_resolvent_smul_iff`, which states that for a set-valued operator $A$, a scalar $\rho$, and points $x,y$,

$$
y \in J_{\rho A}(x) \quad\Longleftrightarrow\quad
x \in A.\operatorname{identityAddScaled}(\rho)(y).
$$

The proof specializes this to $\rho=\lambda$. Thus the hypothesis `hy : y ∈ J[(lam • A)] x` is rewritten as

$$
x \in A.\operatorname{identityAddScaled}(\lambda)(y).
$$

Next, the proof unfolds the definition of `SetValuedOperator.identityAddScaled`. By definition,

$$
A.\operatorname{identityAddScaled}(\lambda)(y)
=
\{\,y+\lambda\bullet a \mid a \in A(y)\,\}.
$$

So after `dsimp`, the hypothesis says that $x$ belongs to this set. The tactic `rcases` then unpacks the existential witness. It produces an element $a$, a proof `ha : a ∈ A y`, and an equality `hx_eq` expressing that $x$ is the corresponding element of the set, namely, up to orientation,

$$
x = y+\lambda\bullet a.
$$

The proof then defines `hxi' : xi = lam • a`. From $\xi=x-y$ and $x=y+\lambda\bullet a$, it follows that

$$
\xi = (y+\lambda\bullet a)-y = \lambda\bullet a.
$$

The Lean proof obtains this by rewriting with `hxi` and the equality `hx_eq`, then using `abel`, which normalizes expressions in an additive commutative group and cancels $y$.

Next, the proof defines `ha_eq : lam⁻¹ • xi = a`. Using $\xi=\lambda\bullet a$, the goal becomes

$$
\lambda^{-1}\bullet(\lambda\bullet a)=a.
$$

The proof rewrites the left-hand side using the scalar multiplication identity `mul_smul`, which encodes compatibility of scalar multiplication, in the form

$$
\lambda^{-1}\bullet(\lambda\bullet a)
=
(\lambda^{-1}\lambda)\bullet a.
$$

Then `simp [hlam]` simplifies $\lambda^{-1}\lambda$ to $1$ using the hypothesis $\lambda\neq 0$, and simplifies $1\bullet a$ to $a$. Hence

$$
\lambda^{-1}\bullet \xi = a.
$$

The proof also establishes `hxy : x - xi = y`. Since $\xi=x-y$, we have

$$
x-\xi=x-(x-y)=y.
$$

Again, this is proved by rewriting with `hxi` and using `abel`.

Finally, the goal is

$$
\lambda^{-1}\bullet \xi \in A(x-\xi).
$$

The rewrite `rw [hxy]` replaces $x-\xi$ by $y$, and the rewrite `rw [ha_eq]` replaces $\lambda^{-1}\bullet \xi$ by $a$. The goal therefore becomes

$$
a \in A(y).
$$

This is exactly the hypothesis `ha` obtained from the resolvent membership. The command `exact ha` closes the proof by using that hypothesis directly.

