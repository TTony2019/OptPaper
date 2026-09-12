## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_8.lean`

## Lean statement
```lean
noncomputable def liapunovF {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (hk : 1 ≤ k) : ℝ :=
  let α := (1 + b * lam) / (2 * lam ^ 2)
  let δ := (2 + (b - a) * lam) / (2 * lam ^ 2)
  let hk' : 2 ≤ k + 1 := by omega
  let Gk : ℝ := auxiliaryG u y a b lam q (k + 1) hk'
  (a + b) / (2 * lam) * ‖u k - q‖ ^ 2 -
    (1 / lam + b) * Gk -
    δ * ∑ i ∈ (Finset.Icc 2 k).attach,
      ‖velocity u i (by
        have hi : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
        omega)‖ ^ 2 +
    2 * α * inner ℝ (velocity u (k + 1) (by omega)) (u k - q)
```

## Statement explanation
The declaration defines a noncomputable real-valued function named `liapunovF`. Its mathematical inputs are a real inner product space $H$, two sequences $u:\mathbb N\to H$ and $y:\mathbb N\to H$, real parameters $a,b,\lambda$, a point $q\in H$, a natural number $k:\mathbb N$, and a proof $hk:1\le k$. The typeclass assumptions `NormedAddCommGroup H` and `InnerProductSpace ℝ H` mean that $H$ carries its real inner product and the induced norm. There is no propositional conclusion: this is a definition, not a theorem.

Inside the definition, two local real constants are introduced:

$$
\alpha=\frac{1+b\lambda}{2\lambda^{2}},
\qquad
\delta=\frac{2+(b-a)\lambda}{2\lambda^{2}}.
$$

Also, from the hypothesis $1\le k$, the definition obtains the proof $hk':2\le k+1$. This proof is needed because both `auxiliaryG` and `velocity` are called at index $k+1$, and the visible call pattern shows that they require an index at least $2$. The definition then sets

$$
G_k=\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,k+1),
$$

where the proof $hk'$ is supplied as the final argument. Since no definition of `auxiliaryG` is provided here, the only mathematical information visible from the source is that $G_k$ is a real number depending on $u,y,a,b,\lambda,q,k+1$ and on the proof $2\le k+1$. Its internal formula is not determined from the given source.

The value of `liapunovF` at these arguments is the real number

$$
\begin{aligned}
&\mathrm{liapunovF}(u,y,a,b,\lambda,q,k,hk)\\
&=
\frac{a+b}{2\lambda}\|u_k-q\|^{2}
-\left(\frac1\lambda+b\right)G_k
-\delta\sum_{i=2}^{k}\|\mathrm{velocity}(u,i)\|^{2}
+2\alpha\left\langle \mathrm{velocity}(u,k+1),\,u_k-q\right\rangle_{\mathbb R}.
\end{aligned}
$$

Here $\|u_k-q\|^{2}$ is the squared distance from the $k$-th term of $u$ to $q$. The sum runs over the finite set $i\in\{2,\dots,k\}$; if $k<2$, the sum is empty. The expression also contains the squared norms of the vectors returned by `velocity` at the indices $i$ from $2$ to $k$, and a final real inner-product term between the velocity at index $k+1$ and the vector $u_k-q$. There is no assumption that $\lambda\ne0$; in Lean the divisions by $\lambda$ and $\lambda^2$ are total, so the formula is well-formed even when $\lambda=0$. Mathematically, the declaration packages a real-valued Lyapunov-type expression attached to the sequences and parameters, but it does not assert any property of that expression.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration. It is a `def`, so the body is a defining term rather than a proof of a theorem. The only proof-producing steps inside the body are the local inequality proofs needed to call functions whose arguments include an index-at-least-two condition.

The `noncomputable` marker means that Lean does not generate executable code for the definition. The two `let` bindings for $\alpha$ and $\delta$ are local abbreviations: they introduce the real constants

$$
\alpha=\frac{1+b\lambda}{2\lambda^{2}},
\qquad
\delta=\frac{2+(b-a)\lambda}{2\lambda^{2}},
$$

which are then used in the final expression.

The local binding

$$
hk':2\le k+1
$$

is proved by the tactic `omega`. The tactic `omega` decides goals in linear integer arithmetic. Here it uses the hypothesis $hk:1\le k$ to derive $2\le k+1$. This proof is necessary because `auxiliaryG` is called at index $k+1$ with an argument requiring $2\le k+1$, and the same inequality is later needed for the `velocity` call at $k+1$.

The binding

$$
G_k:=\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,k+1,hk')
$$

stores the real number returned by `auxiliaryG`. Because the definition of `auxiliaryG` is not available in the provided source, one can only say from the visible call that $G_k$ is a real number depending on the two sequences, the real parameters, the point $q$, the index $k+1$, and the proof $2\le k+1$. This number enters the final formula through the term

$$
-\left(\frac1\lambda+b\right)G_k.
$$

The summation term is

$$
\sum_{i\in(\mathrm{Finset.Icc}\,2\,k).\mathrm{attach}}\|\mathrm{velocity}(u,i)\|^{2}.
$$

The finset $\mathrm{Finset.Icc}\,2\,k$ is the finite set of natural numbers $i$ satisfying $2\le i\le k$. The operation `attach` tags each element with a proof of its membership in that interval. For each such tagged element $i$, the proof `i.property` says that the underlying natural number lies in $2\le i\le k$. The call

$$
\mathrm{Finset.mem\_Icc.mp}(i.property)
$$

turns this membership statement into the conjunction

$$
2\le i \quad\text{and}\quad i\le k.
$$

The projection `.1` extracts the lower bound $2\le i$. That lower bound is exactly what the `velocity` function requires in order to be called at index $i$. The tactic `omega` then closes the required inequality goal $2\le i$. Thus each summand is the squared norm of the velocity vector at an index $i$ between $2$ and $k$. This sum is multiplied by $-\delta$ in the final expression.

The last term is

$$
2\alpha\left\langle \mathrm{velocity}(u,k+1),\,u_k-q\right\rangle_{\mathbb R}.
$$

The proof argument to `velocity u (k+1)` is again produced by `omega`, using $hk:1\le k$ to prove $2\le k+1$. The inner product $\langle\cdot,\cdot\rangle_{\mathbb R}$ is the real inner product on $H$, and its first argument is the velocity vector at index $k+1$, while its second argument is $u_k-q$.

Finally, the whole expression is assembled in $\mathbb R$ using subtraction and addition:

$$
\frac{a+b}{2\lambda}\|u_k-q\|^{2}
-\left(\frac1\lambda+b\right)G_k
-\delta\sum_{i=2}^{k}\|\mathrm{velocity}(u,i)\|^{2}
+2\alpha\left\langle \mathrm{velocity}(u,k+1),\,u_k-q\right\rangle_{\mathbb R}.
$$

No named local theorem or lemma is invoked in a separate proof. The only proof tactic used is `omega`, and the tactics `intro`, `rw`, `simp`, `exact`, and `linarith` do not occur in the definition body.

