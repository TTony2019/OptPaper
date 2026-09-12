## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/cor_3.lean`

## Lean statement
```lean
theorem cor_5_1 (C : Set H) (hC_closed : IsClosed C) (hC_conv : Convex ℝ C)
    (hC_polyhedron : ConvexPolyhedron C) (hC_bounded : Bornology.IsBounded C)
    (hC_int : (0 : H) ∈ interior C) (A0 : H → H)
    (hA0_max_mono : IsMaximalMonotone
      (SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => A0 x.1)))
    (hA0_zero : Filter.Tendsto A0 (𝓝 (0 : H)) (𝓝 (0 : H)))
    (A : SetValuedOperator H H) (hA : ∀ x, A x =
      {v | ∃ u ∈ subderivative (supportFunction C) x,
        ∃ w ∈ SetValuedOperator.ofFunction Set.univ
          (fun x : (Set.univ : Set H) => A0 x.1) x, v = u + w})
    (hA_max : IsMaximalMonotone A) (hA_dom : A.dom = Set.univ)
    (f : H → ℝ) (hf_conv : ConvexOn ℝ Set.univ f) (hf_C1 : ContDiff ℝ 1 f) (hinf : ∃ m, ∀ x, f x ≥ m)
    (B : SetValuedOperator H H) (hB_eq_grad : B =
      SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, lam n > 0) (hlam_nondec : ∀ n, lam n ≤ lam (n+1))
    (x : ℕ → H) (halg : AlgorithmA A B x lam) (xInf : H) (hxInf : Tendsto x atTop (𝓝 xInf)) :
    ∃ (n_star : ℕ), ∀ n ≥ n_star, x (n+1) - x n ∈ normalCone C (-gradient f xInf)
```

## Statement explanation
The theorem `cor_5_1` is a finite-time activation statement for an inertial proximal algorithm with dry friction, in an ambient real inner-product space $H$. It assumes that one has:

- A set $C\subseteq H$ that is closed, convex, a convex polyhedron, bounded, and contains the origin in its interior: $0\in \operatorname{int} C$. The polyhedron condition means concretely that there are finitely many vectors $a_i\in H$ and real numbers $b_i$ such that

  $$
  C=\{x\in H:\langle a_i,x\rangle\le b_i\ \text{for all }i\}.
  $$

- A single-valued map $A0:H\to H$. Its associated singleton-valued operator $x\mapsto\{A0(x)\}$ is assumed maximal monotone. Also, $A0$ has limit $0$ at $0$, i.e.

  $$
  A0(x)\to 0 \quad\text{as } x\to 0.
  $$

- A set-valued operator $A:H\to 2^H$ satisfying, for every $x\in H$,

  $$
  A(x)=\{\,u+A0(x): u\in \partial\sigma_C(x)\,\},
  $$

  where $\sigma_C$ is the support function of $C$,

  $$
  \sigma_C(x)=\sup_{z\in C}\langle z,x\rangle,
  $$

  and $\partial\sigma_C(x)$ is its subderivative:

  $$
  \partial\sigma_C(x)=\{\,v\in H:\forall y\in H,\ \sigma_C(y)\ge \sigma_C(x)+\langle v,y-x\rangle\,\}.
  $$

  Thus $A$ is the sum of the subdifferential operator of the support function of $C$ and the single-valued perturbation $A0$. The operator $A$ is also assumed maximal monotone and to have domain all of $H$.

- A function $f:H\to\mathbb R$ that is convex on all of $H$, continuously differentiable, and bounded below: there exists $m$ such that $f(x)\ge m$ for all $x$.

- An operator $B$ that is exactly the gradient operator of $f$:

  $$
  B(x)=\{\nabla f(x)\}
  $$

  for every $x\in H$.

- A sequence of step sizes $\lambda:\mathbb N\to\mathbb R$ satisfying $\lambda_n>0$ and $\lambda_n\le \lambda_{n+1}$ for all $n$.

- A sequence $x:\mathbb N\to H$ that is an Algorithm A sequence for $A$, $B$, and $\lambda$, and that converges to some point $x_\infty$:

  $$
  x_n\to x_\infty \quad\text{as } n\to\infty.
  $$

The conclusion is that there exists an index $n_\star\in\mathbb N$ such that for every $n\ge n_\star$,

$$
x_{n+1}-x_n \in N_C\bigl(-\nabla f(x_\infty)\bigr),
$$

where $N_C(y)$ denotes the normal cone to $C$ at $y$. In words, after finitely many iterations, every increment of the algorithm lies in the normal cone to the polyhedral set $C$ evaluated at the limiting point $-\nabla f(x_\infty)$. This is an eventual inclusion result, not a statement that the increments converge by themselves; convergence of $x_n$ to $x_\infty$ is an assumption.

## Lean proof
```lean
by
  have hC0 : (0 : H) ∈ C := interior_subset hC_int
  have hA0_at_zero : A0 (0 : H) = 0 := cor51_A0_zero_of_tendsto A0 hA0_zero
  have hA_zero : A (0 : H) = C :=
    cor51_A_zero_eq_C C hC_polyhedron hC0 A0 hA0_at_zero A hA
  have hAzero_int : (0 : H) ∈ interior (A (0 : H)) := by
    simpa [hA_zero] using hC_int
  have hpoly_A0 : ConvexPolyhedron (A (0 : H)) := by
    simpa [hA_zero] using hC_polyhedron
  have hcondition : Filter.Tendsto
      (fun z : H => excess (A z) (subderivative (supportFunction (A (0 : H))) z))
      (𝓝 (0 : H)) (𝓝 0) :=
    cor51_excess_condition C A0 A hA hA_dom hA_zero hA0_zero
  rcases prop_5_1 A B hA_max hA_dom hAzero_int hpoly_A0 hcondition f hf_conv hf_C1
      hinf hB_eq_grad lam hlam_pos hlam_nondec x halg xInf hxInf with ⟨n_star, hn⟩
  refine ⟨n_star, ?_⟩
  intro n hn_ge
  have hmem := hn n hn_ge
  simpa [hA_zero] using hmem
```

## Proof explanation
The proof reduces the corollary to the cited result `prop_5_1`. It first identifies the value $A(0)$ with $C$, then verifies the hypotheses of `prop_5_1` for $A$, and finally rewrites $A(0)$ back to $C$.

1. The proof begins with

   ```lean
   have hC0 : (0 : H) ∈ C := interior_subset hC_int
   ```

   The hypothesis `hC_int` says $0\in\operatorname{int} C$, and `interior_subset` says that the interior of a set is contained in the set. Hence $0\in C$. This is later needed for `cor51_A_zero_eq_C`.

2. Next,

   ```lean
   have hA0_at_zero : A0 (0 : H) = 0 := cor51_A0_zero_of_tendsto A0 hA0_zero
   ```

   The cited result `cor51_A0_zero_of_tendsto` states that if $A0:H\to H$ satisfies $A0(x)\to0$ as $x\to0$, then $A0(0)=0$. Thus the perturbation term vanishes at the origin. This is one of the hypotheses needed to identify $A(0)$ with $C$.

3. The proof then establishes

   ```lean
   have hA_zero : A (0 : H) = C := cor51_A_zero_eq_C C hC_polyhedron hC0 A0 hA0_at_zero A hA
   ```

   The cited result `cor51_A_zero_eq_C` says: if $C$ is a convex polyhedron, $0\in C$, $A0(0)=0$, and $A$ has the sum decomposition

   $$
   A(x)=\{\,u+A0(x):u\in\partial\sigma_C(x)\,\},
   $$

   then $A(0)=C$. So the value of the composite operator at the origin is exactly the set $C$. This is the key identification used throughout the rest of the proof.

4. From this equality and the original interior condition, the proof obtains

   ```lean
   have hAzero_int : (0 : H) ∈ interior (A (0 : H)) := by simpa [hA_zero] using hC_int
   ```

   Since $A(0)=C$, the fact $0\in\operatorname{int} C$ rewrites to $0\in\operatorname{int}(A(0))$. This is one of the hypotheses required by `prop_5_1`.

5. Similarly,

   ```lean
   have hpoly_A0 : ConvexPolyhedron (A (0 : H)) := by simpa [hA_zero] using hC_polyhedron
   ```

   Since $A(0)=C$, the assumption that $C$ is a convex polyhedron becomes the statement that $A(0)$ is a convex polyhedron. This is again needed for `prop_5_1`.

6. The proof next applies `cor51_excess_condition`:

   ```lean
   have hcondition : ... := cor51_excess_condition C A0 A hA hA_dom hA_zero hA0_zero
   ```

   The cited result `cor51_excess_condition` states that, under the sum decomposition for $A$, full domain $A.\operatorname{dom}=H$, the equality $A(0)=C$, and the condition $A0(x)\to0$ as $x\to0$, the excess

   $$
   \operatorname{excess}\!\left(A(z),\ \partial\sigma_{A(0)}(z)\right)
   $$

   tends to $0$ as $z\to0$. Here the `excess` is the one-sided quantity

   $$
   \operatorname{excess}(S,T)=\sup_{s\in S}\operatorname{dist}(s,T).
   $$

   Thus the conclusion says that, near $0$, every point of $A(z)$ is arbitrarily close to the subdifferential of the support function of $A(0)$ at $z$. This is exactly the quantitative `h_condition` hypothesis required by `prop_5_1`.

7. The proof then invokes `prop_5_1`:

   ```lean
   rcases prop_5_1 A B hA_max hA_dom hAzero_int hpoly_A0 hcondition f hf_conv hf_C1 hinf hB_eq_grad lam hlam_pos hlam_nondec x halg xInf hxInf with ⟨ n_star, hn⟩
   ```

   The cited theorem `prop_5_1` says, specialized to the current variables: if $A$ is maximal monotone, has full domain, $0\in\operatorname{int}(A(0))$, $A(0)$ is a convex polyhedron, the excess condition above holds, $f$ is convex, $C^1$, and bounded below, $B$ is the gradient operator of $f$, the step sizes $\lambda_n$ are positive and nondecreasing, $x$ is an Algorithm A sequence for $A,B,\lambda$, and $x_n\to x_\infty$, then there exists $n_\star$ such that for all $n\ge n_\star$,

   $$
   x_{n+1}-x_n \in N_{A(0)}\bigl(-\nabla f(x_\infty)\bigr).
   $$

   The `rcases` command eliminates the existential quantifier, giving the witness `n_star` and the property `hn`.

8. The proof then returns the same witness:

   ```lean
   refine ⟨ n_star, ?_⟩
   ```

   This reduces the goal to proving, for all $n\ge n_\star$, the desired membership.

9. It introduces an arbitrary index satisfying that inequality:

   ```lean
   intro n hn_ge
   ```

   Then

   ```lean
   have hmem := hn n hn_ge
   ```

   gives the membership

   $$
   x_{n+1}-x_n \in N_{A(0)}\bigl(-\nabla f(x_\infty)\bigr).
   $$

10. Finally,

    ```lean
    simpa [hA_zero] using hmem
    ```

    rewrites $A(0)$ to $C$ using the equality `hA_zero : A(0)=C`. The membership becomes

    $$
    x_{n+1}-x_n \in N_C\bigl(-\nabla f(x_\infty)\bigr),
    $$

    which is precisely the conclusion of `cor_5_1`.

The proof does not explicitly invoke the hypotheses `hC_closed`, `hC_conv`, `hC_bounded`, or `hA0_max_mono`; they remain assumptions of the corollary, but the reduction above passes only the needed polyhedral, interior, monotonicity, domain, and excess conditions to the cited results.

