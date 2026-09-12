## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/thm_1.lean`

## Lean statement
```lean
theorem theorem_3_1_convergence {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective)
    (hH_KL : ProductKLFunction (HFunction P (A.M2 nu mu))) :
    Summable (fun n : Nat => ‖A.x n - A.p n‖) ∧
      Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖) ∧
      ∃ x : EuclideanSpace m,
        x ∈ criticalPoints P.objective ∧
          Tendsto A.x atTop (nhds x) ∧ Tendsto A.p atTop (nhds x)
```

## Statement explanation
The declaration `theorem_3_1_convergence` is a convergence theorem for an inertial Tseng-type proximal algorithm. Let $m\in\mathbb N$, let $P$ be problem data in $m$ dimensions, let $A$ be algorithm data for $P$, and let $\nu,\mu\in\mathbb R$. Write

```math
x_n=A.x\,n,\qquad p_n=A.p\,n,\qquad M_1=A.M1\,\nu\,\mu,\qquad M_2=A.M2\,\nu\,\mu,
```

and write $f=P.objective$. The hypothesis `hchosen : chosenAsInLemma33 A nu mu` is unpacked in the proof as $0\lt \nu$, $0\lt \mu$, a further strict condition `hstrict`, and the inequality $M_2\lt M_1$. The hypothesis `hcoercive : CoerciveEReal P.objective` says that the objective is coercive as an extended-real-valued function. The hypothesis

$$
\text{`hH\_KL`}:\ \text{`ProductKLFunction`}\bigl(\text{`HFunction`}\ P\ M_2\bigr)
$$

says that the product-space Kurdyka–Łojasiewicz certificate holds for the Lyapunov function

$$
H(z)=\text{`HFunction`}\ P\ M_2\ z
  =\text{`objectiveWithQuadratic`}\ P\ M_2\ z.1\ z.2.
$$

Thus $H$ is the objective plus a quadratic term with coefficient $M_2$, evaluated on a pair $z$.

The conclusion is a conjunction of three statements:

```math
\sum_n \|x_n-p_n\|<\infty,
```

```math
\sum_n \|x_{n+1}-x_n\|<\infty,
```

and there exists $x\in\mathbb R^m$ such that

$$
x\in \text{`criticalPoints`}\ P.objective,
\qquad
x_n\to x,
\qquad
p_n\to x.
$$

Here $x\in \text{`criticalPoints`}\ P.objective$ means

$$
0\in \partial f(x),
$$

where $\partial f(x)$ is the limiting subdifferential of the objective at $x$. In ordinary language, under the chosen parameters, coercivity, and product-space KL hypothesis, the residuals $x_n-p_n$ and the successive differences $x_{n+1}-x_n$ are absolutely summable, and both sequences $x_n$ and $p_n$ converge to the same critical point of the objective.

## Lean proof
```lean
by
  rcases hchosen with ⟨hnu, hmu, hstrict, hM2ltM1⟩
  let M1 : Real := A.M1 nu mu
  let M2 : Real := A.M2 nu mu
  let D : Real := M1 - M2
  have hDpos : 0 < D := by
    dsimp [D, M1, M2]
    nlinarith [hM2ltM1]
  have hKLOrbit : KLOrbitPackage A nu mu := by
    exact hH_KL P A nu mu rfl
  have h37 :=
    lemma_3_7_pair_cluster_points A nu mu
      (by exact ⟨hnu, hmu, hstrict, hM2ltM1⟩) hcoercive
  rcases h37 with
    ⟨hΩne, hΩsub, hHcrit_eq_diag, hdistΩ, hΩcompact, hΩconn, hHconst⟩
  let Omega : Set (EuclideanSpace m × EuclideanSpace m) := omega (pairSequence A)
  have hOmega_ne : Omega.Nonempty := by
    simpa [Omega] using hΩne
  have hOmega_ne_for_KL : Omega.Nonempty := hOmega_ne
  rcases hOmega_ne with ⟨zstar, hzstarOmega⟩
  have hzstar : zstar ∈ omega (pairSequence A) := by
    simpa [Omega] using hzstarOmega
  have hzcrit : zstar.1 ∈ criticalPoints P.objective := by
    have hzH := hΩsub hzstar
    have hzdiag : zstar ∈ diagonalCriticalSet P := by
      rwa [← hHcrit_eq_diag]
    exact hzdiag.2
  have hOmega_compact : IsCompact Omega := by
    simpa [Omega] using hΩcompact
  have hOmega_const : ∃ c : EReal, ∀ z ∈ Omega, HFunction P (A.M2 nu mu) z = c := by
    simpa [Omega] using hHconst
  have hKL_window := hKLOrbit Omega hOmega_ne_for_KL hOmega_compact hOmega_const zstar hzstarOmega
  rcases hKL_window with ⟨epsilon, eta, phi, heps, heta, hphi, hKL⟩
  let Hreal : Nat -> Real := fun n => (HFunction P M2 (pairSequence A n)).toReal
  have hdescent_real :
      ∀ n, 1 <= n ->
        D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 <= Hreal n - Hreal (n + 1) := by
    intro n hn
    have h := lyapunov_descent_real A nu mu hnu hmu n hn
    simpa [Hreal, D, M1, M2] using h
  have hH_mono_tail :
      ∀ n, 1 <= n -> Hreal (n + 1) <= Hreal n := by
    intro n hn
    have hdrop := hdescent_real n hn
    have hnonneg : 0 <= D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 :=
      mul_nonneg (le_of_lt hDpos) (sq_nonneg _)
    nlinarith
  have hxp_sum : Summable (fun n : Nat => ‖A.x n - A.p n‖) :=
    xp_summable_of_KL_orbit A nu mu
      (by exact ⟨hnu, hmu, hstrict, hM2ltM1⟩) hcoercive hKLOrbit
  have hxinc_sum : Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖) :=
    x_increment_summable_of_xp_summable A hxp_sum
  rcases tendsto_of_summable_successive_norm A.x hxinc_sum with ⟨x, hxlim⟩
  have hplim : Tendsto A.p atTop (nhds x) :=
    p_tendsto_of_x_tendsto_xp_summable A hxlim hxp_sum
  have hxcrit : x ∈ criticalPoints P.objective := by
    have hpair : (x, x) ∈ omega (pairSequence A) :=
      pair_limit_mem_omega A hplim hxlim
    have hHcrit := hΩsub hpair
    have hdiag : (x, x) ∈ diagonalCriticalSet P := by
      rwa [hHcrit_eq_diag] at hHcrit
    exact hdiag.2
  exact ⟨hxp_sum, hxinc_sum, x, hxcrit, hxlim, hplim⟩
```

## Proof explanation
The proof begins by unpacking the hypothesis `hchosen`. The line
```lean
rcases hchosen with ⟨hnu, hmu, hstrict, hM2ltM1⟩
```
destructs the package into $0\lt \nu$, $0\lt \mu$, the additional strict condition `hstrict`, and the inequality $M_2\lt M_1$. The proof then defines

```math
M_1=A.M1\,\nu\,\mu,\qquad M_2=A.M2\,\nu\,\mu,\qquad D=M_1-M_2.
```

Using `dsimp [D, M1, M2]` to unfold these definitions and `nlinarith [hM2ltM1]` to do the arithmetic comparison, it proves

$$
0<D.
$$

Next, the proof obtains the orbit KL package. The hypothesis `hH_KL` is a product-space KL certificate for $H$. Applying it as `hH_KL P A nu mu rfl` specializes it to the current problem, algorithm, and parameters, and the `rfl` discharges the required definitional identification of the Lyapunov function. The result is

$$
\text{`KLOrbitPackage`}\ A\ \nu\ \mu.
$$

Concretely, this package says that for every nonempty compact set $\Omega$ of pairs on which $H$ is constant, and for every $z^*\in\Omega$, there exist $\epsilon\gt 0$, $\eta\gt 0$, and a desingularizing function $\phi$ such that, for every $n\ge2$, if

$$
\mathrm{infDist}\bigl((p_n,x_n),\Omega\bigr)<\epsilon
$$

and

$$
H(z^*)<H(p_n,x_n)<H(z^*)+\eta,
$$

then a KL inequality controls the subgradient estimate by the drop in $H$. This is the form of the KL condition used later by the summability theorem.

The proof then applies `lemma_3_7_pair_cluster_points` to $A,\nu,\mu$, the reconstructed hypothesis `chosenAsInLemma33`, and coercivity of the objective. The lemma returns several facts about

$$
\omega\bigl(\text{`pairSequence`}\ A\bigr),
$$

where

$$
\text{`pairSequence`}\ A\ n=(p_n,x_n),
$$

and $\omega$ denotes the set of sequential cluster points. The facts used are: this $\omega$-set is nonempty; it is contained in `HCriticalSet P M2`; `HCriticalSet P M2` is equal to `diagonalCriticalSet P`; it is compact; and $H$ is constant on it. Here

$$
\text{`diagonalCriticalSet`}\ P
  =\{z\mid z.1=z.2\ \text{and}\ z.1\in \text{`criticalPoints`}\ P.objective\}.
$$

The lemma also gives that the distance from the pair sequence to this $\omega$-set tends to $0$ and that the $\omega$-set is connected, but those facts are not used in the final assembly.

The proof abbreviates

$$
\Omega=\omega\bigl(\text{`pairSequence`}\ A\bigr).
$$

It transports the nonemptiness, compactness, and constancy of $H$ from the lemma to this notation. Since $\Omega$ is nonempty, the proof chooses some $z^*\in\Omega$. It then checks that $z^*_1\in \text{`criticalPoints`}\ P.objective$: because$z^*\in\Omega$and$\Omega\subseteq \text{`HCriticalSet`}\ P\ M_2$, the point$z^*$ lies in `HCriticalSet P M2`; using the equality `HCriticalSet P M2 = diagonalCriticalSet P`, it follows that $z^*\in\text{`diagonalCriticalSet`}\ P$, and the second component of that membership says$z^*_1$ is a critical point of the objective.

The proof then applies the orbit KL package to $\Omega$ and $z^*$. Since $\Omega$ is nonempty, compact, and a set on which $H$ is constant, the KL package supplies $\epsilon,\eta,\phi$ satisfying $\epsilon\gt 0$, $\eta\gt 0$, the desingularizing condition on $\phi$, and the KL inequality along the orbit. This local KL window is recorded, although the final summability conclusion is obtained from the globally available `KLOrbitPackage` rather than directly from this local window.

Next, the proof defines the real-valued Lyapunov values

$$
H_n^{\mathbb R}=\bigl(H(p_n,x_n)\bigr)_{\mathbb R}.
$$

It invokes `lyapunov_descent_real A nu mu hnu hmu n hn` for $n\ge1$. The statement of that theorem is truncated in the provided context, but in the use made here it supplies the descent inequality

```math
D\,\|x_{n+1}-p_{n+1}\|^2\le H_n^{\mathbb R}-H_{n+1}^{\mathbb R}.
```

The command `simpa [Hreal, D, M1, M2]` rewrites the theorem’s conclusion into these local notations. Since $0\lt D$ and $`\|x_{n+1}-p_{n+1}\|^2\ge0`$, the left-hand side is nonnegative. Thus

$$
H_{n+1}^{\mathbb R}\le H_n^{\mathbb R}
$$

for every $n\ge1$. This monotonicity of the real Lyapunov values is proved by `nlinarith` from the descent inequality and nonnegativity. It is recorded here, although the final proof does not directly use it afterward.

The central summability step is the call

$$
\text{`xp\_summable\_of\_KL\_orbit`}\ A\ \nu\ \mu\ \text{reconstructed chosen}\ \text{`hcoercive`}\ \text{`hKLOrbit`}.
$$

Its hypotheses are precisely the reconstructed `chosenAsInLemma33`, coercivity of the objective, and the orbit KL package. Its conclusion is

```math
\sum_n \|x_n-p_n\|<\infty.
```

This is the first conjunct of the theorem. Then the proof applies

$$
\text{`x\_increment\_summable\_of\_xp\_summable`}\ A\ \text{`hxp\_sum`},
$$

which converts summability of the residuals $x_n-p_n$ into summability of the successive increments:

```math
\sum_n \|x_{n+1}-x_n\|<\infty.
```

This is the second conjunct.

With the successive increments of $x_n$ summable, the proof applies

$$
\text{`tendsto\_of\_summable\_successive\_norm`}\ A.x\ \text{`hxinc\_sum`}.
$$

Mathematically, this says that if $`\sum_n\|u_{n+1}-u_n\|<\infty`$, then$u_n$is Cauchy and therefore converges in Euclidean space. Hence there exists some$x\in\mathbb R^m$ such that

$$
x_n\to x.
$$

The proof then applies

$$
\text{`p\_tendsto\_of\_x\_tendsto\_xp\_summable`}\ A\ \text{`hxlim`}\ \text{`hxp\_sum`}.
$$

Since $x_n\to x$ and $`\sum_n\|x_n-p_n\|<\infty`$, the residual$x_n-p_n\to0$, so$p_n\to x$ as well.

It remains to prove that this common limit $x$ is a critical point. The proof applies

$$
\text{`pair\_limit\_mem\_omega`}\ A\ \text{`hplim`}\ \text{`hxlim`},
$$

which, from $p_n\to x$ and $x_n\to x$, gives

$$
(x,x)\in\omega\bigl(\text{`pairSequence`}\ A\bigr).
$$

Then, because $\omega\bigl(\text{`pairSequence`}\ A\bigr)\subseteq \text{`HCriticalSet`}\ P\ M_2$, the pair$(x,x)$ lies in `HCriticalSet P M2`. Rewriting this membership by the equality

$$
\text{`HCriticalSet`}\ P\ M_2=\text{`diagonalCriticalSet`}\ P
$$

places $(x,x)$ in the diagonal critical set. By the definition of the diagonal critical set, this means that the two coordinates are equal, which is automatic for $(x,x)$, and that the first coordinate $x$ lies in $\text{`criticalPoints`}\ P.objective$. Thus

$$
x\in\text{`criticalPoints`}\ P.objective,
$$

i.e. $0\in\partial f(x)$.

Finally, the proof assembles the three required conclusions:

```math
\sum_n\|x_n-p_n\|<\infty,
\qquad
\sum_n\|x_{n+1}-x_n\|<\infty,
```

and the existence of $x$ with $x\in\text{`criticalPoints`}\ P.objective$,$x_n\to x$, and$p_n\to x$.

