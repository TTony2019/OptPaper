## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/rem_1.lean`

## Lean statement
```lean
theorem remark15 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (Ψ : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ Ψ gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi Ψ gradPsi a b lam u y)
    (hconvex : Convex ℝ (ERealFunction.epigraph fun x ↦ (Ψ x : EReal)))
    (hS : (Optimization.argminSet Θ).Nonempty) :
    ∃ q ∈ Optimization.argminSet Θ, Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop
      (nhds (toWeakSpace ℝ H q))
```

## Statement explanation
`remark15` is a theorem about a real Hilbert space $H$. The typeclass assumptions say that $H$ is a normed additive commutative group, an inner product space over $\mathbb R$, and complete; thus $H$ is a real Hilbert space. The functions and parameters are:

- $\phi : H \to \mathrm{EReal}$ and $\Theta : H \to \mathrm{EReal}$, extended-real-valued functions on $H$;
- $\Psi : H \to \mathbb R$, a real-valued function;
- $\mathrm{gradPsi} : H \to H$, a map on $H$;
- $a,b,\lambda,L_{\psi} \in \mathbb R$, real parameters;
- $u,y : \mathbb N \to H$, two sequences in $H$.

The hypotheses are:

- $hH$: the statement `IFBHypothesis phi Θ Ψ gradPsi a b lam Lpsi`, expressing that the data satisfy the standing hypotheses of the inertial forward-backward setting;
- $hIFB$: `IsIFBTrajectory phi Ψ gradPsi a b lam u y`, saying that $(u,y)$ is an inertial forward-backward trajectory for these data;
- $hconvex$: the epigraph of the extended-real-valued function $x \mapsto (\Psi(x):\mathrm{EReal})$ is convex over $\mathbb R$;
- $hS$: the minimizer set $\mathrm{argminSet}\Theta$ is nonempty.

The conclusion is that there exists a minimizer $q$ of $\Theta$ such that the sequence $u_k$ converges weakly to $q$ as $k\to\infty$. In Lean this is written using the canonical map to the weak space:

$$
\exists q \in \mathrm{argminSet}\Theta,\quad
\mathrm{Tendsto}\left(k\mapsto \mathrm{toWeakSpace}_{\mathbb R}H(u_k)\right)
\mathrm{atTop}
\left(\mathrm{nhds}\left(\mathrm{toWeakSpace}_{\mathbb R}H(q)\right)\right).
$$

Equivalently, $u_k \rightharpoonup q$ weakly in $H$, and $q$ minimizes $\Theta$.

## Lean proof
```lean
(theorem1 phi Θ Ψ gradPsi a b lam Lpsi u y hH hIFB).2.1
    ⟨hS, Or.inr (Or.inr (Or.inr hconvex))⟩
```

## Proof explanation
The proof is a single term. It invokes the previously established theorem `theorem1`, instantiating its parameter `psi` by the current function $\Psi$. Thus the hypotheses $hH$ and $hIFB$ of the present theorem exactly match the hypotheses required by `theorem1`.

The conclusion of `theorem1` is a conjunction with three main parts. Specialized to the current variables, it says first that

$$
\mathrm{Tendsto}\left(k\mapsto \Theta(u_k)\right)\mathrm{atTop}
\left(\mathrm{nhds}\left(\mathrm{sInf}(\mathrm{range}\Theta)\right)\right),
$$

so the values $\Theta(u_k)$ tend to the infimum of the range of $\Theta$. Second, it says that if $\mathrm{argminSet}\Theta$ is nonempty and at least one of four regularity alternatives holds, then there is a minimizer $q$ of $\Theta$ to which $u_k$ converges weakly. Third, it says that if $\mathrm{argminSet}\Theta$ is empty, then $\|u_k\|\to\infty$.

The four regularity alternatives in the middle conditional are:

1. $\mathrm{argminSet}\Theta$ is a singleton, so $\Theta$ has a unique minimizer;
2. $\phi$ is represented by a real-valued differentiable function whose derivative is given by an inner product with a gradient map that is weak-to-weak sequentially continuous;
3. $\mathrm{gradPsi}$ is weak-to-weak sequentially continuous;
4. the epigraph of the extended-real-valued function $x\mapsto(\Psi(x):\mathrm{EReal})$ is convex.

The proof uses the projection `.2.1`. Since the conclusion of `theorem1` is a conjunction, the `.2` projection selects the second main conjunct, and `.2.1` selects the first component of that second conjunct. That component is precisely the implication

$$
\left(
(\mathrm{argminSet}\Theta)\neq\emptyset \wedge P
\right)
\to
\exists q\in\mathrm{argminSet}\Theta,\quad
u_k \rightharpoonup q,
$$

where $P$ is the four-way disjunction above.

The proof then applies this implication to the pair

$$
\langle hS,\ \mathrm{Or.inr}(\mathrm{Or.inr}(\mathrm{Or.inr} hconvex))\rangle.
$$

The first component $hS$ proves that $\mathrm{argminSet}\Theta$ is nonempty. The second component is a proof of the disjunction $P$. Because Lean associates $\vee$ to the right, the disjunction has the form

$$
A \vee \bigl(B \vee (C \vee D)\bigr).
$$

The nested `Or.inr` applications select the fourth alternative $D$. Concretely, the first `Or.inr` discards $A$, the second discards $B$, and the third discards $C$, leaving $D$. Here $D$ is exactly

$$
\mathrm{Convex}_{\mathbb R}
\left(\mathrm{epigraph}\bigl(x\mapsto(\Psi(x):\mathrm{EReal})\bigr)\right),
$$

which is the hypothesis `hconvex`.

Thus the antecedent of the middle conditional from `theorem1` is satisfied. Applying that conditional yields exactly the desired conclusion: there exists $q\in\mathrm{argminSet}\Theta$ such that the images of $u_k$ under the canonical map to the weak space converge to the image of $q$. The first and third parts of `theorem1` are not used in this proof. There are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`; the argument is entirely term-level application, projection, pairing, and disjunction injection.

