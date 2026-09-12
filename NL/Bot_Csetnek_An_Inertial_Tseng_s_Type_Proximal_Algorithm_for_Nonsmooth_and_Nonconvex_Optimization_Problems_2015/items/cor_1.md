## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/cor_1.lean`

## Lean statement
```lean
theorem corollary_3_1_semialgebraic_convergence {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) (nu mu : Real)
    (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective)
    (hsemi : IsSemiAlgebraicEReal P.objective)
    (hsemi_to_KL : SemialgebraicToProductKL P.objective (A.M2 nu mu)) :
    Summable (fun n : Nat => ‖A.x n - A.p n‖) ∧
      Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖) ∧
      ∃ x : EuclideanSpace m,
        x ∈ criticalPoints P.objective ∧
          Tendsto A.x atTop (nhds x) ∧ Tendsto A.p atTop (nhds x)
```

## Statement explanation
Fix $m \in \mathbb{N}$, a problem-data object $P$ of dimension $m$, algorithm data $A$ for $P$, and real parameters $\nu,\mu$. The theorem is a convergence corollary. It assumes four hypotheses.

The hypothesis `chosenAsInLemma33 A nu mu` says that the parameters $\nu,\mu$ are chosen as specified in Lemma 3.3 for the algorithm $A$. The hypothesis `CoerciveEReal P.objective` says that the extended-real-valued objective function $P.\mathrm{objective}$ is coercive. The hypothesis `IsSemiAlgebraicEReal P.objective` says that this objective is semialgebraic in the extended-real sense. Finally, `SemialgebraicToProductKL P.objective (A.M2 nu mu)` is the bridge hypothesis relating the semialgebraic objective to the product KL condition for the scalar $A.M_2(\nu,\mu)$.

Under these assumptions, the conclusion consists of three assertions. First, the sequence

$$
n \mapsto \|A.x_n-A.p_n\|
$$

is summable; equivalently, the series

$$
\sum_{n\in\mathbb N}\|A.x_n-A.p_n\|
$$

converges. Second, the sequence

$$
n \mapsto \|A.x_{n+1}-A.x_n\|
$$

is summable. Third, there exists a point $x\in\mathbb R^m$ such that $x$ is a critical point of $P.\mathrm{objective}$, the sequence $A.x_n$ converges to $x$, and the sequence $A.p_n$ also converges to $x$. Thus the main iterates and the auxiliary sequence have finite total separation and finite total consecutive movement, and both converge to a common critical point of the objective.

## Lean proof
```lean
by
  have hH_KL : ProductKLFunction (HFunction P (A.M2 nu mu)) :=
    semialgebraic_objective_yields_productKL_HFunction A nu mu hsemi hsemi_to_KL
  exact theorem_3_1_convergence A nu mu hchosen hcoercive hH_KL
```

## Proof explanation
The proof uses one intermediate lemma and then the main convergence theorem. There are no `intro`, `rw`, `simp`, or `linarith` steps; the only proof commands used are `have` and `exact`.

First, the proof establishes the intermediate assertion

$$
\texttt{hH\_KL} : \texttt{ProductKLFunction }(\texttt{HFunction }P\,(A.M_2(\nu,\mu))).
$$

The term $\texttt{HFunction }P\,(A.M_2(\nu,\mu))$ denotes the product-space function on $\mathrm{EuclideanSpace}_m\times \mathrm{EuclideanSpace}_m$ defined by

$$
(u,v)\mapsto \texttt{objectiveWithQuadratic }P\,(A.M_2(\nu,\mu))\,u\,v.
$$

So it is the function built from the objective together with the quadratic term determined by the scalar $A.M_2(\nu,\mu)$.

According to the supplied definition, the proposition $\texttt{ProductKLFunction }H$ says: for every problem-data object $P'$ of dimension $m$, every algorithm data $A'$ for $P'$, and all real $\nu',\mu'$, if

$$
H=\texttt{HFunction }P'\,(A'.M_2(\nu',\mu')),
$$

then $\texttt{KLOrbitPackage }A'\,\nu'\,\mu'$ holds. The proposition `KLOrbitPackage` is not expanded in the provided source, so its internal mathematical content is not used here beyond being the conclusion of this universal implication.

The cited result `semialgebraic_objective_yields_productKL_HFunction` states that if $P.\mathrm{objective}$ is semialgebraic, i.e. `IsSemiAlgebraicEReal P.objective`, and if the bridge condition

$$
\texttt{SemialgebraicToProductKL }P.\mathrm{objective}\,(A.M_2(\nu,\mu))
$$

holds, then

$$
\texttt{ProductKLFunction }(\texttt{HFunction }P\,(A.M_2(\nu,\mu)))
$$

holds. The proof applies this result to the current $A,\nu,\mu$, with $m$ and $P$ inferred from context. The hypothesis `hsemi` supplies semialgebraicity, and `hsemi_to_KL` supplies the bridge condition. The resulting conclusion is exactly `hH_KL`. This step converts the semialgebraic assumption on the objective into the product KL condition required by the convergence theorem.

Second, the proof applies `theorem_3_1_convergence` to the current $A,\nu,\mu$:

$$
\texttt{theorem\_3\_1\_convergence }A\,\nu\,\mu\,\texttt{hchosen}\,\texttt{hcoercive}\,\texttt{hH\_KL}.
$$

The cited theorem states that for any $m$, any $P$ of dimension $m$, any algorithm data $A$ for $P$, and real $\nu,\mu$, if

$$
\texttt{chosenAsInLemma33 }A\,\nu\,\mu,\qquad
\texttt{CoerciveEReal }P.\mathrm{objective},\qquad
\texttt{ProductKLFunction }(\texttt{HFunction }P\,(A.M_2(\nu,\mu)))
$$

all hold, then the two summability assertions

$$
\sum_{n\in\mathbb N}\|A.x_n-A.p_n\|<\infty,
\qquad
\sum_{n\in\mathbb N}\|A.x_{n+1}-A.x_n\|<\infty
$$

hold, and there exists $x\in\mathbb R^m$ such that $x$ is a critical point of $P.\mathrm{objective}$ and both sequences $A.x_n$ and $A.p_n$ converge to $x$. Applying this theorem with the current hypotheses `hchosen`, `hcoercive`, and `hH_KL` gives exactly the desired conjunction. The `exact` command supplies this proof term directly and leaves no remaining goals.

Thus the corollary follows by first deriving the product KL condition from semialgebraicity and the bridge hypothesis, and then invoking the main convergence theorem under the chosen parameter assumptions and coercivity.

