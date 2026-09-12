## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/lem_6.lean`

## Lean statement
```lean
theorem lemma_3_6_cluster_points {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective) :
    (omega A.p).Nonempty ∧
      omega A.p ⊆ criticalPoints P.objective ∧
      Tendsto (fun n : Nat => Metric.infDist (A.p n) (omega A.p)) atTop (nhds 0) ∧
      IsCompact (omega A.p) ∧
      IsConnected (omega A.p) ∧
      (∃ c : Real, ∀ p ∈ omega A.p, P.objective p = (c : EReal))
```

## Statement explanation
Let $m$ be a natural number and let $P$ be problem data on $\mathbb R^m$. The objective is $f=P.objective$, an extended-real-valued function $f:\mathbb R^m\to\overline{\mathbb R}$. Let $A$ be algorithm data for $P$; it supplies the sequences $A.x_n$ and $A.p_n$ in $\mathbb R^m$. Let $\nu,\mu\in\mathbb R$. The assumption `hchosen` is the named parameter condition `chosenAsInLemma33 A nu mu`; `hcoercive` is the coercivity assumption on $f$. For a sequence $z_n$, $\omega(z)$ denotes its set of sequential cluster points. For a function $g$,

```math
\mathrm{criticalPoints}(g)=\{x:0\in\partial_L g(x)\},
```

where $\partial_L$ is the limiting subdifferential. The theorem asserts, under `hchosen` and `hcoercive`, that: $\omega(A.p)$ is nonempty; every element of $\omega(A.p)$ is a critical point of $f$; the distance from $A.p_n$ to $\omega(A.p)$ tends to $0$; $\omega(A.p)$ is compact; $\omega(A.p)$ is connected; and there is a real $c$ such that $f(p)=(c:\overline{\mathbb R})$ for every $p\in\omega(A.p)$. In words, the sequence $A.p_n$ has a nonempty compact connected cluster set, approaches that set asymptotically, and the objective is constant on that set with value a real number; moreover all points of that set are critical points of the nonsmooth objective.

## Lean proof
```lean
by
  have hboundedBelow :
      ∃ C : Real, ∀ x : EuclideanSpace m, (C : EReal) <= P.objective x := by
    have hmin :=
      exists_minimizer_of_proper_lsc_coercive P.objective (objective_isProper P)
        (objective_lowerSemicontinuous P) hcoercive
    rcases hmin.1 with ⟨C, hCinf⟩
    rcases hmin.2 with ⟨xmin, hxmin_min, hxmin_eq_inf⟩
    have hmin_all : ∀ x : EuclideanSpace m, P.objective xmin ≤ P.objective x := by
      simpa [IsMinOn, IsMinFilter] using hxmin_min
    refine ⟨C, ?_⟩
    intro x
    rw [← hCinf, ← hxmin_eq_inf]
    exact hmin_all x
  rcases lemma_3_4_decrease A nu mu hchosen hboundedBelow with
    ⟨hxp_sum, hxx_sum, hobj_conv⟩
  have hp_inc : Tendsto (fun n : Nat => A.p (n + 1) - A.p n) atTop
      (nhds (0 : EuclideanSpace m)) :=
    p_increments_tendsto_zero A hxp_sum hxx_sum
  have hp_bounded : Bornology.IsBounded (Set.range A.p) := by
    exact p_range_bounded_of_coercive A nu mu hchosen hcoercive
  have hcluster := cluster_set_properties_of_vanishing_increments A.p hp_bounded hp_inc
  rcases hcluster with ⟨homega_nonempty, homega_compact, homega_connected, hdist⟩
  have hcrit_subset : omega A.p ⊆ criticalPoints P.objective := by
    intro pstar hpstar
    exact cluster_point_critical_core A nu mu hchosen hboundedBelow hxp_sum hxx_sum
      hobj_conv hpstar
  have hconstant :
      ∃ c : Real, ∀ p ∈ omega A.p, P.objective p = (c : EReal) := by
    exact objective_constant_on_omega_core A nu mu hchosen hboundedBelow hxp_sum hxx_sum
      hobj_conv
  exact ⟨homega_nonempty, hcrit_subset, hdist, homega_compact, homega_connected,
    hconstant⟩
```

## Proof explanation
The proof first establishes that $f$ is bounded below by a real constant. It invokes `exists_minimizer_of_proper_lsc_coercive` with $g=f$. The hypotheses supplied to this theorem are properness, via `objective_isProper P`, lower semicontinuity, via `objective_lowerSemicontinuous P`, and coercivity, via `hcoercive`. Its conclusion is that there is a real $C$ and a point $x_{\min}$ such that

$$
\inf(\mathrm{range} f)=(C:\overline{\mathbb R}),
$$

that $x_{\min}$ minimizes $f$ on all of $\mathbb R^m$, and that

$$
f(x_{\min})=\inf(\mathrm{range} f).
$$

The proof destructs this pair of conclusions. The `simpa` step unfolding `IsMinOn` and `IsMinFilter` converts the minimizing property of $x_{\min}$ into the pointwise inequality $f(x_{\min})\le f(x)$ for every $x$. Then, for an arbitrary $x$, the goal $(C:\overline{\mathbb R})\le f(x)$ is rewritten in reverse using the two equalities above: first $C$ is replaced by the infimum, and then the infimum is replaced by $f(x_{\min})$. The goal becomes $f(x_{\min})\le f(x)$, which is exactly the pointwise inequality. Hence $f$ is bounded below by the real constant $C$, giving `hboundedBelow`.

Next, the lemma `lemma_3_4_decrease` is applied with $A$, $\nu$, $\mu$, `hchosen`, and `hboundedBelow`. Its content is that, under the parameter choice and the bounded-below assumption, the two nonnegative sequences

```math
\|A.x_n-A.p_n\|^2
```

and

```math
\|A.x_{n+1}-A.x_n\|^2
```

are summable, and there exists an extended real $l$ such that $f(A.p_n)\to l$. The proof records these three facts as `hxp_sum`, `hxx_sum`, and `hobj_conv`.

From the two summability facts, the theorem `p_increments_tendsto_zero` yields

$$
A.p_{n+1}-A.p_n\to 0.
$$

This is the vanishing-increment property for the sequence $A.p_n$. Separately, `p_range_bounded_of_coercive` uses `hchosen` and the coercivity hypothesis $hcoercive$ to conclude that the range $`\{A.p_n:n\in\mathbb N\}`$ is bounded.

Now the sequence $z_n=A.p_n$ satisfies both hypotheses of `cluster_set_properties_of_vanishing_increments`: its range is bounded and its increments tend to $0$. Applying that theorem to $z=A.p$ gives four properties of the cluster set $\omega(A.p)$: it is nonempty, compact, connected, and

$$
\mathrm{infDist}(A.p_n,\omega(A.p))\to 0.
$$

Next, to identify cluster points as critical points, take any $p^\star\in\omega(A.p)$. The theorem `cluster_point_critical_core` is applied with the same data $A,\nu,\mu$, the assumption `hchosen`, the bounded-below fact just proved, the two summability facts, the objective convergence fact, and the membership $p^\star\in\omega(A.p)$. Its conclusion is

$$
p^\star\in\mathrm{criticalPoints}(f).
$$

Since $p^\star$ was arbitrary, this proves $\omega(A.p)\subseteq\mathrm{criticalPoints}(f)$.

Then `objective_constant_on_omega_core`, using the same hypotheses, gives a real $c$ such that

$$
f(p)=(c:\overline{\mathbb R})
$$

for every $p\in\omega(A.p)$. This is the constancy of the objective on the cluster set.

Finally, the `exact` command assembles the six components in the order required by the theorem statement: nonemptiness, the critical-point inclusion, the distance convergence, compactness, connectedness, and constancy. The `rcases` steps unpack conjunctions, `intro` introduces arbitrary points or variables, `rw` rewrites $C$ and the infimum by the two equalities, and `simpa` was used only to unfold the minimizing predicate into a pointwise inequality. No `linarith` is used.

