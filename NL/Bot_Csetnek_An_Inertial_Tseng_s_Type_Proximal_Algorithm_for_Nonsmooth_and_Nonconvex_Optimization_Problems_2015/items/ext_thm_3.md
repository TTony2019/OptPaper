## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_thm_3.lean`

## Lean statement
```lean
theorem cluster_set_properties_of_vanishing_increments {m : Nat}
    (z : Nat -> EuclideanSpace m)
    (hbounded : Bornology.IsBounded (Set.range z))
    (hincrements : Tendsto (fun n : Nat => z (n + 1) - z n) atTop
      (nhds (0 : EuclideanSpace m))) :
    (omega z).Nonempty ∧ IsCompact (omega z) ∧ IsConnected (omega z) ∧
      Tendsto (fun n : Nat => Metric.infDist (z n) (omega z)) atTop (nhds 0)
```

## Statement explanation
The declaration `cluster_set_properties_of_vanishing_increments` is a theorem about a sequence $z=(z_n)_{n\in\mathbb N}$ in the Euclidean space $E_m=\mathbb R^m$. The parameter $m$ is a natural number, and `EuclideanSpace m` is the real inner-product space $\mathbb R^m$ with the usual Euclidean metric. Thus $z$ is a sequence of vectors in $\mathbb R^m$.

The two hypotheses are as follows. First, `hbounded : Bornology.IsBounded (Set.range z)` says that the set of values

```math
\mathrm{range}(z)=\{z_n:n\in\mathbb N\}
```

is bounded. Second, `hincrements` says that

$$
\mathrm{Tendsto}\bigl(n\mapsto z_{n+1}-z_n\bigr)\mathrm{atTop}(\mathrm{nhds}0),
$$

i.e. the consecutive forward differences $z_{n+1}-z_n$ tend to the zero vector in $E_m$ as $n\to\infty$.

For a sequence in a topological space, `omega z` is defined in `ext_def_5.lean` as the set of sequential cluster points of $z$. The lemma `omega_eq_mapClusterPt` states that, when the ambient space is first-countable, this set equals the set of map-cluster points

```math
C_z=\{x:\mathrm{MapClusterPt} x \mathrm{atTop} z\}.
```

Since $E_m$ is a metric space and hence first-countable, this equality applies here. Conceptually, $\omega(z)$ is the cluster set of the sequence: the points $x$ such that every neighborhood of $x$ contains $z_n$ for infinitely many $n$, equivalently the limits of subsequences of $z$.

The conclusion is the four-part conjunction:

$$
(\omega(z)).\mathrm{Nonempty}
\land \mathrm{IsCompact}(\omega(z))
\land \mathrm{IsConnected}(\omega(z))
\land
\mathrm{Tendsto}\bigl(n\mapsto \mathrm{infDist}(z_n,\omega(z))\bigr)\mathrm{atTop}(\mathrm{nhds}0).
$$

Thus: a bounded sequence in $\mathbb R^m$ whose consecutive increments vanish has a nonempty compact connected cluster set, and the sequence is asymptotically at distance zero from that cluster set.

## Lean proof
```lean
by
  have hstep : Tendsto (fun n : Nat => z n - z (n + 1)) atTop
      (nhds (0 : EuclideanSpace m)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hincrements.neg
  have hcluster := sequenceClusterPointSet_isCompact_isConnected (x := z) hbounded hstep
  have hEq : omega z = {x | MapClusterPt x atTop z} := omega_eq_mapClusterPt z
  have hcompact : IsCompact (omega z) := by
    simpa [hEq] using hcluster.1
  have hconnected : IsConnected (omega z) := by
    simpa [hEq] using hcluster.2
  have hK : IsCompact (closure (Set.range z)) := by
    haveI : ProperSpace (EuclideanSpace m) :=
      FiniteDimensional.proper Real (EuclideanSpace m)
    simpa using hbounded.isCompact_closure
  have hzK : forall n : Nat, z n ∈ closure (Set.range z) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  have hdistMap := tendsto_infDist_mapClusterPt_of_isCompact
    (K := closure (Set.range z)) (z := z) hK hzK
  have hdist : Tendsto (fun n : Nat => Metric.infDist (z n) (omega z)) atTop
      (nhds 0) := by
    simpa [hEq] using hdistMap
  exact ⟨hconnected.1, hcompact, hconnected, hdist⟩
```

## Proof explanation
The proof first changes the hypothesis on forward increments into a hypothesis on backward increments. From `hincrements.neg`, the sequence of negatives of $z_{n+1}-z_n$ tends to $-0=0$. Since

$$
-(z_{n+1}-z_n)=z_n-z_{n+1},
$$

the `simpa` step, using only algebraic normalization lemmas such as `sub_eq_add_neg`, `add_comm`, `add_left_comm`, and `add_assoc`, proves

$$
\mathrm{Tendsto}\bigl(n\mapsto z_n-z_{n+1}\bigr)\mathrm{atTop}(\mathrm{nhds}0).
$$

This is the intermediate fact `hstep`. The algebraic lemmas mentioned are not doing any mathematical topology; they only rewrite subtraction as addition of a negative and reorder the resulting sums so that the Lean expression matches the required form.

Next the proof applies the cited theorem `sequenceClusterPointSet_isCompact_isConnected` with $x=z$, using `hbounded` and `hstep`. That theorem says that for a bounded sequence $x$ in the Hilbert-space setting in which it is stated, if $x_n-x_{n+1}\to0$, then the set

```math
C_x=\{y:\mathrm{MapClusterPt} y \mathrm{atTop} x\}
```

is compact and connected. Specialized to $x=z$, it gives

$$
\mathrm{IsCompact}(C_z)\land \mathrm{IsConnected}(C_z),
$$

where

```math
C_z=\{y:\mathrm{MapClusterPt} y \mathrm{atTop} z\}.
```

This conjunction is named `hcluster`.

The proof then invokes `omega_eq_mapClusterPt z`, which gives the equality

$$
\omega(z)=C_z.
$$

This is the first-countability identification of sequential cluster points with map-cluster points along $\mathrm{atTop}$. Using this equality as a rewrite rule, `simpa [hEq] using hcluster.1` transfers compactness of $C_z$ to compactness of $\omega(z)$, producing `hcompact`. Similarly, `simpa [hEq] using hcluster.2` transfers connectedness of $C_z$ to connectedness of $\omega(z)$, producing `hconnected`.

The proof now prepares the compact set needed for the distance estimate. The line
```lean
haveI : ProperSpace (EuclideanSpace m) :=
  FiniteDimensional.proper Real (EuclideanSpace m)
```
introduces a local instance saying that the Euclidean space $E_m$ is proper. In a proper metric space, closed bounded subsets are compact. Therefore the theorem `Bornology.IsBounded.isCompact_closure`, invoked as `hbounded.isCompact_closure`, concludes that the closure of the bounded range of $z$ is compact:

$$
\mathrm{IsCompact}\left(\overline{\mathrm{range}(z)}\right).
$$

This is `hK`.

Next the proof shows that every term of the sequence lies in this compact closure. After `intro n` fixes an arbitrary natural number $n$, the term $\langle n,\mathrm{rfl}\rangle$ witnesses that $z_n\in\mathrm{range}(z)$. The lemma `subset_closure` then gives

$$
z_n\in \overline{\mathrm{range}(z)}.
$$

Thus `hzK` states that for every $n\in\mathbb N$, $z_n$ belongs to the compact set $K=\overline{\mathrm{range}(z)}$.

The proof then applies `tendsto_infDist_mapClusterPt_of_isCompact` with this compact set $K$ and the sequence $z$, using `hK` and `hzK`. That lemma says that if $K$ is compact in a metric space and every term $z_n$ lies in $K$, then the distance from $z_n$ to the map-cluster point set tends to zero:

$$
\mathrm{Tendsto}\left(n\mapsto \mathrm{infDist}(z_n,C_z)\right)\mathrm{atTop}(\mathrm{nhds}0).
$$

Here $\mathrm{infDist}(z_n,C_z)$ means the infimum of the distances from $z_n$ to points of $C_z$. This is the compactness phenomenon that a sequence staying in a compact set has its cluster points nearby, so its distance to the cluster set vanishes. The result is named `hdistMap`.

Using the equality $\omega(z)=C_z$ again, `simpa [hEq] using hdistMap` rewrites the target set $C_z$ to $\omega(z)$, yielding

$$
\mathrm{Tendsto}\left(n\mapsto \mathrm{infDist}(z_n,\omega(z))\right)\mathrm{atTop}(\mathrm{nhds}0).
$$

This is `hdist`.

Finally, the proof closes with
```lean
exact ⟨hconnected.1, hcompact, hconnected, hdist⟩
```
which assembles the required four conjuncts. The first component is `hconnected.1`: connectedness of $\omega(z)$ includes nonemptiness, so this projection gives $(\omega(z)).\mathrm{Nonempty}$. The second component is compactness `hcompact`. The third is the full connectedness assertion `hconnected`. The fourth is the distance convergence `hdist`. The proof does not use `rw` or `linarith`; its main logical steps are `intro` to prove the universal membership statement, `simpa` to rewrite by equalities and algebraic normal forms, and `exact` to supply the final conjunction.

