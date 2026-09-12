## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_6.lean`

## Lean statement
```lean
theorem opial_trajectory_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : Set H) (x : ℝ → H) (hS : S.Nonempty)
    (hdist : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds l))
    (hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop (nhds (toWeakSpace ℝ H z))) → z ∈ S) :
    ∃ z ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The declaration is a theorem about a complete real inner product space $H$, i.e. a real Hilbert space. It fixes a subset $S\subseteq H$, a trajectory $x:\mathbb R\to H$, and three hypotheses.

First, `hS : S.Nonempty` says that $S$ is nonempty. Second, `hdist` says that for every $z\in S$, there exists a real number $l$ such that

$$
\|x(t)-z\| \to l \qquad \text{as } t\to\infty .
$$

Thus the distance from the trajectory to each point of $S$ has a finite limit along the continuous parameter $t\to\infty$; the limit may depend on $z$. Third, `hcluster` says that every weak sequential cluster point of the trajectory lies in $S$. More precisely, if there is a sequence $u:\mathbb N\to\mathbb R$ with $u(n)\to\infty$ and if

$$
x(u(n)) \rightharpoonup z
$$

weakly as $n\to\infty$, then $z\in S$. In the Lean statement this weak convergence is written using the canonical map `toWeakSpace ℝ H` into the weak topology.

The conclusion asserts that there exists $z\in S$ such that the whole trajectory converges weakly to $z$ as $t\to\infty$:

$$
x(t)\rightharpoonup z \qquad \text{as } t\to\infty .
$$

Equivalently, in Lean notation,

$$
\operatorname{Tendsto}\bigl(t\mapsto \operatorname{toWeakSpace}_{\mathbb R}(x(t))\bigr)
\ \text{to}\ 
\operatorname{nhds}\bigl(\operatorname{toWeakSpace}_{\mathbb R}(z)\bigr).
$$

This is the Opial trajectory lemma: under the assumption that the distance from the trajectory to every point of $S$ stabilizes and every weak sequential cluster point belongs to $S$, the trajectory has a genuine weak limit lying in $S$.

## Lean proof
```lean
by
  have hcluster' : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n ↦ f (x (u n))) atTop (nhds (f z))) → z ∈ S := by
    rintro z ⟨u, hu, hfun⟩
    exact hcluster z ⟨u, hu, by
      rw [weakConvergence_iff_forall_tendsto_inner_right]
      intro v
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        hfun (InnerProductSpace.toDual ℝ H v)⟩
  obtain ⟨z, hz, hf⟩ := opial_lemma_continuous_weak x S hS hdist hcluster'
  exact ⟨z, hz, by
    rw [weakConvergence_iff_forall_tendsto_inner_right]
    intro u
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hf (InnerProductSpace.toDual ℝ H u)⟩
```

## Proof explanation
The proof first derives a local version of the cluster hypothesis `hcluster'` in which weak convergence is replaced by convergence of every continuous linear functional. Since $H$ is a real Hilbert space, these two formulations are equivalent.

The line

```lean
have hcluster' : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n ↦ f (x (u n))) atTop (nhds (f z))) → z ∈ S := by
```

introduces a local claim: for every $z$, if there is a sequence $u(n)\to\infty$ such that for every continuous linear functional $f:H\to\mathbb R$,

$$
f(x(u(n))) \to f(z),
$$

then $z\in S$. This is not an additional assumption; it is proved from the original weak-cluster hypothesis.

The command

```lean
rintro z ⟨u, hu, hfun⟩
```

fixes an arbitrary $z$ and destructs the existential-and-conjunction hypothesis. Thus $u:\mathbb N\to\mathbb R$ is a sequence, `hu` is the statement $u(n)\to\infty$, and `hfun` is the assertion that $f(x(u(n)))\to f(z)$ for every continuous linear functional $f$. The goal is now $z\in S$.

To apply the original hypothesis `hcluster z`, the proof must show that $x(u(n))$ converges weakly to $z$. It supplies the same sequence $u$, the same limit statement `hu`, and then proves weak convergence by rewriting with the cited equivalence

$$
\operatorname{Tendsto}\bigl(n\mapsto \operatorname{toWeakSpace}_{\mathbb R}(x(u(n)))\bigr)
\text{ to } \operatorname{nhds}\bigl(\operatorname{toWeakSpace}_{\mathbb R}(z)\bigr)
\iff
\forall v:H,\ 
\langle x(u(n)),v\rangle_{\mathbb R}\to \langle z,v\rangle_{\mathbb R}.
$$

This is exactly the content of `weakConvergence_iff_forall_tendsto_inner_right`, specialized to the complete real inner product space $H$, the sequence index type $\mathbb N$, and the two vectors $x(u(n))$ and $z$. The command

```lean
rw [weakConvergence_iff_forall_tendsto_inner_right]
```

replaces the weak-convergence goal by the equivalent inner-product goal.

Then

```lean
intro v
```

fixes an arbitrary vector $v\in H$. The proof must show

$$
\langle x(u(n)),v\rangle_{\mathbb R}\to \langle z,v\rangle_{\mathbb R}.
$$

The hypothesis `hfun` says that every continuous linear functional converges along the sequence. In particular, it applies to the continuous linear functional `InnerProductSpace.toDual ℝ H v`, which is the Riesz-representing functional associated to the vector $v$. Thus

$$
(\operatorname{toDual} v)(x(u(n)))\to (\operatorname{toDual} v)(z).
$$

The command

```lean
simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
  hfun (InnerProductSpace.toDual ℝ H v)
```

uses the lemma `InnerProductSpace.toDual_apply_apply` to identify the value of the Riesz functional as an inner product, and uses `real_inner_comm`, the symmetry of the real inner product, to rearrange it into the required form $\langle x(u(n)),v\rangle_{\mathbb R}\to \langle z,v\rangle_{\mathbb R}$. This proves the inner-product convergence for the fixed $v$. Since $v$ was arbitrary, the weak-convergence criterion applies, so $x(u(n))\rightharpoonup z$. The original hypothesis `hcluster z` then gives $z\in S$. This completes the derivation of `hcluster'`.

Next,

```lean
obtain ⟨z, hz, hf⟩ := opial_lemma_continuous_weak x S hS hdist hcluster'
```

applies the cited Opial lemma for continuous trajectories. Its hypotheses are precisely the nonempty set $S$, the trajectory $x$, the distance-limit condition `hdist`, and the functional version of the cluster hypothesis `hcluster'`. Its conclusion provides a point $z\in S$ and the statement `hf` that for every continuous linear functional $f:H\to\mathbb R$,

$$
f(x(t))\to f(z) \qquad \text{as } t\to\infty.
$$

Thus the Opial lemma already gives convergence of every continuous linear functional of the trajectory to the corresponding value at some $z\in S$.

It remains to convert this functional convergence back into weak convergence in the weak topology. The proof uses

```lean
exact ⟨z, hz, by
  rw [weakConvergence_iff_forall_tendsto_inner_right]
  intro u
  simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    hf (InnerProductSpace.toDual ℝ H u)⟩
```

Here the final weak-convergence goal is again rewritten using `weakConvergence_iff_forall_tendsto_inner_right`. This converts it to the requirement that for every $u\in H$,

$$
\langle x(t),u\rangle_{\mathbb R}\to \langle z,u\rangle_{\mathbb R}
\qquad \text{as } t\to\infty.
$$

The command `intro u` fixes an arbitrary $u$. Then `hf (InnerProductSpace.toDual ℝ H u)` gives convergence of the continuous linear functional representing $u$. Using `InnerProductSpace.toDual_apply_apply` and `real_inner_comm`, `simpa` converts that functional convergence into precisely the desired inner-product convergence $\langle x(t),u\rangle_{\mathbb R}\to \langle z,u\rangle_{\mathbb R}$. Since $u$ was arbitrary, the weak-convergence criterion gives

$$
x(t)\rightharpoonup z
$$

as $t\to\infty$, with $z\in S$. This is exactly the conclusion of the theorem.

No arithmetic tactic such as `linarith` is used; the proof is carried out by deriving the functional form of the cluster hypothesis, applying the Opial lemma, and then translating between functional convergence and weak convergence via the inner-product characterization.

