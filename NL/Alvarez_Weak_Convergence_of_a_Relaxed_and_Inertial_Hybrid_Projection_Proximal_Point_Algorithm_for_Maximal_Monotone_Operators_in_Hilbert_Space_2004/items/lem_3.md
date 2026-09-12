## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/lem_3.lean`

## Lean statement
```lean
lemma lemma_2_4_opial
    (x : ℕ → H) (S : Set H)
    (hS : S.Nonempty)
    (hdist : ∀ xbar ∈ S, ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar‖) atTop (𝓝 l))
    (hcluster :
      ∀ xhat : H, ∀ subseq : ℕ → ℕ, StrictMono subseq →
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (x (subseq j))) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) →
        xhat ∈ S) :
    ∃ xstar ∈ S,
      Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (x k)) atTop
        (𝓝 (toWeakSpace ℝ H xstar))
```

## Statement explanation
The declaration is a form of Opial’s lemma. In the ambient setting, $H$ is a real Hilbert space, and $w$ denotes the canonical map

$$
w(v)=\mathrm{toWeakSpace}_{\mathbb R,H}(v),
$$

which views a vector $v\in H$ as an element of the weak-topology version of $H$. Thus convergence of $w(x_k)$ to $w(y)$ is exactly weak convergence of $x_k$ to $y$.

The declaration takes the following data.

- $x:\mathbb N\to H$ is a sequence in $H$.
- $S\subseteq H$ is a subset of $H$.
- The hypothesis `hS` states that $S$ is nonempty.
- The hypothesis `hdist` states that for every $\bar x\in S$, the real sequence of distances

$$
k\mapsto \lVert x_k-\bar x\rVert
$$

converges as $k\to\infty$; that is, there exists $l\in\mathbb R$ such that

$$
\lVert x_k-\bar x\rVert\to l.
$$

- The hypothesis `hcluster` states that for every $\hat x\in H$ and every strictly increasing sequence of indices

$$
\phi:\mathbb N\to\mathbb N,
$$

if the subsequence $x_{\phi(j)}$ converges weakly to $\hat x$, i.e.

$$
w(x_{\phi(j)})\to w(\hat x),
$$

then necessarily $\hat x\in S$. In other words, every weak sequential cluster point of the sequence $x$ lies in $S$.

The conclusion is that there exists $x^\star\in S$ such that the whole sequence converges weakly to $x^\star$:

$$
\exists x^\star\in S,\qquad w(x_k)\to w(x^\star).
$$

Equivalently, $x_k\rightharpoonup x^\star$ weakly in $H$.

So the lemma says: if the distance norms from $x_k$ to every point of $S$ converge, and if all weak sequential limits of subsequences lie in $S$, then the entire sequence is weakly convergent to some point of $S$.

## Lean proof
```lean
by
  have hcluster' : ∀ (z : H),
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) → z ∈ S := by
    intro z hp
    rcases hp.exists_subseq_tendsto with ⟨φ, hφ, hφz⟩
    have hsubseq :
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (x (φ j))) atTop
          (𝓝 (toWeakSpace ℝ H z)) := by
      simpa [Function.comp] using hφz
    exact hcluster z φ hφ hsubseq
  exact opial_lemma hS x hdist hcluster'
```

## Proof explanation
The proof invokes `opial_lemma`, but first rewrites the hypothesis `hcluster` into the exact form expected by that theorem. Let $u_n=w(x_n)$. The theorem `opial_lemma` expects a condition saying that every sequential cluster point of $(u_n)$ lies in the target set. The assumed `hcluster` is stated in terms of arbitrary strictly increasing subsequences; the proof converts it into the existential cluster-point formulation.

The proof defines an intermediate fact `hcluster'`:

$$
\forall z\in H,\qquad
\mathrm{IsSequentialClusterPt}(u,w(z))\implies z\in S.
$$

To prove this, it fixes such a $z$ and assumes that $w(z)$ is a sequential cluster point of the sequence $u_n=w(x_n)$. By the definition of `IsSequentialClusterPt`,

$$
\mathrm{IsSequentialClusterPt}(u,w(z))
$$

means that there exists a strictly increasing map $\phi:\mathbb N\to\mathbb N$ such that the subsequence $u\circ\phi$ converges to $w(z)$. Concretely,

$$
\exists \phi,\quad \mathrm{StrictMono}(\phi)\ \wedge\ \mathrm{Tendsto}(u\circ\phi)\text{ to }w(z).
$$

The tactic `intro` introduces the arbitrary $z$ and the hypothesis that $w(z)$ is a sequential cluster point. The tactic `rcases` then destructs the existential supplied by that hypothesis, producing:
- a map $\phi:\mathbb N\to\mathbb N$,
- a proof that $\phi$ is strictly increasing,
- a proof that $u\circ\phi$ converges to $w(z)$.

The proof then forms `hsubseq`, the statement

$$
\mathrm{Tendsto}\bigl(j\mapsto w(x_{\phi(j)})\bigr)\text{ to }w(z).
$$

Initially the convergence obtained from the cluster-point hypothesis is for the composed function $u\circ\phi$. Since

$$
(u\circ\phi)(j)=u(\phi(j))=w(x_{\phi(j)}),
$$

the command `simpa` using `Function.comp` rewrites the composed form into the displayed subsequence form. This is exactly the kind of convergence required by `hcluster`.

Now the proof applies the original hypothesis `hcluster` with $\hat x=z$, subsequence $\phi$, strict monotonicity of $\phi$, and the convergence `hsubseq`. The conclusion of that application is $z\in S$. This proves `hcluster'`.

Finally, the proof applies `opial_lemma`. The cited theorem says that for a nonempty set $C\subseteq H$, a sequence $x:\mathbb N\to H$, the distance-convergence condition

$$
\forall z\in C,\ \exists l\in\mathbb R,\quad \lVert x_n-z\rVert\to l,
$$

and the cluster-point condition

$$
\forall z\in H,\quad
\mathrm{IsSequentialClusterPt}(w(x_n),w(z))\implies z\in C,
$$

one obtains

$$
\exists z\in C,\quad w(x_n)\to w(z).
$$

In the proof, this theorem is instantiated with $C=S$, the given sequence $x$, the nonemptiness hypothesis `hS`, the distance hypothesis `hdist`, and the newly proved cluster-point hypothesis `hcluster'`. Its conclusion is exactly

$$
\exists x^\star\in S,\qquad w(x_k)\to w(x^\star),
$$

which is the statement to be proved. The final `exact` closes the goal by providing this result directly.

