## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_2.lean`

## Lean statement
```lean
theorem gradient_cocoercive_of_lipschitz {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (tau : ℝ) (htau : 0 < tau)
    (hconvex : ConvexOn ℝ Set.univ Psi)
    (hgrad : ∀ x, HasGradientAt Psi (∇ Psi x) x)
    (hLipschitz : LipschitzWith ⟨tau, le_of_lt htau⟩ (∇ Psi)) :
    CocoerciveOn tau⁻¹ Set.univ (fun x : Set.univ ↦ ∇ Psi x)
```

## Statement explanation
The theorem is set in a type \(H\) which is a complete real inner product space over \(\mathbb R\); the Lean assumptions are `NormedAddCommGroup H`, `InnerProductSpace ℝ H`, and `CompleteSpace H`.

The variables and hypotheses are:

- \( \Psi : H \to \mathbb R \), a real-valued function on \(H\).
- \( \tau : \mathbb R \), with hypothesis \( \mathrm{htau} : 0 < \tau \), so \(\tau\) is a positive real number.
- \( \mathrm{hconvex} : \mathrm{ConvexOn}\ \mathbb R\ \mathrm{Set.univ}\ \Psi \), meaning \(\Psi\) is convex on the whole space \(H\).
- \( \mathrm{hgrad} : \forall x,\ \mathrm{HasGradientAt}\ \Psi\ (\nabla \Psi\, x)\ x \), meaning at every point \(x\), the vector \(\nabla \Psi\, x\) is the gradient of \(\Psi\) at \(x\).
- \( \mathrm{hLipschitz} : \mathrm{LipschitzWith}\ \langle \tau, \mathrm{le\_of\_lt}\ \mathrm{htau}\rangle\ (\nabla \Psi) \), meaning the gradient map \(\nabla \Psi\) is Lipschitz continuous with Lipschitz constant \(\tau\). The notation \(\langle \tau, \mathrm{le\_of\_lt}\ \mathrm{htau}\rangle\) is a nonnegative real constant obtained from \(\tau\) together with a proof that \(\tau \ge 0\).

The conclusion is

\[
\mathrm{CocoerciveOn}\ \tau^{-1}\ \mathrm{Set.univ}\ (\lambda x : \mathrm{Set.univ}, \nabla \Psi\, x).
\]

Thus the gradient of \(\Psi\), regarded as a map on the whole space \(H\), is cocoercive on the whole space with constant \(\tau^{-1}\). In expanded form, for every pair of points \(x,y \in H\), this asserts a cocoercivity inequality of the form

\[
\tau^{-1}\|\nabla \Psi(x)-\nabla \Psi(y)\|^2
\le
\langle \nabla \Psi(x)-\nabla \Psi(y), x-y\rangle
\]

(up to the symmetry of the real inner product).

## Lean proof
```lean
by
  have hdiff : Differentiable ℝ Psi := fun x => (hgrad x).differentiableAt
  have hLipschitz' : LipschitzWith (Real.toNNReal tau) (∇ Psi) := by
    simpa [Real.toNNReal_of_nonneg htau.le] using hLipschitz
  simpa [one_div] using baillon_haddad Psi (∇ Psi) tau htau hconvex hdiff hgrad hLipschitz'
```

## Proof explanation
The proof is a direct reduction to the Baillon–Haddad theorem.

First, the proof derives differentiability of \(\Psi\) from the pointwise gradient hypothesis. The command

`have hdiff : Differentiable ℝ Psi := fun x => (hgrad x).differentiableAt`

uses that `hgrad x : HasGradientAt Psi (∇ Psi x) x` includes the fact that \(\Psi\) is differentiable at \(x\). The field or lemma `differentiableAt` extracts this differentiability-at-a-point fact. Since this holds for every \(x\), the lambda expression proves that \(\Psi\) is differentiability everywhere.

Next, the proof adjusts the Lipschitz hypothesis to match the form expected by `baillon_haddad`. The original hypothesis `hLipschitz` has Lipschitz constant \(\langle \tau, \mathrm{le\_of\_lt}\ \mathrm{htau}\rangle\), while the Baillon–Haddad theorem expects the constant `Real.toNNReal tau`. The command

`have hLipschitz' : LipschitzWith (Real.toNNReal tau) (∇ Psi) := by simpa [Real.toNNReal_of_nonneg htau.le] using hLipschitz`

uses that, because \(0 < \tau\), one has \(\tau \ge 0\). The lemma `Real.toNNReal_of_nonneg htau.le` states that `Real.toNNReal tau` is exactly the nonnegative real number built from \(\tau\) and this nonnegativity proof. The `simpa` call rewrites this equality and reuses the original Lipschitz hypothesis.

Finally, the proof applies the existing formalized Baillon–Haddad theorem:

`simpa [one_div] using baillon_haddad Psi (∇ Psi) tau htau hconvex hdiff hgrad hLipschitz'`

This theorem states, under the hypotheses supplied here—convexity of \(\Psi\), differentiability of \(\Psi\), gradient identity, and Lipschitz continuity of \(\nabla \Psi\) with constant \(\tau\)—that the gradient map \(\nabla \Psi\) is \(\tau^{-1}\)-cocoercive on `Set.univ`. The arguments supplied are \(\Psi\), the gradient function \(\nabla \Psi\), the Lipschitz constant \(\tau\), the positivity proof `htau`, the convexity proof `hconvex`, the differentiability proof `hdiff`, the gradient proof `hgrad`, and the normalized Lipschitz proof `hLipschitz'`. The `simpa [one_div]` simplification converts between \(1/\tau\) and \(\tau^{-1}\) notation as needed to close the target.

