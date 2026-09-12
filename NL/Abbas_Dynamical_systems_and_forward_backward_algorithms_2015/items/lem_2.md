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
The declaration `gradient_cocoercive_of_lipschitz` is a theorem about a real Hilbert space \(H\), namely a complete real inner product space. It takes a real-valued function \(\Psi:H\to\mathbb R\), a positive real number \(\tau\), and assumes:

- \(\Psi\) is convex on all of \(H\): for all \(x,y\in H\) and \(t\in[0,1]\),
  \[
  \Psi(tx+(1-t)y)\le t\Psi(x)+(1-t)\Psi(y).
  \]
- For every \(x\in H\), \(\Psi\) has gradient \(\nabla\Psi(x)\) at \(x\), meaning that the derivative of \(\Psi\) at \(x\) is represented by the vector \(\nabla\Psi(x)\).
- The gradient field \(\nabla\Psi\) is Lipschitz with constant \(\tau\): for all \(x,y\in H\),
  \[
  \|\nabla\Psi(x)-\nabla\Psi(y)\|\le \tau\|x-y\|.
  \]

The conclusion is that \(\nabla\Psi\) is cocoercive with parameter \(\tau^{-1}\) on the whole space. Concretely, this means that for all \(x,y\in H\),
\[
\langle \nabla\Psi(x)-\nabla\Psi(y),\,x-y\rangle
\ge \tau^{-1}\|\nabla\Psi(x)-\nabla\Psi(y)\|^2.
\]
Thus the theorem says: for a convex real-valued function whose gradient is \(\tau\)-Lipschitz, the gradient is \((1/\tau)\)-cocoercive. This is exactly the Baillon-Haddad theorem specialized to the present function \(\Psi\) and constant \(\tau\).

## Lean proof
```lean
by
  have hdiff : Differentiable ℝ Psi := fun x => (hgrad x).differentiableAt
  have hLipschitz' : LipschitzWith (Real.toNNReal tau) (∇ Psi) := by
    simpa [Real.toNNReal_of_nonneg htau.le] using hLipschitz
  simpa [one_div] using baillon_haddad Psi (∇ Psi) tau htau hconvex hdiff hgrad hLipschitz'
```

## Proof explanation
The proof proceeds in three steps.

First, it derives differentiability of \(\Psi\). For each \(x\in H\), the hypothesis `hgrad x` states that \(\Psi\) has gradient \(\nabla\Psi(x)\) at \(x\). A function that has a gradient at a point is differentiable at that point, so `(hgrad x).differentiableAt` gives differentiability of \(\Psi\) at \(x\). Quantifying over all \(x\) produces the global statement `Differentiable ℝ Psi`, recorded as `hdiff`. This intermediate fact is needed because `baillon_haddad` requires differentiability as a separate hypothesis, even though here it already follows from the existence of a gradient everywhere.

Second, the proof normalizes the Lipschitz constant. The original hypothesis `hLipschitz` says that \(\nabla\Psi\) is Lipschitz with the nonnegative real constant built from \(\tau\) and the proof that \(0\le\tau\). Since \(\tau>0\), the lemma `Real.toNNReal_of_nonneg htau.le` identifies `Real.toNNReal tau` with that same nonnegative real constant. The `simpa` step rewrites the constant using this lemma and thus proves `hLipschitz'`, which states the same Lipschitz property in the form expected by `baillon_haddad`, namely that \(\nabla\Psi\) is Lipschitz with constant `Real.toNNReal tau`. Mathematically, this step changes nothing: the gradient field is still \(\tau\)-Lipschitz.

Third, the proof applies `baillon_haddad`. Specialized to \(f=\Psi\), `gradf` equal to the gradient field \(\nabla\Psi\), and \(L=\tau\), the theorem `baillon_haddad` says that if \(\tau>0\), \(\Psi\) is convex on all of \(H\), \(\Psi\) is differentiable, \(\nabla\Psi\) is the gradient of \(\Psi\) everywhere, and \(\nabla\Psi\) is \(\tau\)-Lipschitz, then \(\nabla\Psi\) is \((1/\tau)\)-cocoercive on the whole space. The proof supplies exactly the required hypotheses `htau`, `hconvex`, `hdiff`, `hgrad`, and `hLipschitz'`. The conclusion obtained is cocoercivity with parameter \(1/\tau\). The final `simpa [one_div]` rewrites \(1/\tau\) as \(\tau^{-1}\), because `one_div` is the simplification rule \(1/a=a^{-1}\). Therefore the result matches the target conclusion, which states cocoercivity with parameter \(\tau^{-1}\).

In terms of Lean commands, `have` introduces the intermediate facts `hdiff` and `hLipschitz'`; the lambda expression `fun x => ...` assembles the pointwise differentiability proofs into a global differentiability proof; and `simpa ... using ...` simplifies the goal and closes it using the cited result. The proof does not use `intro`, `rw`, `exact`, or `linarith`.

