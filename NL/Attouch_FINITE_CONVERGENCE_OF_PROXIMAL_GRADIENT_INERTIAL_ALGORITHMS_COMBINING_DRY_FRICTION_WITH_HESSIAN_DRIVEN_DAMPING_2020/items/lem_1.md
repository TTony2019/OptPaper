## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/lem_1.lean`

## Lean statement
```lean
theorem proximal_eq_zero_of_norm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (phi : H → ℝ) (r lam : ℝ) (hlam : 0 < lam)
    (hconvex : ConvexOn ℝ Set.univ phi) (hcontinuous : Continuous phi) (_hr : 0 < r)
    (hball : Metric.closedBall (0 : H) r ⊆ subdifferential phi 0)
    (x : H) (hx : ‖x‖ ≤ lam * r) :
    ERealFunction.scaledProximityOperator phi.toEReal
      (toEReal_mem_gammaZero_of_continuous_convexOn_univ hcontinuous hconvex)
      ⟨lam, hlam⟩ x = 0
```

## Statement explanation
The declaration `proximal_eq_zero_of_norm_le` is a theorem about a real Hilbert space \(H\). The typeclass assumptions say that \(H\) is a normed additive commutative group, a real inner product space, and complete. The data are a function \(\phi:H\to\mathbb R\), real numbers \(r,\lambda\), and a point \(x\in H\). The hypotheses are:

- \(0<\lambda\);
- \(\phi\) is convex on all of \(H\), expressed as \(\operatorname{ConvexOn}\ \mathbb R\ \operatorname{Set.univ}\ \phi\);
- \(\phi\) is continuous;
- \(0<r\);
- the closed ball \(B(0,r)=\{u\in H:\|u\|\le r\}\) is contained in the subdifferential \(\partial\phi(0)\);
- \(\|x\|\le \lambda r\).

Here the subdifferential \(\partial\phi(0)\) is the set of \(u\in H\) such that for every \(y\in H\),
\[
\phi(0)+\langle y,u\rangle_{\mathbb R}\le \phi(y),
\]
with the inequality read in the extended reals. Thus the ball hypothesis says that every vector of norm at most \(r\) is a subgradient of \(\phi\) at \(0\).

The conclusion is that the scaled proximal operator of the extended-real function \(\phi.toEReal\), with step \(\lambda\), evaluated at \(x\), is \(0\). The symbol \(\phi.toEReal\) denotes the same function \(\phi\) regarded as taking values in \(]-\infty,+\infty]\), and the argument `toEReal_mem_gammaZero_of_continuous_convexOn_univ hcontinuous hconvex` is the proof that \(\phi.toEReal\in\Gamma_0(H)\). In ordinary proximal notation the conclusion is
\[
\operatorname{prox}_{\lambda\phi}(x)=0.
\]
Equivalently, \(0\) is the proximal point of the function \(\lambda\phi\) from the point \(x\). The theorem gives a sufficient condition for this: if all vectors of norm at most \(r\) are subgradients of \(\phi\) at \(0\), then any \(x\) with \(\|x\|\le \lambda r\) has \(\lambda^{-1}x\) in that ball, hence \(\lambda^{-1}x\in\partial\phi(0)\). Equivalently \(x\in\lambda\partial\phi(0)=\partial(\lambda\phi)(0)\), which is exactly the first-order optimality condition for \(0\) to be the proximal point of \(\lambda\phi\) at \(x\).

## Lean proof
```lean
by
  have hΓ : phi.toEReal ∈ Γ₀(H) :=
    toEReal_mem_gammaZero_of_continuous_convexOn_univ hcontinuous hconvex
  have hscaled_norm : ‖lam⁻¹ • x‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), inv_mul_le_iff₀ hlam]
    simpa [mul_comm] using hx
  have hmem : lam⁻¹ • x ∈ subdifferential phi 0 :=
    hball (mem_closedBall_zero_iff.mpr hscaled_norm)
  rw [ERealFunction.scaledProximityOperator, eq_comm]
  refine (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
    (f := (⟨lam, hlam⟩ : PosReal) • phi.toEReal)
    (ERealFunction.smul_mem_gammaZero phi.toEReal hΓ ⟨lam, hlam⟩) x 0).2 ?_
  rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
  change x - 0 ∈ (lam : ℝ) • ((∂ (Function.toEReal phi)) 0)
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hlam.ne']
  simpa [sub_zero] using hmem
```

## Proof explanation
The proof reduces the desired equality to the membership \(\lambda^{-1}x\in\partial\phi(0)\), which is supplied by the ball hypothesis.

1. First, `have hΓ : phi.toEReal ∈ Γ₀(H)` invokes `toEReal_mem_gammaZero_of_continuous_convexOn_univ`. This theorem says that if a real-valued function on \(H\) is continuous and convex on all of \(H\), then its extended-real version belongs to \(\Gamma_0(H)\). Applied to \(\phi\), with hypotheses `hcontinuous` and `hconvex`, it gives \(\phi.toEReal\in\Gamma_0(H)\). This is needed so that the scaled function \(\lambda\phi.toEReal\) is an admissible object for the proximal characterization.

2. Next, `have hscaled_norm : ‖lam⁻¹ • x‖ ≤ r` proves \(\|\lambda^{-1}\cdot x\|\le r\). The rewrites unfold the norm of a scalar multiple: `norm_smul` gives
\[
\|\lambda^{-1}\cdot x\|=\|\lambda^{-1}\|\,\|x\|.
\]
Over \(\mathbb R\), `Real.norm_eq_abs` replaces \(\|\lambda^{-1}\|\) by \(|\lambda^{-1}|\). Since \(0<\lambda\), `inv_pos.mpr hlam` gives \(0<\lambda^{-1}\), so `abs_of_pos` gives \(|\lambda^{-1}|=\lambda^{-1}\). The inequality is therefore \(\lambda^{-1}\|x\|\le r\). Because \(\lambda>0\), `inv_mul_le_iff₀ hlam` rearranges this into \(\|x\|\le \lambda r\), up to commutativity of multiplication, which is exactly `hx`. Thus \(\lambda^{-1}x\) lies in the closed ball of radius \(r\).

3. The line `have hmem : lam⁻¹ • x ∈ subdifferential phi 0` then applies `mem_closedBall_zero_iff.mpr hscaled_norm`. The lemma `mem_closedBall_zero_iff` says that \(u\in\operatorname{closedBall}(0,r)\) is equivalent to \(\|u\|\le r\). Applying `.mpr` to `hscaled_norm` places \(\lambda^{-1}x\) in the closed ball \(B(0,r)\). The hypothesis `hball` states that this ball is contained in \(\partial\phi(0)\), so applying it gives
\[
\lambda^{-1}x\in\partial\phi(0).
\]
This is the key subgradient information that will be transported back to \(x\).

4. The command `rw [ERealFunction.scaledProximityOperator, eq_comm]` first unfolds the definition of the scaled proximal operator. By definition, `scaledProximityOperator f hf γ` is the proximal operator of the scaled function \(\gamma f\), so the goal becomes
\[
\operatorname{prox}_{\lambda\phi.toEReal}(x)=0.
\]
The rewrite `eq_comm` reverses this equality to
\[
0=\operatorname{prox}_{\lambda\phi.toEReal}(x),
\]
matching the orientation of the proximal characterization theorem.

5. The `refine` step applies `eq_proximityOperator_iff_sub_mem_subdifferential`. That theorem states that for \(f\in\Gamma_0(H)\) and points \(x,p\in H\),
\[
p=\operatorname{Prox}_f(x)\quad\Longleftrightarrow\quad x-p\in\partial f(p).
\]
Here the proof chooses
\[
f=\lambda\phi.toEReal,\qquad p=0.
\]
The required membership \(f\in\Gamma_0(H)\) is supplied by `smul_mem_gammaZero`: if \(g\in\Gamma_0(H)\) and \(\gamma\) is a positive real, then \(\gamma g\in\Gamma_0(H)\). Since \(\phi.toEReal\in\Gamma_0(H)\) and \(\lambda>0\), we get \(\lambda\phi.toEReal\in\Gamma_0(H)\). The reverse implication `.2` of the characterization turns the equality \(0=\operatorname{Prox}_{\lambda\phi}(x)\) into the membership
\[
x-0\in\partial(\lambda\phi.toEReal)(0).
\]

6. The rewrite `subdifferential_posReal_smul_eq_smul` applies the rule
\[
\partial(\lambda f)=\lambda\cdot\partial f
\]
for a positive scalar \(\lambda\). Specialized to \(f=\phi.toEReal\) and evaluated at \(0\), it gives
\[
\partial(\lambda\phi.toEReal)(0)=\lambda\cdot\partial(\phi.toEReal)(0).
\]
The `change` line only restates the resulting goal in explicit set-valued-operator notation:
\[
x-0\in\lambda\cdot\partial(\phi.toEReal)(0).
\]
Mathematically, this is the subgradient scaling rule: being a subgradient of \(\lambda\phi\) at \(0\) is the same as being \(\lambda\) times a subgradient of \(\phi\) at \(0\).

7. The rewrite `Set.mem_smul_set_iff_inv_smul_mem₀ hlam.ne'` uses the fact that \(\lambda\ne0\), which follows from \(0<\lambda\). The lemma states that for a nonzero scalar \(a\) and a set \(S\),
\[
z\in a\cdot S\quad\Longleftrightarrow\quad a^{-1}\cdot z\in S.
\]
Here \(a=\lambda\), \(z=x-0\), and \(S=\partial(\phi.toEReal)(0)\). The goal therefore becomes
\[
\lambda^{-1}\cdot(x-0)\in\partial(\phi.toEReal)(0).
\]
This is the algebraic step of dividing the subgradient membership by \(\lambda\).

8. Finally, `simpa [sub_zero] using hmem` simplifies \(x-0\) to \(x\), so the goal is
\[
\lambda^{-1}\cdot x\in\partial(\phi.toEReal)(0).
\]
The hypothesis `hmem` says exactly that \(\lambda^{-1}\cdot x\in\partial\phi(0)\). The simplification identifies the subdifferential of the real-valued function \(\phi\) with that of its extended-real version \(\phi.toEReal\), because coercing \(\phi.toEReal(y)\) back to `EReal` gives the same value as \(\phi(y)\), as recorded by `toEReal_apply`. Hence the goal is exactly `hmem`, and the proof is complete.

The hypothesis \(0<r\) is present in the statement but is not used in the displayed proof. The completeness assumption is part of the ambient Hilbert-space setting required for the proximal operator theory, though it is not explicitly named in the proof script.

