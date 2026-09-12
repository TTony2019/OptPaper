## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/ext_thm_2.lean`

## Lean statement
```lean
theorem variableMetric_composite_proximal_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f g : H → EReal) (A : H →L[ℝ] H) (b : H)
    (M : H →L[ℝ] H) (lam : ℝ) (hlam : 0 < lam)
    (hconvex : Convex ℝ (ERealFunction.epigraph g))
    (hlsc : LowerSemicontinuous g) (hproper : ERealFunction.IsProper g)
    (hf : ∀ x, f x = (((1 / 2 : ℝ) * ‖A x - b‖ ^ 2 : ℝ) : EReal) + g x)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A))
    (_hM_positive : ∀ v, v ≠ 0 → 0 < @inner ℝ H _ (M v) v) (proxF : H → H)
    (hproxF : ∀ x, ∃ (_hp : f (proxF x) ≠ ⊤),
      M (x - proxF x) ∈ (fun u ↦ lam • u) '' subdifferential f (proxF x)) (x : H) :
    proxF x = ERealFunction.scaledProximityOperator (ERealFunction.properIoi g hproper)
      (properIoi_mem_gammaZero_of_epigraph_convex_lsc hproper hconvex hlsc) ⟨lam, hlam⟩
      (x - lam • A.adjoint (A x - b))
```

## Statement explanation
Let \(H\) be a real Hilbert space. Let \(f,g: H \to \overline{\mathbb R}\) be extended-real functions, let \(A: H \to H\) be a continuous linear map, let \(b \in H\), let \(M: H \to H\) be a continuous linear map, and let \(\lambda \in \mathbb R\) with \(\lambda>0\). Write \(A^*\) for the Hilbert adjoint of \(A\). The hypotheses are that \(g\) is proper, that its epigraph is convex, and that \(g\) is lower semicontinuous; that
\[
f(x)=\frac12\|Ax-b\|^2+g(x)
\]
for every \(x\); that
\[
M=I-\lambda A^*A;
\]
that \(M\) is positive definite, meaning \(\langle Mv,v\rangle>0\) for every \(v\ne0\); and that a function \(\operatorname{prox}_F:H\to H\) satisfies the variable-metric proximal optimality condition: for each \(x\), with \(p=\operatorname{prox}_F x\), there exists \(u\in\partial f(p)\) such that
\[
M(x-p)=\lambda u,
\]
and also \(f(p)\ne+\infty\).

Here \(\partial\) is the convex subdifferential: for an extended-real function \(h\), the relation \(u\in\partial h(p)\) means
\[
\langle y-p,u\rangle+h(p)\le h(y)
\]
for every \(y\in H\). The expression `properIoi g hproper` is the same function \(g\), but regarded as a function whose values lie in \(\{z\in\overline{\mathbb R}:z>-\infty\}\); properness supplies the fact that \(g\) never takes the value \(-\infty\). The cited result `properIoi_mem_gammaZero_of_epigraph_convex_lsc` says that because \(g\) is proper, convex in the epigraph sense, and lower semicontinuous, this version of \(g\) belongs to \(\Gamma_0(H)\). For a function \(h\in\Gamma_0(H)\) and \(\lambda>0\), the scaled proximity operator \(\operatorname{Prox}_{\lambda h}(z)\) is the unique minimizer of
\[
y\mapsto \lambda h(y)+\frac12\|z-y\|^2.
\]

The conclusion of the theorem is
\[
\operatorname{prox}_F(x)
=
\operatorname{Prox}_{\lambda \iota(g)}
\bigl(x-\lambda A^*(Ax-b)\bigr),
\]
where \(\iota(g)\) denotes `properIoi g hproper`. Thus the theorem says that the variable-metric proximal point of the composite function \(f=\frac12\|A\cdot-b\|^2+g\), taken with metric \(M=I-\lambda A^*A\), coincides with the ordinary \(\lambda\)-scaled proximal point of \(g\) evaluated at the gradient step \(x-\lambda A^*(Ax-b)\). The positive-definiteness hypothesis on \(M\) is part of the statement, though the proof given below does not explicitly invoke it.

## Lean proof
```lean
by
  rcases hproxF x with ⟨hp, u, hu, hMu⟩
  have hres : x - lam • A.adjoint (A x - b) - proxF x =
      lam • (u - A.adjoint (A (proxF x) - b)) := by
    have hMu' : x - proxF x - lam • A.adjoint (A (x - proxF x)) = lam • u := by
      rw [hM] at hMu
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at hMu
      exact hMu.symm
    calc
      x - lam • A.adjoint (A x - b) - proxF x =
          x - proxF x - lam • A.adjoint (A (x - proxF x)) -
            lam • A.adjoint (A (proxF x) - b) := by
              simp [map_sub]
              module
      _ = lam • u - lam • A.adjoint (A (proxF x) - b) := by rw [hMu']
      _ = lam • (u - A.adjoint (A (proxF x) - b)) := by module
  have hg : u - A.adjoint (A (proxF x) - b) ∈ subdifferential g (proxF x) :=
    subgradientEReal_quadratic_add A b (proxF x) u g f hconvex hproper hf hp hu
  have hΓ : ERealFunction.properIoi g hproper ∈ Γ₀(H) :=
    properIoi_mem_gammaZero_of_epigraph_convex_lsc hproper hconvex hlsc
  rw [ERealFunction.scaledProximityOperator]
  refine (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
    (f := (⟨lam, hlam⟩ : PosReal) • ERealFunction.properIoi g hproper)
    (ERealFunction.smul_mem_gammaZero _ hΓ ⟨lam, hlam⟩)
    (x - lam • A.adjoint (A x - b)) (proxF x)).2 ?_
  rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
  change x - lam • A.adjoint (A x - b) - proxF x ∈
    (lam : ℝ) • (subdifferential (ERealFunction.properIoi g hproper) (proxF x))
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hlam.ne']
  rw [hres, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  simpa [ERealFunction.properIoi, ERealFunction.subdifferential] using hg
```

## Proof explanation
Fix \(x\), and write \(p=\operatorname{prox}_F x\). The proof begins by using `rcases` on the hypothesis `hproxF x`. This destroys the existential statement and produces a proof \(hp:f(p)\ne+\infty\), a vector \(u\), a proof \(hu:u\in\partial f(p)\), and an equality
\[
\lambda u=M(x-p).
\]
This is exactly the variable-metric proximal optimality condition read as an equality between \(\lambda u\) and the metric displacement \(M(x-p)\).

The next step derives the auxiliary identity
\[
x-p-\lambda A^*(A(x-p))=\lambda u.
\]
Indeed, from \(M=I-\lambda A^*A\), we have
\[
M(x-p)=x-p-\lambda A^*(A(x-p)).
\]
The equality \(\lambda u=M(x-p)\) therefore gives the displayed identity after reversing the sides. In Lean this is done by rewriting with `hM`, simplifying the continuous-linear-map operations, and then using `hMu.symm`.

The proof then establishes the algebraic identity
\[
x-\lambda A^*(Ax-b)-p
=
\lambda\bigl(u-A^*(Ap-b)\bigr).
\]
It proves this by a `calc` chain. First, using linearity of \(A\),
\[
Ax-b=A(x-p)+(Ap-b),
\]
so
\[
x-\lambda A^*(Ax-b)-p
=
x-p-\lambda A^*(A(x-p))-\lambda A^*(Ap-b).
\]
The tactic `simp [map_sub]` uses linearity to rewrite the difference inside \(A\), and `module` normalizes the resulting module expression. Second, the previously derived identity replaces \(x-p-\lambda A^*(A(x-p))\) by \(\lambda u\), giving
\[
\lambda u-\lambda A^*(Ap-b).
\]
Third, `module` distributes the scalar \(\lambda\), producing
\[
\lambda\bigl(u-A^*(Ap-b)\bigr).
\]
This is the identity needed later.

Now the cited theorem `subgradientEReal_quadratic_add` is applied with \(A,b,p,u,g,f\). Its assumptions match the present hypotheses: \(g\) has convex epigraph, \(g\) is proper, \(f\) is given by
\[
f(z)=\frac12\|Az-b\|^2+g(z),
\]
the value \(f(p)\) is not \(+\infty\), and \(u\in\partial f(p)\). Its conclusion is
\[
u-A^*(Ap-b)\in\partial g(p).
\]
Mathematically, this is the subgradient decomposition for a smooth quadratic plus a nonsmooth convex function: the quadratic part has gradient \(A^*(Az-b)\), so any subgradient \(u\) of \(f\) at \(p\) differs from that gradient by a subgradient of \(g\) at \(p\).

Next, the proof applies `properIoi_mem_gammaZero_of_epigraph_convex_lsc` to \(g\), using properness, convexity of the epigraph, and lower semicontinuity. It concludes
\[
\iota(g):=\operatorname{properIoi}(g,\text{hproper})\in\Gamma_0(H).
\]
Thus \(g\), viewed as a function with values greater than \(-\infty\), is a proper convex lower semicontinuous function in the sense required for proximal theory.

The definition of `scaledProximityOperator` is then unfolded with `rw`. The goal becomes an equality with the proximity operator of the scaled function \(\lambda\iota(g)\). To prove it, the proof invokes the cited equivalence `eq_proximityOperator_iff_sub_mem_subdifferential`. For a function \(h\in\Gamma_0(H)\) and points \(z,p\in H\), that theorem states
\[
p=\operatorname{Prox}_h(z)
\iff
z-p\in\partial h(p).
\]
This is the first-order optimality condition for the proximal minimization problem. The membership \(h\in\Gamma_0(H)\) needed for \(h=\lambda\iota(g)\) is supplied by `smul_mem_gammaZero`, which says that a positive scalar multiple of a \(\Gamma_0(H)\) function remains in \(\Gamma_0(H)\). The proof uses the backward direction of the equivalence, so it remains to prove
\[
z-p\in\partial(\lambda\iota(g))(p),
\]
where
\[
z=x-\lambda A^*(Ax-b).
\]

The subdifferential of the scaled function is then rewritten using `subdifferential_posReal_smul_eq_smul`, which states
\[
\partial(\lambda\iota(g))(p)
=
\lambda\cdot\partial\iota(g)(p).
\]
Here the right-hand side is the set of all vectors \(\lambda w\) with \(w\in\partial\iota(g)(p)\). After this rewrite, the `change` tactic restates the goal as
\[
z-p\in\lambda\cdot\partial\iota(g)(p).
\]

Since \(\lambda\ne0\), the lemma `Set.mem_smul_set_iff_inv_smul_mem₀` converts membership in \(\lambda\cdot S\) into membership of \(\lambda^{-1}\) times the vector in \(S\). Therefore the goal becomes
\[
\lambda^{-1}(z-p)\in\partial\iota(g)(p).
\]
Using the earlier identity
\[
z-p=x-\lambda A^*(Ax-b)-p
=
\lambda\bigl(u-A^*(Ap-b)\bigr),
\]
we obtain
\[
\lambda^{-1}(z-p)
=
\lambda^{-1}\bigl(\lambda(u-A^*(Ap-b))\bigr)
=
u-A^*(Ap-b).
\]
The simplifications `smul_smul`, `inv_mul_cancel₀ hlam.ne'`, and `one_smul` perform exactly this cancellation. Hence the goal is reduced to
\[
u-A^*(Ap-b)\in\partial\iota(g)(p).
\]

Finally, the proof uses `simpa [ERealFunction.properIoi, ERealFunction.subdifferential] using hg`. The simplification unfolds `properIoi` and `subdifferential`. Since `properIoi g hproper` coerces back to \(g\), membership in \(\partial\iota(g)(p)\) is the same subgradient inequality as membership in \(\partial g(p)\). The already established fact
\[
u-A^*(Ap-b)\in\partial g(p)
\]
therefore proves the desired membership. Consequently the backward direction of the proximal characterization applies, and
\[
p=\operatorname{prox}_F x
=
\operatorname{Prox}_{\lambda\iota(g)}
\bigl(x-\lambda A^*(Ax-b)\bigr),
\]
which is the stated variable-metric composite proximal identity.

