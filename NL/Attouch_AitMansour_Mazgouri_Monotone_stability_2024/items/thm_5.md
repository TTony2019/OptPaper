## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_5.lean`

## Lean statement
```lean
theorem thm_5 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (β γ : ℝ)
    (δ : M → ℝ) (k₁ γ₁ : ℝ)
    (hβγ : β * γ > 1)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁) :
    ∀ μ μ' : M, let cmax
```

## Statement explanation
The declaration `thm_5` is a stability estimate for two trajectories of the DIN system, parametrized by elements of \(M\). The space \(H\) is a complete real inner product space, hence a real Hilbert space, and \(M\) is a real normed additive commutative group used as a parameter space. For each \(\mu\in M\), the function \(\phi_\mu=\phi(\mu,\cdot)\) is a real-valued potential on \(H\), with gradient field \(\operatorname{grad}\phi_\mu=\operatorname{grad}\phi(\mu,\cdot)\) and Hessian field \(\operatorname{hess}\phi_\mu=\operatorname{hess}\phi(\mu,\cdot)\). The functions
\[
x,dx,ddx:M\to \mathbb R\to H
\]
represent, for each parameter \(\mu\), the position \(x_\mu\), velocity \(dx_\mu\), and acceleration \(ddx_\mu\) of the associated DIN trajectory. The maps \(u_0,v_0:M\to H\) give the initial position and velocity, while \(\beta,\gamma\in\mathbb R\) and \(\delta:M\to\mathbb R\) are the DIN and strong-convexity parameters. The constants \(k_1,\gamma_1\) control the dependence of the gradient field on the parameter \(\mu\).

The hypotheses are as follows. First, the stability parameters satisfy
\[
\beta\gamma>1,\qquad \beta>0,\qquad \gamma>0.
\]
For every \(\mu\), the potential \(\phi_\mu\) is differentiable on \(H\), and \(\operatorname{grad}\phi_\mu(q)\) is the actual gradient of \(\phi_\mu\) at \(q\), meaning that the derivative of \(\phi_\mu\) at \(q\) is represented by the inner product with \(\operatorname{grad}\phi_\mu(q)\). Each \(\phi_\mu\) is strongly convex with modulus \(\delta(\mu)\). The constants satisfy
\[
k_1>0,\qquad 0<\gamma_1,\qquad \gamma_1\le 1.
\]
The hypothesis `hDIN` says that for each \(\mu\), the triple \((x_\mu,dx_\mu,ddx_\mu)\) is a DIN trajectory associated with \(\phi_\mu\), \(\operatorname{grad}\phi_\mu\), \(\operatorname{hess}\phi_\mu\), parameters \(\gamma,\beta\), and initial data \(u_0(\mu),v_0(\mu)\). The hypotheses `hderiv` and `hddx` say that, for almost every \(t\ge 0\) with respect to Lebesgue measure restricted to \([0,\infty)\),
\[
x_\mu'(t)=dx_\mu(t),\qquad dx_\mu'(t)=ddx_\mu(t),
\]
so \(x_\mu\) is a twice differentiable trajectory in the almost-everywhere sense. The hypothesis `hhess` says that for every \(\mu\) and \(q\), the Fréchet derivative of \(\operatorname{grad}\phi_\mu\) at \(q\) is a continuous linear map \(L\) satisfying
\[
Lv=\operatorname{hess}\phi_\mu(q)v
\]
for every \(v\in H\). Thus \(\operatorname{hess}\phi_\mu\) is the Hessian field of the potential. The hypothesis `hlip` says that for every \(\mu\) and every \(T'>0\), the gradient field \(\operatorname{grad}\phi_\mu\) is Lipschitz on the image \(x_\mu([0,T'])\) of the trajectory segment. Finally, `h9` says that for every \(x_*\in H\) and all \(\mu,\mu'\in M\),
\[
\|\operatorname{grad}\phi_\mu(x_*)-\operatorname{grad}\phi_{\mu'}(x_*)\|
\le k_1\|\mu-\mu'\|^{\gamma_1}.
\]
Thus the gradient field depends on the parameter \(\mu\) in a uniform Hölder manner with exponent \(\gamma_1\).

The conclusion is an estimate for the distance between two trajectories \(x_\mu\) and \(x_{\mu'}\). For \(\mu,\mu'\in M\), define
\[
c_{\max}
=
\max\left\{
\operatorname{energyRate}(\beta,\gamma,\delta(\mu)),
\operatorname{energyRate}(\beta,\gamma,\delta(\mu'))
\right\},
\]
where
\[
\operatorname{energyRate}(\beta,\gamma,\delta)
=
\frac{(\beta\delta+\gamma)-\sqrt{(\beta\delta+\gamma)^2-4\delta}}{2}.
\]
Also define the auxiliary initial coordinate
\[
\operatorname{dinAuxInitial}(\mu)
=
-\left(\sqrt{\left(\gamma-\frac1\beta\right)\frac1\beta}\right)^{-1}
\left(
v_0(\mu)+\beta\,\operatorname{grad}\phi_\mu(u_0(\mu))
+\left(\gamma-\frac1\beta\right)u_0(\mu)
\right).
\]
Then for Lebesgue-almost every \(t\in\mathbb R\), if \(0\le t\), one has
\[
\|x_\mu(t)-x_{\mu'}(t)\|
\le
e^{-c_{\max}t}
\sqrt{
\|u_0(\mu)-u_0(\mu')\|^2
+
\|\operatorname{dinAuxInitial}(\mu)-\operatorname{dinAuxInitial}(\mu')\|^2
}
+
\frac{\beta k_1}{c_{\max}}
\bigl(1-e^{-c_{\max}t}\bigr)
\|\mu-\mu'\|^{\gamma_1}.
\]
In words, the two DIN trajectories starting from \(u_0(\mu),v_0(\mu)\) and \(u_0(\mu'),v_0(\mu')\) remain close for nonnegative times. Their distance is bounded by an exponentially decaying term measuring the mismatch of the initial data, including the transformed auxiliary initial coordinate, plus a term measuring the mismatch of the parameters \(\mu,\mu'\) with Hölder exponent \(\gamma_1\). The decay rate is the maximum of the two energy rates determined by the strong-convexity moduli \(\delta(\mu)\) and \(\delta(\mu')\).

## Lean proof
```lean
max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
        ‖x μ t - x μ' t‖ ≤ Real.exp (-cmax * t) *
            Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
          (β * k₁ / cmax) * (1 - Real.exp (-cmax * t)) * ‖μ - μ'‖ ^ γ₁ := by
  intro μ μ'
  filter_upwards [] with t
  intro ht
  exact thm_5_estimate_all φ gradφ hessφ x dx ddx u₀ v₀ β γ δ k₁ γ₁ hβγ hβ hγ hdiff
    hgrad hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 μ μ' t ht
```

## Proof explanation
The proof is a direct reduction to the already established all-parameters estimate `thm_5_estimate_all`. It begins with
\[
\texttt{intro }\mu\ \mu'.
\]
Since the goal is \(\forall \mu\,\mu':M,\dots\), this introduces two arbitrary parameters \(\mu,\mu'\in M\). The remaining goal is the local-let statement with \(c_{\max}\) defined from \(\delta(\mu)\) and \(\delta(\mu')\), followed by an almost-everywhere inequality over Lebesgue measure.

Next the proof uses
\[
\texttt{filter\_upwards [] with }t.
\]
The goal at this point is an almost-everywhere assertion of the form
\[
\forall^{\mathrm{a.e.}} t,\quad 0\le t\to \text{(the inequality)}.
\]
The tactic `filter_upwards` reduces such a goal to proving the property for a generic \(t\). The empty list means that no previously established almost-everywhere facts are being combined; it is enough to prove the statement for an arbitrary \(t\), because a property that holds for every \(t\) certainly holds almost everywhere. The variable \(t\) introduced here is that generic time.

Then the proof uses
\[
\texttt{intro }ht.
\]
This introduces the hypothesis \(0\le t\). The goal is now exactly the displayed inequality for this particular \(t\), namely
\[
\|x_\mu(t)-x_{\mu'}(t)\|
\le
e^{-c_{\max}t}
\sqrt{
\|u_0(\mu)-u_0(\mu')\|^2
+
\|\operatorname{dinAuxInitial}(\mu)-\operatorname{dinAuxInitial}(\mu')\|^2
}
+
\frac{\beta k_1}{c_{\max}}
\bigl(1-e^{-c_{\max}t}\bigr)
\|\mu-\mu'\|^{\gamma_1}.
\]

Finally the proof uses
\[
\texttt{exact thm\_5\_estimate\_all }\dots\ \mu\ \mu'\ t\ ht.
\]
The cited theorem `thm_5_estimate_all` has the same hypotheses as `thm_5`: the potential \(\phi\), its gradient \(\operatorname{grad}\phi\), its Hessian \(\operatorname{hess}\phi\), the trajectory maps \(x,dx,ddx\), initial data \(u_0,v_0\), parameters \(\beta,\gamma,\delta,k_1,\gamma_1\), and all of the assumptions `hβγ`, `hβ`, `hγ`, `hdiff`, `hgrad`, `hstrong`, `hk₁`, `hγ₁_pos`, `hγ₁_le`, `hDIN`, `hderiv`, `hddx`, `hhess`, `hlip`, and `h9`. In the form used here, it takes two parameters \(\mu,\mu'\), a real time \(t\), and the proof \(0\le t\), and returns precisely the inequality displayed above with
\[
c_{\max}
=
\max\left\{
\operatorname{energyRate}(\beta,\gamma,\delta(\mu)),
\operatorname{energyRate}(\beta,\gamma,\delta(\mu'))
\right\}.
\]
Thus the current theorem does not reprove the analytic estimate; it simply packages the pointwise estimate supplied by `thm_5_estimate_all` into an almost-everywhere statement over Lebesgue measure. The `exact` command closes the goal by applying that theorem with all the global hypotheses and the chosen \(\mu,\mu',t,ht\). No rewriting, simplification, or arithmetic tactic such as `rw`, `simp`, or `linarith` is used in this proof.

