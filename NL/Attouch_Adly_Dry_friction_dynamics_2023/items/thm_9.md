## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_9.lean`

## Lean statement
```lean
theorem theorem_A_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {t₀ r : ℝ}
    (hr : 0 < r) (f : H → ℝ) (z : ℝ → H) (hf : ContDiff ℝ 1 f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hgradient_lip : LocallyLipschitz (gradient f))
    (hinitial : r < ‖gradient f (z t₀)‖)
    (hsolution : IsDrygradTrajectory r f z t₀)
    (hz_diff : Differentiable ℝ z) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀)
```

## Statement explanation
The declaration `theorem_A_1` is stated for a real Hilbert space \(H\), encoded by the typeclasses `NormedAddCommGroup`, `InnerProductSpace ℝ H`, and `CompleteSpace H`. It fixes real parameters \(t_0\) and \(r\) with \(0<r\), a function \(f:H\to\mathbb R\), and a trajectory \(z:\mathbb R\to H\). The hypotheses are:

- `hf`: \(f\) is \(C^1\), i.e. continuously differentiable.
- `hf_lower`: \(f\) is bounded below, meaning there exists \(m\in\mathbb R\) such that \(m\le f(x)\) for every \(x\in H\).
- `hgradient_lip`: the gradient map \(\nabla f\) is locally Lipschitz.
- `hinitial`: the initial gradient norm satisfies
  \[
  r<\|\nabla f(z(t_0))\|.
  \]
- `hsolution`: \(z\) is a dry-gradient trajectory for \(f\) with threshold \(r\) and initial time \(t_0\), written `IsDrygradTrajectory r f z t₀`. The provided source does not expand the internal definition of this predicate, so it is treated as the hypothesis that \(z\) satisfies the dry-gradient trajectory condition.
- `hz_diff`: \(z\) is differentiable as a map \(\mathbb R\to H\).

The conclusion is
\[
\operatorname{AntitoneOn}\bigl(t\mapsto f(z(t))\bigr)\bigl([t_0,\infty)\bigr).
\]
Mathematically, this says that the energy function \(t\mapsto f(z(t))\) is nonincreasing on the interval \([t_0,\infty)\): whenever \(t_0\le s\le t\), one has
\[
f(z(t))\le f(z(s)).
\]
Thus theorem_A_1 extracts only the monotonicity of the potential energy along the dry-friction gradient trajectory; it does not itself assert convergence, integrability, or any limit behavior.

## Lean proof
```lean
(theorem_2_1 hr f z hf hf_lower hgradient_lip hz_diff hinitial hsolution).1
```

## Proof explanation
The proof is not a tactic proof. It is a single term obtained by applying `theorem_2_1` and then projecting out the first conjunct of its conclusion.

The cited theorem `theorem_2_1` applies under the same typeclass assumptions on \(H\) and under the hypotheses \(0<r\), \(f\) is \(C^1\), \(f\) is bounded below, \(\nabla f\) is locally Lipschitz, \(z\) is differentiable, \(r<\|\nabla f(z(t_0))\|\), and \(z\) is a dry-gradient trajectory for \(r\), \(f\), and \(t_0\). Its conclusion is the conjunction
\[
\operatorname{AntitoneOn}\bigl(t\mapsto f(z(t))\bigr)\bigl([t_0,\infty)\bigr)
\]
together with
\[
\operatorname{IntegrableOn}\bigl(t\mapsto \|\operatorname{deriv} z(t)\|^2\bigr)\bigl([t_0,\infty)\bigr),
\]
\[
\operatorname{IntegrableOn}\bigl(t\mapsto \|\operatorname{deriv} z(t)\|\bigr)\bigl([t_0,\infty)\bigr),
\]
and the existence of a limit point \(z_\infty\in H\) such that
\[
z(t)\to z_\infty\quad\text{as }t\to\infty,
\qquad
\|\nabla f(z_\infty)\|=r,
\]
and either there is \(T\ge t_0\) with \(z(t)=z_\infty\) for all \(t\ge T\), or else
\[
r<\|\nabla f(z(t))\|\quad\text{for all }t\ge t_0.
\]
The proof only needs the first conjunct of this stronger statement.

The Lean term applies `theorem_2_1` with the arguments
`hr f z hf hf_lower hgradient_lip hz_diff hinitial hsolution`.
The order of `hz_diff` and `hinitial` in this call follows the argument order of `theorem_2_1`; the target statement lists those hypotheses in a different order, but that does not affect the mathematical content. All hypotheses required by `theorem_2_1` are exactly the available hypotheses of `theorem_A_1`.

After `theorem_2_1` produces its conjunction, the projection `.1` extracts the first component, namely
\[
\operatorname{AntitoneOn}\bigl(t\mapsto f(z(t))\bigr)\bigl([t_0,\infty)\bigr).
\]
This is precisely the conclusion of `theorem_A_1`. No rewriting, simplification, arithmetic reasoning, or logical introduction is performed, so commands such as `intro`, `rw`, `simp`, and `linarith` play no role here. The only proof step is the elimination of a conjunction by taking its first component.

