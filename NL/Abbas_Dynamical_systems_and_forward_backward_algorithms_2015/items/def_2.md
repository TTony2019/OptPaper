## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/def_2.lean`

## Lean statement
```lean
noncomputable def lyapunovGamma {H : Type*} [NormedAddCommGroup H]
    (x : ℝ → H) (mu : ℝ) (g : ℝ → ℝ) (z : H) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 + mu * g t
```

## Statement explanation
The declaration defines a noncomputable function named `lyapunovGamma`. The implicit type parameter is an arbitrary type \(H\) equipped with the typeclass instance `NormedAddCommGroup H`, so \(H\) is an additive commutative group with a norm; in particular, one can subtract two elements of \(H\) and take the norm of the resulting element. The explicit arguments are:

- \(x : \mathbb{R} \to H\), a function from real numbers to \(H\), thought of as a state or trajectory parameterized by a real variable;
- \(\mu : \mathbb{R}\), a real scalar;
- \(g : \mathbb{R} \to \mathbb{R}\), a real-valued function of the real variable;
- \(z : H\), a point of \(H\), used as a reference or target point;
- \(t : \mathbb{R}\), the real variable at which the function is evaluated.

The result is a real number, and `lyapunovGamma x mu g z t` is defined to be

\[
\frac12 \left\|x(t)-z\right\|^2 + \mu g(t).
\]

Here \(x(t)-z\) is the displacement from the reference point \(z\) to the current state \(x(t)\), and \(\left\|x(t)-z\right\|^2\) is its squared norm. The term \(\frac12\left\|x(t)-z\right\|^2\) is therefore one half of the squared distance from \(x(t)\) to \(z\). The term \(\mu g(t)\) is the real number obtained by multiplying the scalar \(\mu\) by the value \(g(t)\). No hypotheses are imposed on \(x\), \(\mu\), \(g\), \(z\), or \(t\) beyond their types; for example, \(\mu\) is not required to be nonnegative, and \(g\) is not required to be continuous or differentiable. The declaration is a definition, not a theorem: it names the real-valued function

\[
t \mapsto \frac12 \left\|x(t)-z\right\|^2 + \mu g(t)
\]

for fixed \(x\), \(\mu\), \(g\), and \(z\). It does not assert any inequality, monotonicity, decrease property, or Lyapunov property.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source consists only of a definition body and contains no theorem to prove, so there are no hypotheses to introduce, no rewrites or simplifications to perform, and no applications of exactness, linear arithmetic, or any named theorem or lemma. No local result is cited, because no proof step invokes one.

The mathematical content is exactly the defining formula above. In Lean, whenever the expression `lyapunovGamma x mu g z t` appears, it can be unfolded to

\[
\left(\frac12 : \mathbb{R}\right) \cdot \left\|x(t)-z\right\|^2 + \mu \cdot g(t),
\]

which is the same as

\[
\frac12 \left\|x(t)-z\right\|^2 + \mu g(t).
\]

The marker `noncomputable` affects only how Lean treats computation for this definition; it does not add any mathematical hypotheses or conclusions. The definition itself merely introduces a real-valued function of \(t\) built from the squared distance from \(x(t)\) to \(z\) and the scalar multiple \(\mu g(t)\).

