## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_5.lean`

## Lean statement
```lean
theorem reverse_time_scaling_average
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {α s₀ : ℝ} (hα : 1 < α) (hs₀ : 0 < s₀)
    (x z : ℝ → H) (hx : ContDiff ℝ 2 x)
    (hinitial : x s₀ = z (s₀ ^ 2 / (2 * (α - 1))))
    (hrelation : ∀ s ∈ Set.Ici s₀,
      z (s ^ 2 / (2 * (α - 1))) =
        x s + (s / (α - 1)) • deriv x s) :
    ∃ y : ℝ → H,
      y = timeScaledTrajectory z
          (fun s : ℝ => s ^ 2 / (2 * (α - 1))) ∧
      IsWeightedAverageOn
        (fun s : ℝ => s ^ 2 / (2 * (α - 1)))
        (fun s : ℝ => s / (α - 1)) x y (deriv x) s₀
```

## Statement explanation
The declaration is a theorem named `reverse_time_scaling_average`. It is stated for a type \(H\) carrying the structures of a real normed additive commutative group, a real inner product space, and a complete space; thus \(H\) is a complete real inner product space, in particular a real normed vector space. The real parameters are \(\alpha\) and \(s_0\), with hypotheses \(h_\alpha : 1 < \alpha\) and \(h_{s_0} : 0 < s_0\). The theorem also takes two curves \(x,z : \mathbb R \to H\). The curve \(x\) is assumed to be twice continuously differentiable, \(h_x : \operatorname{ContDiff}_{\mathbb R}^2 x\). There is an initial matching hypothesis

\[
h_{\mathrm{initial}} : x(s_0)=z\!\left(\frac{s_0^2}{2(\alpha-1)}\right),
\]

and a relation hypothesis

\[
h_{\mathrm{relation}} : \forall s \in \operatorname{Ici}s_0,\quad
z\!\left(\frac{s^2}{2(\alpha-1)}\right)
=
x(s)+\frac{s}{\alpha-1}\cdot \operatorname{deriv}x(s),
\]

where \(s \in \operatorname{Ici}s_0\) means \(s \ge s_0\), and the dot denotes scalar multiplication by the real number \(\frac{s}{\alpha-1}\).

The conclusion asserts the existence of a curve \(y : \mathbb R \to H\) such that

\[
y = \operatorname{timeScaledTrajectory} z \left(s \mapsto \frac{s^2}{2(\alpha-1)}\right)
\]

and

\[
\operatorname{IsWeightedAverageOn}
\left(s \mapsto \frac{s^2}{2(\alpha-1)}\right)
\left(s \mapsto \frac{s}{\alpha-1}\right)
x\ y\ (\operatorname{deriv}x)\ s_0.
\]

The cited definition `timeScaledTrajectory` says that for \(z : \mathbb R \to H\) and a time change \(\tau : \mathbb R \to \mathbb R\),

\[
\operatorname{timeScaledTrajectory} z \tau = \bigl(s \mapsto z(\tau(s))\bigr).
\]

Thus the first conjunct of the conclusion says precisely that

\[
y(s)=z\!\left(\frac{s^2}{2(\alpha-1)}\right)
\]

for every real \(s\).

The cited definition `IsWeightedAverageOn` unfolds to the following three requirements, where we write

\[
\tau(s)=\frac{s^2}{2(\alpha-1)},\qquad d\tau(s)=\frac{s}{\alpha-1}.
\]

First, \(\operatorname{IsIncreasingC1TimeScaleOn}\ \tau\ d\tau\ s_0\) must hold. Second, the initial values must agree:

\[
x(s_0)=y(s_0).
\]

Third, for every \(s \in \operatorname{Ici}s_0\), the curve \(x\) must have derivative \(\operatorname{deriv}x(s)\) at \(s\), and the weighted-average relation

\[
\operatorname{deriv}x(s)+ (d\tau(s))^{-1}\cdot (x(s)-y(s))=0
\]

must hold. Here \((d\tau(s))^{-1}\) is the reciprocal of the real number \(d\tau(s)\), and the dot is scalar multiplication on \(H\).

The cited theorem `quadraticTimeScale_isIncreasingC1TimeScaleOn` provides exactly the first requirement: if \(1<\alpha\) and \(0<s_0\), then

\[
\operatorname{IsIncreasingC1TimeScaleOn}
\left(s \mapsto \frac{s^2}{2(\alpha-1)}\right)
\left(s \mapsto \frac{s}{\alpha-1}\right)
s_0.
\]

Its full internal definition of `IsIncreasingC1TimeScaleOn` is not needed beyond this stated consequence. Mathematically, the theorem says that if \(x\) is \(C^2\), and \(z\) is related to \(x\) by the reverse time-scaled formula

\[
z(\tau(s))=x(s)+d\tau(s)\operatorname{deriv}x(s)\qquad (s\ge s_0),
\]

with \(x(s_0)=z(\tau(s_0))\), then the curve \(y=z\circ\tau\) satisfies the weighted-average relation

\[
\operatorname{deriv}x(s)+d\tau(s)^{-1}(x(s)-y(s))=0.
\]

Indeed, this is just the rearrangement of \(y(s)=x(s)+d\tau(s)\operatorname{deriv}x(s)\). The theorem packages this as an existence statement for a curve \(y\) satisfying `IsWeightedAverageOn`.

## Lean proof
```lean
by
  let τ : ℝ → ℝ := fun s => s ^ 2 / (2 * (α - 1))
  let dτ : ℝ → ℝ := fun s => s / (α - 1)
  let y : ℝ → H := timeScaledTrajectory z τ
  have hτ := quadraticTimeScale_isIncreasingC1TimeScaleOn hα hs₀
  have hxderiv : ∀ s : ℝ, HasDerivAt x (deriv x s) s := by
    intro s
    exact (hx.differentiable (by norm_num) s).hasDerivAt
  have haverage : IsWeightedAverageOn τ dτ x y (deriv x) s₀ := by
    refine ⟨hτ, ?_, ?_⟩
    · dsimp [y, timeScaledTrajectory, τ]
      exact hinitial
    · intro s hs
      refine ⟨hxderiv s, ?_⟩
      have hpos : 0 < dτ s := by
        dsimp [dτ]
        exact div_pos (lt_of_lt_of_le hs₀ hs) (sub_pos.mpr hα)
      have hne : dτ s ≠ 0 := ne_of_gt hpos
      have hrel := hrelation s hs
      dsimp [y, timeScaledTrajectory, τ, dτ] at hrel ⊢
      rw [hrel]
      rw [show x s - (x s + (s / (α - 1)) • deriv x s) =
          -((s / (α - 1)) • deriv x s) by abel]
      rw [smul_neg, smul_smul, inv_mul_cancel₀ hne, one_smul]
      abel
  refine ⟨y, ?_, ?_⟩
  · rfl
  · simpa [τ, dτ] using haverage
```

## Proof explanation
The proof begins by introducing local abbreviations. It sets

\[
\tau : \mathbb R \to \mathbb R,\qquad
\tau(s)=\frac{s^2}{2(\alpha-1)},
\]

\[
d\tau : \mathbb R \to \mathbb R,\qquad
d\tau(s)=\frac{s}{\alpha-1},
\]

and

\[
y : \mathbb R \to H,\qquad
y=\operatorname{timeScaledTrajectory} z \tau.
\]

Thus, by the definition of `timeScaledTrajectory`,

\[
y(s)=z(\tau(s))=z\!\left(\frac{s^2}{2(\alpha-1)}\right).
\]

These `let` declarations do not add new mathematical assumptions; they only name the functions that occur in the conclusion.

Next the proof obtains the time-scale property. It writes

\[
h\tau := \text{quadraticTimeScale\_isIncreasingC1TimeScaleOn}\ h_\alpha\ h_{s_0}.
\]

The cited theorem `quadraticTimeScale_isIncreasingC1TimeScaleOn` applies because \(1<\alpha\) and \(0<s_0\). Its conclusion is that the pair of functions

\[
\tau(s)=\frac{s^2}{2(\alpha-1)},\qquad
d\tau(s)=\frac{s}{\alpha-1}
\]

satisfies \(\operatorname{IsIncreasingC1TimeScaleOn}\) at \(s_0\). This is exactly the first conjunct required by `IsWeightedAverageOn`.

The proof then establishes that \(x\) has derivative \(\operatorname{deriv}x(s)\) at every point \(s\). It defines

\[
hxderiv : \forall s,\ \operatorname{HasDerivAt} x (\operatorname{deriv}x(s)) s.
\]

To prove this, it fixes an arbitrary \(s\) with `intro s`. Since \(h_x\) says that \(x\) is \(C^2\), in particular \(x\) is differentiable. The invocation `hx.differentiable (by norm_num)` uses that a \(C^2\) function is differentiable, with the numerical side condition \(2\ne 0\) discharged by `norm_num`. Applying the resulting differentiability to the point \(s\) gives differentiability of \(x\) at \(s\). The field access `.hasDerivAt` then gives

\[
\operatorname{HasDerivAt} x (\operatorname{deriv}x(s)) s.
\]

This supplies the derivative component required in the third conjunct of `IsWeightedAverageOn`.

The main local claim is

\[
haverage : \operatorname{IsWeightedAverageOn}\ \tau\ d\tau\ x\ y\ (\operatorname{deriv}x)\ s_0.
\]

The proof establishes this by `refine ⟨hτ, ?_, ?_⟩`, splitting the definition into its three conjuncts.

The first conjunct is exactly \(h\tau\), already proved.

The second conjunct requires \(x(s_0)=y(s_0)\). The proof uses `dsimp [y, timeScaledTrajectory, τ]` to unfold the definitions. The goal becomes

\[
x(s_0)=z\!\left(\frac{s_0^2}{2(\alpha-1)}\right).
\]

This is precisely the hypothesis \(h_{\mathrm{initial}}\). The command `exact hinitial` closes the goal.

The third conjunct requires that for every \(s \in \operatorname{Ici}s_0\),

\[
\operatorname{HasDerivAt} x (\operatorname{deriv}x(s)) s
\]

and

\[
\operatorname{deriv}x(s)+(d\tau(s))^{-1}\cdot (x(s)-y(s))=0.
\]

The proof introduces such an \(s\) with `intro s hs`, where \(hs : s \in \operatorname{Ici}s_0\), i.e. \(s_0 \le s\). Then `refine ⟨hxderiv s, ?_⟩` supplies the first part using \(hxderiv\), and leaves the weighted-average equation as the remaining goal.

To prove the remaining equation, the proof first shows that \(d\tau(s)\) is nonzero. It establishes

\[
hpos : 0<d\tau(s).
\]

After unfolding \(d\tau\), this means

\[
0<\frac{s}{\alpha-1}.
\]

The proof uses `lt_of_lt_of_le hs₀ hs`: from \(0<s_0\) and \(s_0\le s\), it obtains \(0<s\). It also uses `sub_pos.mpr hα`: from \(1<\alpha\), it obtains \(0<\alpha-1\). Then `div_pos` combines the positive numerator and positive denominator to give

\[
0<\frac{s}{\alpha-1}.
\]

Consequently, `hne : dτ(s) \ne 0` is obtained from `ne_of_gt hpos`. This nonzero fact is needed later to cancel \(d\tau(s)\) by its inverse.

Next the proof invokes the relation hypothesis. `hrel := hrelation s hs` gives

\[
z\!\left(\frac{s^2}{2(\alpha-1)}\right)
=
x(s)+\frac{s}{\alpha-1}\cdot \operatorname{deriv}x(s).
\]

The command `dsimp [y, timeScaledTrajectory, τ, dτ] at hrel ⊢` unfolds the local definitions in both `hrel` and the current goal. The goal is therefore the equation

\[
\operatorname{deriv}x(s)
+
\left(\frac{s}{\alpha-1}\right)^{-1}
\cdot
\left(
x(s)-z\!\left(\frac{s^2}{2(\alpha-1)}\right)
\right)
=0.
\]

Then `rw [hrel]` replaces the occurrence of

\[
z\!\left(\frac{s^2}{2(\alpha-1)}\right)
\]

by

\[
x(s)+\frac{s}{\alpha-1}\cdot \operatorname{deriv}x(s).
\]

So the inner difference becomes

\[
x(s)-\left(x(s)+\frac{s}{\alpha-1}\cdot \operatorname{deriv}x(s)\right).
\]

The proof next rewrites this difference using a local equality proved by `abel`:

\[
x(s)-\left(x(s)+\frac{s}{\alpha-1}\cdot \operatorname{deriv}x(s)\right)
=
-\left(\frac{s}{\alpha-1}\cdot \operatorname{deriv}x(s)\right).
\]

The `abel` tactic proves identities in additive abelian groups; here \(H\) is an additive commutative group, so it can cancel the common \(x(s)\). After this rewrite, the goal becomes

\[
\operatorname{deriv}x(s)
+
\left(\frac{s}{\alpha-1}\right)^{-1}
\cdot
\left(
-\left(\frac{s}{\alpha-1}\cdot \operatorname{deriv}x(s)\right)
\right)
=0.
\]

The proof then applies the scalar-multiplication rewrites

\[
\text{smul\_neg},\quad \text{smul\_smul},\quad
\text{inv\_mul\_cancel₀ } hne,\quad \text{one\_smul}.
\]

These steps move the negative sign out of the scalar product, reassociate the scalar multiplication, cancel the scalar factor using

\[
\left(\frac{s}{\alpha-1}\right)^{-1}\cdot \frac{s}{\alpha-1}=1,
\]

which is possible because \(d\tau(s)\ne 0\), and remove the scalar \(1\). The equation reduces to

\[
\operatorname{deriv}x(s)+(-\operatorname{deriv}x(s))=0.
\]

The final `abel` closes this additive identity. Thus the weighted-average equation is proved for the arbitrary \(s \ge s_0\). Therefore the local claim `haverage` is established.

Finally, the proof constructs the existential witness. `refine ⟨y, ?_, ?_⟩` chooses \(y\) as the desired curve. The first goal is

\[
y=\operatorname{timeScaledTrajectory} z
\left(s \mapsto \frac{s^2}{2(\alpha-1)}\right).
\]

This is closed by `rfl`, because \(y\) was defined as `timeScaledTrajectory z τ` and \(\tau\) was defined as \(s \mapsto s^2/(2(\alpha-1))\); the equality holds by definitional unfolding. The second goal is the `IsWeightedAverageOn` statement with the explicit functions

\[
s \mapsto \frac{s^2}{2(\alpha-1)},\qquad
s \mapsto \frac{s}{\alpha-1}.
\]

The command `simpa [τ, dτ] using haverage` unfolds the local abbreviations \(\tau\) and \(d\tau\) in the goal and then uses the already established `haverage` to close it. Hence the existence of \(y\) satisfying both required properties is proved.

