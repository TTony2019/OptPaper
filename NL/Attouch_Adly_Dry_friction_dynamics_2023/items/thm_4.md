## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_4.lean`

## Lean statement
```lean
theorem theorem_3_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {t₀ r : ℝ} (hr : 0 < r) (A : H →L[ℝ] H) (g p : ℝ → H)
    (hsymm : A.IsSymmetric) (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x)
    (hdualDrygrad : ∀ t, p t ∈ frictionBallProjector r (g t) ∧
      HasDerivAt g (A (p t - g t)) t)
    (hcoercive : ∃ μ ν : ℝ, 0 < μ ∧ 0 < ν ∧ ∀ ξ : H,
      μ * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ ∧ inner ℝ (A ξ) ξ ≤ ν * ‖ξ‖ ^ 2)
    (henergyDeriv : ∀ t : ℝ, HasDerivAt
      (fun s => Metric.infDist (g s) (frictionBall r) ^ 2 / 2)
      (- inner ℝ (g t - p t) (A (g t - p t))) t)
    (hinitial : r < ‖g t₀‖) :
    ∃ Cupper Clower μ ν : ℝ, 0 < Cupper ∧ 0 < Clower ∧ 0 < μ ∧ 0 < ν ∧
      (∀ t ∈ Set.Ici t₀, Metric.infDist (g t) (frictionBall r) ≤ Cupper * Real.exp (-μ * t)) ∧
      (∀ t ∈ Set.Ici t₀, Clower * Real.exp (-ν * t) ≤ Metric.infDist (g t) (frictionBall r)) ∧
      ∀ t ∈ Set.Ici t₀, g t ∉ frictionBall r
```

## Statement explanation
The theorem assumes an ambient space \(H\) that is a normed additive commutative group and a real inner product space. The variables \(t_0,r\in\mathbb R\) are real numbers, with the hypothesis \(0<r\). The data also include a continuous linear operator \(A:H\to H\), curves \(g,p:\mathbb R\to H\), and the following hypotheses.

- \(A\) is symmetric: for all \(x,y\), \(\langle A x,y\rangle=\langle x,A y\rangle\).
- \(A\) is strictly positive definite: for every nonzero \(x\), \(0<\langle A x,x\rangle\).
- For every time \(t\), \(p(t)\) belongs to the set of friction-ball projectors of \(g(t)\) onto the set \(\operatorname{frictionBall} r\), and the derivative of \(g\) at \(t\) is \(A(p(t)-g(t))\). Thus \(g'(t)=A(p(t)-g(t))\).
- The operator \(A\) is coercive with positive constants: there exist \(\mu,\nu>0\) such that for every \(\xi\in H\),
  \[
  \mu\|\xi\|^2 \le \langle A\xi,\xi\rangle \le \nu\|\xi\|^2.
  \]
- For every \(t\), the function
  \[
  s\mapsto \frac{\operatorname{Metric.infDist}(g(s),\operatorname{frictionBall} r)^2}{2}
  \]
  has derivative at \(t\) equal to
  \[
  -\langle g(t)-p(t), A(g(t)-p(t))\rangle.
  \]
- Initially, \(g(t_0)\) is outside the friction ball: \(r<\|g(t_0)\|\).

The conclusion states that there exist positive constants \(C_{\text{upper}}\), \(C_{\text{lower}}\), \(\mu\), and \(\nu\) such that for every \(t\ge t_0\),

\[
\operatorname{Metric.infDist}(g(t),\operatorname{frictionBall} r)
\le C_{\text{upper}} e^{-\mu t},
\]
\[
C_{\text{lower}} e^{-\nu t}
\le \operatorname{Metric.infDist}(g(t),\operatorname{frictionBall} r),
\]
and
\[
g(t)\notin \operatorname{frictionBall} r.
\]

Thus the distance of \(g(t)\) from the friction ball decays exponentially from above and below, and \(g(t)\) never enters the friction ball after time \(t_0\).

## Lean proof
```lean
by
  rcases hcoercive with ⟨μ, ν, hμ, hν, hquad⟩
  let E : ℝ → ℝ := fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2
  have hd0 : 0 < Metric.infDist (g t₀) (frictionBall r) :=
    frictionBall_not_mem_initial_infDist_pos (le_of_lt hr) hinitial
  have hEderiv : ∀ t, HasDerivAt E
      (- inner ℝ (g t - p t) (A (g t - p t))) t := by
    intro t
    simpa [E] using henergyDeriv t
  have hupperDiff : ∀ t, deriv E t + 2 * μ * E t ≤ 0 := by
    intro t
    have hq := (hquad (g t - p t)).1
    have hdist := (hdualDrygrad t).1.2
    have hnorm : ‖g t - p t‖ = Metric.infDist (g t) (frictionBall r) := by
      simpa [dist_eq_norm] using hdist
    rw [hnorm] at hq
    rw [(hEderiv t).deriv]
    rw [real_inner_comm (A (g t - p t)) (g t - p t)]
    dsimp [E]
    nlinarith
  have hlowerDiff : ∀ t, 0 ≤ deriv E t + 2 * ν * E t := by
    intro t
    have hq := (hquad (g t - p t)).2
    have hdist := (hdualDrygrad t).1.2
    have hnorm : ‖g t - p t‖ = Metric.infDist (g t) (frictionBall r) := by
      simpa [dist_eq_norm] using hdist
    rw [hnorm] at hq
    rw [(hEderiv t).deriv]
    rw [real_inner_comm (A (g t - p t)) (g t - p t)]
    dsimp [E]
    nlinarith
  have hEderiv' : ∀ t, HasDerivAt E (deriv E t) t := by
    intro t
    convert hEderiv t using 1
    exact (hEderiv t).deriv
  have hlowerDistance : ∀ t ∈ Set.Ici t₀,
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (-ν * (t - t₀)) ≤
        Metric.infDist (g t) (frictionBall r) := by
    intro t ht
    have henergy : E t₀ * Real.exp (-(2 * ν) * (t - t₀)) ≤ E t := by
      have hdiv : (Real.exp (2 * ν * t₀) * E t₀) / Real.exp (2 * ν * t) ≤ E t :=
        (div_le_iff₀ (Real.exp_pos _)).mpr
          (by simpa [mul_comm] using weighted_energy_monotone hEderiv' hlowerDiff ht)
      calc
        E t₀ * Real.exp (-(2 * ν) * (t - t₀)) =
            E t₀ * (Real.exp (2 * ν * t₀) / Real.exp (2 * ν * t)) := by
              rw [← Real.exp_sub]
              congr 2 <;> ring
        _ = (Real.exp (2 * ν * t₀) * E t₀) / Real.exp (2 * ν * t) := by ring
        _ ≤ E t := hdiv
    have hsq : Metric.infDist (g t₀) (frictionBall r) ^ 2 *
        Real.exp (-(2 * ν) * (t - t₀)) ≤ Metric.infDist (g t) (frictionBall r) ^ 2 := by
      dsimp [E] at henergy
      nlinarith
    have hident : (Metric.infDist (g t₀) (frictionBall r) *
        Real.exp (-ν * (t - t₀))) ^ 2 =
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * ν) * (t - t₀)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2 <;> ring
    exact (sq_le_sq₀ (mul_nonneg Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)))
      Metric.infDist_nonneg).mp (by rwa [hident])
  refine ⟨Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀),
    Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀), μ, ν,
    mul_pos hd0 (Real.exp_pos _), mul_pos hd0 (Real.exp_pos _), hμ, hν, ?_, ?_, ?_⟩
  · intro t ht
    have henergy : E t ≤ E t₀ * Real.exp (-(2 * μ) * (t - t₀)) := by
      have hdiv : E t ≤ (Real.exp (2 * μ * t₀) * E t₀) / Real.exp (2 * μ * t) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr
          (by simpa [mul_comm] using weighted_energy_antitone hEderiv' hupperDiff ht)
      calc
        E t ≤ (Real.exp (2 * μ * t₀) * E t₀) / Real.exp (2 * μ * t) := hdiv
        _ = E t₀ * (Real.exp (2 * μ * t₀) / Real.exp (2 * μ * t)) := by ring
        _ = E t₀ * Real.exp (2 * μ * t₀ - 2 * μ * t) := by rw [Real.exp_sub]
        _ = E t₀ * Real.exp (-(2 * μ) * (t - t₀)) := by congr 2 <;> ring
    have hsq : Metric.infDist (g t) (frictionBall r) ^ 2 ≤
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * μ) * (t - t₀)) := by
      dsimp [E] at henergy
      nlinarith
    have hident : (Metric.infDist (g t₀) (frictionBall r) *
        Real.exp (-μ * (t - t₀))) ^ 2 =
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * μ) * (t - t₀)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2 <;> ring
    have hdist : Metric.infDist (g t) (frictionBall r) ≤
        Metric.infDist (g t₀) (frictionBall r) * Real.exp (-μ * (t - t₀)) :=
      (sq_le_sq₀ Metric.infDist_nonneg (mul_nonneg Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)))).mp
        (by rwa [hident])
    convert hdist using 1
    calc
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀) * Real.exp (-μ * t) =
          Metric.infDist (g t₀) (frictionBall r) * (Real.exp (μ * t₀) * Real.exp (-μ * t)) := by ring
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀ + -μ * t) := by rw [← Real.exp_add]
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (-μ * (t - t₀)) := by congr 2 <;> ring
  · intro t ht
    have hdist := hlowerDistance t ht
    convert hdist using 1
    calc
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀) * Real.exp (-ν * t) =
          Metric.infDist (g t₀) (frictionBall r) * (Real.exp (ν * t₀) * Real.exp (-ν * t)) := by ring
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀ + -ν * t) := by rw [← Real.exp_add]
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (-ν * (t - t₀)) := by congr 2 <;> ring
  · intro t ht hmem
    have hlower := hlowerDistance t ht
    have hposdist : 0 < Metric.infDist (g t) (frictionBall r) :=
      lt_of_lt_of_le (mul_pos hd0 (Real.exp_pos _)) hlower
    have hzero := Metric.infDist_zero_of_mem hmem
    linarith
```

## Proof explanation
The proof defines an energy functional
\[
E(t)=\frac{\operatorname{Metric.infDist}(g(t),\operatorname{frictionBall} r)^2}{2}.
\]
The first step is to extract the coercivity constants \(\mu,\nu\) from the hypothesis `hcoercive` using `rcases`. The proof then introduces this \(E\) with `let E : ℝ → ℝ := ...`.

The initial positive distance
\[
0<\operatorname{Metric.infDist}(g(t_0),\operatorname{frictionBall} r)
\]
is obtained from the lemma `frictionBall_not_mem_initial_infDist_pos`, using \(0<r\) and the initial condition \(r<\|g(t_0)\|\).

Next, the derivative hypothesis for the energy is rewritten in terms of \(E\). The proof has
\[
\operatorname{HasDerivAt} E
\left(-\langle g(t)-p(t), A(g(t)-p(t))\rangle\right) t
\]
for every \(t\).

The core of the proof consists in deriving differential inequalities for \(E\). For every \(t\), the proof obtains
\[
\frac{d}{dt}E(t)+2\mu E(t)\le 0
\]
and
\[
0\le \frac{d}{dt}E(t)+2\nu E(t).
\]
To prove these, the proof applies the coercivity bounds to \(\xi=g(t)-p(t)\). Since \(p(t)\) is a friction-ball projector, the distance from \(g(t)\) to \(p(t)\) equals the infimum distance:
\[
\|g(t)-p(t)\|=\operatorname{Metric.infDist}(g(t),\operatorname{frictionBall} r).
\]
After substituting this equality and the derivative formula for \(E\), and using symmetry of the real inner product, the goals become algebraic inequalities involving the squared distance. The tactic `nlinarith` discharges these inequalities using the coercivity bounds.

The proof then records that \(E\) has derivative exactly \(\operatorname{deriv} E(t)\) at each \(t\), using the derivative formula already proved.

For the lower distance bound, the proof uses an auxiliary lemma `weighted_energy_monotone`. This lemma encodes that the differential inequality
\[
0\le \frac{d}{dt}E(t)+2\nu E(t)
\]
implies the weighted energy \(e^{2\nu t}E(t)\) is nondecreasing on \([t_0,\infty)\). Therefore, for \(t\ge t_0\),
\[
e^{2\nu t_0}E(t_0)\le e^{2\nu t}E(t).
\]
Dividing by the positive quantity \(e^{2\nu t}\) gives
\[
E(t_0)e^{-2\nu(t-t_0)}\le E(t).
\]
Since \(E(t)=\frac12 d(t)^2\), this yields an analogous squared-distance inequality:
\[
d(t_0)^2 e^{-2\nu(t-t_0)}\le d(t)^2.
\]
Using the fact that the square of a product factors as
\[
\left(d(t_0)e^{-\nu(t-t_0)}\right)^2
=
d(t_0)^2 e^{-2\nu(t-t_0)},
\]
the proof converts the squared inequality into a distance inequality by `sq_le_sq₀`, because both sides are nonnegative. This gives
\[
d(t_0)e^{-\nu(t-t_0)}\le d(t).
\]

For the upper distance bound, the proof similarly uses `weighted_energy_antitone`. The differential inequality
\[
\frac{d}{dt}E(t)+2\mu E(t)\le 0
\]
implies that the weighted energy \(e^{2\mu t}E(t)\) is nonincreasing on \([t_0,\infty)\). Hence, for \(t\ge t_0\),
\[
E(t)\le E(t_0)e^{-2\mu(t-t_0)}.
\]
Again, passing from the squared distance to the distance via `sq_le_sq₀` gives
\[
d(t)\le d(t_0)e^{-\mu(t-t_0)}.
\]

The proof then chooses the constants in the conclusion as
\[
C_{\text{upper}}=d(t_0)e^{\mu t_0},\qquad
C_{\text{lower}}=d(t_0)e^{\nu t_0},
\]
with the same \(\mu,\nu\) from coercivity. Their positivity follows from `mul_pos`, using the positive initial distance and positivity of the real exponential. The upper bound \(d(t)\le C_{\text{upper}}e^{-\mu t}\) is obtained from
\[
d(t)\le d(t_0)e^{-\mu(t-t_0)}
\]
by rewriting
\[
d(t_0)e^{\mu t_0}e^{-\mu t}
=
d(t_0)e^{-\mu(t-t_0)}.
\]
Similarly, the lower bound
\[
C_{\text{lower}}e^{-\nu t}\le d(t)
\]
is obtained from
\[
d(t_0)e^{-\nu(t-t_0)}\le d(t)
\]
by rewriting
\[
d(t_0)e^{\nu t_0}e^{-\nu t}
=
d(t_0)e^{-\nu(t-t_0)}.
\]
These rewrites use the identities for the real exponential, especially `Real.exp_add` and `Real.exp_sub`.

Finally, to prove that \(g(t)\notin \operatorname{frictionBall} r\) for \(t\ge t_0\), the proof assumes for contradiction that \(g(t)\in \operatorname{frictionBall} r\). Then by the lemma `Metric.infDist_zero_of_mem`, the distance \(d(t)\) would be zero. But the previously proved lower bound and the positivity of the initial distance give
\[
0<d(t),
\]
which contradicts \(d(t)=0\). The tactic `linarith` closes this contradiction.

The assumptions `hsymm` and `hpos` are part of the theorem statement, but the displayed proof mainly relies on `hcoercive`, `hdualDrygrad`, `henergyDeriv`, and `hinitial`.

