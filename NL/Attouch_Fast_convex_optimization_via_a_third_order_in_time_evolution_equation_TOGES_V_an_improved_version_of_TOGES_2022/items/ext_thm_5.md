## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/ext_thm_5.lean`

## Lean statement
```lean
theorem moreau_envelope_regularity_and_minimizers {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hProper : ERealFunction.IsProper f) (_hlsc : LowerSemicontinuous f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (envelope : H → EReal) (prox : H → H)
    (hprox : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (henvelope : ∀ x, envelope x =
      f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal)) :
    Convex ℝ (ERealFunction.epigraph envelope) ∧
    ContDiff ℝ 1 (fun x => (envelope x).toReal) ∧
    sInf (Set.range envelope) = sInf (Set.range f) ∧
    {x | envelope x = sInf (Set.range envelope)} =
      {x | f x = sInf (Set.range f)} ∧
    (∀ x, f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) =
      envelope x)
```

## Statement explanation
The theorem `moreau_envelope_regularity_and_minimizers` is stated for a complete real inner-product space $H$, that is, a real Hilbert space. The function $f:H\to\overline{\mathbb R}$ is an extended-real-valued function, where $\overline{\mathbb R}$ is Lean’s `EReal`. The scalar $\lambda$ is assumed positive, $f$ is assumed proper, lower semicontinuous, and convex in the sense that its epigraph is convex. The function $e$, named `envelope`, plays the role of the Moreau envelope, and $p$, named `prox`, is a proximal selection. The hypothesis `hprox` says that for every $x\in H$, the point $p(x)$ lies in the resolvent of the set-valued operator $\lambda\,\partial f$ at $x$; in the usual convex-analytic reading, this is the proximal relation $x-p(x)\in \lambda\,\partial f(p(x))$. The hypothesis `henvelope` says that for every $x$,

$$
e(x)=f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right),
$$

where the real quantity $\frac{1}{2\lambda}\|x-p(x)\|^2$ is coerced into the extended reals.

The conclusion is a five-part conjunction. First, the epigraph of the envelope is convex:

$$
\mathrm{epi}(e)\ \text{is convex over }\mathbb R.
$$

Second, the real-valued function obtained from the envelope by applying `toReal` is $C^1$:

$$
x\mapsto (e(x))_{\mathbb R}
\quad\text{is continuously differentiable}.
$$

Third, the envelope and the original function have the same infimum:

$$
\inf_{x\in H} e(x)=\inf_{x\in H} f(x).
$$

Fourth, their sets of minimizers coincide:

$$
\{x\in H\mid e(x)=\inf_{y\in H} e(y)\}
=
\{x\in H\mid f(x)=\inf_{y\in H} f(y)\}.
$$

Fifth, the defining envelope formula is restated in the opposite orientation:

$$
\forall x\in H,\qquad
f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right)=e(x).
$$

Thus the theorem says that, under the given convex-analytic hypotheses, the Moreau envelope has the expected convexity and differentiability, preserves the infimum, and has exactly the same minimizers as the original proper convex function. The assumptions `[CompleteSpace H]` and `_hlsc` are present in the statement, but the displayed proof does not invoke them.

## Lean proof
```lean
by
  refine ⟨?_, ?_, moreau_infimum_eq f lam hlam hProper hconvex envelope prox hprox henvelope,
    ?_, ?_⟩
  · exact moreau_envelope_convex f lam hlam hProper hconvex envelope prox hprox henvelope
  · exact moreau_envelope_contDiff f lam hlam hProper hconvex envelope prox hprox henvelope
  · ext x
    constructor
    · intro hx
      have hinfs := moreau_infimum_eq f lam hlam hProper hconvex envelope prox hprox henvelope
      have hpdom := moreau_prox_mem_dom f hProper hconvex prox lam hprox x
      have hpfin : ((f (prox x)).toReal : EReal) = f (prox x) :=
        EReal.coe_toReal (ne_of_lt hpdom) (hProper.1 _)
      have hp_le_env : f (prox x) ≤ envelope x := by
        rw [henvelope x]
        exact le_add_of_nonneg_right (by
          exact_mod_cast mul_nonneg (by positivity) (sq_nonneg ‖x - prox x‖))
      have henv_eq : envelope x = sInf (Set.range f) := hx.trans hinfs
      have hp_eq : f (prox x) = sInf (Set.range f) := by
        apply le_antisymm
        · calc
            f (prox x) ≤ envelope x := hp_le_env
            _ = sInf (Set.range f) := henv_eq
        · exact (isGLB_sInf (Set.range f)).1 ⟨prox x, rfl⟩
      have hsum : f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) =
          f (prox x) := by
        calc
          f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) = envelope x :=
            (henvelope x).symm
          _ = sInf (Set.range f) := henv_eq
          _ = f (prox x) := hp_eq.symm
      rw [← hpfin, ← EReal.coe_add] at hsum
      norm_cast at hsum
      have hq : 1 / (2 * lam) * ‖x - prox x‖ ^ 2 = 0 := by linarith
      have hcoeff : 0 < 1 / (2 * lam) := by positivity
      have hsq : ‖x - prox x‖ ^ 2 = 0 := by nlinarith
      have hnorm : ‖x - prox x‖ = 0 := by nlinarith [norm_nonneg (x - prox x)]
      have hxp : x = prox x := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
      rw [hxp]
      exact hp_eq
    · intro hx
      have hinfs := moreau_infimum_eq f lam hlam hProper hconvex envelope prox hprox henvelope
      have henv_le : envelope x ≤ f x := by
        calc
          envelope x = f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) :=
            henvelope x
          _ ≤ f x + ((1 / (2 * lam) * ‖x - x‖ ^ 2 : ℝ) : EReal) :=
            moreau_proximal_objective_le f lam hlam hProper hconvex prox hprox x x
          _ = f x := by simp
      apply le_antisymm
      · calc
          envelope x ≤ f x := henv_le
          _ = sInf (Set.range f) := hx
          _ = sInf (Set.range envelope) := hinfs.symm
      · exact (isGLB_sInf (Set.range envelope)).1 ⟨x, rfl⟩
  · intro x
    exact (henvelope x).symm
```

## Proof explanation
The proof begins by building the five-part conjunction with `refine ⟨?_, ?_, moreau_infimum_eq f lam hlam hProper hconvex envelope prox hprox henvelope, ?_, ?_⟩`. The third conjunct is filled immediately by the theorem `moreau_infimum_eq`. In its stated form, `moreau_infimum_eq` takes a positive $\lambda$, a proper convex extended-real function $f$, an envelope $e$, and a prox selection $p$ satisfying the resolvent and envelope hypotheses, and concludes

$$
\inf \mathrm{range}(e)=\inf \mathrm{range}(f).
$$

The two remaining explicit conjuncts are then proved. The first is proved by `moreau_envelope_convex`, which has the same hypotheses as `moreau_infimum_eq` and concludes that the epigraph of the envelope is convex. The second is proved by `moreau_envelope_contDiff`, which under the same hypotheses concludes that

$$
x\mapsto (e(x))_{\mathbb R}
$$

is $C^1$. These two lemmas directly supply the first two conclusions of the theorem.

The proof then turns to the equality of minimizer sets. It uses `ext x` to reduce equality of sets to proving, for an arbitrary $x$, the equivalence

$$
e(x)=\inf \mathrm{range}(e)
\iff
f(x)=\inf \mathrm{range}(f).
$$

The tactic `constructor` splits this equivalence into the forward and backward implications.

For the forward direction, assume $e(x)=\inf \mathrm{range}(e)$. The proof again obtains `hinfs`, the equality

$$
\inf \mathrm{range}(e)=\inf \mathrm{range}(f)
$$

from `moreau_infimum_eq`. It then applies `moreau_prox_mem_dom`, whose content is that, for proper convex $f$ and a prox selection from the resolvent of $\lambda\,\partial f$, the point $p(x)$ belongs to the domain of $f$. Hence $f(p(x))<+\infty$. This is used to make the real value of $f(p(x))$ usable. Specifically, `hpfin` proves

$$
((f(p(x)))_{\mathbb R}:\overline{\mathbb R})=f(p(x)).
$$

This follows from `EReal.coe_toReal`, which says that if an extended real number is neither $+\infty$ nor $-\infty$, then coercing its `toReal` value back into the extended reals returns the original number. The condition $f(p(x))\ne+\infty$ comes from membership in the domain, and the condition $f(p(x))\ne-\infty$ comes from properness of $f$.

Next the proof establishes

$$
f(p(x))\le e(x).
$$

Indeed, by `henvelope`,

$$
e(x)=f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right).
$$

Since $\lambda>0$, the coefficient $\frac{1}{2\lambda}$ is positive, and since $\|x-p(x)\|^2\ge 0$, the added extended-real term is nonnegative. The lemma `le_add_of_nonneg_right` then gives

$$
f(p(x))\le f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right)=e(x).
$$

Using the assumed $e(x)=\inf \mathrm{range}(e)$ and the equality of infima, the proof gets

$$
e(x)=\inf \mathrm{range}(f).
$$

Combining this with $f(p(x))\le e(x)$ gives

$$
f(p(x))\le \inf \mathrm{range}(f).
$$

The reverse inequality comes from `isGLB_sInf`. The theorem `isGLB_sInf` says that $\inf \mathrm{range}(f)$ is a greatest lower bound of the set of values of $f$; in particular it is a lower bound, so for every value in the range, the infimum is at most that value. Since $f(p(x))\in \mathrm{range}(f)$, this gives

$$
\inf \mathrm{range}(f)\le f(p(x)).
$$

Therefore

$$
f(p(x))=\inf \mathrm{range}(f).
$$

Now the proof shows that the quadratic term must vanish. From the envelope identity and the two infimum equalities, it obtains

$$
f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right)
=
f(p(x)).
$$

Using `hpfin`, the expression $f(p(x))$ is rewritten as the coercion of its real value, and using `EReal.coe_add`, the addition inside the extended reals is converted into addition of real numbers. Then `norm_cast` transports the equality back to the real numbers, yielding

$$
(f(p(x)))_{\mathbb R}+\frac{1}{2\lambda}\|x-p(x)\|^2
=
(f(p(x)))_{\mathbb R}.
$$

The tactic `linarith` cancels the common real term and proves

$$
\frac{1}{2\lambda}\|x-p(x)\|^2=0.
$$

Since `positivity` proves $\frac{1}{2\lambda}>0$, `nlinarith` concludes

$$
\|x-p(x)\|^2=0.
$$

Using nonnegativity of the norm and another `nlinarith`, the proof gets

$$
\|x-p(x)\|=0.
$$

Then `norm_eq_zero.mp` gives $x-p(x)=0$, and `sub_eq_zero.mp` gives $x=p(x)$. Rewriting the goal with $x=p(x)$, the desired equality $f(x)=\inf \mathrm{range}(f)$ becomes $f(p(x))=\inf \mathrm{range}(f)$, which is exactly the previously proved statement `hp_eq`. This proves the forward implication.

For the backward direction, assume

$$
f(x)=\inf \mathrm{range}(f).
$$

The proof again uses the equality of infima from `moreau_infimum_eq`. It first proves

$$
e(x)\le f(x).
$$

By `henvelope`,

$$
e(x)=f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right).
$$

The lemma `moreau_proximal_objective_le`, specialized to the same point $x$ for both variables, gives

$$
f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right)
\le
f(x)+\left(\frac{1}{2\lambda}\|x-x\|^2:\overline{\mathbb R}\right).
$$

Since $\|x-x\|^2=0$, the right-hand side simplifies by `simp` to $f(x)$. Hence $e(x)\le f(x)$.

Now the proof applies `le_antisymm` to prove

$$
e(x)=\inf \mathrm{range}(e).
$$

One inequality is

$$
e(x)\le f(x)=\inf \mathrm{range}(f)=\inf \mathrm{range}(e),
$$

using the assumed equality for $f(x)$ and the equality of infima. The reverse inequality is again supplied by `isGLB_sInf`: since $e(x)$ belongs to $\mathrm{range}(e)$, the infimum $\inf \mathrm{range}(e)$ is a lower bound, so

$$
\inf \mathrm{range}(e)\le e(x).
$$

Thus the backward implication is proved, completing the equality of the two minimizer sets.

Finally, the last conjunct of the theorem is proved by `intro x; exact (henvelope x).symm`. This simply uses the hypothesis `henvelope`, which states

$$
e(x)=f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right),
$$

and reverses it to obtain

$$
f(p(x))+\left(\frac{1}{2\lambda}\|x-p(x)\|^2:\overline{\mathbb R}\right)=e(x).
$$

This completes all five clauses of the theorem.

