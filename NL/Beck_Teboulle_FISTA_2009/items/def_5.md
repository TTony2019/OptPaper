## Source file
`Beck_Teboulle_FISTA_2009/items/def_5.lean`

## Lean statement
```lean
def solutionSet {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | IsMinOn (compositeObjective f g) univ x}
```

## Statement explanation
The declaration introduces a definition named `solutionSet`. It takes an implicit natural number \(n\) and two explicit functions
\[
f,g : \mathbb{R}^n \to \mathbb{R},
\]
where Lean writes the domain as `EuclideanSpace ℝ (Fin n)`, the \(n\)-dimensional real Euclidean space. There are no additional hypotheses: no convexity, continuity, differentiability, coercivity, or existence assumption is part of the declaration. The definition produces a subset of \(\mathbb{R}^n\), namely
\[
\operatorname{solutionSet}(f,g)
=
\{x \in \mathbb{R}^n \mid
\operatorname{IsMinOn}(\operatorname{compositeObjective}(f,g),\mathbb{R}^n,x)\}.
\]
Here `compositeObjective f g` is the real-valued function on \(\mathbb{R}^n\) built from \(f\) and \(g\) in the surrounding development; this declaration does not expose its formula. The identifier `univ` denotes the whole domain \(\mathbb{R}^n\).

In Mathlib, \(\operatorname{IsMinOn} h s x\) means that \(x \in s\) and \(h(x) \le h(y)\) for every \(y \in s\). Since here \(s\) is the universal set \(\mathbb{R}^n\), the membership condition \(x \in \mathbb{R}^n\) is automatic, and the proposition says precisely that
\[
(\operatorname{compositeObjective}(f,g))(x)
\le
(\operatorname{compositeObjective}(f,g))(y)
\quad\text{for all } y \in \mathbb{R}^n.
\]
Thus `solutionSet f g` is the set of global minimizers of the composite objective over the entire Euclidean space:
\[
\operatorname{solutionSet}(f,g)
=
\arg\min_{x \in \mathbb{R}^n}
(\operatorname{compositeObjective}(f,g))(x).
\]
The declaration does not assert that this set is nonempty, that a minimizer is unique, or that the minimizers have any additional property. It simply defines the solution set of the minimization problem.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, so its mathematical content is the definitional equality itself, not a theorem proved from earlier facts. No hypotheses are introduced, no goal is transformed, and no named lemma or theorem is invoked. In particular, there are no occurrences of tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`.

The entire content is that for every point \(x\) in \(\mathbb{R}^n\),
\[
x \in \operatorname{solutionSet}(f,g)
\iff
\operatorname{IsMinOn}(\operatorname{compositeObjective}(f,g),\mathbb{R}^n,x).
\]
Expanding the definition of \(\operatorname{IsMinOn}\) and the fact that the domain is all of \(\mathbb{R}^n\), this is equivalent to
\[
x \in \operatorname{solutionSet}(f,g)
\iff
\bigl(
\forall y \in \mathbb{R}^n,\ 
(\operatorname{compositeObjective}(f,g))(x)
\le
(\operatorname{compositeObjective}(f,g))(y)
\bigr).
\]
This is exactly the statement that \(x\) is a global minimizer of the composite objective. No further mathematical step is needed or present.

