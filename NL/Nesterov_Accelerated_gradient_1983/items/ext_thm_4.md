## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_thm_4.lean`

## Lean statement
```lean
theorem firstOrder_complexity_lower_bound_reference :
    citedFirstOrderComplexityLowerBoundSource =
      "A. S. Nemirovskii and D. B. Yudin, Complexity of problems and efficiency of optimization methods, Nauka, Moscow, 1979 (Russian)."
```

## Statement explanation
The declaration is a `theorem` named `firstOrder_complexity_lower_bound_reference`. It has no parameters, no hypotheses, and no variables bound by binders: its type is a single closed proposition, namely the equality

\[
\texttt{citedFirstOrderComplexityLowerBoundSource}
=
\text{“A. S. Nemirovskii and D. B. Yudin, Complexity of problems and efficiency of optimization methods, Nauka, Moscow, 1979 (Russian).”}
\]

Both sides of this equality are terms of the type `String` (Lean's type of character strings), so the equality is the propositional equality of `String`, not a numerical or set-theoretic statement. The left-hand side is the identifier `citedFirstOrderComplexityLowerBoundSource`, an already-defined constant of the environment; the right-hand side is a string literal, i.e., a concrete element of `String`. Because the declaration has no hypotheses and no universal quantifiers, there is nothing to assume and nothing to instantiate: the statement is simply that the value denoted by the identifier `citedFirstOrderComplexityLowerBoundSource` is that particular bibliographic string.

Mathematically, the content is one of provenance rather than of optimization theory. It records that whatever formal object the formalization uses to name the first-order complexity lower bound carries, as its reference, the 1979 monograph of Nemirovskii and Yudin. In other words, the declaration is a bookkeeping assertion linking a named constant of the development to its literature source; it does not assert any inequality, rate, or lower-bound theorem about algorithms, only that the stored citation is exactly the stated text.

## Lean proof
```lean
rfl
```

## Proof explanation
The proof is the single tactic `rfl`. In Lean, `rfl` is the reflexivity constructor for equality: it proves goals of the form \(a = a\), and when the goal is \(a = b\), the elaborator attempts to unify \(b\) with \(a\) not merely up to propositional equality but up to definitional equality. This means Lean is permitted to unfold definitions of the constants occurring in the two sides (delta reduction), substitute defined values and perform the accompanying beta, iota, and zeta reductions, and then check whether the resulting two terms are syntactically the same.

Consequently, the fact that `rfl` succeeds here is itself the mathematical information supplied by the proof: the constant `citedFirstOrderComplexityLowerBoundSource` definitionally reduces to precisely the string literal displayed on the right-hand side. If the two sides were only propositionally equal but not definitionally equal — for instance if proving the equality required appealing to a decision procedure on strings such as `String.decEq`, or to `simp`, or to a rewriting lemma — then `rfl` alone would not close the goal. The accepted `rfl` therefore certifies that the equality holds by definition, with no auxiliary fact used.

No part of the proof introduces variables with `intro`, rewrites a subterm with `rw`, normalizes with `simp`, or discharges an arithmetic goal with `linarith`; those commands would be inappropriate for a closed equality between string terms. Likewise, no named theorem, lemma, or previously established fact is invoked: there are no cited results in the local import graph for this declaration, and the proof calls none. Whether `citedFirstOrderComplexityLowerBoundSource` was introduced by a definition, an abbreviation, or a local notation is not determined by the provided source; the only consequence that can be read off is the one established above, namely that its definiens is definitionally the Nemirovskii–Yudin 1979 citation string, and that this definitional identity is exactly what the theorem asserts.

