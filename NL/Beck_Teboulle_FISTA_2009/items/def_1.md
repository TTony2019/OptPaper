## Source file
`Beck_Teboulle_FISTA_2009/items/def_1.lean`

## Lean statement
```lean
def positivePart (a : ℝ) : ℝ :=
  max a 0
```

## Statement explanation
The declaration introduces a definition named `positivePart`. It takes one explicit argument $a$, whose type is $\mathbb{R}$, so $a$ is an arbitrary real number. It returns a value of type $\mathbb{R}$, again a real number. There are no hypotheses, assumptions, or side conditions: the definition applies uniformly to every real $a$.

The defining expression is $\max(a,0)$. Thus, by definition,

```math
\mathrm{positivePart}(a) = \max\{a,0\}
```

for every $a \in \mathbb{R}$. Mathematically, this is the positive part of the real number $a$. If $a \ge 0$, then the larger of $a$ and $0$ is $a$, so the result is $a$. If $a \le 0$, then the larger of $a$ and $0$ is $0$, so the result is $0$. In other words, the function replaces every negative input by $0$ and leaves nonnegative inputs unchanged. The declaration only introduces this function; it does not assert any further properties such as continuity, measurability, or algebraic identities.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a definition, and the Lean source explicitly states that there is no separate proof part. Consequently, there are no hypotheses to introduce, no goals to establish, no named lemmas or theorems invoked, and no tactic steps such as `intro`, `rw`, `simp`, `exact`, or `linarith`. The entire mathematical content is the defining equality

```math
\mathrm{positivePart}(a) = \max\{a,0\}
```

for an arbitrary real number $a$.

