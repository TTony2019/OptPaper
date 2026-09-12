## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_def_3.lean`

## Lean statement
```lean
def IsFrictionBallProjection {H : Type*} [PseudoMetricSpace H] [Zero H]
    (r : ℝ) (x p : H) : Prop := p ∈ frictionBallProjector r x
```

## Statement explanation
The declaration introduces a ternary predicate \( \mathrm{IsFrictionBallProjection} \). Its arguments are a real number \(r\), and two elements \(x\) and \(p\) of a type \(H\). The ambient assumptions on \(H\) are that it carries a pseudo-metric space structure and a distinguished zero element \(0 \in H\). The pseudo-metric supplies a distance-like function satisfying the usual axioms except possibly separation, and \( \mathrm{Zero}(H) \) supplies the element \(0\). Neither assumption is used to impose an extra condition in the displayed body of the definition; they are part of the context in which the expression \( \mathrm{frictionBallProjector}(r,x) \) is formed.

For fixed \(r\), \(x\), and \(p\), the definition states exactly that
\[
\mathrm{IsFrictionBallProjection}(r,x,p)
\quad\text{is the proposition}\quad
p \in \mathrm{frictionBallProjector}(r,x).
\]
Thus \( \mathrm{frictionBallProjector}(r,x) \) is a previously defined set-like object of elements of \(H\), and the predicate says that \(p\) belongs to it. In ordinary mathematical language, \(p\) is a friction-ball projection of \(x\) at radius \(r\), as encoded by the operator \( \mathrm{frictionBallProjector} \). The definition does not assert existence or uniqueness of such a \(p\), does not require \(r\) to be nonnegative, and does not state any distance inequality or other geometric condition. Any such geometric content would have to come from the separate definition of \( \mathrm{frictionBallProjector} \), which is not included here.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, so its content is a definitional equation rather than a proof of a proposition. For specific \(r\), \(x\), and \(p\), unfolding the definition gives the proposition
\[
p \in \mathrm{frictionBallProjector}(r,x).
\]
There are no hypotheses to introduce, no goals to rewrite or simplify, and no named lemmas or theorems invoked. Consequently, no tactic such as `intro`, `rw`, `simp`, `exact`, or `linarith` occurs in the definition. If this predicate is used later, the only information obtainable from this declaration alone is that \(p\) lies in the set denoted by \( \mathrm{frictionBallProjector}(r,x) \).

