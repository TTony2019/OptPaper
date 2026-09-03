## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/def_3.lean`

## Lean statement
```lean
def dualBregmanDistance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (fstar : H → ℝ) (gradFstar : H → H)
    (g gLimit : H) : ℝ :=
  bregmanDistance fstar gradFstar g gLimit
```

## Statement explanation
The declaration defines a function named `dualBregmanDistance`. The type variable \(H\) is implicit and can be any type with the required structures: \(H : \mathsf{Type*}\). The hypothesis \([\mathsf{NormedAddCommGroup}\ H]\) means that \(H\) is a normed additive commutative group, and \([\mathsf{InnerProductSpace}\ \mathbb R\ H]\) means that \(H\) is additionally an inner product space over the real numbers. The explicit arguments are: \(fstar : H \to \mathbb R\), a real-valued function on \(H\); \(\mathsf{gradFstar} : H \to H\), a function from \(H\) to itself, called “gradFstar” but mathematically not assumed beyond its type; and two elements \(g : H\) and \(gLimit : H\) of the space \(H\). The declared result is a real number. The definition states that \(\mathsf{dualBregmanDistance}\ fstar\ \mathsf{gradFstar}\ g\ gLimit\) is exactly the expression \(\mathsf{bregmanDistance}\ fstar\ \mathsf{gradFstar}\ g\ gLimit\). Thus, the definition only introduces this function as being equal to the previously available Bregman-distance construction applied to the same arguments.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. This declaration is a definition, not a theorem, and the source contains no proof commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`. The definition is accepted by Lean by showing that the right-hand side, \(\mathsf{bregmanDistance}\ fstar\ \mathsf{gradFstar}\ g\ gLimit\), has the required result type \(\mathbb R\) under the given hypotheses. Mathematically, the declaration simply makes \(\mathsf{dualBregmanDistance}\) expand definitionally to the specified Bregman-distance expression; no additional properties are asserted or proved.

