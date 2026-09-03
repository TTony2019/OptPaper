## Source file
`Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001/items/ext_def_1.lean`

## Lean statement
```lean
noncomputable def distanceToSet (y : H) (C : Set H) : EReal :=
  sInf ((fun c : H => (‖y - c‖ : EReal)) '' C)
```

## Statement explanation
The declaration is a noncomputable definition named `distanceToSet`. It takes two explicit arguments: `y : H`, a point in an ambient type `H`, and `C : Set H`, a subset of `H`. The context is assumed to provide enough structure on `H` for the expression `‖y - c‖` to make sense, so `H` is a type equipped with subtraction and a norm, although no explicit type-class hypotheses appear in this snippet. The output type is `EReal`, the extended real numbers.

The defined value is
`distanceToSet y C = sInf ((fun c : H => (‖y - c‖ : EReal)) '' C)`,
where the function `fun c : H => (‖y - c‖ : EReal)` maps each point `c` of `H` to the extended-real-valued norm of `y - c`. The image `'' C` is the set of all these values as `c` ranges over `C`. Thus `distanceToSet y C` is the extended-real infimum, denoted `sInf`, of the set `{‖y - c‖ : EReal | c ∈ C}`. In words, it is defined as the distance from the point `y` to the set `C`, measured as an extended real number. There are no additional hypotheses or asserted mathematical properties in this declaration.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is only a definition: `noncomputable def distanceToSet ... := ...`. The source explicitly says there is no proof part. Consequently, there are no Lean proof commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain.

The mathematical content lies entirely in the defining expression. First, `fun c : H => (‖y - c‖ : EReal)` forms the function sending each candidate point `c` to the extended-real norm of the difference `y - c`. Second, the image notation `'' C` collects the values of this function over all `c` in the set `C`. Third, `sInf` takes the greatest lower bound of that collection in the extended real numbers. Therefore the definition gives `distanceToSet y C` as the infimum distance from `y` to any point of `C`. No theorem is proved; the declaration merely introduces this definition.

