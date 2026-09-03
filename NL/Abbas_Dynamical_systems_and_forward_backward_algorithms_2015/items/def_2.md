## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/def_2.lean`

## Lean statement
```lean
noncomputable def lyapunovGamma {H : Type*} [NormedAddCommGroup H]
    (x : ℝ → H) (mu : ℝ) (g : ℝ → ℝ) (z : H) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 + mu * g t
```

## Statement explanation
In the declaration, `H : Type*` means `H` is an arbitrary type (a set/space in a type-theoretic sense). The hypothesis `[NormedAddCommGroup H]` says that `H` is equipped with the structure of a normed additive commutative group: it has an addition, subtraction, zero, a norm, and satisfies the usual group and norm axioms. The variables are:
- `x : ℝ → H`, a function assigning to each real time `t` a point `x t` in `H`, so `x` is a curve in the normed space `H`;
- `mu : ℝ`, a real-valued parameter;
- `g : ℝ → ℝ`, a real-valued function of a real variable;
- `z : H`, a fixed point in `H`;
- `t : ℝ`, a real number at which the functions are evaluated.

The declared object is `lyapunovGamma x mu g z t`, whose value is the real number
`(1 / 2 : ℝ) * ‖x t - z‖ ^ 2 + mu * g t`.
Here `x t` denotes the evaluation of `x` at `t`, and `x t - z` is the difference of two points in `H`. The symbol `‖·‖` is the norm on `H`, so `‖x t - z‖ ^ 2` is the squared norm of that difference. The first term multiplies this squared norm by the real number `1 / 2`. The second term is the product of the real parameter `mu` with the real number `g t`. The sum of these two real terms is the real value of the definition.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration. The source contains only the definition and a comment stating “No separate proof part.” Thus there are no Lean proof commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain. The declaration simply introduces `lyapunovGamma` as a noncomputable definition whose value is given explicitly by the displayed real expression.

