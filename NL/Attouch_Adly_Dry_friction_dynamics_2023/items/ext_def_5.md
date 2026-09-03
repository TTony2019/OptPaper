## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_def_5.lean`

## Lean statement
```lean
def bregmanDistance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : H → ℝ) (gradF : H → H) (a b : H) : ℝ := F b - F a - inner ℝ (gradF a) (b - a)
```

## Statement explanation
The declaration is a definition of a real-valued quantity called `bregmanDistance`. It is parameterized by a type `H` equipped with the structure of a real inner product space: the hypotheses `[NormedAddCommGroup H]` and `InnerProductSpace ℝ H` mean that `H` is a normed additive commutative group over the real numbers, with a real inner product. There are also three explicit objects: `F : H → ℝ`, a real-valued function on `H`; `gradF : H → H`, an arbitrary map from `H` to itself, which is not assumed in the source to be related to `F`; and two points `a b : H` in the space. The conclusion is that for these inputs, `bregmanDistance F gradF a b` is a real number defined by the expression `F b - F a - inner ℝ (gradF a) (b - a)`. In mathematical notation this is  
`F(b) - F(a) - ⟨gradF(a), b - a⟩`,  
where `F(b)` and `F(a)` are real numbers, `b - a` is vector subtraction in `H`, and the last term is the real inner product of `gradF(a)` with `b - a`. Thus the definition introduces the standard Bregman distance/divergence with respect to a function `F` and a gradient-like field `gradF`, evaluated from `a` to `b`.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part in the source. The declaration is a `def`, not a theorem, so it does not have a proof by tactic steps such as `intro`, `rw`, `simp`, `exact`, or `linarith`. Its entire content is the definitional right-hand side `F b - F a - inner ℝ (gradF a) (b - a)`, which Lean is asked to accept as an expression of type `ℝ`. No mathematical verification is needed beyond typechecking that the subtraction and inner product terms make sense under the given assumptions. The Lean command `def` creates a constant that unfolds definitionally to this expression whenever used.

