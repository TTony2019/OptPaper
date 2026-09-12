## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/ext_def_4.lean`

## Lean statement
```lean
def IsSeparatelyContinuous' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X × Y → ℝ) : Prop :=
  (∀ (y : Y), Continuous (fun (x : X) => F (x, y))) ∧
  (∀ (x : X), Continuous (fun (y : Y) => F (x, y)))
```

## Statement explanation
The declaration defines a binary predicate on a real-valued function of two variables. The variables are two types \(X\) and \(Y\), each equipped with a topological structure through the typeclass assumptions `[TopologicalSpace X]` and `[TopologicalSpace Y]`. The main argument is a function
\[
F : X \times Y \to \mathbb{R},
\]
where \(\mathbb{R}\) is understood with its usual topology. The definition produces a proposition, written `IsSeparatelyContinuous' F`, asserting the conjunction of two conditions:

1. For every fixed \(y \in Y\), the one-variable section
\[
x \mapsto F(x,y)
\]
is a continuous map from \(X\) to \(\mathbb{R}\).

2. For every fixed \(x \in X\), the one-variable section
\[
y \mapsto F(x,y)
\]
is a continuous map from \(Y\) to \(\mathbb{R}\).

Thus the definition says that \(F\) is continuous in each variable separately: continuity is required only after one of the two inputs is fixed and the resulting function of the remaining variable is considered. The statement does not itself assert any continuity property of the two-variable map \(F : X \times Y \to \mathbb{R}\); it records only the two families of one-variable continuity conditions described above.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration. It is a `def`, so Lean simply introduces the name `IsSeparatelyContinuous'` as an abbreviation for the stated proposition. No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named theorem, lemma, or local result is invoked. Consequently there are no proof steps to analyze beyond the definitional unfolding: the proposition is exactly the conjunction of the two displayed continuity conditions, one for each fixed coordinate.

