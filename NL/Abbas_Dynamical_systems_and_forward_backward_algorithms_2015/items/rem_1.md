## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/rem_1.lean`

## Lean statement
```lean
def remark_2_3_variable_regularization {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (_hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (lam : ℝ → ℝ) (beta : ℝ) (x0 v0 : H)
    (_hlam_pos : ∀ t, 0 ≤ t → 0 < lam t)
    (_hlam_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval lam 0 b)
    (_hbeta : 0 < beta) (_hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x))
    (_hv0 : v0 ∈ ERealFunction.subdifferential Phi x0) : Prop :=
    ∃! xv : (ℝ → H) × (ℝ → H),
      (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval xv.1 0 b) ∧
      (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval xv.2 0 b) ∧
      (∀ t, 0 ≤ t → xv.2 t ∈ ERealFunction.subdifferential Phi (xv.1 t)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ici 0),
        lam t • deriv xv.1 t + deriv xv.2 t + xv.2 t + B (xv.1 t) = 0) ∧
      xv.1 0 = x0 ∧ xv.2 0 = v0
```

## Statement explanation
The declaration defines a proposition named `remark_2_3_variable_regularization`.

The ambient space is an implicit type variable \(H\), equipped with the typeclasses making it a normed additive commutative group, a normed vector space over \(\mathbb R\), a real inner-product space, and complete. Thus \(H\) is a real Hilbert space.

The explicit mathematical inputs are:

- \(\Phi : H \to \operatorname{Set.Ioi}(\bot_{\mathrm{EReal}})\), a function taking values in the extended real numbers strictly above the bottom element. This is interpreted as an extended-real-valued function on \(H\) excluding the bottom value.
- An assumption `_hPhi : Phi ∈ ERealFunction.gammaZero H`, saying that \(\Phi\) belongs to the class `ERealFunction.gammaZero H` used in the surrounding development.
- \(B : H \to H\), an operator on \(H\).
- \(\lambda : \mathbb R \to \mathbb R\), a real-valued parameter function.
- \(\beta : \mathbb R\), a real parameter.
- \(x_0, v_0 : H\), two initial vectors in \(H\).

The declared hypotheses are:

- `_hlam_pos`: For every \(t \ge 0\), \(\lambda(t) > 0\).
- `_hlam_ac`: For every \(b > 0\), \(\lambda\) is absolutely continuous on the interval \([0,b]\).
- `_hbeta`: \(\beta > 0\).
- `_hB`: \(B\) is \(\beta\)-cocoercive on \(\operatorname{Set.univ}\), the whole space. In the source, the function is written as \(x \mapsto B x\) on the subtype consisting of all points of \(H\).
- `_hv0`: \(v_0 \in \operatorname{ERealFunction.subdifferential} \Phi(x_0)\), i.e. \(v_0\) is in the subdifferential of \(\Phi\) at \(x_0\).

The conclusion is the following proposition:

There exists a unique pair
\[
xv = (x,v) \in (\mathbb R \to H) \times (\mathbb R \to H)
\]
such that:

1. For every \(b > 0\), the first component \(xv.1 = x\) is absolutely continuous on \([0,b]\).
2. For every \(b > 0\), the second component \(xv.2 = v\) is absolutely continuous on \([0,b]\).
3. For every \(t \ge 0\), \(v(t) \in \operatorname{ERealFunction.subdifferential} \Phi(x(t))\).
4. For almost every \(t \ge 0\) with respect to Lebesgue measure restricted to \([0,\infty)\),
\[
\lambda(t)\, x'(t) + v'(t) + v(t) + B(x(t)) = 0,
\]
where `deriv` is denoted by the derivative.
5. The initial conditions hold:
\[
x(0) = x_0, \qquad v(0) = v_0.
\]

Thus the declaration states the existence and uniqueness of a pair of absolutely continuous forward curves \((x,v)\) satisfying a subdifferential inclusion and an almost-everywhere differential equation together with initial data.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part in the Lean source. The declaration is a `def` whose declared type is `Prop`, and its body after `:=` is exactly the proposition stated above. It is therefore a definition of a predicate/proposition, not a theorem supplied with a proof.

Because there is no proof, there are no `intro`, `rw`, `simp`, `exact`, `linarith`, or other tactic commands to explain. The statement is expressed directly with logical and analytic notation: `∃!` asserts uniqueness of existence; `∧` combines the required conditions; `∀` and `∀ᵐ ... ∂ ...` express pointwise and almost-everywhere quantifiers; `AbsolutelyContinuousOnInterval` expresses absolute continuity on a finite interval; and `deriv` gives the derivative used in the differential equation. No mathematical fact beyond the stated uniqueness existence proposition is asserted or proved here.

