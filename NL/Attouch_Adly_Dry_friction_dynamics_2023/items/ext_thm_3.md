## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_thm_3.lean`

## Lean statement
```lean
theorem fubini_tonelli_nonnegative {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure α) (ν : MeasureTheory.Measure β)
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] (K : α → β → ENNReal)
    (hK : Measurable (fun p : α × β => K p.1 p.2)) :
    ∫⁻ x, ∫⁻ y, K x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, K x y ∂μ ∂ν
```

## Statement explanation
The declaration is a theorem named `fubini_tonelli_nonnegative`. It states a Fubini–Tonelli interchange for two iterated Lebesgue integrals of a nonnegative, product-measurable function.

Variables and types:
- `α` and `β` are arbitrary types, equipped with measurable space structures via `[MeasurableSpace α]` and `[MeasurableSpace β]`.
- `μ` is a measure on `α`, and `ν` is a measure on `β`.
- The typeclass assumptions `[MeasureTheory.SFinite μ]` and `[MeasureTheory.SFinite ν]` say that both measures are s-finite, meaning each can be written as a countable sum of finite measures.
- `K : α → β → ENNReal` is a function taking a point `x : α` and a point `y : β` to a value in `ENNReal`, the extended nonnegative real numbers.
- The hypothesis `hK : Measurable (fun p : α × β => K p.1 p.2)` says that the associated function on the product `α × β`, sending a pair `(x, y)` to `K x y`, is measurable with respect to the product measurable space structure on `α × β`.

Conclusion:
- `∫⁻ x, ∫⁻ y, K x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, K x y ∂μ ∂ν`.
In standard notation, this is
`∫_α (∫_β K(x,y) dν(y)) dμ(x) = ∫_β (∫_α K(x,y) dμ(x)) dν(y)`.
Thus the theorem says that, under these hypotheses, the two iterated integrals with respect to `μ` and `ν` may be exchanged.

## Lean proof
```lean
MeasureTheory.lintegral_lintegral_swap (μ := μ) (ν := ν) (f := K) hK.aemeasurable
```

## Proof explanation
The proof is a single application of an existing library lemma, `MeasureTheory.lintegral_lintegral_swap`. The command supplies that lemma with the explicit measure arguments `μ := μ`, `ν := ν`, and the function argument `f := K`. This lemma states, for s-finite measures `μ` and `ν` and a function `f : α → β → ENNReal`, that if the associated function on the product is almost everywhere measurable with respect to the product measure, then the iterated integrals may be swapped.

The only minor conversion needed is that the hypothesis `hK` gives ordinary measurability on the product. The expression `hK.aemeasurable` forms from this the corresponding almost-everywhere measurability property required by the library lemma. Since ordinary measurability implies almost-everywhere measurability, this is a valid hypothesis.

The Lean command used is `exact`. It closes the goal by saying that the statement to be proved is precisely the instance of the library lemma with these chosen arguments. Therefore no additional construction or computation is needed; the theorem is proved directly by this single lemma application.

