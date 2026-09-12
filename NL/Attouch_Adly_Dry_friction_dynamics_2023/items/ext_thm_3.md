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
Let \(\alpha\) and \(\beta\) be types equipped with measurable spaces, let \(\mu\) be a measure on \(\alpha\), and let \(\nu\) be a measure on \(\beta\). The hypotheses \([\mathrm{SFinite}\,\mu]\) and \([\mathrm{SFinite}\,\nu]\) say that the two measures satisfy Mathlib’s `MeasureTheory.SFinite` condition, i.e. s-finiteness, which is the measure-finiteness assumption needed by the Fubini–Tonelli swap being invoked.

The function \(K : \alpha \to \beta \to \mathrm{ENNReal}\) is a curried two-variable kernel taking values in the extended nonnegative real numbers. Equivalently, it is a function on the product \(\alpha \times \beta\), written \(K(x,y)\), whose values lie in \(\overline{\mathbb{R}}_{\ge 0}\). The hypothesis `hK` states that the uncurried function
\[
p \mapsto K(p_1,p_2)
\]
from \(\alpha \times \beta\) to \(\mathrm{ENNReal}\) is measurable with respect to the product measurable structure on \(\alpha \times \beta\).

The conclusion is that the two iterated Lebesgue integrals of \(K\) agree:
\[
\int_{\alpha}^{-} \left(\int_{\beta}^{-} K(x,y)\,d\nu(y)\right)d\mu(x)
=
\int_{\beta}^{-} \left(\int_{\alpha}^{-} K(x,y)\,d\mu(x)\right)d\nu(y).
\]
Thus, on the left one first integrates in \(y\) with respect to \(\nu\) and then in \(x\) with respect to \(\mu\); on the right the order is reversed. Since the values are extended nonnegative reals, both iterated integrals are always defined in \(\overline{\mathbb{R}}_{\ge 0}\), and no separate integrability hypothesis is required. The equality may therefore hold as \(+\infty = +\infty\). This is Tonelli’s theorem in kernel form: for a nonnegative measurable kernel on a product of s-finite measure spaces, the order of iterated integration can be swapped.

## Lean proof
```lean
MeasureTheory.lintegral_lintegral_swap (μ := μ) (ν := ν) (f := K) hK.aemeasurable
```

## Proof explanation
The proof is a single term-level application rather than a tactic block. It invokes
`MeasureTheory.lintegral_lintegral_swap` with the named arguments `μ := μ`, `ν := ν`, and `f := K`, and it supplies `hK.aemeasurable` as the measurability argument. There are no uses of `intro`, `rw`, `simp`, `linarith`, or other tactics; the term is the analogue of an `exact` application of the swap lemma.

The argument `hK.aemeasurable` comes from the general fact that a measurable function is almost everywhere measurable. Here `hK` says that the uncurried kernel \(p \mapsto K(p_1,p_2)\) is measurable on \(\alpha \times \beta\). Applying `hK.aemeasurable` weakens that to almost-everywhere measurability with respect to the product measure \(\mu \otimes \nu\). This is the precise form of measurability that the Fubini–Tonelli lemma requires.

The cited result `MeasureTheory.lintegral_lintegral_swap` is the Mathlib form of the Fubini–Tonelli swap theorem for nonnegative functions. In this application, its inputs are the two s-finite measures \(\mu\) and \(\nu\), the kernel \(K\), and the a.e.-measurability of the uncurried kernel with respect to \(\mu \otimes \nu\). Its output is exactly the displayed equality
\[
\int_{\alpha}^{-} \left(\int_{\beta}^{-} K(x,y)\,d\nu(y)\right)d\mu(x)
=
\int_{\beta}^{-} \left(\int_{\alpha}^{-} K(x,y)\,d\mu(x)\right)d\nu(y).
\]
Because that is precisely the goal of `fubini_tonelli_nonnegative`, the term closes the proof. The proof uses only the a.e.-measurability consequence of `hK`; the original measurability hypothesis is stronger than what the invoked swap lemma needs.

