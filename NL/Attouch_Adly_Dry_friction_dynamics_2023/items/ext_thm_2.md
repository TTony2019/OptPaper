## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_thm_2.lean`

## Lean statement
```lean
theorem time_scaling_and_averaging_theorem {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (z : ℝ → H) (τ dτ ddτ : ℝ → ℝ) (x y dx dy ddx : ℝ → H) (s₀ : ℝ)
    (hy : y = timeScaledTrajectory z τ) (haverage : IsWeightedAverage τ dτ x y dx s₀)
    (hdτ_pos : ∀ s ∈ Set.Ici s₀, 0 < dτ s)
    (hdy : ∀ s ∈ Set.Ici s₀, HasDerivAt y (dy s) s)
    (hddx : ∀ s ∈ Set.Ici s₀, HasDerivAt dx (ddx s) s)
    (hddτ : ∀ s ∈ Set.Ici s₀, HasDerivAt dτ (ddτ s) s) :
    (∀ s ∈ Set.Ici s₀, x s = x s₀ + ∫ u in s₀..s, dx u) ∧
      ∀ s ∈ Set.Ioi s₀,
        ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s) = 0
```

## Statement explanation
The theorem is stated in a real Banach space \(H\), so \(H\) is a type equipped with a normed additive commutative group structure, a normed space structure over \(\mathbb{R}\), and a completeness assumption. The fixed base time is \(s_0 \in \mathbb{R}\). The following functions are given:
\[
z : \mathbb{R} \to H,\qquad
\tau,d\tau,dd\tau : \mathbb{R} \to \mathbb{R},\qquad
x,y,dx,dy,ddx : \mathbb{R} \to H.
\]
The hypotheses are:
- \(y = \operatorname{timeScaledTrajectory}(z,\tau)\).
- \( \operatorname{IsWeightedAverage}(\tau,d\tau,x,y,dx,s_0) \), named `haverage`. This packaged hypothesis is unpacked in the proof; from it the proof extracts differentiability of \(x\) and a weighted averaging equation.
- For every \(s \in \operatorname{Set.Ici} s_0\), i.e. every \(s \ge s_0\), one has \(0 < d\tau(s)\).
- For every \(s \ge s_0\), \(y\) has derivative \(dy(s)\) at \(s\).
- For every \(s \ge s_0\), \(dx\) has derivative \(ddx(s)\) at \(s\).
- For every \(s \ge s_0\), \(d\tau\) has derivative \(dd\tau(s)\) at \(s\).

The conclusion is a conjunction of two statements. First, for every \(s \ge s_0\),
\[
x(s) = x(s_0) + \int_{s_0}^{s} dx(u)\,du.
\]
Second, for every \(s > s_0\),
\[
ddx(s) - \frac{dd\tau(s)}{(d\tau(s))^2} \bullet (x(s)-y(s))
+
(d\tau(s))^{-1} \bullet (dx(s)-dy(s)) = 0.
\]
Here \(\bullet\) denotes scalar multiplication in the normed space \(H\), and the division and inverse are those of real numbers.

## Lean proof
```lean
by
  rcases haverage with ⟨hτ, hxy0, haverage⟩
  have hdx : ∀ s ∈ Set.Ici s₀, HasDerivAt x (dx s) s := fun s hs =>
    (haverage s hs).1
  have hode : ∀ s ∈ Set.Ici s₀, dx s + (dτ s)⁻¹ • (x s - y s) = 0 := fun s hs =>
    (haverage s hs).2
  constructor
  · intro s hs
    have hsle : s₀ ≤ s := hs
    have hxDeriv : ∀ u ∈ Set.uIcc s₀ s, HasDerivAt x (dx u) u := by
      rw [Set.uIcc_of_le hsle]
      intro u hu
      exact hdx u (Set.mem_Ici.mpr hu.1)
    have hdxCont : ContinuousOn dx (Set.uIcc s₀ s) := by
      rw [Set.uIcc_of_le hsle]
      intro u hu
      exact (hddx u (Set.mem_Ici.mpr hu.1)).continuousAt.continuousWithinAt
    have hdxInt : IntervalIntegrable dx MeasureTheory.volume s₀ s := hdxCont.intervalIntegrable
    have hftc : ∫ u in s₀..s, dx u = x s - x s₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hxDeriv hdxInt
    rw [hftc]
    abel
  · intro s hs
    have hsIci : s ∈ Set.Ici s₀ := Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hs))
    have hdτne : dτ s ≠ 0 := ne_of_gt (hdτ_pos s hsIci)
    let F : ℝ → H := fun t => dx t + (dτ t)⁻¹ • (x t - y t)
    have hinv : HasDerivAt (fun t : ℝ => (dτ t)⁻¹)
        (-ddτ s / (dτ s) ^ 2) s :=
      (hddτ s hsIci).inv hdτne
    have hdiff : HasDerivAt (fun t : ℝ => x t - y t) (dx s - dy s) s :=
      (hdx s hsIci).sub (hdy s hsIci)
    have hFderiv : HasDerivAt F
        (ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s)) s := by
      dsimp [F]
      convert (hddx s hsIci).add (hinv.smul hdiff) using 1
      all_goals simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, div_eq_mul_inv]
    have hFzero : (fun _ : ℝ => (0 : H)) =ᶠ[nhds s] F := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      simpa [F] using (hode t (le_of_lt ht)).symm
    have hconst : HasDerivAt (fun _ : ℝ => (0 : H))
        (ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s)) s :=
      hFderiv.congr_of_eventuallyEq hFzero
    exact hconst.unique (hasDerivAt_const s (0 : H))
```

## Proof explanation
The proof begins by decomposing the hypothesis `haverage` using `rcases` into three components named `hτ`, `hxy0`, and `haverage`. Only the final component is used. From it, the proof obtains two facts. The first fact, named `hdx`, states that for every \(s \ge s_0\), the function \(x\) has derivative \(dx(s)\) at \(s\). The second fact, named `hode`, states that for every \(s \ge s_0\),
\[
dx(s) + (d\tau(s))^{-1} \bullet (x(s)-y(s)) = 0.
\]
These are obtained as the first and second projections of `haverage s hs`.

The main goal is a conjunction, so the tactic `constructor` splits it into the two advertised statements.

For the first statement, the proof fixes \(s \ge s_0\) and proves the integral identity. Since \(s_0 \le s\), it rewrites the unordered interval \(\operatorname{Set.uIcc} s_0\, s\) as the ordinary interval \([s_0,s]\) using `Set.uIcc_of_le`. It then proves that for every \(u \in [s_0,s]\), the function \(x\) has derivative \(dx(u)\) at \(u\). Next, it proves that \(dx\) is continuous on \([s_0,s]\): for each \(u\) in that interval, the hypothesis `hddx` gives that \(dx\) is differentiable at \(u\), and differentiability implies continuity. The continuity on the interval then gives interval integrability of \(dx\). The fundamental theorem of calculus for interval integrals is applied via
\[
\verb|intervalIntegral.integral_eq_sub_of_hasDerivAt|
\]
to obtain
\[
\int_{s_0}^{s} dx(u)\,du = x(s) - x(s_0).
\]
Rewriting with this equality in the goal reduces it to
\[
x(s) = x(s_0) + (x(s)-x(s_0)),
\]
which is proved by the algebraic tactic `abel`.

For the second statement, the proof fixes \(s > s_0\). It first notes that \(s \ge s_0\), and from positivity of \(d\tau\) it obtains \(d\tau(s) \ne 0\). Define a function \(F:\mathbb{R}\to H\) by
\[
F(t) = dx(t) + (d\tau(t))^{-1} \bullet (x(t)-y(t)).
\]
The equation `hode` says exactly that \(F(t)=0\) for all \(t \ge s_0\). Since \(s > s_0\), this equality holds on a neighborhood of \(s\).

The proof then differentiates \(F\) at \(s\). It computes the derivative of \(t \mapsto (d\tau(t))^{-1}\) at \(s\) as
\[
-\frac{dd\tau(s)}{(d\tau(s))^2},
\]
using differentiability of \(d\tau\) and the fact that \(d\tau(s)\ne 0\). It also computes the derivative of \(t \mapsto x(t)-y(t)\) at \(s\) as
\[
dx(s)-dy(s),
\]
using differentiability of \(x\) and \(y\). Combining these with the derivative of \(dx\), the derivative of \(F\) at \(s\) is
\[
ddx(s) - \frac{dd\tau(s)}{(d\tau(s))^2} \bullet (x(s)-y(s))
+
(d\tau(s))^{-1} \bullet (dx(s)-dy(s)).
\]
The Lean commands `dsimp`, `convert`, and `simp` are used to unfold \(F\), combine derivative rules for addition and scalar multiplication, and rearrange the algebraic expression into exactly this form.

On the other hand, because \(F\) equals the zero function on a neighborhood of \(s\), the derivative of the zero function at \(s\) is the same expression. This is done using `filter_upwards` to obtain the eventual equality near \(s\), and `HasDerivAt.congr_of_eventuallyEq` to transfer the derivative from \(F\) to the zero function. Finally, the derivative of the constant zero function is \(0\), so by uniqueness of derivatives, the expression computed for the derivative must be equal to \(0\). This proves the desired second statement.

