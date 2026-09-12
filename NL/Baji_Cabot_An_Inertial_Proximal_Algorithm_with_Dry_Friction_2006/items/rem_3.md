## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/rem_3.lean`

## Lean statement
```lean
theorem rem_5_2 (x : ℕ → H) (xInf : H) (n0 : ℕ) (K : ℝ) (q : ℝ) (hK : K > 0) (hq0 : q > 0) (hq1 : q < 1)
    (h_vel_decay : ∀ n ≥ n0, ‖x (n+1) - x n‖ ≤ K * q ^ n) (hxInf : Tendsto x atTop (𝓝 xInf)) :
    ∀ n ≥ n0, ‖x n - xInf‖ ≤ (K / (1 - q)) * q ^ n
```

## Statement explanation
The theorem `rem_5_2` concerns a sequence \(x:\mathbb N\to H\) in the ambient normed type \(H\), a candidate limit point \(x_\infty\in H\), a starting index \(n_0\in\mathbb N\), and real numbers \(K\) and \(q\). Its hypotheses are \(K>0\), \(q>0\), and \(q<1\), so \(q\in(0,1)\). It also assumes that, from index \(n_0\) onward, consecutive differences of the sequence decay geometrically:
\[
\forall n\ge n_0,\qquad \|x_{n+1}-x_n\|\le K q^n.
\]
Finally, it assumes that the sequence converges to \(x_\infty\):
\[
x_n \to x_\infty \quad\text{as } n\to\infty.
\]
The conclusion is that the distance from \(x_n\) to the limit obeys the same geometric decay bound:
\[
\forall n\ge n_0,\qquad \|x_n-x_\infty\|\le \frac{K}{1-q}\,q^n.
\]
Mathematically, this says that if a convergent sequence has geometric decay of its successive increments with ratio \(q\in(0,1)\), then its distance to the limit is bounded by the corresponding geometric tail sum, namely \(K q^n/(1-q)\).

## Lean proof
```lean
by
  intro n hn
  have hK_nonneg : 0 ≤ K := le_of_lt hK
  have hq_nonneg : 0 ≤ q := le_of_lt hq0
  let R : ℝ := (K / (1 - q)) * q ^ n
  have h_eventual : (fun m : ℕ => ‖x n - x m‖) ≤ᶠ[atTop] (fun _ : ℕ => R) := by
    change ∀ᶠ m : ℕ in atTop, ‖x n - x m‖ ≤ R
    rw [Filter.eventually_atTop]
    refine ⟨n, ?_⟩
    intro m hm
    exact rem52_finite_tail_bound x n0 n m K q hK_nonneg hq_nonneg hq1
      h_vel_decay hn hm
  have hcont : Continuous (fun y : H => ‖x n - y‖) :=
    (continuous_const.sub continuous_id).norm
  have h_tend : Tendsto (fun m : ℕ => ‖x n - x m‖) atTop (𝓝 ‖x n - xInf‖) := by
    simpa using (hcont.tendsto xInf).comp hxInf
  have h_const : Tendsto (fun _ : ℕ => R) atTop (𝓝 R) := tendsto_const_nhds
  have h_le : ‖x n - xInf‖ ≤ R := le_of_tendsto_of_tendsto h_tend h_const h_eventual
  simpa [R] using h_le
```

## Proof explanation
The proof begins with `intro n hn`, which fixes an arbitrary index \(n\) and assumes the hypothesis \(n\ge n_0\). The goal is then to prove
\[
\|x_n-x_\infty\|\le \frac{K}{1-q}\,q^n.
\]
Next, the proof derives the non-strict inequalities \(0\le K\) and \(0\le q\) from \(K>0\) and \(q>0\) using `le_of_lt`. These non-strict nonnegativity facts are needed because the cited finite-tail bound `rem52_finite_tail_bound` is stated with assumptions \(0\le K\) and \(0\le q\), not strict positivity.

The proof then defines
\[
R=\frac{K}{1-q}\,q^n.
\]
The first main step is to show that the values \(\|x_n-x_m\|\) are eventually bounded by \(R\). In Lean this is expressed by proving that the function \(m\mapsto \|x_n-x_m\|\) is eventually less than or equal to the constant function \(m\mapsto R\) along \(\operatorname{atTop}\). After rewriting the eventual statement using `Filter.eventually_atTop`, this becomes the assertion that there exists a threshold \(N\) such that for every \(m\ge N\),
\[
\|x_n-x_m\|\le R.
\]
The proof chooses the threshold \(N=n\). Then, for an arbitrary \(m\ge n\), it applies `rem52_finite_tail_bound`. That cited result states that if \(x\) is a sequence, \(n_0,n,m\) are natural numbers, \(K,q\) are real numbers with \(0\le K\), \(0\le q\), \(q<1\), if the velocity estimate
\[
\|x_{i+1}-x_i\|\le K q^i
\]
holds for all \(i\ge n_0\), and if \(n_0\le n\le m\), then
\[
\|x_n-x_m\|\le \frac{K}{1-q}\,q^n.
\]
In the present proof, the hypothesis \(h\_vel\_decay\) supplies exactly the required consecutive-difference estimate; the already introduced assumption \(hn\) gives \(n_0\le n\); and the new assumption \(hm\) gives \(n\le m\). Therefore `rem52_finite_tail_bound` yields
\[
\|x_n-x_m\|\le \frac{K}{1-q}\,q^n=R.
\]
This proves the eventual bound.

The proof next shows that the map
\[
y\mapsto \|x_n-y\|
\]
is continuous. This is done by observing that \(y\mapsto x_n\) is constant and continuous, that \(y\mapsto y\) is the identity and hence continuous, that subtraction is continuous, and that the norm is continuous. Thus the composite \(y\mapsto \|x_n-y\|\) is continuous. Applying this continuity at \(x_\infty\) and composing with the assumed convergence \(x_m\to x_\infty\), the proof obtains
\[
\|x_n-x_m\|\to \|x_n-x_\infty\|
\quad\text{as } m\to\infty.
\]
This is the content of the step constructing `h_tend` by composing `hcont.tendsto xInf` with `hxInf`.

The constant sequence \(m\mapsto R\) tends to \(R\), by `tendsto_const_nhds`. Thus the proof has two convergent sequences:
\[
m\mapsto \|x_n-x_m\| \to \|x_n-x_\infty\|,
\]
and
\[
m\mapsto R \to R,
\]
with the eventual inequality
\[
\|x_n-x_m\|\le R
\]
for all sufficiently large \(m\). The order-limit principle `le_of_tendsto_of_tendsto` then gives the inequality of the limits:
\[
\|x_n-x_\infty\|\le R.
\]
Finally, `simpa [R] using h_le` unfolds the definition of \(R\), yielding
\[
\|x_n-x_\infty\|\le \frac{K}{1-q}\,q^n.
\]
Since \(n\ge n_0\) was arbitrary, this proves the stated universal conclusion.

