## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/ext_def_2.lean`

## Lean statement
```lean
lemma firmly_nonexpansive_iff_averaged {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) : IsFirmlyNonexpansive T ↔
    ∃ (N : H → H), (∀ x y : H, ‖N x - N y‖ ≤ ‖x - y‖) ∧ (∀ x : H, T x = (1/2 : ℝ) • (x + N x))
```

## Statement explanation
The declaration states that a self-map \(T\) of a real inner product space \(H\) is firmly nonexpansive if and only if it can be written as the half-average of the identity map and a nonexpansive map \(N\). Here \(H\) is assumed to be a normed additive commutative group with a real inner product structure. The map \(T:H\to H\) is arbitrary; in particular, it is not assumed to be linear, continuous, or convex-valued. The scalar \(1/2\) in the formula is real scalar multiplication.

In the proof, the predicate `IsFirmlyNonexpansive` is used in the concrete form
\[
\forall x,y\in H,\qquad \|T x-T y\|^{2}\le \langle T x-T y,\;x-y\rangle .
\]
The right-hand side of the equivalence says that there exists a map \(N:H\to H\) such that \(N\) is nonexpansive,
\[
\forall x,y\in H,\qquad \|N x-N y\|\le \|x-y\|,
\]
and such that for every \(x\in H\),
\[
T x=\frac12\bigl(x+N x\bigr).
\]
Thus the lemma characterizes firmly nonexpansive maps exactly as maps of the form
\[
T=\frac12\bigl(\mathrm{id}+N\bigr)
\]
with \(N\) nonexpansive. No uniqueness of \(N\) is asserted. In the forward direction the proof constructs the particular choice \(N(x)=2T(x)-x\), and in the reverse direction it reconstructs \(T\) from an arbitrary nonexpansive \(N\) satisfying the averaging identity.

## Lean proof
```lean
by
  constructor
  · intro hT
    -- Define N = 2T - I (the "reflection" of T)
    let N : H → H := λ x => (2 : ℝ) • T x - x
    refine ⟨N, ?_, ?_⟩
    · -- N is nonexpansive: ‖N x - N y‖ ≤ ‖x - y‖
      intro x y
      have h := hT x y
      -- h : ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y)
      have h_diff : N x - N y = (2 : ℝ) • (T x - T y) - (x - y) := by
        dsimp [N]
        rw [smul_sub (2 : ℝ) (T x) (T y)]
        abel
      rw [h_diff]
      set a := T x - T y
      set b := x - y
      -- Prove: ‖2a - b‖² ≤ ‖b‖² via the identity ‖2a-b‖² = 4‖a‖² - 4⟨a,b⟩ + ‖b‖²
      have h_sq : ‖(2 : ℝ) • a - b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
        have h_eq : ‖(2 : ℝ) • a - b‖ ^ 2 - ‖b‖ ^ 2 = 4 * (‖a‖ ^ 2 - inner ℝ a b) := by
          rw [norm_sub_sq (𝕜 := ℝ) ((2 : ℝ) • a) b]
          simp
          -- Goal: (‖2a‖² - 2*inner(2a,b) + ‖b‖²) - ‖b‖² = 4*(‖a‖² - inner a b)
          have h_inner : inner ℝ ((2 : ℝ) • a) b = (2 : ℝ) * inner ℝ a b := by
            rw [inner_smul_left (x := a) (y := b) (r := (2 : ℝ))]
            simp
          rw [h_inner]
          have h_norm : ‖(2 : ℝ) • a‖ ^ 2 = 4 * ‖a‖ ^ 2 := by
            rw [norm_smul (r := (2 : ℝ)) (x := a)]
            norm_num
            ring
          rw [h_norm]
          ring
        have h_nonpos : ‖(2 : ℝ) • a - b‖ ^ 2 - ‖b‖ ^ 2 ≤ 0 := by
          rw [h_eq]
          nlinarith
        linarith
      have hpos1 : 0 ≤ ‖(2 : ℝ) • a - b‖ := norm_nonneg _
      have hpos2 : 0 ≤ ‖b‖ := norm_nonneg _
      nlinarith
    · -- T = (I + N)/2
      intro x
      dsimp [N]
      -- Goal: T x = (1/2) • (x + (2•Tx - x))
      -- Compute the RHS and show it equals T x
      have hcalc : (1/2 : ℝ) • (x + ((2 : ℝ) • T x - x)) = T x := by
        calc
          (1/2 : ℝ) • (x + ((2 : ℝ) • T x - x)) = (1/2 : ℝ) • (((2 : ℝ) • T x) + (x - x)) := by abel
          _ = (1/2 : ℝ) • ((2 : ℝ) • T x) := by simp
          _ = ((1/2 : ℝ) * (2 : ℝ)) • T x := by rw [mul_smul]
          _ = (1 : ℝ) • T x := by norm_num
          _ = T x := by simp
      exact hcalc.symm
  · intro ⟨N, hN_nonexp, hT⟩
    intro x y
    have hN := hN_nonexp x y
    -- hN : ‖N x - N y‖ ≤ ‖x - y‖
    have hTx_diff : T x - T y = (1/2 : ℝ) • ((x - y) + (N x - N y)) := by
      rw [hT x, hT y]
      rw [← smul_sub (1/2 : ℝ) (x + N x) (y + N y)]
      congr 1
      abel
    have h_key : inner ℝ (T x - T y) (x - y) - ‖T x - T y‖ ^ 2 =
        (1/4 : ℝ) * (‖x - y‖ ^ 2 - ‖N x - N y‖ ^ 2) := by
      rw [hTx_diff]
      set a := x - y
      set b := N x - N y
      -- Compute ⟨(1/2)(a+b), a⟩ and ‖(1/2)(a+b)‖²
      have h1 : inner ℝ ((1/2 : ℝ) • (a + b)) a = (1/2 : ℝ) * (‖a‖ ^ 2 + inner ℝ b a) := by
        rw [inner_smul_left (x := a + b) (y := a) (r := (1/2 : ℝ))]
        simp
        rw [inner_add_left, real_inner_self_eq_norm_sq]
      have h2 : ‖(1/2 : ℝ) • (a + b)‖ ^ 2 = (1/4 : ℝ) * (‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2) := by
        calc
          ‖(1/2 : ℝ) • (a + b)‖ ^ 2 = (‖(1/2 : ℝ)‖ * ‖a + b‖) ^ 2 := by
            rw [norm_smul (r := (1/2 : ℝ)) (x := a + b)]
          _ = ((1/2 : ℝ) * ‖a + b‖) ^ 2 := by norm_num
          _ = ((1/2 : ℝ) ^ 2) * ‖a + b‖ ^ 2 := by ring
          _ = (1/4 : ℝ) * ‖a + b‖ ^ 2 := by norm_num
          _ = (1/4 : ℝ) * (‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2) := by
            rw [norm_add_sq (𝕜 := ℝ) a b]; simp
      rw [h1, h2]
      -- Simplify: (1/2)(‖a‖²+⟨b,a⟩) - (1/4)(‖a‖²+2⟨a,b⟩+‖b‖²) = (1/4)(‖a‖²-‖b‖²)
      rw [real_inner_comm b a]
      ring
    have hN_sq : ‖N x - N y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hpos1 : 0 ≤ ‖N x - N y‖ := norm_nonneg _
      have hpos2 : 0 ≤ ‖x - y‖ := norm_nonneg _
      nlinarith
    have h_nonneg : 0 ≤ inner ℝ (T x - T y) (x - y) - ‖T x - T y‖ ^ 2 := by
      rw [h_key]
      nlinarith
    exact sub_nonneg.mp h_nonneg
```

## Proof explanation
The proof begins with `constructor`, which splits the iff statement into the two implications.

For the forward implication, the proof assumes \(T\) is firmly nonexpansive and defines
\[
N(x)=2T(x)-x.
\]
It then uses `refine` to provide this \(N\) and to produce the two required properties.

First it proves that \(N\) is nonexpansive. For arbitrary \(x,y\in H\), it applies the firm-nonexpansiveness hypothesis to obtain
\[
\|T x-T y\|^{2}\le \langle T x-T y,\;x-y\rangle .
\]
It computes
\[
N x-N y
=
\bigl(2T(x)-x\bigr)-\bigl(2T(y)-y\bigr)
=
2(T x-T y)-(x-y),
\]
using `dsimp` to unfold the definition of \(N\), `rw` for the scalar subtraction identity, and `abel` to normalize the additive expression. Setting
\[
a=T x-T y,\qquad b=x-y,
\]
the goal becomes
\[
\|2a-b\|\le \|b\|.
\]
The proof establishes the squared inequality instead. It uses the identity for the squared norm of a difference, `norm_sub_sq`, together with `inner_smul_left`, which gives
\[
\langle 2a,b\rangle=2\langle a,b\rangle,
\]
and `norm_smul`, which gives
\[
\|2a\|=2\|a\|.
\]
These reduce the difference of squares to
\[
\|2a-b\|^{2}-\|b\|^{2}
=
4\bigl(\|a\|^{2}-\langle a,b\rangle\bigr).
\]
Since the firm-nonexpansiveness hypothesis says
\[
\|a\|^{2}\le \langle a,b\rangle,
\]
the right-hand side is nonpositive. The tactic `nlinarith` uses this inequality to conclude
\[
\|2a-b\|^{2}\le \|b\|^{2}.
\]
Because both norms are nonnegative, the proof then uses `nlinarith` again to pass from the square inequality to
\[
\|2a-b\|\le \|b\|.
\]
This is exactly \(\|N x-N y\|\le \|x-y\|\), so \(N\) is nonexpansive.

Second, the proof verifies the averaging identity. For arbitrary \(x\), the definition of \(N\) gives
\[
x+N x=x+\bigl(2T(x)-x\bigr)=2T(x).
\]
Therefore
\[
\frac12\bigl(x+N x\bigr)
=
\frac12\bigl(2T(x)\bigr)
=
T(x).
\]
The `calc` block performs exactly this computation: `abel` rearranges the additive terms, `simp` removes the zero term, `mul_smul` uses \((1/2)(2T x)=((1/2)\cdot 2)T x\), and `norm_num` evaluates \((1/2)\cdot 2=1\). The final `exact hcalc.symm` closes the goal.

For the reverse implication, the proof assumes that there exists a nonexpansive \(N\) with
\[
T(x)=\frac12\bigl(x+N(x)\bigr)
\]
for every \(x\). It must show that \(T\) is firmly nonexpansive, i.e. for arbitrary \(x,y\),
\[
\|T x-T y\|^{2}\le \langle T x-T y,\;x-y\rangle .
\]
The hypothesis that \(N\) is nonexpansive gives
\[
\|N x-N y\|\le \|x-y\|.
\]

The proof first derives the difference formula
\[
T x-T y
=
\frac12\Bigl((x-y)+(N x-N y)\Bigr).
\]
This follows by substituting the averaging formula for \(T x\) and \(T y\), subtracting, and using the linearity of scalar multiplication over subtraction; the tactics `rw`, `smul_sub`, and `abel` perform these operations.

It then sets
\[
a=x-y,\qquad b=N x-N y,
\]
so that
\[
T x-T y=\frac12(a+b).
\]
The key computation is
\[
\langle T x-T y,\;x-y\rangle-\|T x-T y\|^{2}
=
\frac14\bigl(\|a\|^{2}-\|b\|^{2}\bigr).
\]
To obtain it, the proof uses `inner_smul_left` and `inner_add_left` to compute
\[
\left\langle \frac12(a+b),\,a\right\rangle
=
\frac12\bigl(\|a\|^{2}+\langle b,a\rangle\bigr),
\]
where `real_inner_self_eq_norm_sq` identifies \(\langle a,a\rangle\) with \(\|a\|^{2}\). It uses `norm_smul` and `norm_add_sq` to compute
\[
\left\|\frac12(a+b)\right\|^{2}
=
\frac14\bigl(\|a\|^{2}+2\langle a,b\rangle+\|b\|^{2}\bigr),
\]
where the identity \(\|a+b\|^{2}=\|a\|^{2}+2\langle a,b\rangle+\|b\|^{2}\) is the real inner-product expansion. Symmetry of the real inner product, `real_inner_comm`, gives \(\langle b,a\rangle=\langle a,b\rangle\), and the final algebraic simplification is done by `ring`.

Since \(N\) is nonexpansive, \(\|b\|\le \|a\|\). Because both are nonnegative, their squares satisfy
\[
\|b\|^{2}\le \|a\|^{2}.
\]
The tactic `nlinarith` uses this to show that the right-hand side of the key identity is nonnegative, hence
\[
0\le \langle T x-T y,\;x-y\rangle-\|T x-T y\|^{2}.
\]
Finally, `sub_nonneg.mp` converts this nonnegativity of a difference into
\[
\|T x-T y\|^{2}\le \langle T x-T y,\;x-y\rangle,
\]
which is precisely the firm-nonexpansiveness condition for \(T\). This completes the reverse implication and therefore the proof of the equivalence.

