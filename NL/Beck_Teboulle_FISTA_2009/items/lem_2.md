## Source file
`Beck_Teboulle_FISTA_2009/items/lem_2.lean`

## Lean statement
```lean
theorem proxMap_optimality_condition {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ} (hL : 0 < L) (hg_conv : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin n))) g)
    (y z : EuclideanSpace ℝ (Fin n)) :
    IsProxPoint f g L y z ↔
    ∃ (γ : EuclideanSpace ℝ (Fin n)), γ ∈ subdifferential g z ∧
      gradient f y + L • (z - y) + γ = 0
```

## Statement explanation
The theorem `proxMap_optimality_condition` fixes a natural number $n$, two functions

$$
f,g:\mathbb R^n\to\mathbb R,
$$

a real number $L$ with $0<L$, and two points $y,z\in\mathbb R^n$. It assumes that $g$ is convex on the whole space $\mathbb R^n$. The conclusion is an equivalence:

$$
z \text{ is a proximal point for } f,g,L,y
$$

if and only if there exists a vector $\gamma\in\mathbb R^n$ such that

$$
\gamma\in \partial g(z)
$$

and

$$
\nabla f(y)+L(z-y)+\gamma=0.
$$

Here $\partial g(z)$ is the subdifferential of $g$ at $z$, defined by

$$
\gamma\in\partial g(z)
\quad\Longleftrightarrow\quad
\forall v,\quad g(z)+\langle \gamma,v-z\rangle\le g(v).
$$

The quadratic approximation used in the statement is

$$
Q(x,y)
=
f(y)+\langle \nabla f(y),x-y\rangle
+\frac L2\|x-y\|^2+g(x).
$$

In the proof, the hypothesis `h_prox : IsProxPoint f g L y z` is applied to the trivial membership proof `mem_univ x` to obtain

$$
Q(z,y)\le Q(x,y)
$$

for every $x\in\mathbb R^n$. Thus the left side of the theorem expresses exactly that $z$ minimizes the function $x\mapsto Q(x,y)$ over the whole space. The right side is the first-order optimality condition for this minimization: the gradient at $z$ of the smooth part

$$
x\mapsto f(y)+\langle \nabla f(y),x-y\rangle+\frac L2\|x-y\|^2
$$

is $\nabla f(y)+L(z-y)$, and the nonsmooth part $g$ contributes a subgradient $\gamma\in\partial g(z)$. The equation

$$
\nabla f(y)+L(z-y)+\gamma=0
$$

therefore says that $0$ belongs to the sum of the smooth gradient and the subdifferential of $g$ at $z$. Convexity of $g$ is used in the proof to control $g$ along line segments.

## Lean proof
```lean
by
  constructor
  · intro h_prox
    have h_min (x : EuclideanSpace ℝ (Fin n)) :
        quadraticApprox f g L z y ≤ quadraticApprox f g L x y := h_prox (mem_univ x)
    set γ := -gradient f y - L • (z - y) with hγ_def
    set a := gradient f y + L • (z - y) with ha_def
    have hγ_subdiff : γ ∈ subdifferential g z := by
      intro w
      set D := g w - g z + ⟪a, w - z⟫ with hD_def
      set C := (L / 2) * ‖w - z‖ ^ 2 with hC_def
      have hC_nonneg : 0 ≤ C := by nlinarith [sq_nonneg ‖w - z‖]
      have h_core (t : ℝ) (ht_pos : 0 < t) (ht_le1 : t ≤ 1) : D + C * t ≥ 0 := by
        set x_t := z + t • (w - z) with hxt_def
        have hQ := h_min x_t
        dsimp [quadraticApprox] at hQ
        -- quadraticApprox def: f y + ⟨∇f y, x-y⟩ + ... (∇f FIRST, then x-y)
        -- Normalize to ⟨v, ∇f⟩ order via inner_comm
        -- hQ uses ⟨∇f y, v⟩ order; match it in h_nonneg
        have h_nonneg : 0 ≤ (⟪gradient f y, x_t - y⟫ - ⟪gradient f y, z - y⟫) +
            (L / 2) * (‖x_t - y‖ ^ 2 - ‖z - y‖ ^ 2) + (g x_t - g z) := by
          linarith
        -- Inner product: ⟨∇f, x_t-y⟩ - ⟨∇f, z-y⟩ = t·⟨∇f, w-z⟩
        have h_inner : ⟪gradient f y, x_t - y⟫ - ⟪gradient f y, z - y⟫ =
            t * ⟪gradient f y, w - z⟫ := by
          calc
            ⟪gradient f y, x_t - y⟫ - ⟪gradient f y, z - y⟫
                = ⟪gradient f y, (x_t - y) - (z - y)⟫ := by
                  rw [← inner_sub_right]
            _ = ⟪gradient f y, x_t - z⟫ := by abel
            _ = ⟪gradient f y, t • (w - z)⟫ := by dsimp [x_t]; abel
            _ = t * ⟪gradient f y, w - z⟫ := by rw [inner_smul_right]
        -- Norm difference
        have h_norm : ‖x_t - y‖ ^ 2 - ‖z - y‖ ^ 2 =
            2 * t * ⟪z - y, w - z⟫ + t ^ 2 * ‖w - z‖ ^ 2 := by
          dsimp [x_t]
          calc
            ‖(z + t • (w - z)) - y‖ ^ 2 - ‖z - y‖ ^ 2
                = ‖(z - y) + t • (w - z)‖ ^ 2 - ‖z - y‖ ^ 2 := by abel
            _ = (‖z - y‖ ^ 2 + 2 * ⟪z - y, t • (w - z)⟫ + ‖t • (w - z)‖ ^ 2) - ‖z - y‖ ^ 2 := by
              rw [norm_add_sq_real]
            _ = 2 * ⟪z - y, t • (w - z)⟫ + ‖t • (w - z)‖ ^ 2 := by ring
            _ = 2 * (t * ⟪z - y, w - z⟫) + ‖t • (w - z)‖ ^ 2 := by rw [inner_smul_right]
            _ = 2 * t * ⟪z - y, w - z⟫ + ‖t • (w - z)‖ ^ 2 := by ring
            _ = 2 * t * ⟪z - y, w - z⟫ + ((|t|) * ‖w - z‖) ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs]
            _ = 2 * t * ⟪z - y, w - z⟫ + (t * ‖w - z‖) ^ 2 := by rw [abs_of_pos ht_pos]
            _ = 2 * t * ⟪z - y, w - z⟫ + t ^ 2 * ‖w - z‖ ^ 2 := by ring
        rw [h_inner, h_norm] at h_nonneg
        -- h_nonneg: 0 ≤ t·⟨w-z,∇f⟩ + (L/2)(2t·⟨z-y,w-z⟩ + t²·‖w-z‖²) + g(x_t) - g(z)
        -- Expand the middle term
        have h_expand : (L / 2) * (2 * t * ⟪z - y, w - z⟫ + t ^ 2 * ‖w - z‖ ^ 2) =
            L * t * ⟪z - y, w - z⟫ + (L / 2) * t ^ 2 * ‖w - z‖ ^ 2 := by ring
        rw [h_expand] at h_nonneg
        -- Relate to a: t·⟨∇f, w-z⟩ + L·t·⟨z-y, w-z⟩ = t·⟨a, w-z⟩
        have ha_eq : t * ⟪gradient f y, w - z⟫ + L * t * ⟪z - y, w - z⟫ = t * ⟪a, w - z⟫ := by
          calc
            t * ⟪gradient f y, w - z⟫ + L * t * ⟪z - y, w - z⟫
                = t * (⟪gradient f y, w - z⟫ + L * ⟪z - y, w - z⟫) := by ring
            _ = t * (⟪gradient f y, w - z⟫ + ⟪L • (z - y), w - z⟫) := by
              rw [inner_smul_left]; simp
            _ = t * ⟪gradient f y + L • (z - y), w - z⟫ := by rw [inner_add_left]
            _ = t * ⟪a, w - z⟫ := rfl
        have h_nonneg' : 0 ≤ t * ⟪a, w - z⟫ + (L / 2) * t ^ 2 * ‖w - z‖ ^ 2 + (g x_t - g z) := by
          linarith
        -- Convexity: g(x_t) - g(z) ≤ t(g(w) - g(z))
        have h_conv : g x_t - g z ≤ t * (g w - g z) := by
          have h_xt_eq : x_t = (1 - t) • z + t • w := by
            dsimp [x_t]; simp [smul_sub, sub_smul]; abel
          rw [h_xt_eq]
          have h_ineq := hg_conv.2 (mem_univ z) (mem_univ w)
            (by linarith : 0 ≤ 1 - t) (by linarith : 0 ≤ t) (by ring : (1 - t) + t = 1)
          have h_ineq' : g ((1 - t) • z + t • w) ≤ (1 - t) * g z + t * g w := by
            simpa [smul_eq_mul] using h_ineq
          linarith
        -- Combine: replace g(x_t)-g(z) with upper bound
        nlinarith
      -- Now: D + C·t ≥ 0 ∀ t ∈ (0,1]. Need D ≥ 0.
      by_cases hD_nonneg : 0 ≤ D
      · -- D ≥ 0 means g w - g z ≥ -⟨a, w-z⟩ = ⟨γ, w-z⟩
        have h_gamma_inner : ⟪γ, w - z⟫ = -⟪a, w - z⟫ := by
          dsimp [γ, a]
          calc
            ⟪-gradient f y - L • (z - y), w - z⟫
                = ⟪(-gradient f y) - L • (z - y), w - z⟫ := rfl
            _ = ⟪-gradient f y, w - z⟫ - ⟪L • (z - y), w - z⟫ := by rw [inner_sub_left]
            _ = -⟪gradient f y, w - z⟫ - L * ⟪z - y, w - z⟫ := by simp [inner_smul_left]
            _ = -(⟪gradient f y, w - z⟫ + L * ⟪z - y, w - z⟫) := by ring
            _ = -⟪gradient f y + L • (z - y), w - z⟫ := by
              simp [inner_add_left, inner_smul_left]
        rw [h_gamma_inner]; linarith
      · -- D < 0. Pick t small enough to get contradiction via h_core.
        by_cases hC_zero : C = 0
        · have h1 := h_core 1 (by norm_num) (by norm_num)
          rw [hC_zero] at h1; nlinarith
        · have hC_pos : 0 < C := by
            by_contra! h; apply hC_zero; linarith
          by_cases h_ratio : -D / (2 * C) ≤ 1
          · set t := -D / (2 * C) with ht_def
            have ht_pos : 0 < t := div_pos (by linarith) (by nlinarith)
            have ht_le1 : t ≤ 1 := h_ratio
            have h_core_t := h_core t ht_pos ht_le1
            have hCt_eq : C * t = -D / 2 := by
              dsimp [t]; field_simp [hC_pos.ne.symm]
            rw [hCt_eq] at h_core_t; nlinarith
          · have h_core_1 := h_core 1 (by norm_num) (by norm_num)
            -- From -D/(2C) > 1 and C > 0: -D > 2C, so D < -2C
            have h_pos_2C : 0 < 2 * C := by nlinarith
            have h_Div : -D / (2 * C) > 1 := by linarith
            have h_D_lt : D < -2 * C := by
              have h_mul : -D > 2 * C := by
                calc
                  -D = (-D / (2 * C)) * (2 * C) := by field_simp [h_pos_2C.ne.symm]
                  _ > 1 * (2 * C) := by nlinarith
                  _ = 2 * C := by ring
              linarith
            nlinarith
    exact ⟨γ, hγ_subdiff, by dsimp [a, γ]; abel⟩
  · -- Backward direction (←): purely algebraic
    rintro ⟨γ, hγ_subdiff, hγ_eq⟩
    have hγ_formula : γ = -gradient f y - L • (z - y) := by
      calc
        γ = (gradient f y + L • (z - y) + γ) - (gradient f y + L • (z - y)) := by abel
        _ = 0 - (gradient f y + L • (z - y)) := by rw [hγ_eq]
        _ = -gradient f y - L • (z - y) := by abel
    have h_subgrad (x : EuclideanSpace ℝ (Fin n)) :
        g z + ⟪-gradient f y - L • (z - y), x - z⟫ ≤ g x := by
      rw [← hγ_formula]; exact hγ_subdiff x
    intro x hx
    dsimp [quadraticApprox]
    have h_subgrad_x : g x - g z ≥ -⟪gradient f y + L • (z - y), x - z⟫ := by
      have h := h_subgrad x
      have h_neg_sum : -gradient f y - L • (z - y) = -(gradient f y + L • (z - y)) := by abel
      rw [h_neg_sum, inner_neg_left] at h; linarith
    have h_norm_diff : ‖x - y‖ ^ 2 - ‖z - y‖ ^ 2 = ‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫ := by
      calc
        ‖x - y‖ ^ 2 - ‖z - y‖ ^ 2
            = ‖(x - z) + (z - y)‖ ^ 2 - ‖z - y‖ ^ 2 := by abel
        _ = (‖x - z‖ ^ 2 + 2 * inner ℝ (x - z) (z - y) + ‖z - y‖ ^ 2) - ‖z - y‖ ^ 2 := by
          rw [norm_add_sq_real]
        _ = ‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫ := by ring
    have h_diff_nonneg : 0 ≤ (⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2 + g x) -
        (⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) := by
      have h_inner_diff : ⟪gradient f y, x - y⟫ - ⟪gradient f y, z - y⟫ = ⟪gradient f y, x - z⟫ := by
        rw [← inner_sub_right]; abel
      have h_expr : (⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2 + g x) -
          (⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) =
          ⟪gradient f y, x - z⟫ + (L / 2) * (‖x - y‖ ^ 2 - ‖z - y‖ ^ 2) + (g x - g z) := by nlinarith
      rw [h_expr, h_norm_diff]
      have h_lower : ⟪gradient f y, x - z⟫ + (L / 2) * (‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫) + (g x - g z) ≥
          (L / 2) * ‖x - z‖ ^ 2 := by
        calc
          ⟪gradient f y, x - z⟫ + (L / 2) * (‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫) + (g x - g z) ≥
              ⟪gradient f y, x - z⟫ + (L / 2) * (‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫)
              + (-⟪gradient f y + L • (z - y), x - z⟫) := by nlinarith
          _ = (L / 2) * ‖x - z‖ ^ 2 := by
            rw [inner_add_left]
            simp [inner_smul_left]
            rw [real_inner_comm (x - z) (z - y)]
            ring
      have h_nonneg_sq : 0 ≤ (L / 2) * ‖x - z‖ ^ 2 := by nlinarith [sq_nonneg ‖x - z‖]
      linarith
    linarith
```

## Proof explanation
The proof begins with `constructor`, which splits the biconditional into two implications.

For the forward implication, assume `h_prox : IsProxPoint f g L y z`. Applying it to `mem_univ x` gives the minimizer property

$$
Q(z,y)\le Q(x,y)
$$

for every $x$. The proof sets

$$
\gamma=-\nabla f(y)-L(z-y),
\qquad
a=\nabla f(y)+L(z-y),
$$

so that $\gamma=-a$. It then aims to prove $\gamma\in\partial g(z)$. Fix an arbitrary $w$. Define

$$
D=g(w)-g(z)+\langle a,w-z\rangle,
\qquad
C=\frac L2\|w-z\|^2.
$$

Since $\gamma=-a$, the desired subgradient inequality

$$
g(z)+\langle\gamma,w-z\rangle\le g(w)
$$

is equivalent to $D\ge0$. The term $C$ is nonnegative because $L>0$ and $\|w-z\|^2\ge0$; Lean records this with `nlinarith [sq_nonneg ‖w-z‖]`.

The key step is to prove

$$
D+Ct\ge0
$$

for every $t\in(0,1]$. For such a $t$, set

$$
x_t=z+t(w-z).
$$

The minimization property gives $Q(z,y)\le Q(x_t,y)$. After cancelling the common terms and subtracting, this becomes

$$
0\le
\langle \nabla f(y),x_t-y\rangle-\langle \nabla f(y),z-y\rangle
+\frac L2\bigl(\|x_t-y\|^2-\|z-y\|^2\bigr)
+g(x_t)-g(z).
$$

The proof computes the two differences separately. First,

$$
\langle \nabla f(y),x_t-y\rangle-\langle \nabla f(y),z-y\rangle
=
t\langle \nabla f(y),w-z\rangle,
$$

because $x_t-z=t(w-z)$. This is handled in Lean by rewriting with `inner_sub_right`, `abel`, and `inner_smul_right`. Second,

$$
\|x_t-y\|^2-\|z-y\|^2
=
2t\langle z-y,w-z\rangle+t^2\|w-z\|^2.
$$

This follows by writing $x_t-y=(z-y)+t(w-z)$ and expanding $\|u+v\|^2$; the proof uses `norm_add_sq_real`, `norm_smul`, and the positivity of $t$ to replace $|t|$ by $t$. Substituting these identities gives

$$
0\le
t\langle a,w-z\rangle
+\frac L2t^2\|w-z\|^2
+g(x_t)-g(z).
$$

Now $x_t=(1-t)z+tw$. Since $0\le 1-t$, $0\le t$, and $(1-t)+t=1$, convexity of $g$ gives

$$
g(x_t)\le (1-t)g(z)+t g(w),
$$

hence

$$
g(x_t)-g(z)\le t(g(w)-g(z)).
$$

Combining this with the previous inequality yields

$$
0\le t\bigl(\langle a,w-z\rangle+g(w)-g(z)\bigr)
+\frac L2t^2\|w-z\|^2
=
t(D+Ct).
$$

Because $t>0$, this implies $D+Ct\ge0$. The Lean proof packages this nonlinear arithmetic with `nlinarith`.

It remains to deduce $D\ge0$. If $D\ge0$, this is immediate. In that case the proof also verifies

$$
\langle\gamma,w-z\rangle=-\langle a,w-z\rangle,
$$

and $D\ge0$ becomes

$$
g(w)-g(z)\ge-\langle a,w-z\rangle
=
\langle\gamma,w-z\rangle,
$$

which is exactly the subgradient inequality.

If $D<0$, the proof derives a contradiction from the positivity of $C$ and the bounds $D+Ct\ge0$. If $C=0$, then taking $t=1$ gives $D\ge0$, contradicting $D<0$. Otherwise $C>0$. If

$$
-\frac{D}{2C}\le 1,
$$

the proof chooses

$$
t=-\frac{D}{2C}.
$$

Since $D<0$ and $C>0$, this $t$ lies in $(0,1]$. The inequality $D+Ct\ge0$ becomes

$$
D-\frac D2=\frac D2\ge0,
$$

contradicting $D<0$. If instead

$$
-\frac{D}{2C}>1,
$$

then from $C>0$ the proof obtains $-D>2C$, hence $D<-2C$. Taking $t=1$ gives $D+C<-C<0$, contradicting the already established $D+C\ge0$. Thus $D\ge0$ after all, so $\gamma\in\partial g(z)$. Finally the proof assembles the witness $\gamma$, the subgradient membership, and the equation

$$
\nabla f(y)+L(z-y)+\gamma=0,
$$

which holds because $\gamma=-(\nabla f(y)+L(z-y))$. The closing `abel` is just the additive rearrangement proving this identity.

For the backward implication, assume there exists $\gamma$ with

$$
\gamma\in\partial g(z)
\qquad\text{and}\qquad
\nabla f(y)+L(z-y)+\gamma=0.
$$

The proof first rewrites the equation as

$$
\gamma=-\nabla f(y)-L(z-y).
$$

Thus the subgradient inequality for $\gamma$ becomes, for every $x$,

$$
g(z)+\langle -\nabla f(y)-L(z-y),x-z\rangle\le g(x).
$$

Equivalently, with $a=\nabla f(y)+L(z-y)$,

$$
g(x)-g(z)\ge-\langle a,x-z\rangle.
$$

To prove that $z$ minimizes $Q(\cdot,y)$, take an arbitrary $x$. The proof expands `quadraticApprox` and computes

$$
Q(x,y)-Q(z,y)
=
\langle \nabla f(y),x-z\rangle
+\frac L2\bigl(\|x-y\|^2-\|z-y\|^2\bigr)
+g(x)-g(z).
$$

Next it uses the identity

$$
\|x-y\|^2-\|z-y\|^2
=
\|x-z\|^2+2\langle x-z,z-y\rangle,
$$

obtained by writing $x-y=(x-z)+(z-y)$ and expanding. Substituting this identity and the lower bound for $g(x)-g(z)$, the difference is bounded below by

$$
\langle \nabla f(y),x-z\rangle
+\frac L2\bigl(\|x-z\|^2+2\langle x-z,z-y\rangle\bigr)
-\langle a,x-z\rangle.
$$

Since

$$
a=\nabla f(y)+L(z-y),
$$

we have

$$
\langle a,x-z\rangle
=
\langle \nabla f(y),x-z\rangle
+L\langle z-y,x-z\rangle,
$$

and by symmetry of the inner product,

$$
\langle z-y,x-z\rangle=\langle x-z,z-y\rangle.
$$

Therefore the linear terms cancel and the lower bound reduces to

$$
\frac L2\|x-z\|^2\ge0,
$$

using $L>0$. Hence

$$
Q(x,y)-Q(z,y)\ge0,
$$

so $Q(z,y)\le Q(x,y)$. Since $x$ was arbitrary, $z$ is a proximal point for $f,g,L,y$. This proves the reverse implication and completes the equivalence. The Lean tactics `rw`, `simp`, `ring`, `field_simp`, `linarith`, and `nlinarith` are used throughout to perform the inner-product rewrites, algebraic simplifications, division manipulations, and linear or nonlinear inequality reasoning described above.

