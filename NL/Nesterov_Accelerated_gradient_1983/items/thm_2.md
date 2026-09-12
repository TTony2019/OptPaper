## Source file
`Nesterov_Accelerated_gradient_1983/items/thm_2.lean`

## Lean statement
```lean
theorem composite_accelerated_rate {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (P : ExtremalProblem m E) (T : E → ℝ → E)
    (M : CompositeAcceleratedMethod P T) (xstar : E) (Lbar : EuclideanSpace ℝ (Fin m))
    (hstar : xstar ∈ P.solutionSet)
    (hC11 : ∀ i, IsC11 (P.f i) (Lbar i))
    (hT : HasAuxiliaryMappingEstimates P T)
    (hLower : HasAuxiliaryValueLowerBound P T Lbar)
    (hApos : 0 < M.initialA)
    (hFmono : ∀ u v : EuclideanSpace ℝ (Fin m), (∀ i, 0 ≤ u i) → (∀ i, u i ≤ v i) →
      P.F u ≤ P.F v) :
    (∀ k, P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) - P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤
      (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2) / (k + 2 : ℝ) ^ 2) ∧
    ∀ ε : ℝ, 0 < ε →
      let NG
```

## Statement explanation
Let $E$ be a complete real inner-product space, $m$ a natural number, $P$ an extremal problem with $m$ component functions $P.f_i:E\to\mathbb R$, and $P.F$ the objective functional on the vector of component values. For a point $y\in E$, write

$$
G(y)=P.F\bigl(\mathrm{WithLp.toLp}\,2\,(i\mapsto P.f_i(y))\bigr),
$$

that is, $P.F$ applied to the vector $(P.f_1(y),\dots,P.f_m(y))$. The theorem concerns a composite accelerated method $M$ for $P$ and an auxiliary mapping $T:E\to\mathbb R\to E$. The fields $M.x_k$, $M.y_k$, $M.A_k$, $M.weight_k$, $M.initialA$, $M.y_0$, and $M.searchIndex_k$ are respectively the method’s $k$-th iterate, auxiliary point, auxiliary coefficient, weight, initial value, initial auxiliary point, and search index.

The hypotheses are: $x^*$ is a solution of $P$, i.e. $x^*\in P.solutionSet$; for every component index $i$, $P.f_i$ satisfies the $C^{1,1}$-type condition `IsC11` with constant $Lbar_i$; the auxiliary mapping $T$ satisfies the auxiliary estimates `HasAuxiliaryMappingEstimates`; the auxiliary values satisfy the lower bound `HasAuxiliaryValueLowerBound` relative to $Lbar$; the initial value is positive, $0<M.initialA$; and $P.F$ is monotone on nonnegative vectors in the sense that if $u,v\in\mathbb R^m$, $u\ge 0$ coordinatewise, and $u\le v$ coordinatewise, then $P.F(u)\le P.F(v)$.

The conclusion is a conjunction. First, for every natural number $k$,

$$
G(M.x_k)-G(x^*)
\le
\frac{4\,P.F(Lbar)\,\|M.y_0-x^*\|^2}{(k+2)^2}.
$$

This is the accelerated $O(1/k^2)$ convergence rate for the composite objective values. Second, for every real $\varepsilon>0$, define

$$
NG=\sqrt{\frac{4\,P.F(Lbar)\,\|M.y_0-x^*\|^2}{\varepsilon}},
$$

$$
D=\left\lceil \max\left(\log_2\!\left(\frac{P.F(Lbar)}{M.initialA}\right),0\right)\right\rceil,
$$

$$
NA=\lceil NG\rceil+D,\qquad NF=2\lceil NG\rceil+D.
$$

Then there exist natural numbers `iterations`, `auxiliarySolves`, `gradientCollections`, and `functionEvaluations` such that the three counts equal the corresponding count functions at `iterations`,

$$
\text{auxiliarySolves}=\text{compositeAuxiliarySolveCount}(P,T,M,\text{iterations}),
$$

$$
\text{gradientCollections}=\text{compositeGradientCollectionCount}(P,T,M,\text{iterations}),
$$

$$
\text{functionEvaluations}=\text{compositeFunctionEvaluationCount}(P,T,M,\text{iterations}),
$$

and they satisfy the bounds

$$
\text{auxiliarySolves}\le NA.\mathrm{toNat},\qquad
\text{gradientCollections}\le (\lceil NG\rceil).\mathrm{toNat},
$$

$$
\text{functionEvaluations}\le NF.\mathrm{toNat},
$$

and finally

$$
G(M.x_{\text{iterations}})-G(x^*)\le \varepsilon.
$$

The count functions are

$$
\text{compositeAuxiliarySolveCount}(n)
=
n+\sum_{j=0}^{n-1} M.searchIndex_j,
$$

$$
\text{compositeGradientCollectionCount}(n)=n,
$$

$$
\text{compositeFunctionEvaluationCount}(n)
=
2n+\sum_{j=0}^{n-1} M.searchIndex_j.
$$

Thus the theorem states both a convergence-rate estimate and a complexity estimate: to reach accuracy $\varepsilon$, the number of iterations is governed by $\lceil NG\rceil$, while the search-index sum is governed by the logarithmic doubling term $D$.

## Lean proof
```lean
Real.sqrt (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 / ε)
      let doublingAllowance := max (Real.logb 2 (P.F Lbar / M.initialA)) 0
      let NA := Int.ceil NG + Int.ceil doublingAllowance
      let NF := 2 * Int.ceil NG + Int.ceil doublingAllowance
      ∃ iterations auxiliarySolves gradientCollections functionEvaluations : ℕ,
        auxiliarySolves = compositeAuxiliarySolveCount P T M iterations ∧
        gradientCollections = compositeGradientCollectionCount P T M iterations ∧
        functionEvaluations = compositeFunctionEvaluationCount P T M iterations ∧
        auxiliarySolves ≤ NA.toNat ∧
        gradientCollections ≤ (Int.ceil NG).toNat ∧
        functionEvaluations ≤ NF.toNat ∧
        P.F (WithLp.toLp 2 (fun i => P.f i (M.x iterations))) -
            P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤ ε := by
  have hAle : M.initialA ≤ P.F Lbar := composite_initialA_le M hC11 hFmono
  have hgap_nonneg : ∀ k : ℕ,
      0 ≤ P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar)) := by
    intro k
    have hxQ : M.x k ∈ P.Q := by
      rw [M.update_x k]
      exact (hT.1 (M.y k) (M.A k)).1
    rcases (P.solution_iff xstar).mp hstar with ⟨_, hmin⟩
    linarith [hmin (M.x k) hxQ]
  have hrate : ∀ k : ℕ,
      P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) - P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤
        (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2) / (k + 2 : ℝ) ^ 2 := by
    intro k
    let gap := P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
      P.F (WithLp.toLp 2 (fun i => P.f i xstar))
    have hweight := composite_weight_lower P T M k
    have hbase : 0 ≤ 1 + (k : ℝ) / 2 := by positivity
    have hweight0 : 0 ≤ M.weight k := le_trans hbase hweight
    have hsq : (1 + (k : ℝ) / 2) ^ 2 ≤ M.weight k ^ 2 :=
      (sq_le_sq₀ hbase hweight0).2 hweight
    have hscaled : (1 + (k : ℝ) / 2) ^ 2 * gap ≤
        P.F Lbar * ‖M.y0 - xstar‖ ^ 2 := by
      calc
        (1 + (k : ℝ) / 2) ^ 2 * gap ≤ M.weight k ^ 2 * gap :=
          mul_le_mul_of_nonneg_right hsq (hgap_nonneg k)
        _ ≤ P.F Lbar * ‖M.y0 - xstar‖ ^ 2 :=
          composite_lyapunov M hT hLower xstar hstar hApos hAle k
    have hden : 0 < (k + 2 : ℝ) ^ 2 := by positivity
    apply (le_div_iff₀ hden).2
    norm_num [Nat.cast_add, Nat.cast_ofNat] at hscaled ⊢
    nlinarith
  constructor
  · exact hrate
  · intro ε hε
    dsimp
    let NG := Real.sqrt (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 / ε)
    let D := Int.ceil (max (Real.logb 2 (P.F Lbar / M.initialA)) 0)
    have hC0 : 0 ≤ 4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 := by
      have h0 := composite_lyapunov M hT hLower xstar hstar hApos hAle 0
      rw [M.weight_zero] at h0
      nlinarith [hgap_nonneg 0]
    have hNG0 : 0 ≤ NG := Real.sqrt_nonneg _
    have hN0 : 0 ≤ Int.ceil NG := Int.ceil_nonneg hNG0
    have hD0 : 0 ≤ D := by
      exact Int.ceil_nonneg (le_max_right _ _)
    let iterations := (Int.ceil NG).toNat
    have hNGle : NG ≤ (iterations : ℝ) := by
      rw [show (iterations : ℝ) = (Int.ceil NG : ℤ) by
        exact_mod_cast (Int.toNat_of_nonneg hN0)]
      exact (Int.le_ceil NG : NG ≤ (Int.ceil NG : ℝ))
    have hsqNG : NG ^ 2 = 4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 / ε := by
      dsimp [NG]
      exact Real.sq_sqrt (div_nonneg hC0 (le_of_lt hε))
    have haccuracy :
        P.F (WithLp.toLp 2 (fun i => P.f i (M.x iterations))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤ ε := by
      have hden : 0 < (iterations + 2 : ℝ) ^ 2 := by positivity
      calc
        P.F (WithLp.toLp 2 (fun i => P.f i (M.x iterations))) -
            P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤
            (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2) / (iterations + 2 : ℝ) ^ 2 := hrate iterations
        _ ≤ ε := by
          apply (div_le_iff₀ hden).2
          have hsquares : NG ^ 2 ≤ (iterations : ℝ) ^ 2 :=
            (sq_le_sq₀ hNG0 (by positivity)).2 hNGle
          rw [hsqNG] at hsquares
          have hCiterations : 4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 ≤
              ε * (iterations : ℝ) ^ 2 := by
            nlinarith [(div_le_iff₀ hε).mp hsquares]
          have hiter0 : 0 ≤ (iterations : ℝ) := by positivity
          have hinc : (iterations : ℝ) ^ 2 ≤ (iterations + 2 : ℝ) ^ 2 := by
            nlinarith
          exact hCiterations.trans (mul_le_mul_of_nonneg_left hinc (le_of_lt hε))
    refine ⟨iterations, compositeAuxiliarySolveCount P T M iterations,
      compositeGradientCollectionCount P T M iterations,
      compositeFunctionEvaluationCount P T M iterations, rfl, rfl, rfl, ?_, ?_, ?_, haccuracy⟩
    · change iterations + (Finset.range iterations).sum M.searchIndex ≤
        (Int.ceil NG + D).toNat
      rw [Int.toNat_add hN0 hD0]
      exact Nat.add_le_add_left
        (by simpa [D] using composite_searchIndex_sum_le M hLower hApos iterations) _
    · rfl
    · change 2 * iterations + (Finset.range iterations).sum M.searchIndex ≤
        (2 * Int.ceil NG + D).toNat
      have htwoN : 0 ≤ 2 * Int.ceil NG := by omega
      rw [Int.toNat_add htwoN hD0]
      rw [Int.toNat_mul (by omega) hN0]
      exact Nat.add_le_add_left
        (by simpa [D] using composite_searchIndex_sum_le M hLower hApos iterations) _
```

## Proof explanation
The proof first derives an upper bound for the initial value. Using `composite_initialA_le` with the hypotheses $hC11$ and $hFmono$, it obtains

$$
M.initialA\le P.F(Lbar).
$$

This says that the method’s initial estimate is at most the objective value at the vector $Lbar$. The lemma `composite_initialA_le` uses exactly the $C^{1,1}$-type component assumptions and the monotonicity of $P.F$ on nonnegative vectors. The resulting inequality is stored as `hAle` and is later needed both in the Lyapunov inequality and in the search-index bound.

Next the proof shows that the objective gap is always nonnegative. For each $k$, it wants

$$
0\le G(M.x_k)-G(x^*).
$$

To see this, the proof first shows that $M.x_k$ is feasible, i.e. $M.x_k\in P.Q$. It rewrites $M.x_k$ using the method’s update identity `M.update_x k`, identifying $M.x_k$ with the auxiliary image $T(M.y_k,M.A_k)$. The first component of the auxiliary estimate hypothesis `hT`, applied to $M.y_k$ and $M.A_k$, gives that this image lies in $P.Q$. Thus $M.x_k\in P.Q$.

Then the proof uses $hstar:x^*\in P.solutionSet$. The characterization `P.solution_iff` says, in particular, that a solution point is feasible and minimizes the objective over the feasible set. Applying this minimality statement to the feasible point $M.x_k$ gives

$$
G(x^*)\le G(M.x_k).
$$

The `linarith` tactic rearranges this to

$$
0\le G(M.x_k)-G(x^*).
$$

This nonnegativity is used to multiply inequalities by the gap without changing the direction.

The main rate estimate is then proved for each $k$. Let

$$
\mathrm{gap}=G(M.x_k)-G(x^*).
$$

The lemma `composite_weight_lower` gives

$$
1+\frac{k}{2}\le M.weight_k.
$$

Since $1+\frac{k}{2}\ge0$, also $M.weight_k\ge0$. Because squaring is monotone on nonnegative reals, this yields

$$
\left(1+\frac{k}{2}\right)^2\le M.weight_k^2.
$$

Multiplying by the nonnegative gap gives

$$
\left(1+\frac{k}{2}\right)^2 \mathrm{gap}
\le M.weight_k^2\,\mathrm{gap}.
$$

The central Lyapunov inequality `composite_lyapunov`, applied with the previously obtained `hAle`, $hT$, $hLower$, $hstar$, $hApos$, and $k$, states

$$
M.weight_k^2\,\mathrm{gap}
\le P.F(Lbar)\,\|M.y_0-x^*\|^2.
$$

Combining these two inequalities gives

$$
\left(1+\frac{k}{2}\right)^2 \mathrm{gap}
\le P.F(Lbar)\,\|M.y_0-x^*\|^2.
$$

Since

$$
1+\frac{k}{2}=\frac{k+2}{2},
$$

this is equivalent to

$$
(k+2)^2\,\mathrm{gap}
\le 4\,P.F(Lbar)\,\|M.y_0-x^*\|^2.
$$

The denominator $(k+2)^2$ is positive, so dividing by it yields

$$
\mathrm{gap}
\le
\frac{4\,P.F(Lbar)\,\|M.y_0-x^*\|^2}{(k+2)^2}.
$$

The proof uses `positivity` to establish positivity of $(k+2)^2$, then `le_div_iff₀` to replace the division goal by the equivalent multiplication inequality, and finally `norm_num` and `nlinarith` to solve the resulting polynomial arithmetic. This proves the first conjunct of the theorem.

For the second conjunct, fix $\varepsilon>0$. The proof defines

$$
NG=\sqrt{\frac{C}{\varepsilon}},
\qquad
C=4\,P.F(Lbar)\,\|M.y_0-x^*\|^2,
$$

and

$$
D=\left\lceil \max\left(\log_2\!\left(\frac{P.F(Lbar)}{M.initialA}\right),0\right)\right\rceil.
$$

First it proves $C\ge0$. It applies `composite_lyapunov` at $k=0$, obtaining

$$
M.weight_0^2\bigl(G(M.x_0)-G(x^*)\bigr)
\le P.F(Lbar)\,\|M.y_0-x^*\|^2.
$$

Using the zero-weight identity `M.weight_zero`, this simplifies the left-hand side, and since the gap at $0$ is nonnegative by the already proved nonnegativity result, the right-hand side must be nonnegative. Hence $C\ge0$. Consequently $NG\ge0$, and `Int.ceil_nonneg` gives $\lceil NG\rceil\ge0$. Also $D\ge0$, because $D$ is the ceiling of a maximum that is at least $0$.

Let

$$
\text{iterations}=(\lceil NG\rceil).\mathrm{toNat}.
$$

Since $\lceil NG\rceil\ge0$, this natural number has the same real value as $\lceil NG\rceil$. The integer ceiling lemma `Int.le_ceil` gives

$$
NG\le \lceil NG\rceil,
$$

so

$$
NG\le \text{iterations}
$$

as real numbers. Also, by `Real.sq_sqrt`, since the radicand $C/\varepsilon$ is nonnegative,

$$
NG^2=\frac{C}{\varepsilon}.
$$

The proof now proves the desired accuracy at `iterations`. From $NG\le\text{iterations}$ and nonnegativity of both quantities, it obtains

$$
NG^2\le \text{iterations}^2.
$$

Substituting $NG^2=C/\varepsilon$ gives

$$
\frac{C}{\varepsilon}\le \text{iterations}^2.
$$

Multiplying by $\varepsilon>0$ yields

$$
C\le \varepsilon\,\text{iterations}^2.
$$

Since $\text{iterations}^2\le(\text{iterations}+2)^2$, it follows that

$$
C\le \varepsilon\,(\text{iterations}+2)^2.
$$

Dividing by the positive number $(\text{iterations}+2)^2$ gives

$$
\frac{C}{(\text{iterations}+2)^2}\le \varepsilon.
$$

The already established rate estimate at $k=\text{iterations}$ says

$$
G(M.x_{\text{iterations}})-G(x^*)
\le
\frac{C}{(\text{iterations}+2)^2}.
$$

Combining the last two inequalities gives

$$
G(M.x_{\text{iterations}})-G(x^*)\le \varepsilon.
$$

This is the accuracy part of the existential statement.

Finally the proof supplies the existential witnesses. It chooses

$$
\text{auxiliarySolves}=\text{compositeAuxiliarySolveCount}(P,T,M,\text{iterations}),
$$

$$
\text{gradientCollections}=\text{compositeGradientCollectionCount}(P,T,M,\text{iterations}),
$$

$$
\text{functionEvaluations}=\text{compositeFunctionEvaluationCount}(P,T,M,\text{iterations}).
$$

The three equality conjuncts hold by `rfl`, because these are exactly the chosen terms.

For the auxiliary-solve bound, the definition gives

$$
\text{auxiliarySolves}
=
\text{iterations}
+
\sum_{j=0}^{\text{iterations}-1} M.searchIndex_j.
$$

The lemma `composite_searchIndex_sum_le`, applied with $N=\text{iterations}$, $hLower$, and $hApos$, states

$$
\sum_{j=0}^{\text{iterations}-1} M.searchIndex_j
\le
\left\lceil \max\left(\log_2\!\left(\frac{P.F(Lbar)}{M.initialA}\right),0\right)\right\rceil.\mathrm{toNat}.
$$

By definition of $D$, this is

$$
\sum_{j=0}^{\text{iterations}-1} M.searchIndex_j\le D.\mathrm{toNat}.
$$

Since $\lceil NG\rceil$ and $D$ are nonnegative integers, `Int.toNat_add` gives

$$
(\lceil NG\rceil+D).\mathrm{toNat}
=
(\lceil NG\rceil).\mathrm{toNat}+D.\mathrm{toNat}
=
\text{iterations}+D.\mathrm{toNat}.
$$

Adding `iterations` to both sides of the search-index inequality gives

$$
\text{iterations}
+
\sum_{j=0}^{\text{iterations}-1} M.searchIndex_j
\le
\text{iterations}+D.\mathrm{toNat}
=
NA.\mathrm{toNat}.
$$

This proves the auxiliary-solve bound.

For the gradient-collection bound, the definition gives

$$
\text{gradientCollections}=\text{iterations}=(\lceil NG\rceil).\mathrm{toNat}.
$$

Therefore the required inequality

$$
\text{gradientCollections}\le(\lceil NG\rceil).\mathrm{toNat}
$$

is exactly `rfl`.

For the function-evaluation bound, the definition gives

$$
\text{functionEvaluations}
=
2\,\text{iterations}
+
\sum_{j=0}^{\text{iterations}-1} M.searchIndex_j.
$$

The proof must show this is at most

$$
(2\lceil NG\rceil+D).\mathrm{toNat}.
$$

Since $2\lceil NG\rceil\ge0$ and $D\ge0$, `Int.toNat_add` splits the natural conversion:

$$
(2\lceil NG\rceil+D).\mathrm{toNat}
=
(2\lceil NG\rceil).\mathrm{toNat}+D.\mathrm{toNat}.
$$

Then `Int.toNat_mul` uses nonnegativity of $2$ and of $\lceil NG\rceil$ to get

$$
(2\lceil NG\rceil).\mathrm{toNat}
=
2\,(\lceil NG\rceil).\mathrm{toNat}
=
2\,\text{iterations}.
$$

Thus the target becomes

$$
2\,\text{iterations}
+
\sum_{j=0}^{\text{iterations}-1} M.searchIndex_j
\le
2\,\text{iterations}+D.\mathrm{toNat}.
$$

The same `composite_searchIndex_sum_le` bound as before gives the required inequality for the sum, and `Nat.add_le_add_left` adds $2\,\text{iterations}$ to both sides. This completes the function-evaluation bound.

All conjuncts of the existential statement have now been verified, so the proof finishes the second part of the theorem.

