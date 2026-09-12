## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/ext_thm_1.lean`

## Lean statement
```lean
theorem cauchy_lipschitz_continuation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (F : X → X) (Y₀ : X)
    (hF : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ U, ∀ z ∈ U, ‖F y - F z‖ ≤ L * ‖y - z‖) :
    ∃ Tmax : WithTop ℝ, ∃ Y : ℝ → X,
      IsMaximalClassicalSolution F Y₀ Tmax Y ∧
        (∀ Tmax' Y', IsMaximalClassicalSolution F Y₀ Tmax' Y' →
          Tmax' = Tmax ∧ ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax → Y' t = Y t) ∧
        (∀ T : ℝ, Tmax = (T : WithTop ℝ) →
          ∀ l : X, Tendsto Y
            (nhdsWithin T {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax}) (nhds l) →
              ∃ S : ℝ, T < S ∧ ∃ Z,
                IsClassicalSolutionOn F Y₀ {t : ℝ | 0 ≤ t ∧ t < S} Z ∧
                (∀ t, 0 ≤ t → t < T → Z t = Y t))
```

## Statement explanation
Let $X$ be a complete real normed vector space, let $F:X\to X$ be a vector field, and let $Y_0\in X$ be an initial value. The hypothesis `hF` says that $F$ is locally Lipschitz in the following pointwise-neighborhood sense: for every $x\in X$, there is a neighborhood $U$ of $x$ and a constant $L\ge 0$ such that

$$
\|F(y)-F(z)\|\le L\|y-z\|
$$

for all $y,z\in U$. No global Lipschitz constant is assumed.

The declaration asserts the existence of a maximal forward classical solution of the ordinary differential equation

$$
Y'(t)=F(Y(t)),\qquad Y(0)=Y_0,
$$

together with uniqueness and a continuation criterion at a finite maximal time.

Concretely, a set $I\subseteq \mathbb R$ and a curve $Y:\mathbb R\to X$ form a classical solution on $I$ when $0\in I$, $Y(0)=Y_0$, and for every $t\in I$, $Y$ has derivative $F(Y(t))$ at $t$. This is the content of `IsClassicalSolutionOn`.

The predicate `IsMaximalClassicalSolution F Y₀ Tmax Y` says that $0<T_{\max}$, that $Y$ is a classical solution on

$$
D_{T_{\max}}=\{t\in\mathbb R:0\le t,\ t<T_{\max}\},
$$

where $t<T_{\max}$ is understood in $\mathbb R\cup\{+\infty\}$, and that no forward extension is possible. More precisely, if $I$ is an order-connected subset of $\mathbb R$ containing $0$, if $Z$ is a classical solution on $I$, if $D_{T_{\max}}\subseteq I$, and if $Z$ agrees with $Y$ on $D_{T_{\max}}$, then

$$
I\cap[0,\infty)\subseteq D_{T_{\max}}.
$$

Thus the solution cannot be extended to any larger forward interval.

The theorem `cauchy_lipschitz_continuation` concludes that there exist $T_{\max}:\mathrm{WithTop}\,\mathbb R$ and $Y:\mathbb R\to X$ such that:

1. $Y$ is a maximal classical solution with maximal time $T_{\max}$.

2. Any other maximal classical solution $Y'$ with maximal time $T_{\max}'$ has $T_{\max}'=T_{\max}$, and agrees with $Y$ at every $t$ with $0\le t<T_{\max}$.

3. If $T_{\max}$ is finite, say $T_{\max}=T\in\mathbb R$, and if

$$
Y(t)\to l
$$

as $t\to T$ from the left within the forward solution domain $\{t:0\le t<T_{\max}\}$, then there exists $S>T$ and a classical solution $Z$ on $\{t:0\le t<S\}$ which agrees with $Y$ on $\{t:0\le t<T\}$.

So a finite maximal time cannot occur together with a finite left limit of the solution. If such a limit exists, the solution extends past that time.

## Lean proof
```lean
by
  classical
  obtain ⟨p, hpmax⟩ := zorn_le (pointedSolution_chain_upper_bound F hF Y₀)
  obtain ⟨Tmax, hTmax_pos, hforward⟩ :=
    forward_endpoint_of_open_preconnected p.open_dom p.preconnected_dom p.zero_mem
  let D : Set ℝ := {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax}
  have hD : D = p.dom ∩ Set.Ici 0 := hforward.symm
  have hpclassical : IsClassicalSolutionOn F Y₀ D p.curve := by
    refine ⟨?_, p.initial, ?_⟩
    · rw [hD]
      exact ⟨p.zero_mem, by simp⟩
    · intro t ht
      have htp : t ∈ p.dom := (hD ▸ ht).1
      exact p.ode t htp
  have hmaxp : IsMaximalClassicalSolution F Y₀ Tmax p.curve := by
    refine ⟨hTmax_pos, hpclassical, ?_⟩
    induction Tmax using WithTop.recTopCoe with
    | top =>
        intro I Z hIconn hI0 hZ hsub heq t ht
        exact ⟨ht.2, by simp⟩
    | coe T =>
        intro I Z hIconn hI0 hZ hsub heq
        have hTpos : 0 < T := by simpa using hTmax_pos
        have hforward' : p.dom ∩ Set.Ici 0 = {t : ℝ | 0 ≤ t ∧ t < T} := by
          simpa using hforward
        have hsub' : {t : ℝ | 0 ≤ t ∧ t < T} ⊆ I := by
          simpa using hsub
        have heq' : ∀ t : ℝ, 0 ≤ t → t < T → p.curve t = Z t := by
          intro t ht0 ht
          exact heq t ht0 (by simpa using ht)
        simpa using pointedSolution_forward_maximal_of_ordConnected F hF Y₀ p hpmax
          hTpos hforward' I Z hIconn hI0 hZ hsub' heq'
  -- The remaining two fields use the same bridge together with forward
  -- uniqueness and the endpoint-gluing construction.
  refine ⟨Tmax, p.curve, hmaxp, ?_⟩
  refine ⟨?_, ?_⟩
  · intro Tmax' Y' hmax'
    let D' : Set ℝ := {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < Tmax'}
    have hcommon : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax →
        (t : WithTop ℝ) < Tmax' → p.curve t = Y' t :=
      classicalSolution_eq_of_below_both F hF Y₀ hpclassical hmax'.2.1
    have hDconn : Set.OrdConnected D := by
      rw [hD]
      exact p.preconnected_dom.ordConnected.inter Set.ordConnected_Ici
    have hD'conn : Set.OrdConnected D' := by
      induction Tmax' using WithTop.recTopCoe with
      | top =>
          rw [show D' = Set.Ici 0 by ext t; simp [D']]
          exact Set.ordConnected_Ici
      | coe T' =>
          rw [show D' = Set.Ico 0 T' by ext t; simp [D']]
          exact Set.ordConnected_Ico
    have hle : Tmax ≤ Tmax' := by
      by_contra hnot
      have hlt : Tmax' < Tmax := lt_of_not_ge hnot
      have hD'sub : D' ⊆ D := by
        intro t ht
        exact ⟨ht.1, lt_trans ht.2 hlt⟩
      have hsub := hmax'.2.2 D p.curve hDconn hpclassical.1 hpclassical hD'sub
        (fun t ht0 ht' => (hcommon t ht0 (hD'sub ⟨ht0, ht'⟩).2 ht').symm)
      have hDom : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax →
          (t : WithTop ℝ) < Tmax' := by
        intro t ht0 ht
        have := hsub ⟨⟨ht0, ht⟩, ht0⟩
        exact this.2
      exact (not_le_of_gt hlt) (withTop_le_of_forward_subset hmaxp.1 hDom)
    have hDsub : D ⊆ D' := by
      intro t ht
      change 0 ≤ t ∧ (t : WithTop ℝ) < Tmax at ht
      change 0 ≤ t ∧ (t : WithTop ℝ) < Tmax'
      exact ⟨ht.1, lt_of_lt_of_le ht.2 hle⟩
    have hge : Tmax' ≤ Tmax := by
      by_contra hnot
      have hlt : Tmax < Tmax' := lt_of_not_ge hnot
      have hsub := hmaxp.2.2 D' Y' hD'conn hmax'.2.1.1 hmax'.2.1 hDsub
        (fun t ht0 ht => hcommon t ht0 ht (lt_trans ht hlt))
      have hDom : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < Tmax' →
          (t : WithTop ℝ) < Tmax := by
        intro t ht0 ht
        have := hsub ⟨⟨ht0, ht⟩, ht0⟩
        exact this.2
      exact (not_le_of_gt hlt) (withTop_le_of_forward_subset hmax'.1 hDom)
    have heq : Tmax' = Tmax := le_antisymm hge hle
    refine ⟨heq, ?_⟩
    intro t ht0 ht
    exact (hcommon t ht0 ht (by simpa [heq] using ht)).symm
  · intro T hTmax l hlim
    have hTpos : 0 < T := by simpa [hTmax] using hTmax_pos
    have hsmall : Set.Ioo (T / 2) T ⊆ D := by
      intro r hr
      change 0 ≤ r ∧ (r : WithTop ℝ) < Tmax
      constructor
      · linarith [hTpos, hr.1]
      · simpa [hTmax] using hr.2
    have hlimsmall := tendsto_nhdsWithin_mono_left hsmall hlim
    have hplim : Tendsto p.curve (nhdsWithin T (Set.Iio T)) (nhds l) := by
      rw [nhdsWithin_Ioo_eq_nhdsLT (by linarith [hTpos])] at hlimsmall
      exact hlimsmall
    obtain ⟨ε, hε, α, hαT, hα⟩ :=
      local_classical_solution_of_locally_lipschitz F hF T l
    let ε₀ : ℝ := min ε (T / 2)
    have hε₀ : 0 < ε₀ := by dsimp [ε₀]; exact lt_min hε (by linarith)
    have hε₀ε : ε₀ ≤ ε := min_le_left _ _
    have hε₀T : ε₀ ≤ T / 2 := min_le_right _ _
    have hα₀ : ∀ r ∈ Set.Ioo (T - ε₀) (T + ε₀),
        HasDerivAt α (F (α r)) r := by
      intro r hr
      apply hα r
      exact ⟨lt_of_le_of_lt (sub_le_sub_left hε₀ε T) hr.1,
        by linarith [hε₀ε, hr.2]⟩
    have hpode : ∀ r ∈ Set.Ioo (T - ε₀) T,
        HasDerivAt p.curve (F (p.curve r)) r := by
      intro r hr
      apply p.ode r
      have : r ∈ D := by
        change 0 ≤ r ∧ (r : WithTop ℝ) < Tmax
        constructor
        · linarith [hε₀T, hr.1]
        · simpa [hTmax] using hr.2
      rw [hD] at this
      exact this.1
    obtain ⟨ρ, hρ, hρε₀, hleft⟩ :=
      ode_eqOn_left_of_tendsto F hF hε₀ hpode hα₀ hplim hαT
    have hEq : Set.EqOn p.curve α (p.dom ∩ Set.Ioo (T - ρ) (T + ε₀)) := by
      rintro r ⟨hrdom, hr⟩
      have hrT : r < T := by
        by_contra hn
        have hTr : T ≤ r := le_of_not_gt hn
        have hr0 : 0 ≤ r := by linarith
        have hmem : r ∈ D := by rw [hD]; exact ⟨hrdom, hr0⟩
        have : r < T := by simpa [hTmax] using hmem.2
        linarith
      exact hleft ⟨hr.1, hrT⟩
    have hcdom : T - ρ / 2 ∈ p.dom := by
      have hmem : T - ρ / 2 ∈ D := by
        constructor
        · linarith [hε₀T, hρε₀]
        · rw [hTmax]
          exact_mod_cast (show T - ρ / 2 < T by linarith [hρ])
      exact (hD ▸ hmem).1
    have hcIoo : T - ρ / 2 ∈ Set.Ioo (T - ρ) (T + ε₀) := by constructor <;> linarith
    obtain ⟨q, hpq, hαq, _⟩ := pointedSolution_extend_of_eqOn F Y₀ p
      (a := T - ρ) (b := T + ε₀) (by linarith) α
      (fun r hr => hα₀ r ⟨by linarith [hρε₀, hr.1], hr.2⟩) hEq ⟨T - ρ / 2, hcdom, hcIoo⟩
    let S : ℝ := T + ρ / 2
    refine ⟨S, by dsimp [S]; linarith, q.curve, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · constructor
        · exact le_rfl
        · dsimp [S]; linarith
      · exact (hpq.2 p.zero_mem).symm.trans p.initial
      · intro t ht
        rcases lt_or_ge t T with htT | htT
        · apply q.ode t (hpq.1 ?_)
          have hmem : t ∈ D := ⟨ht.1, by simpa [hTmax] using htT⟩
          exact (hD ▸ hmem).1
        · apply q.ode t (hαq ?_)
          constructor <;> dsimp [S] at ht ⊢ <;> linarith [hρ, hρε₀]
    · intro t ht0 htT
      exact (hpq.2 ((hD ▸ (show t ∈ D from ⟨ht0, by simpa [hTmax] using htT⟩)).1)).symm
```

## Proof explanation
The proof begins with `classical`, which only permits classical logic and has no mathematical content. It then uses Zorn’s lemma. The auxiliary order is the extension order on pointed solutions of the ODE. The cited lemma `pointedSolution_chain_upper_bound F hF Y₀` states that every chain in this order is bounded above. Applying `zorn_le` therefore produces a maximal pointed solution $p$, with maximality meaning that if $p\le q$, then $q\le p$. In mathematical terms, $p$ is a local solution that cannot be extended any further within the pointed-solution order.

Next, `forward_endpoint_of_open_preconnected` is applied to the domain of $p$. The lemma says that if $D$ is open, preconnected, and contains $0$, then there is $T_{\max}:\mathrm{WithTop}\,\mathbb R$ such that $0<T_{\max}$ and

$$
D\cap[0,\infty)=\{t\in\mathbb R:0\le t,\ t<T_{\max}\}.
$$

This is the standard fact that an open preconnected subset of $\mathbb R$ has interval-like forward part. Applying it to $p.\mathrm{dom}$, the proof obtains $T_{\max}$ and the equality

$$
p.\mathrm{dom}\cap[0,\infty)=\{t:0\le t,\ t<T_{\max}\}.
$$

The proof then sets

$$
D=\{t\in\mathbb R:0\le t,\ t<T_{\max}\}.
$$

The curve $p.\mathrm{curve}$ is shown to be a classical solution on $D$. The initial condition $0\in D$ follows from $0\in p.\mathrm{dom}$ and $0\ge 0$. The condition $p.\mathrm{curve}(0)=Y_0$ is exactly $p.\mathrm{initial}$. For $t\in D$, the equality $D=p.\mathrm{dom}\cap[0,\infty)$ gives $t\in p.\mathrm{dom}$, and $p.\mathrm{ode}\,t$ gives the required derivative

$$
p.\mathrm{curve}'(t)=F(p.\mathrm{curve}(t)).
$$

Thus `hpclassical` is established.

The proof then establishes `hmaxp`, namely that $T_{\max},p.\mathrm{curve}$ is a maximal classical solution. The maximality condition is proved by splitting on whether $T_{\max}=\top$ or $T_{\max}$ is a finite real number $T$.

If $T_{\max}=\top$, then $D=\{t:0\le t\}$ is all of $[0,\infty)$. Therefore $I\cap[0,\infty)\subseteq D$ is immediate, and the proof finishes this case by showing membership in $D$ from $0\le t$.

If $T_{\max}=T$ is finite, the proof converts the forward domain to

$$
p.\mathrm{dom}\cap[0,\infty)=\{t:0\le t<T\}
$$

and applies `pointedSolution_forward_maximal_of_ordConnected`. That lemma says: if $F$ is locally Lipschitz, $p$ is a maximal pointed solution, $T>0$, the forward domain of $p$ is $\{t:0\le t<T\}$, $I$ is order-connected and contains $0$, $Z$ is a classical solution on $I$, $\{t:0\le t<T\}\subseteq I$, and $p.\mathrm{curve}=Z$ on $\{t:0\le t<T\}$, then

$$
I\cap[0,\infty)\subseteq\{t:0\le t<T\}.
$$

This is exactly the maximality condition needed for `IsMaximalClassicalSolution`. The `simpa` at the end just rewrites the finite $T_{\max}$ and the coercions between $\mathbb R$ and $\mathrm{WithTop}\,\mathbb R$.

The uniqueness part then begins. Let $T_{\max}',Y'$ be another maximal classical solution. Define

$$
D'=\{t:0\le t,\ t<T_{\max}'\}.
$$

The cited lemma `classicalSolution_eq_of_below_both` is the forward uniqueness theorem for locally Lipschitz ODEs. It says that if $Y_1$ is a classical solution on $\{0\le t<T_1\}$ and $Y_2$ is a classical solution on $\{0\le t<T_2\}$, both with initial value $Y_0$, then for every $t$ with $0\le t<T_1$ and $0\le t<T_2$,

$$
Y_1(t)=Y_2(t).
$$

Applied to $p.\mathrm{curve}$ and $Y'$, it yields equality on the common forward interval:

$$
0\le t,\ t<T_{\max},\ t<T_{\max}'
\quad\Longrightarrow\quad
p.\mathrm{curve}(t)=Y'(t).
$$

The proof then compares the endpoints $T_{\max}$ and $T_{\max}'$. It notes that $D$ is order-connected because $p.\mathrm{dom}$ is preconnected and intersecting with $[0,\infty)$ preserves that property. Similarly $D'$ is order-connected: if $T_{\max}'=\top$, it is $[0,\infty)$; if $T_{\max}'=T'$ is finite, it is $\{t:0\le t<T'\}$, which is an order-connected interval.

To prove $T_{\max}\le T_{\max}'$, the proof argues by contradiction. If $T_{\max}'<T_{\max}$, then $D'\subseteq D$. It applies the maximality property of the already assumed maximal solution $Y'$ with $I=D$ and $Z=p.\mathrm{curve}$. The conditions are satisfied: $D$ is order-connected, contains $0$, $p.\mathrm{curve}$ is a classical solution on $D$, $D'\subseteq D$, and the two curves agree on $D'$ by the common-interval uniqueness just obtained. The maximality of $Y'$ therefore gives

$$
D\cap[0,\infty)=D\subseteq D',
$$

so every $t\in D$ satisfies $t<T_{\max}'$. The lemma `withTop_le_of_forward_subset` converts this pointwise statement into $T_{\max}\le T_{\max}'$. It says that if $0<A$ and every finite $t\ge 0$ with $t<A$ also satisfies $t<B$, then $A\le B$. This contradicts $T_{\max}'<T_{\max}$, so $T_{\max}\le T_{\max}'$.

The reverse inequality is proved similarly: if $T_{\max}<T_{\max}'$, then $D\subseteq D'$, and one applies the maximality property of $p$ with $I=D'$ and $Z=Y'$. The same `withTop_le_of_forward_subset` argument gives $T_{\max}'\le T_{\max}$. Hence

$$
T_{\max}'=T_{\max}.
$$

Finally the common-interval equality gives $Y'(t)=p.\mathrm{curve}(t)=Y(t)$ for every $0\le t<T_{\max}$.

The continuation part begins with the assumption that $T_{\max}=T$ is finite. The proof first derives $T>0$. It then restricts the given limit to the smaller left interval $(T/2,T)$. Since this interval is contained in $D$, the limit remains valid. Rewriting the neighborhood filter on $(T/2,T)$ at $T$ as the left-neighborhood filter at $T$ gives

$$
p.\mathrm{curve}(t)\to l
$$

as $t\to T$ from the left.

Next the proof invokes `local_classical_solution_of_locally_lipschitz`, the local Picard–Lindelöf existence theorem: for locally Lipschitz $F$, for every $t_0$ and $x$, there exist $\varepsilon>0$ and a curve $\alpha$ such that $\alpha(t_0)=x$ and

$$
\alpha'(t)=F(\alpha(t))
$$

for all $t\in(t_0-\varepsilon,t_0+\varepsilon)$. Applying this with $t_0=T$ and $x=l$, the proof obtains $\varepsilon>0$, a curve $\alpha$, the value $\alpha(T)=l$, and the ODE on $(T-\varepsilon,T+\varepsilon)$.

It then sets

$$
\varepsilon_0=\min(\varepsilon,T/2).
$$

Thus $\varepsilon_0>0$, $\varepsilon_0\le\varepsilon$, and $\varepsilon_0\le T/2$. The curve $\alpha$ solves the ODE on $(T-\varepsilon_0,T+\varepsilon_0)$, and $p.\mathrm{curve}$ solves the ODE on $(T-\varepsilon_0,T)$.

Now `ode_eqOn_left_of_tendsto` is applied. This lemma states that if two curves $u,v$ solve the ODE on overlapping left intervals around $T$, if $u$ tends to $l$ as $t\to T$ from the left, and if $v(T)=l$, then $u=v$ on some interval $(T-\rho,T)$ with $0<\rho<\varepsilon$. Applied with $u=p.\mathrm{curve}$ and $v=\alpha$, it gives $\rho>0$, $\rho<\varepsilon_0$, and

$$
p.\mathrm{curve}=\alpha
$$

on $(T-\rho,T)$.

The proof then upgrades this equality to $p.\mathrm{dom}\cap(T-\rho,T+\varepsilon_0)$. For a point $r$ in this intersection, it shows $r<T$ by contradiction: if $T\le r$, then $r\in D$, so $r<T_{\max}=T$, impossible. Hence the earlier left-hand equality applies and gives $p.\mathrm{curve}(r)=\alpha(r)$.

To glue the local solution $\alpha$ onto $p$, the proof chooses

$$
c=T-\frac{\rho}{2}.
$$

It checks that $c\in p.\mathrm{dom}$ and that

$$
c\in(T-\rho,T+\varepsilon_0).
$$

Then it applies `pointedSolution_extend_of_eqOn`. This lemma says that if $p$ is a pointed solution, $a<b$, $\alpha$ solves the ODE on $(a,b)$, $\alpha$ agrees with $p.\mathrm{curve}$ on $p.\mathrm{dom}\cap(a,b)$, and there is some point $c\in p.\mathrm{dom}\cap(a,b)$, then there exists a pointed solution $q$ extending $p$, with $(a,b)\subseteq q.\mathrm{dom}$, and with $q.\mathrm{curve}=\alpha$ on $(a,b)$. Here $a=T-\rho$ and $b=T+\varepsilon_0$, so the lemma produces a solution $q$ extending $p$ beyond $T$.

Finally the proof sets

$$
S=T+\frac{\rho}{2}.
$$

Since $\rho>0$, $S>T$. It claims that $q.\mathrm{curve}$ is a classical solution on $\{t:0\le t<S\}$. Indeed, $0\in\{t:0\le t<S\}$ because $S>0$. The initial condition follows from $q$ extending $p$ and from $p.\mathrm{curve}(0)=Y_0$. For the derivative, it splits $t<S$ into two cases. If $t<T$, then $t\in p.\mathrm{dom}$, and since $q$ extends $p$, $t\in q.\mathrm{dom}$, so $q.\mathrm{ode}$ gives the derivative. If $T\le t<S$, then $t\in(T-\rho,T+\varepsilon_0)$, because $S=T+\rho/2<T+\varepsilon_0$ since $\rho<\varepsilon_0$. Hence $t\in q.\mathrm{dom}$, and $q.\mathrm{ode}$ again gives the derivative.

Finally, for $0\le t<T$, the extension $q$ of $p$ gives

$$
q.\mathrm{curve}(t)=p.\mathrm{curve}(t)=Y(t).
$$

Thus the maximal solution is extended past the finite endpoint $T$, completing the continuation criterion. The tactic `linarith` handles the many linear inequalities among $T,\rho,\varepsilon_0,S$, and `simpa` performs the necessary simplification of coercions into $\mathrm{WithTop}\,\mathbb R$ and of interval membership.

