## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/ext_lem_1.lean`

## Lean statement
```lean
theorem opial_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {S : Set H} (hS_nonempty : S.Nonempty) (z : ℕ → H)
    (h_cluster : ∀ (w : H) (φ : ℕ → ℕ), StrictMono φ →
      (Tendsto (fun k : ℕ => toWeakSpace ℝ H (z (φ k))) atTop (𝓝 (toWeakSpace ℝ H w))) → w ∈ S)
    (h_dist : ∀ ζ ∈ S, ∃ l : ℝ, Tendsto (fun n : ℕ => ‖z n - ζ‖) atTop (𝓝 l)) :
    ∃ zstar ∈ S, Tendsto (fun n : ℕ => toWeakSpace ℝ H (z n)) atTop (𝓝 (toWeakSpace ℝ H zstar))
```

## Statement explanation
The declaration `opial_lemma` is a theorem about a sequence in a real Hilbert space. Let $H$ be a normed additive commutative group equipped with a real inner product and complete in the induced norm, so $H$ is a real Hilbert space. Let $S\subseteq H$ be a nonempty set, and let $z:\mathbb N\to H$ be a sequence, with $z_n=z(n)$. Write $\iota_H$ for the canonical map `toWeakSpace ℝ H`, so $\iota_H(x)$ is the element corresponding to $x\in H$ in the weak topology. Convergence of $\iota_H(z_n)$ to $\iota_H(z_\star)$ means exactly that $z_n$ converges weakly to $z_\star$.

The first hypothesis, `h_cluster`, says that for every $w\in H$ and every strictly increasing sequence $\varphi:\mathbb N\to\mathbb N$, if the subsequence $z_{\varphi(k)}$ converges weakly to $w$, then $w\in S$. In symbols,

$$
\forall w\in H,\ \forall \varphi:\mathbb N\to\mathbb N,\ 
\operatorname{StrictMono}(\varphi)\implies
\bigl(\iota_H(z_{\varphi(k)})\to \iota_H(w)\ \text{as }k\to\infty\bigr)
\implies w\in S .
$$

Thus every weak limit of every strictly increasing subsequence of $z$ lies in $S$.

The second hypothesis, `h_dist`, says that for every point $\zeta\in S$, the real sequence of distances from $z_n$ to $\zeta$ converges. That is,

$$
\forall \zeta\in S,\ \exists l\in\mathbb R,\quad
\|z_n-\zeta\|\to l\ \text{as }n\to\infty .
$$

The conclusion is that there exists a point $z_\star\in S$ such that the whole sequence $z_n$ converges weakly to $z_\star$:

$$
\exists z_\star\in S,\quad
\iota_H(z_n)\to \iota_H(z_\star)\ \text{as }n\to\infty .
$$

In ordinary language, this is an Opial-type lemma: if every weak subsequential limit of $z_n$ is forced to lie in $S$, and if the distances from $z_n$ to every point of $S$ converge, then $z_n$ has a unique weak subsequential limit, and in fact the full sequence converges weakly to that limit, which belongs to $S$.

## Lean proof
```lean
by
  rcases hS_nonempty with ⟨ζ₀, hζ₀⟩
  -- Step 1: z is bounded
  have hz_bounded : Bornology.IsBounded (Set.range z) :=
    bounded_range_of_convergent_distance (h_dist ζ₀ hζ₀)
  -- Step 2: Every strictly monotone subsequence has a weakly convergent sub-subsequence
  have h_weak_subseq : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ (w : H) (ψ : ℕ → ℕ), StrictMono ψ ∧
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ (ψ n)))) atTop
          (𝓝 (toWeakSpace ℝ H w)) := by
    intro φ hφ
    have hzφ_bounded : Bornology.IsBounded (Set.range (z ∘ φ)) := by
      apply Bornology.IsBounded.subset hz_bounded
      rintro y ⟨n, rfl⟩
      exact Set.mem_range_self (φ n)
    rcases exists_weakly_convergent_subseq_of_bounded hzφ_bounded with ⟨w, ψ, hψ, h_tendsto⟩
    refine ⟨w, ψ, hψ, ?_⟩
    simpa [Function.comp] using h_tendsto
  -- Step 3: All weak subsequential limits are unique (Opial's polarization argument)
  have h_unique_limit : ∀ (w₁ w₂ : H) (φ₁ φ₂ : ℕ → ℕ),
      StrictMono φ₁ → StrictMono φ₂ →
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ₁ n))) atTop (𝓝 (toWeakSpace ℝ H w₁)) →
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ₂ n))) atTop (𝓝 (toWeakSpace ℝ H w₂)) →
      w₁ = w₂ := by
    intro w₁ w₂ φ₁ φ₂ hφ₁ hφ₂ h_tendsto₁ h_tendsto₂
    have hw₁S : w₁ ∈ S := h_cluster w₁ φ₁ hφ₁ h_tendsto₁
    have hw₂S : w₂ ∈ S := h_cluster w₂ φ₂ hφ₂ h_tendsto₂
    exact weak_subseq_limits_equal h_dist hw₁S hw₂S φ₁ hφ₁ h_tendsto₁ φ₂ hφ₂ h_tendsto₂
  -- Step 4: Get one weak cluster point
  rcases exists_weakly_convergent_subseq_of_bounded hz_bounded with ⟨a, φ₀, hφ₀, h_tendsto₀⟩
  have haS : a ∈ S := h_cluster a φ₀ hφ₀ h_tendsto₀
  -- Step 5: Every strictly monotone subsequence has a sub-subsequence converging to a
  have h_all_to_a : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ (ψ n)))) atTop
          (𝓝 (toWeakSpace ℝ H a)) := by
    intro φ hφ
    rcases h_weak_subseq φ hφ with ⟨w, ψ, hψ, h_tendsto⟩
    have hw_eq_a : w = a := h_unique_limit w a (φ ∘ ψ) φ₀
      (hφ.comp hψ) hφ₀ h_tendsto h_tendsto₀
    subst hw_eq_a
    exact ⟨ψ, hψ, h_tendsto⟩
  -- Step 6: Use `tendsto_of_subseq_tendsto` to conclude full sequence converges
  refine ⟨a, haS, ?_⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns_tendsto
  -- hns_tendsto : Tendsto ns atTop atTop
  -- Extract strictly monotone subsequence from ns
  rcases exists_strictMono_subseq_of_tendsto_atTop hns_tendsto with ⟨ms, hms_mono, hns_ms_mono⟩
  -- hns_ms_mono : StrictMono (ns ∘ ms)
  -- Now apply h_all_to_a to the strictly monotone subsequence ns ∘ ms
  rcases h_all_to_a (ns ∘ ms) hns_ms_mono with ⟨ψ, hψ, h_tendstoψ⟩
  -- h_tendstoψ : Tendsto (fun n => toWeakSpace ℝ H (z ((ns ∘ ms) (ψ n)))) atTop (𝓝 (toWeakSpace ℝ H a))
  -- This is: Tendsto (fun n => toWeakSpace ℝ H (z (ns (ms (ψ n))))) atTop (𝓝 (toWeakSpace ℝ H a))
  -- tendsto_of_subseq_tendsto expects: ∃ ms', Tendsto (fun n => x (ns (ms' n))) atTop f
  -- where x = fun n => toWeakSpace ℝ H (z n)
  -- So we need to produce ms' : ℕ → ℕ such that
  -- Tendsto (fun n => toWeakSpace ℝ H (z (ns (ms' n)))) atTop (𝓝 (toWeakSpace ℝ H a))
  -- Take ms' := ms ∘ ψ, then:
  -- z (ns ((ms ∘ ψ) n)) = z ((ns ∘ ms) (ψ n))
  -- This converges to a by h_tendstoψ
  refine ⟨ms ∘ ψ, ?_⟩
  -- `z (ns ((ms ∘ ψ) n)) = z ((ns ∘ ms) (ψ n))` by associativity
  have h_eq : (fun n : ℕ => toWeakSpace ℝ H (z (ns ((ms ∘ ψ) n)))) =
      (fun n : ℕ => toWeakSpace ℝ H (z ((ns ∘ ms) (ψ n)))) := by
    ext n
    simp [Function.comp]
  simpa [h_eq] using h_tendstoψ
```

## Proof explanation
1. The proof begins by choosing a point of $S$. The command `rcases hS_nonempty with ⟨ζ₀, hζ₀⟩` destroys the hypothesis that $S$ is nonempty and produces a point $\zeta_0\in H$ together with the proof $h\zeta_0:\zeta_0\in S$. Applying `h_dist` to this point gives a real number $l$ such that $\|z_n-\zeta_0\|\to l$. The cited theorem `bounded_range_of_convergent_distance` is then used: it says that for a sequence $z$ in a normed additive commutative group, if there exists a point $\zeta$ such that the real sequence $\|z_n-\zeta\|$ converges, then the range $\{z_n:n\in\mathbb N\}$ is bounded. Specialized here, the convergence of $\|z_n-\zeta_0\|$ implies that the whole range of $z$ is bounded. This is the intermediate fact `hz_bounded`.

2. The proof next establishes `h_weak_subseq`: every strictly increasing subsequence of $z$ has a further strictly increasing sub-subsequence that converges weakly. Given an arbitrary strictly increasing $\varphi:\mathbb N\to\mathbb N$, the proof first observes that the range of the composed sequence $z\circ\varphi$ is bounded. This uses `Bornology.IsBounded.subset`: if a set is bounded, every subset of it is bounded. Since every value $(z\circ\varphi)(n)=z(\varphi(n))$ lies in the range of $z$, the boundedness of the range of $z$ implies boundedness of the range of $z\circ\varphi$. The cited theorem `exists_weakly_convergent_subseq_of_bounded` is then applied. Its mathematical content is that in a complete real inner product space, every bounded sequence has a weakly convergent subsequence. Specialized to $z\circ\varphi$, it produces a point $w\in H$ and a strictly increasing sequence $\psi:\mathbb N\to\mathbb N$ such that

$$
\iota_H\bigl((z\circ\varphi)(\psi(n))\bigr)\to \iota_H(w).
$$

Unfolding composition gives

$$
\iota_H(z_{\varphi(\psi(n))})\to \iota_H(w).
$$

The Lean tactic `simpa [Function.comp]` is used precisely to rewrite the composed function into this form.

3. The proof then proves `h_unique_limit`: all weak subsequential limits are equal. Suppose $w_1,w_2\in H$ and strictly increasing $\varphi_1,\varphi_2:\mathbb N\to\mathbb N$ are such that $z_{\varphi_1(n)}$ converges weakly to $w_1$ and $z_{\varphi_2(n)}$ converges weakly to $w_2$. By the hypothesis `h_cluster`, both $w_1$ and $w_2$ belong to $S$. The cited lemma `weak_subseq_limits_equal` then applies. Its statement says that if for every $\zeta\in S$ the distances $\|z_n-\zeta\|$ converge, and if two points $a,b\in S$ are weak limits of the same sequence $z$ along two strictly increasing subsequences, then $a=b$. Specialized to $a=w_1$ and $b=w_2$, it gives $w_1=w_2$. Thus any two weak subsequential limits of $z$ must coincide. This is the Opial polarization/uniqueness step: the distance-convergence hypothesis rules out two distinct weak subsequential limits.

4. The proof now extracts one weak cluster point of the full sequence. It applies `exists_weakly_convergent_subseq_of_bounded` to the already established boundedness of the range of $z$. This produces a point $a\in H$, a strictly increasing sequence $\varphi_0:\mathbb N\to\mathbb N$, and the weak convergence

$$
\iota_H(z_{\varphi_0(n)})\to \iota_H(a).
$$

Applying `h_cluster` to $a$, $\varphi_0$, and this convergence gives $haS:a\in S$. So $a$ is a weak subsequential limit of $z$ and is known to lie in $S$.

5. The proof next shows `h_all_to_a`: for every strictly increasing $\varphi:\mathbb N\to\mathbb N$, there exists a further strictly increasing subsequence converging weakly to this same point $a$. Given $\varphi$, the earlier result `h_weak_subseq` gives some $w$ and a strictly increasing $\psi$ such that $z_{\varphi(\psi(n))}$ converges weakly to $w$. Since $\varphi\circ\psi$ and $\varphi_0$ are both strictly increasing, and since the two corresponding subsequences converge weakly to $w$ and $a$, respectively, the uniqueness result `h_unique_limit` gives $w=a$. The tactic `subst hw_eq_a` replaces $w$ by $a$, and then the same $\psi$ witnesses that the subsequence $z_{\varphi(\psi(n))}$ converges weakly to $a$. Thus every strictly increasing subsequence of $z$ has a further strictly increasing subsequence whose weak limit is $a$.

6. It remains to upgrade this subsequential information to convergence of the full sequence. The proof sets the final goal with `refine ⟨a, haS, ?_⟩`, so it remains to prove

$$
\iota_H(z_n)\to \iota_H(a).
$$

It then applies the standard criterion `tendsto_of_subseq_tendsto`. The exact full statement of this Mathlib lemma is not included in the provided context, but the consequence used here is: to prove $x_n\to a$, it suffices to show that for every index sequence $ns:\mathbb N\to\mathbb N$ tending to infinity, there is a further index sequence $ms'$ such that $x_{ns(ms'(n))}\to a$. The tactic `apply tendsto_of_subseq_tendsto` reduces the goal to exactly this subsequence criterion.

The proof then introduces an arbitrary $ns$ with $hns_tendsto:\operatorname{Tendsto}(ns,\operatorname{atTop},\operatorname{atTop})$, meaning $ns(n)\to\infty$. The cited lemma `exists_strictMono_subseq_of_tendsto_atTop` is applied to $ns$. Its mathematical content is that from any sequence $ns$ tending to infinity one can choose a strictly increasing sequence $ms:\mathbb N\to\mathbb N$ such that the composed sequence $ns\circ ms$ is also strictly increasing. The proof obtains such an $ms$.

Because $ns\circ ms$ is strictly increasing, the earlier result `h_all_to_a` applies to it, producing a strictly increasing $\psi$ such that

$$
\iota_H\bigl(z_{(ns\circ ms)(\psi(n))}\bigr)\to \iota_H(a).
$$

The proof then chooses $ms'=ms\circ\psi$ as the required further subsequence of the subsequence indexed by $ns$. The only remaining point is that

$$
z_{ns((ms\circ\psi)(n))}=z_{(ns\circ ms)(\psi(n))}.
$$

This equality is proved by `ext n; simp [Function.comp]`, which checks the pointwise identity of the two composed functions. Then `simpa [h_eq] using h_tendstoψ` transports the known convergence along $(ns\circ ms)\circ\psi$ to convergence along $ns\circ(ms\circ\psi)$. This verifies the subsequence criterion for the weak sequence $\iota_H(z_n)$. Therefore `tendsto_of_subseq_tendsto` yields the full weak convergence $\iota_H(z_n)\to \iota_H(a)$. Since $a\in S$, this completes the proof of

$$
\exists z_\star\in S,\quad \iota_H(z_n)\to \iota_H(z_\star).
$$

The proof uses `intro` to introduce arbitrary subsequences, `rcases` to destruct nonempty/existential hypotheses, `have` to record intermediate facts, `refine` to supply witnesses, `apply` to reduce goals by cited lemmas, `subst` to replace a variable by an equal one, `ext` and `simp [Function.comp]` to handle function composition, and `simpa` to rewrite and close goals. It does not use `linarith` or `rw`.

