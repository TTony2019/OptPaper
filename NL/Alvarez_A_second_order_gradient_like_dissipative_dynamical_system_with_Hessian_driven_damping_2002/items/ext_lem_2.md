## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/ext_lem_2.lean`

## Lean statement
```lean
theorem opial_continuous_time {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (x : ℝ → H) (S : Set H) (hS : S.Nonempty)
    (hcluster : ∀ s : ℕ → ℝ, Tendsto s atTop atTop → ∀ z,
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H z)) → z ∈ S)
    (hdist : ∀ z ∈ S, ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d)) :
    ∃ z ∈ S, Tendsto (fun t => toWeakSpace ℝ H (x t)) atTop
      (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The declaration `opial_continuous_time` is a continuous-time form of Opial’s lemma for a trajectory in a real Hilbert space. The ambient space is a type \(H\) with a normed additive commutative group structure, a real inner product space structure, and the completeness property, so \(H\) is a complete real inner product space, i.e. a real Hilbert space. The trajectory is a function
\[
x:\mathbb R\to H,
\]
and \(S\subseteq H\) is a nonempty set, as expressed by \(S\neq\varnothing\).

The first hypothesis, \(hcluster\), says that every weak sequential limit of the trajectory, sampled along times tending to \(+\infty\), lies in \(S\). More explicitly, for every sequence \(s:\mathbb N\to\mathbb R\) with
\[
\lim_{n\to\infty} s_n=+\infty,
\]
and for every \(z\in H\), if
\[
\operatorname{toWeakSpace}_{\mathbb R,H}\bigl(x(s_n)\bigr)
\to
\operatorname{toWeakSpace}_{\mathbb R,H}(z)
\]
in the weak topology, then \(z\in S\). Equivalently, every weak sequential cluster point obtained by sampling \(x\) at times tending to infinity belongs to \(S\).

The second hypothesis, \(hdist\), says that for each \(z\in S\), the real-valued distance function
\[
t\mapsto \lVert x(t)-z\rVert
\]
has a limit as \(t\to+\infty\). That is, for every \(z\in S\), there exists a real number \(d\) such that
\[
\lim_{t\to+\infty}\lVert x(t)-z\rVert=d.
\]

The conclusion is that the whole continuous-time trajectory has a weak limit as \(t\to+\infty\), and that this limit belongs to \(S\). Precisely, there exists \(z\in S\) such that
\[
\operatorname{toWeakSpace}_{\mathbb R,H}\bigl(x(t)\bigr)
\to
\operatorname{toWeakSpace}_{\mathbb R,H}(z)
\]
in the weak topology as \(t\to+\infty\). In ordinary mathematical notation, \(x(t)\rightharpoonup z\) weakly as \(t\to+\infty\).

## Lean proof
```lean
by
  rcases opial_sampled x S hS hcluster hdist (fun n : ℕ => (n : ℝ))
      tendsto_natCast_atTop_atTop with ⟨p, hpS, hpweak⟩
  have hsample : ∀ s : ℕ → ℝ, Tendsto s atTop atTop →
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H p)) := by
    intro s hs
    rcases opial_sampled x S hS hcluster hdist s hs with ⟨q, hqS, hqweak⟩
    have hpq : p = q := weak_limit_eq_of_time_distance_limits x S hdist
      tendsto_natCast_atTop_atTop hs hpS hqS hpweak hqweak
    simpa [hpq] using hqweak
  refine ⟨p, hpS, Filter.tendsto_iff_seq_tendsto.2 ?_⟩
  intro s hs
  simpa [Function.comp_def] using hsample s hs
```

## Proof explanation
The proof begins by applying the sequential Opial lemma `opial_sampled` to the particular time sequence \(s(n)=n\). In its present specialization, `opial_sampled` states that if \(x:\mathbb R\to H\), \(S\subseteq H\) is nonempty, \(hcluster\) and \(hdist\) hold, and \(s:\mathbb N\to\mathbb R\) satisfies \(s_n\to+\infty\), then there exists some point in \(S\) to which the sampled sequence
\[
n\mapsto \operatorname{toWeakSpace}_{\mathbb R,H}\bigl(x(s_n)\bigr)
\]
weakly converges. The proof uses the sequence \(n\mapsto (n:\mathbb R)\). The theorem `tendsto_natCast_atTop_atTop` supplies exactly the fact that
\[
n\mapsto (n:\mathbb R)
\]
tends to \(+\infty\). Therefore `opial_sampled` gives an element \(p\in S\) and a proof `hpweak` that
\[
\operatorname{toWeakSpace}_{\mathbb R,H}\bigl(x(n)\bigr)
\to
\operatorname{toWeakSpace}_{\mathbb R,H}(p)
\]
as \(n\to\infty\). The `rcases` tactic destructs the existential conclusion into the witness \(p\), the membership proof \(hpS:p\in S\), and the weak convergence statement \(hpweak\).

Next, the proof establishes an auxiliary statement `hsample`: for every sequence \(s:\mathbb N\to\mathbb R\) with \(s_n\to+\infty\), the sampled sequence \(x(s_n)\) weakly converges to the same point \(p\). The tactic `intro s hs` introduces an arbitrary such sequence \(s\) and the hypothesis \(hs\) that \(s_n\to+\infty\). Applying `opial_sampled` to this \(s\) gives another point \(q\in S\) and a weak convergence
\[
\operatorname{toWeakSpace}_{\mathbb R,H}\bigl(x(s_n)\bigr)
\to
\operatorname{toWeakSpace}_{\mathbb R,H}(q).
\]
The proof must show that \(q=p\). This is exactly the role of `weak_limit_eq_of_time_distance_limits`. Specialized to the current variables, that lemma says that if \(hdist\) holds, if \(u\) and \(v\) are two sequences of real times both tending to \(+\infty\), if \(p,q\in S\), and if
\[
x(u_n)\rightharpoonup p,\qquad x(v_n)\rightharpoonup q
\]
weakly, then \(p=q\). Here the proof takes \(u(n)=n\) and \(v(n)=s_n\). The relevant hypotheses are `tendsto_natCast_atTop_atTop` for \(u\), `hs` for \(v\), `hpS` and `hqS` for membership in \(S\), `hpweak` for the weak limit along integer times, and `hqweak` for the weak limit along the arbitrary sequence \(s\). The conclusion is
\[
p=q.
\]
Mathematically, this lemma rules out having two different weak limits for two different ways of sampling the same trajectory: the distance-limit hypothesis \(hdist\) forces the limiting behavior to be consistent, so the two weak limits must coincide.

The tactic `simpa [hpq] using hqweak` then uses the equality \(hpq:p=q\) to replace the limit point \(q\) by \(p\) in the conclusion of `hqweak`. Since `hqweak` states convergence to the weak image of \(q\), rewriting along \(p=q\) turns it into convergence to the weak image of \(p\), which is precisely the desired statement `hsample s hs`.

Finally, the proof constructs the required existential conclusion. The tactic `refine ⟨p, hpS, ?_⟩` chooses \(p\) as the witness, uses `hpS` as the proof that \(p\in S\), and leaves the remaining goal: prove that
\[
t\mapsto \operatorname{toWeakSpace}_{\mathbb R,H}\bigl(x(t)\bigr)
\]
converges to
\[
\operatorname{toWeakSpace}_{\mathbb R,H}(p)
\]
as \(t\to+\infty\).

To prove this continuous-time convergence, the proof uses `Filter.tendsto_iff_seq_tendsto.2`. This theorem is the sequential criterion for filter convergence: in the present instance, to show that a function of the real variable \(t\) converges along the filter `atTop` to a given neighborhood filter, it suffices to show that for every sequence \(s:\mathbb N\to\mathbb R\) with \(s_n\to+\infty\), the composed sequence
\[
n\mapsto \operatorname{toWeakSpace}_{\mathbb R,H}\bigl(x(s_n)\bigr)
\]
converges to the same weak limit. The `.2` direction is precisely the direction that takes this sequential convergence statement and produces the filter convergence statement.

The tactic `intro s hs` introduces an arbitrary sequence \(s\) and the assumption \(hs:s_n\to+\infty\). The remaining goal is convergence of the composed sequence. The final line
\[
\texttt{simpa [Function.comp_def] using hsample s hs}
\]
unfolds the definition of function composition, turning the composed sequence into the explicit sequence \(n\mapsto \operatorname{toWeakSpace}_{\mathbb R,H}(x(s_n))\), and then applies the already established `hsample s hs`. Since this argument works for an arbitrary sequence \(s\) tending to \(+\infty\), the sequential criterion yields the desired continuous-time weak convergence of \(x(t)\) to \(p\) as \(t\to+\infty\). Thus the conclusion
\[
\exists z\in S,\quad
\operatorname{toWeakSpace}_{\mathbb R,H}\bigl(x(t)\bigr)
\to
\operatorname{toWeakSpace}_{\mathbb R,H}(z)
\]
is proved with witness \(p\).

