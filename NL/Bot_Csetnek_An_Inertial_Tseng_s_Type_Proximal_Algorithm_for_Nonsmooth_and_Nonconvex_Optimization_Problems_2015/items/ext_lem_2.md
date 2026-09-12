## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_lem_2.lean`

## Lean statement
```lean
theorem lemma_2_2_descent_summable (a b : Nat -> Real)
    (hb_nonneg : ∀ n, 0 <= b n)
    (ha_bddBelow : BddBelow (Set.range a))
    (hdesc : ∀ n, a (n + 1) + b n <= a n) :
    Antitone a ∧ (∃ l : Real, Tendsto a atTop (nhds l)) ∧ Summable b
```

## Statement explanation
The declaration `lemma_2_2_descent_summable` concerns two real sequences $a=(a_n)_{n\in\mathbb N}$ and $b=(b_n)_{n\in\mathbb N}$. Its hypotheses are:

$$
\forall n\in\mathbb N,\quad 0\le b_n,
$$

so $b$ is nonnegative;

$$
\mathrm{BddBelow}(\{a_n:n\in\mathbb N\}),
$$

meaning there exists $L\in\mathbb R$ such that $L\le a_n$ for every $n$; and

$$
\forall n\in\mathbb N,\quad a_{n+1}+b_n\le a_n.
$$

The last inequality says that the drop from $a_n$ to $a_{n+1}$ is at least $b_n$, since it is equivalent to $a_n-a_{n+1}\ge b_n$. Its conclusion is the conjunction of three facts:

$$
\mathrm{Antitone}(a),
$$

meaning that if $m\le n$, then $a_n\le a_m$, so $a$ is nonincreasing;

$$
\exists l\in\mathbb R,\quad a_n\to l \text{ as } n\to\infty,
$$

so $a$ converges to some real limit; and

$$
\mathrm{Summable}(b),
$$

so the series $\sum_{n=0}^{\infty} b_n$ converges.

Mathematically, the theorem says that a bounded-below real sequence whose decreases are dominated by the nonnegative terms $b_n$ must be nonincreasing, must converge, and must have finite total decrease in the sense that $\sum b_n$ is summable. The convergence of $a$ comes from monotone convergence for a nonincreasing sequence that is bounded below. The summability of $b$ comes from telescoping the decreases and using the lower bound on $a$ to bound all partial sums of $b$.

## Lean proof
```lean
by
  have hbdd : BddBelow (Set.range a) := ha_bddBelow
  obtain ⟨L, hL⟩ := ha_bddBelow
  have hstep : ∀ n, a (n + 1) ≤ a n := by
    intro n
    have hb : 0 ≤ b n := hb_nonneg n
    have hd : a (n + 1) + b n ≤ a n := hdesc n
    linarith
  have hanti : Antitone a := by
    intro m n hmn
    induction hmn with
    | refl => rfl
    | step hmn ih => exact le_trans (hstep _) ih
  have hconv : ∃ l : Real, Tendsto a atTop (nhds l) := by
    exact ⟨⨅ n, a n, tendsto_atTop_ciInf hanti hbdd⟩
  have hlower : ∀ n, L ≤ a n := by
    intro n
    exact hL ⟨n, rfl⟩
  have htel : ∀ n, (∑ i ∈ Finset.range n, b i) + a n ≤ a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have hd : a (n + 1) + b n ≤ a n := hdesc n
        linarith
  have hsumbdd : ∀ n, ∑ i ∈ Finset.range n, b i ≤ a 0 - L := by
    intro n
    have ht := htel n
    have hLn := hlower n
    linarith
  exact ⟨hanti, hconv, summable_of_sum_range_le hb_nonneg hsumbdd⟩
```

## Proof explanation
The proof begins by renaming the bounded-below hypothesis as `hbdd` and then unpacking it with `obtain ⟨L, hL⟩ := ha_bddBelow`. Since `BddBelow (Set.range a)` means that the set of values $\{a_n:n\in\mathbb N\}$ has a lower bound, this step produces a real number $L$ such that every element of that range is at least $L$. Thus $hL$ is the assertion that for every $n$, the value $a_n$ lies above $L$, which later is used in the form $L\le a_n$.

Next the proof establishes the one-step monotonicity statement

$$
hstep:\quad \forall n,\quad a_{n+1}\le a_n.
$$

For a fixed $n$, the hypothesis `hb_nonneg n` gives $0\le b_n$, and `hdesc n` gives $a_{n+1}+b_n\le a_n$. Since $b_n\ge 0$, we have $a_{n+1}\le a_{n+1}+b_n$, and combining this with $a_{n+1}+b_n\le a_n$ yields $a_{n+1}\le a_n$. The tactic `linarith` performs exactly this linear inequality reasoning over the real numbers.

The proof then proves `hanti : Antitone a`. After introducing arbitrary $m,n$ with $m\le n$, it proceeds by induction on the proof of $m\le n$. In the reflexive case $m=n$, the goal is the reflexive inequality $a_m\le a_m$, closed by `rfl`. In the step case, the induction hypothesis is $a_n\le a_m$, and the goal is $a_{n+1}\le a_m$. The previously proved `hstep n` gives $a_{n+1}\le a_n$. Applying transitivity of $\le$, via `le_trans (hstep _) ih`, combines $a_{n+1}\le a_n$ with $a_n\le a_m$ to obtain $a_{n+1}\le a_m$. Thus $a$ is antitone.

For convergence, the proof invokes `tendsto_atTop_ciInf hanti hbdd`. In this context, this theorem says that an antitone real sequence which is bounded below converges to its infimum. Concretely, it provides

$$
\mathrm{Tendsto}\ a\ \mathrm{atTop}\ (\mathrm{nhds}(\bigwedge_n a_n)),
$$

where $\bigwedge_n a_n$ is the infimum of the values of $a$. The proof packages this as the existential statement $\exists l\in\mathbb R,\ a_n\to l$ by choosing $l=\bigwedge_n a_n$.

The proof then records the lower bound in the form

$$
hlower:\quad \forall n,\quad L\le a_n.
$$

For a fixed $n$, the term $a_n$ belongs to the range of $a$, witnessed by $n$ itself, so applying `hL` to that range element gives $L\le a_n$.

The key telescoping estimate is

$$
htel:\quad \forall n,\quad
\left(\sum_{i=0}^{n-1} b_i\right)+a_n\le a_0.
$$

Here the finite sum over `Finset.range n` represents $\sum_{i=0}^{n-1} b_i$. The proof is by induction on $n$. For $n=0$, the sum is empty, so the inequality is $0+a_0\le a_0$, which `simp` simplifies and closes. In the successor step, assuming

$$
\left(\sum_{i=0}^{n-1} b_i\right)+a_n\le a_0,
$$

the tactic `rw [Finset.sum_range_succ]` rewrites the sum through $n$ as

$$
\sum_{i=0}^{n} b_i
=\left(\sum_{i=0}^{n-1} b_i\right)+b_n.
$$

The descent hypothesis `hdesc n` gives $a_{n+1}+b_n\le a_n$. Adding $\sum_{i=0}^{n-1} b_i$ to both sides and chaining with the induction hypothesis yields

$$
\left(\sum_{i=0}^{n} b_i\right)+a_{n+1}\le a_0.
$$

Again `linarith` carries out this linear rearrangement. This proves the telescoping inequality for all $n$.

From the telescoping inequality and the lower bound, the proof derives a uniform bound on the partial sums of $b$:

$$
hsumbdd:\quad \forall n,\quad
\sum_{i=0}^{n-1} b_i\le a_0-L.
$$

Indeed, from

$$
\left(\sum_{i=0}^{n-1} b_i\right)+a_n\le a_0
$$

and $L\le a_n$, it follows that

$$
\left(\sum_{i=0}^{n-1} b_i\right)+L
\le
\left(\sum_{i=0}^{n-1} b_i\right)+a_n
\le a_0,
$$

hence $\sum_{i=0}^{n-1} b_i\le a_0-L$. The tactic `linarith` performs this deduction.

Finally, the proof invokes `summable_of_sum_range_le hb_nonneg hsumbdd`. The exact consequence used here is the standard bounded-partial-sum criterion for nonnegative series: if $b_n\ge 0$ for every $n$, and if there is a constant $C$ such that every finite partial sum satisfies

$$
\sum_{i=0}^{n-1} b_i\le C,
$$

then the series $\sum_{n=0}^{\infty} b_n$ is summable. In this proof the constant is $C=a_0-L$. Thus `summable_of_sum_range_le` returns `Summable b`.

The final line `exact ⟨hanti, hconv, summable_of_sum_range_le hb_nonneg hsumbdd⟩` combines the three established conclusions— $a$ is antitone, $a$ converges, and $b$ is summable—into the conjunction required by the theorem statement.

