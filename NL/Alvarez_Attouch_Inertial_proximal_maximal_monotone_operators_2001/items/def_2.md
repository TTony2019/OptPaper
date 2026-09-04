## Source file
`Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001/items/def_2.lean`

## Lean statement
```lean
theorem resolvent_of_maximal_monotone
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∀ u : H, ∃! z : H, u ∈ A.identityAddScaled lambda z) ∧
      ∃ J : H → H, (∀ u : H, J u ∈ J[(lambda • A)] u) ∧
        LipschitzWith 1 J ∧ ∀ z : H, J z = z ↔ 0 ∈ A z
```

## Statement explanation
The theorem concerns a set-valued operator \(A\) from an implicit space \(H\) to sets in \(H\), written in Lean as `SetValuedOperator H H`. The assumption `hA` says that \(A\) is maximal monotone. The scalar `lambda` is a real number, and `hlambda` says \(0 < \lambda\).

The notation `A.identityAddScaled lambda z` denotes the set of points of the form \(z+\lambda a\) with \(a\in A z\). Thus
\[
u\in A.\mathrm{identityAddScaled}\,\lambda\,z
\]
means there exists \(a\in A z\) such that \(u=z+\lambda a\). This is the inclusion \(u\in (I+\lambda A)z\).

The notation \(J[(\lambda\bullet A)]u\) denotes the resolvent of the scaled operator \(\lambda\bullet A\) at \(u\). Thus \(J u\in J[(\lambda\bullet A)]u\) means precisely that \(u\in A.\mathrm{identityAddScaled}\,\lambda\,(J u)\).

The theorem states two conclusions:

1. For every \(u\in H\), there exists a unique \(z\in H\) such that
   \[
   u\in A.\mathrm{identityAddScaled}\,\lambda\,z.
   \]
2. There exists a function \(J:H\to H\) such that:
   - for every \(u\), \(J u\) belongs to the resolvent of \(\lambda A\) at \(u\);
   - \(J\) is \(1\)-Lipschitz, i.e. nonexpansive;
   - for every \(z\in H\), \(J z=z\) if and only if \(0\in A z\).

In words, a maximal monotone operator has a unique resolvent value at every point, and there is a nonexpansive selection of the resolvent whose fixed points are exactly the zeros of the original operator.

## Lean proof
```lean
by
  classical
  have hunique : ∀ u : H, ∃! z : H, u ∈ A.identityAddScaled lambda z :=
    fun u => identityAddScaled_existsUnique_of_maximal_monotone A hA hlambda u
  let J : H → H := fun u => Classical.choose (hunique u)
  have hJ_identity : ∀ u : H, u ∈ A.identityAddScaled lambda (J u) := by
    intro u
    exact (Classical.choose_spec (hunique u)).1
  have hJ : ∀ u : H, J u ∈ J[(lambda • A)] u := by
    intro u
    exact (mem_resolvent_smul_iff A lambda u (J u)).mpr (hJ_identity u)
  refine ⟨hunique, J, hJ, resolvent_selection_lipschitz A hA hlambda J hJ, ?_⟩
  intro z
  constructor
  · intro hfix
    rcases hJ_identity z with ⟨a, ha, hza⟩
    have hscaled : lambda • a = 0 := by
      rw [hfix] at hza ha
      apply add_left_cancel (a := z)
      simpa using hza.symm
    have ha_zero : a = 0 := (smul_eq_zero.mp hscaled).resolve_left hlambda.ne'
    simpa [hfix, ha_zero] using ha
  · intro hzero
    have hz : z ∈ A.identityAddScaled lambda z := ⟨0, hzero, by simp⟩
    exact (hunique z).unique (hJ_identity z) hz
```

## Proof explanation
The proof starts with `classical`, enabling classical choice and decidability.

First, the proof obtains uniqueness of the resolvent point:
\[
\forall u,\ \exists! z,\ u\in A.\mathrm{identityAddScaled}\,\lambda\,z.
\]
This is given by the lemma `identityAddScaled_existsUnique_of_maximal_monotone`, applied to `A`, `hA`, and `hlambda`. This proves the first conjunct.

Then the proof defines a function \(J:H\to H\) by choosing, for each \(u\), the unique \(z\) satisfying that inclusion:
\[
J u := \text{Classical.choose } (hunique\ u).
\]
The `Classical.choose_spec` command gives the defining property of this chosen element, which is recorded as `hJ_identity`:
\[
\forall u,\ u\in A.\mathrm{identityAddScaled}\,\lambda\,(J u).
\]
This is exactly the first component of the chosen witness.

Next, the proof converts this inclusion into resolvent membership. The lemma `mem_resolvent_smul_iff` is used in the reverse direction to prove
\[
J u\in J[(\lambda\bullet A)]u
\]
for every \(u\). This gives the statement `hJ`.

The proof then assembles the existential statement using `refine`. The first three components are:
- `hunique`, the uniqueness statement;
- the function `J`;
- `hJ`, the resolvent membership property.
The Lipschitz condition is supplied by the lemma `resolvent_selection_lipschitz`, using `A`, `hA`, `hlambda`, `J`, and `hJ`. What remains is the fixed-point equivalence.

For the fixed-point equivalence, the proof introduces an arbitrary \(z\) and splits the bidirectional implication with `constructor`.

For the forward direction, assume \(J z=z\). From `hJ_identity z`, there exist \(a\in A(J z)\) and an equation
\[
z=J z+\lambda a.
\]
After rewriting \(J z\) to \(z\) using the fixed-point assumption, this becomes
\[
z=z+\lambda a.
\]
Cancelling \(z\) gives \(\lambda a=0\). Since \(\lambda>0\), one has \(\lambda\neq 0\), so \(a=0\). After rewriting `a` to `0` and using the fixed-point equality again, the membership \(a\in A(J z)\) becomes \(0\in A z\).

For the reverse direction, assume \(0\in A z\). Then, because \(z=z+\lambda 0\), the proof obtains
\[
z\in A.\mathrm{identityAddScaled}\,\lambda\,z.
\]
But `hunique z` says there is a unique \(w\) such that \(z\in A.\mathrm{identityAddScaled}\,\lambda\,w\). Both \(J z\) and \(z\) are such witnesses: the first is `hJ_identity z`, and the second is the newly proved inclusion. Therefore uniqueness gives \(J z=z\).

Important Lean commands used include `intro` to introduce arbitrary variables and implications, `rcases` to unpack the existential membership, `rw` to rewrite using equalities, `exact` to supply a direct proof, `simpa` to simplify goals using assumptions, and `constructor` to split an if-and-only-if goal. The proof does not use `linarith`.

