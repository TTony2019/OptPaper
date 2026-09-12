## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/def_3.lean`

## Lean statement
```lean
noncomputable def ProblemData.IsSolution {m : Nat} (P : ProblemData m)
    (x : EuclideanSpace m) : Prop :=
  IsMinOn P.objective Set.univ x
```

## Statement explanation
The declaration `ProblemData.IsSolution` is a noncomputable definition, not a theorem asserting existence of a solution. It is parameterized by an implicit dimension $m : \mathbb{N}$, by problem data $P : \operatorname{ProblemData} m$, and by a candidate point $x : \operatorname{EuclideanSpace} m$. It returns a proposition. Its defining equation is

$$
\operatorname{ProblemData.IsSolution}(P,x)
\;\Longleftrightarrow\;
\operatorname{IsMinOn}(P.\mathrm{objective}, \operatorname{univ}, x),
$$

where $\operatorname{univ}$ is the Lean set `Set.univ`, the whole ambient type $\operatorname{EuclideanSpace} m$.

In Mathlib, $\operatorname{IsMinOn}(f,s,a)$ means that $a$ is a minimum point of the function $f$ on the set $s$. Concretely, it contains the conditions $a \in s$ and $f(a) \le f(b)$ for every $b \in s$. Specializing this to the definition above, $f$ is the objective function $P.\mathrm{objective}$, the set $s$ is the entire space $\operatorname{EuclideanSpace} m$, and the point $a$ is $x$. Since $s$ is the whole space, the membership condition $x \in s$ is automatic. Thus the definition says exactly that

$$
P.\mathrm{objective}(x) \le P.\mathrm{objective}(y)
$$

for every $y \in \operatorname{EuclideanSpace} m$. In ordinary mathematical language, $x$ is a global minimizer of the objective function associated with the problem data $P$, over the whole Euclidean space. The definition uses no feasibility constraints or other fields of $P$; the minimization set is explicitly `Set.univ`. It does not assert that such a point $x$ exists; it only defines the property that $x$ has if it is a global minimizer.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `def`, so the code following it is empty and no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur. The definition simply introduces the name `ProblemData.IsSolution` with the defining equation

$$
\operatorname{ProblemData.IsSolution}(P,x)
:=
\operatorname{IsMinOn}(P.\mathrm{objective}, \operatorname{univ}, x).
$$

Unfolding this definition, a proof of `ProblemData.IsSolution P x` is exactly a proof of `IsMinOn P.objective Set.univ x`. By the meaning of `IsMinOn`, that requires proving that $x$ belongs to `Set.univ`, which is immediate because `Set.univ` is the whole type, and that every point $y$ in the ambient Euclidean space satisfies

$$
P.\mathrm{objective}(x) \le P.\mathrm{objective}(y).
$$

The first condition adds no mathematical restriction. The second is the global minimality condition: no point in the entire space has a strictly smaller objective value than $x$. Conversely, any proof of this global minimality statement can be used as a proof of `ProblemData.IsSolution P x` by definitional unfolding.

No named local theorem, lemma, or previously established fact is cited, because there is no proof body. The only imported notion used is `IsMinOn`, and its role here is precisely to express that $x$ minimizes $P.\mathrm{objective}$ over `Set.univ`. The `noncomputable` marker affects only Lean’s computation or code-extraction behavior, not the mathematical meaning of the predicate.

