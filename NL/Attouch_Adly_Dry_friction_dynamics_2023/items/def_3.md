## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/def_3.lean`

## Lean statement
```lean
def dualBregmanDistance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (fstar : H → ℝ) (gradFstar : H → H)
    (g gLimit : H) : ℝ :=
  bregmanDistance fstar gradFstar g gLimit
```

## Statement explanation
The declaration `dualBregmanDistance` is a definition, not a theorem. It is made in a context where $H$ is an arbitrary type carrying two typeclass structures: $H$ is a normed additive commutative group, and $H$ is a real inner product space. Thus $H$ has the algebraic operations of addition, subtraction, and zero, a norm, and an inner product over $\mathbb{R}$. The explicit arguments are:

- `fstar`, a function $f^\star : H \to \mathbb{R}$;
- `gradFstar`, a function $G : H \to H$;
- `g`, an element of $H$;
- `gLimit`, another element of $H$.

No convexity, differentiability, monotonicity, convergence, or limit hypothesis is present. In particular, although the names suggest that $f^\star$ is a conjugate function and that $G$ is a gradient-type map, the definition itself only treats them as an arbitrary real-valued function and an arbitrary self-map of $H$. Likewise, `gLimit` is simply a point of $H$; no statement that it is a limit of anything is part of the definition.

The body of the definition is

$$
\mathrm{dualBregmanDistance}(f^\star,G,g,g_{\mathrm{Limit}})
=
\mathrm{bregmanDistance}(f^\star,G,g,g_{\mathrm{Limit}}).
$$

So the definition introduces the dual Bregman distance as exactly the already-existing Bregman distance evaluated with the same four arguments. Since the definition of `bregmanDistance` is not included in the provided source, this explanation does not assert any particular formula for it. The mathematical content of this declaration is precisely the definitional identification: the new name `dualBregmanDistance` is an abbreviation for `bregmanDistance` specialized to $f^\star$, $G$, $g$, and $g_{\mathrm{Limit}}$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source contains only a comment saying that there is no separate proof. Consequently there are no proof steps involving tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named lemma or theorem is invoked.

The only mathematical content is the definitional equality obtained by unfolding the new name:

$$
\mathrm{dualBregmanDistance}(f^\star,G,g,g_{\mathrm{Limit}})
=
\mathrm{bregmanDistance}(f^\star,G,g,g_{\mathrm{Limit}}).
$$

In Lean terms, `dualBregmanDistance fstar gradFstar g gLimit` is definitionally equal to `bregmanDistance fstar gradFstar g gLimit`. Therefore any later use of the dual Bregman distance can be replaced by the corresponding Bregman distance with the same arguments, without adding any additional hypotheses. No local result is cited because there is no proof to cite one in.

