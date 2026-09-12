import Mathlib.Tactic
import Foundation.Hilbert.WeakConvergence

/-!
# Opial's Lemma

Let `H` be a Hilbert space and `{x_k}` a sequence such that there exists a nonempty set
`S ⊂ H` verifying:
- For every `x* ∈ S`, `lim_{k → +∞} |x_k - x*|` exists.
- If `x_{k_j}` weakly converges to `x ∈ H` for a subsequence `k_j → +∞`, then `x ∈ S`.

Then, there exists `x̃ ∈ S` such that `{x_k}` weakly converges to `x̃` in `H`.
-/

/-- Opial's Lemma: weak convergence from distance convergence and weak cluster
points belonging to the target set. -/
recall opial_lemma
