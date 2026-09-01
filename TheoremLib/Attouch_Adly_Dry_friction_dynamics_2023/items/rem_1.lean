import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_thm_5
import Foundation.Analysis.ExtendedRealFunctions

namespace AttouchAdlyDryFrictionDynamics2023

private theorem fenchel_summand_le_conjugate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f fstar : H → EReal)
    (hconjugate : fstar = ERealFunction.conjugate f) (u z : H) :
    ((inner ℝ u z : EReal) - f z) ≤ fstar u := by
  rw [hconjugate, ERealFunction.conjugate_apply_swap]
  exact le_iSup (fun w : H => (inner ℝ u w : EReal) - f w) z

/-- A proper extended-real function has a conjugate value strictly above
`-∞` at every slope. -/
private theorem fenchel_conjugate_ne_bot_of_proper {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : ERealFunction.IsProper f)
    (u : EuclideanSpace ℝ (Fin n)) : ERealFunction.conjugate f u ≠ ⊥ := by
  obtain ⟨p, hp⟩ := hproper.2
  change f p < ⊤ at hp
  have hp_top : f p ≠ ⊤ := ne_of_lt hp
  have hs : (inner ℝ u p : EReal) - f p ≤ ERealFunction.conjugate f u := by
    rw [ERealFunction.conjugate_apply_swap]
    exact le_iSup (fun z : EuclideanSpace ℝ (Fin n) =>
      (inner ℝ u z : EReal) - f z) p
  intro hbot
  rw [hbot] at hs
  have hleft : (inner ℝ u p : EReal) - f p ≠ ⊥ := by
    rw [← EReal.coe_toReal hp_top (hproper.1 p)]
    exact EReal.coe_ne_bot _
  exact hleft (le_bot_iff.mp hs)

/-- The finite-dimensional Fenchel--Moreau step needed for the reverse
subgradient implication. -/
private theorem fenchel_conjugate_conjugate_apply_eq {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n))
    (hconvex : Convex ℝ (ERealFunction.epigraph f))
    (hproper : ERealFunction.IsProper f) (hlsc : LowerSemicontinuous f) :
    ERealFunction.conjugate (ERealFunction.conjugate f) x = f x := by
  have hmem : f ∈ ERealFunction.gamma (EuclideanSpace ℝ (Fin n)) := by
    rw [ERealFunction.mem_gamma_iff]
    exact ⟨ERealFunction.isConvex_of_convex_epigraph hproper hconvex, hlsc⟩
  exact congrFun ((ERealFunction.mem_gamma_iff_eq_biconjugate_of_is_proper hproper).mp hmem) x

private theorem fenchel_dual_subgradient_imp_equality {n : ℕ}
    (f fstar : EuclideanSpace ℝ (Fin n) → EReal) (x y : EuclideanSpace ℝ (Fin n))
    (hconvex : Convex ℝ (ERealFunction.epigraph f))
    (hproper : ERealFunction.IsProper f) (hlsc : LowerSemicontinuous f)
    (hconjugate : fstar = ERealFunction.conjugate f)
    (hsub : x ∈ ERealFunction.subdifferential fstar y) :
    f x + fstar y = (inner ℝ y x : EReal) := by
  have hbiconjugate := fenchel_conjugate_conjugate_apply_eq f x hconvex hproper hlsc
  have hclosed : IsClosed (ERealFunction.epigraph f) :=
    (ERealFunction.lowerSemicontinuous_iff_isClosed_epigraph f).1 hlsc
  change ∀ z : EuclideanSpace ℝ (Fin n),
    (inner ℝ (z - y) x : EReal) + fstar y ≤ fstar z at hsub
  have hsub' : ∀ z : EuclideanSpace ℝ (Fin n),
      fstar y + (inner ℝ x (z - y) : EReal) ≤ fstar z := by
    intro z
    simpa [real_inner_comm, add_comm] using hsub z
  have hlower : (inner ℝ y x : EReal) - f x ≤ fstar y :=
    fenchel_summand_le_conjugate f fstar hconjugate y x
  have hstar_bot : fstar y ≠ ⊥ := by
    rw [hconjugate]
    exact fenchel_conjugate_ne_bot_of_proper f hproper y
  have hupper : f x ≤ (inner ℝ y x : EReal) - fstar y := by
    by_cases hytop : fstar y = ⊤
    · rw [← hbiconjugate, ← hconjugate, ERealFunction.conjugate_apply, hytop]
      apply iSup_le
      intro z
      have hz := hsub' z
      rw [hytop] at hz
      have hztop : fstar z = ⊤ := by simpa using hz
      simp [hztop]
    · rw [← hbiconjugate, ← hconjugate, ERealFunction.conjugate_apply]
      apply iSup_le
      intro z
      by_cases htop : fstar z = ⊤
      · simp [htop]
      · have hbot : fstar z ≠ ⊥ := by
          rw [hconjugate]
          exact fenchel_conjugate_ne_bot_of_proper f hproper z
        have hz := hsub' z
        rw [inner_sub_right, EReal.coe_sub] at hz
        rw [← EReal.coe_toReal htop hbot,
          ← EReal.coe_toReal hytop hstar_bot] at hz ⊢
        have hzreal : (fstar y).toReal + (inner ℝ x z - inner ℝ x y) ≤
            (fstar z).toReal := by
          exact_mod_cast hz
        have hreal : inner ℝ x z - (fstar z).toReal ≤
            inner ℝ x y - (fstar y).toReal := by linarith
        exact_mod_cast (by simpa [real_inner_comm] using hreal)
  have hfx_top : f x ≠ ⊤ := by
    intro htop
    rw [htop] at hupper
    have hright : (inner ℝ y x : EReal) - fstar y ≠ ⊤ := by
      induction hs : fstar y with
      | bot => exact (hstar_bot hs).elim
      | coe r => simpa [EReal.coe_sub] using EReal.coe_ne_top (inner ℝ y x - r)
      | top => simp
    exact hright (top_unique hupper)
  have hstar_top : fstar y ≠ ⊤ := by
    intro htop
    rw [htop] at hupper
    have hbot : f x = ⊥ := le_bot_iff.mp (by simpa using hupper)
    exact hproper.1 x hbot
  rw [← EReal.coe_toReal hfx_top (hproper.1 x),
    ← EReal.coe_toReal hstar_top hstar_bot,
    ← EReal.coe_toReal hfx_top (hproper.1 x)] at hupper hlower ⊢
  norm_num [EReal.coe_add, EReal.coe_sub] at hupper hlower ⊢
  have hupper' : (f x).toReal ≤ inner ℝ y x - (fstar y).toReal := by
    exact_mod_cast hupper
  have hlower' : inner ℝ y x - (f x).toReal ≤ (fstar y).toReal := by
    exact_mod_cast hlower
  exact_mod_cast (by linarith :
    (f x).toReal + (fstar y).toReal = inner ℝ y x)

private theorem fenchel_equality_iff_subgradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f fstar : H → EReal) (x y : H)
    (hproper : ERealFunction.IsProper f) (hconjugate : fstar = ERealFunction.conjugate f) :
    y ∈ ERealFunction.subdifferential f x ↔ f x + fstar y = (inner ℝ y x : EReal) := by
  constructor
  · intro hsub
    change ∀ z : H, (inner ℝ (z - x) y : EReal) + f x ≤ f z at hsub
    have hsub' : ∀ z : H, f x + (inner ℝ y (z - x) : EReal) ≤ f z := by
      intro z
      simpa [real_inner_comm, add_comm] using hsub z
    obtain ⟨p, hp⟩ := hproper.2
    change f p < ⊤ at hp
    have hp_top : f p ≠ ⊤ := ne_of_lt hp
    have hfx_top : f x ≠ ⊤ := by
      intro htop
      have hp' := hsub' p
      rw [htop] at hp'
      exact hp_top (by simpa using hp')
    have hupper : fstar y ≤ (inner ℝ y x : EReal) - f x := by
      rw [hconjugate, ERealFunction.conjugate_apply_swap]
      apply iSup_le
      intro z
      by_cases htop : f z = ⊤
      · simp [htop]
      · have hz := hsub' z
        rw [inner_sub_right, EReal.coe_sub] at hz
        rw [← EReal.coe_toReal htop (hproper.1 z),
          ← EReal.coe_toReal hfx_top (hproper.1 x)] at hz ⊢
        have hzreal : (f x).toReal + (inner ℝ y z - inner ℝ y x) ≤ (f z).toReal := by
          exact_mod_cast hz
        exact_mod_cast (by linarith :
          inner ℝ y z - (f z).toReal ≤ inner ℝ y x - (f x).toReal)
    have hlower : (inner ℝ y x : EReal) - f x ≤ fstar y :=
      fenchel_summand_le_conjugate f fstar hconjugate y x
    have hstar_top : fstar y ≠ ⊤ := by
      intro htop
      rw [htop] at hupper
      have hright_top : (inner ℝ y x : EReal) - f x ≠ ⊤ := by
        rw [← EReal.coe_toReal hfx_top (hproper.1 x)]
        exact EReal.coe_ne_top _
      exact hright_top (by simpa using hupper)
    have hstar_bot : fstar y ≠ ⊥ := by
      intro hbot
      rw [hbot] at hlower
      have hleft_bot : (inner ℝ y x : EReal) - f x ≠ ⊥ := by
        rw [← EReal.coe_toReal hfx_top (hproper.1 x)]
        exact EReal.coe_ne_bot _
      exact hleft_bot (by simpa using hlower)
    rw [← EReal.coe_toReal hfx_top (hproper.1 x),
      ← EReal.coe_toReal hstar_top hstar_bot,
      ← EReal.coe_toReal hfx_top (hproper.1 x)] at hupper hlower ⊢
    norm_num [EReal.coe_add, EReal.coe_sub] at hupper hlower ⊢
    have hupper' : (fstar y).toReal ≤ inner ℝ y x - (f x).toReal := by exact_mod_cast hupper
    have hlower' : inner ℝ y x - (f x).toReal ≤ (fstar y).toReal := by exact_mod_cast hlower
    exact_mod_cast (by linarith : (f x).toReal + (fstar y).toReal = inner ℝ y x)
  · intro heq
    change ∀ z : H, (inner ℝ (z - x) y : EReal) + f x ≤ f z
    obtain ⟨p, hp⟩ := hproper.2
    change f p < ⊤ at hp
    have hp_top : f p ≠ ⊤ := ne_of_lt hp
    have hstar_bot : fstar y ≠ ⊥ := by
      intro hbot
      have hs := fenchel_summand_le_conjugate f fstar hconjugate y p
      rw [hbot] at hs
      have hleft_bot : (inner ℝ y p : EReal) - f p ≠ ⊥ := by
        rw [← EReal.coe_toReal hp_top (hproper.1 p)]
        exact EReal.coe_ne_bot _
      exact hleft_bot (by simpa using hs)
    have hfx_top : f x ≠ ⊤ := by
      intro htop
      rw [htop] at heq
      simp [hstar_bot] at heq
    intro z
    rw [← real_inner_comm (z - x) y, add_comm]
    by_cases htop : f z = ⊤
    · simp [htop]
    · have hs := fenchel_summand_le_conjugate f fstar hconjugate y z
      have hstar_top : fstar y ≠ ⊤ := by
        intro hstar
        rw [hstar] at heq
        simp [hproper.1 x] at heq
      rw [inner_sub_right, EReal.coe_sub]
      rw [← EReal.coe_toReal hfx_top (hproper.1 x)] at heq ⊢
      rw [← EReal.coe_toReal hstar_top hstar_bot] at heq hs
      rw [← EReal.coe_toReal htop (hproper.1 z)] at hs ⊢
      have heq' : (f x).toReal + (fstar y).toReal = inner ℝ y x := by exact_mod_cast heq
      have hs' : inner ℝ y z - (f z).toReal ≤ (fstar y).toReal := by exact_mod_cast hs
      exact_mod_cast (by linarith :
        (f x).toReal + (inner ℝ y z - inner ℝ y x) ≤ (f z).toReal)

private theorem fenchel_equality_imp_dual_subgradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f fstar : H → EReal) (x y : H)
    (hproper : ERealFunction.IsProper f) (hconjugate : fstar = ERealFunction.conjugate f)
    (heq : f x + fstar y = (inner ℝ y x : EReal)) :
    x ∈ ERealFunction.subdifferential fstar y := by
  obtain ⟨p, hp⟩ := hproper.2
  change f p < ⊤ at hp
  have hp_top : f p ≠ ⊤ := ne_of_lt hp
  have hstar_bot : fstar y ≠ ⊥ := by
    intro hbot
    have hs := fenchel_summand_le_conjugate f fstar hconjugate y p
    rw [hbot] at hs
    have hleft_bot : (inner ℝ y p : EReal) - f p ≠ ⊥ := by
      rw [← EReal.coe_toReal hp_top (hproper.1 p)]
      exact EReal.coe_ne_bot _
    exact hleft_bot (by simpa using hs)
  have hfx_top : f x ≠ ⊤ := by
    intro htop
    rw [htop] at heq
    simp [hstar_bot] at heq
  have hstar_top : fstar y ≠ ⊤ := by
    intro htop
    rw [htop] at heq
    simp [hproper.1 x] at heq
  change ∀ z : H, (inner ℝ (z - y) x : EReal) + fstar y ≤ fstar z
  intro z
  rw [← real_inner_comm (z - y) x, add_comm]
  have hs := fenchel_summand_le_conjugate f fstar hconjugate z x
  rw [inner_sub_right, EReal.coe_sub]
  rw [← EReal.coe_toReal hfx_top (hproper.1 x),
    ← EReal.coe_toReal hstar_top hstar_bot] at heq
  rw [← EReal.coe_toReal hstar_top hstar_bot]
  rw [← EReal.coe_toReal hfx_top (hproper.1 x)] at hs
  have heq' : (f x).toReal + (fstar y).toReal = inner ℝ y x := by exact_mod_cast heq
  have hreal : (fstar y).toReal + (inner ℝ x z - inner ℝ x y) =
      inner ℝ z x - (f x).toReal := by
    rw [real_inner_comm z x, real_inner_comm y x]
    linarith
  rw [← EReal.coe_sub, ← EReal.coe_add, hreal, EReal.coe_sub]
  exact hs

/-- Remark 3.1: Fenchel equality characterizes mutually inverse convex subdifferentials. -/
theorem remark_3_1 {n : ℕ}
    (f fstar : EuclideanSpace ℝ (Fin n) → EReal) (x y : EuclideanSpace ℝ (Fin n))
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (hproper : ERealFunction.IsProper f)
    (hlsc : LowerSemicontinuous f) (hconjugate : fstar = ERealFunction.conjugate f) :
    (y ∈ ERealFunction.subdifferential f x ↔ f x + fstar y = (inner ℝ y x : EReal)) ∧
      (f x + fstar y = (inner ℝ y x : EReal) ↔
        x ∈ ERealFunction.subdifferential fstar y) := by
  constructor
  · exact fenchel_equality_iff_subgradient f fstar x y hproper hconjugate
  · constructor
    · exact fenchel_equality_imp_dual_subgradient f fstar x y hproper hconjugate
    · intro hsub
      exact fenchel_dual_subgradient_imp_equality f fstar x y hconvex hproper hlsc hconjugate hsub

end AttouchAdlyDryFrictionDynamics2023
