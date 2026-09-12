import Mathlib
import Foundation.Differentiation.ODE
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- For T>0, the sup norm ‖x‖_∞ := sup_{t∈[0,T]} ‖x(t)‖.  Supplied canonically
  by Foundation.

  Deviation: the value is the real `sSup` of the norm set, hence `0` for a path
  that is unbounded on `[0,T]` (or if the interval is degenerate), whereas the
  paper's `sup` may be `+∞`; consumers carry explicit finiteness where needed. -/
recall pathSupNorm

/-- The integral map Γ_{A,u₀,v₀}(x)(t) := u₀+tv₀+∫₀ᵗ(s-t)[γẋ(s)+Ax(s)]ds.
  Supplied canonically by Foundation.

  Deviation: the paper declares `Γ` as a self-map of `C([0,T];H)` while its
  formula uses `ẋ`; Foundation's `integralMap` is the honest *pointwise*
  version, taking the derivative `dx` as a separate argument and returning the
  value at `t`.  The fixed-point reading used in Section 7 is provided instead
  by the derivative-free centered form of `def_10`. -/
recall integralMap

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
