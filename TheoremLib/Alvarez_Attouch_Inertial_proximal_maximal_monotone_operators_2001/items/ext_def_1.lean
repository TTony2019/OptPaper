import Mathlib

namespace AlvarezAttouch2001

variable {H : Type*} [NormedAddCommGroup H]

/-- The extended-real distance from `y` to `C`, with value `+infinity` when `C` is empty. -/
noncomputable def distanceToSet (y : H) (C : Set H) : EReal :=
  sInf ((fun c : H => (‖y - c‖ : EReal)) '' C)

end AlvarezAttouch2001
