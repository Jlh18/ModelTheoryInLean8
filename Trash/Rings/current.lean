import Rings.Lefschetz

open Lefschetz
open fol
open Fields


namespace fol

variable {L : Language}

def no_finite_model (T : Theory L) : Prop :=
∀ (M : Model T), infinite M.1


end fol

namespace Lefschetz_current

/-- Lefschetz part 1. Any sentence or its negation can be deduced in ACF₀-/
theorem is_complete'_ACF₀ : is_complete' ACF₀ :=
begin
  sorry
end

end Lefschetz_current
