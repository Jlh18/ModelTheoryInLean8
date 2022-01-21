import Rings.AxGroth

open AxGroth
open Fields

lemma ACF₀_ssatisfied_Ax_Groth_formula (n d : ℕ) :
  ACF₀ ⊨ Ax_Groth_formula.{0} n d :=
begin
  rw Lefschetz.characteristic_change,
  use 0,
  intros _ _ _,
  apply ACFₚ_ssatisfied_Ax_Groth_formula,
end
