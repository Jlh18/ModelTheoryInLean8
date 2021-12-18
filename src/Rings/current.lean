import Rings.Rings
import Rings.Fields
import Rings.ToMathlib.list
import Rings.ToMathlib.nat
import Rings.ToMathlib.fol
import Rings.ToMathlib.mv_polynomial
import Rings.ToMathlib.finset
import Rings.ToMathlib.dvector
import Rings.RealizeThings
import algebra.big_operators.finprod
import data.finset.basic
import Rings.AxGroth

open Rings
open AxGroth

noncomputable theory

lemma Ax_Groth_surj_aux
  {n d : ℕ}
  (h0 : char_zero K)
  (ps : poly_map_data K n)
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d)
  (hSurj : @realize_bounded_formula _ (struc_to_ring_struc.Structure K)
    _ _ (@poly_map_data.coeffs_dvector' K _ n d ps)
    (surj_formula n d) dvector.nil) :
  function.surjective (poly_map ps)
  :=
begin
  simp only [surj_formula,
    realize_bounded_formula_bd_alls'
    ] at hSurj,
  sorry,
end
