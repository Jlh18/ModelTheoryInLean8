import set_theory.cardinal
import fol
import completeness
import Rings.Notation
import Rings.ToMathlib.fol

namespace fol
open_locale cardinal

variables {L : Language} {T : Theory L}
  [hcompl : fact (is_complete T)]

include hcompl

instance equality_of_constants : setoid L.constants :=
{ r := λ c d, (bd_const c ≃ bd_const d) ∈ T,
  iseqv :=
  begin
    have hconsis := hcompl.1.1,
    have hcompl1 := hcompl.1,
    obtain ⟨ M , hM0 , hMT ⟩ := (model_existence _).1 hconsis,
    repeat {split},
    { intro c,
      apply or.resolve_right (hcompl1.2 (bd_const c ≃ bd_const c)),
      intro hmem,
      specialize hMT hmem,
      apply hMT,
      simp },
    { intros c d hcd,
      apply or.resolve_right (hcompl1.2 (bd_const d ≃ bd_const c)),
      intro hmem,
      apply hMT hmem,
      specialize hMT hcd,
      simp only [realize_sentence_equal, realize_closed_term] at hMT,
      simp [hMT] },
    { intros c d e hcd hde,
      apply or.resolve_right (hcompl1.2 (bd_const c ≃ bd_const e)),
      intro hmem,
      apply hMT hmem,
      have Hcd := hMT hcd,
      have Hde := hMT hde,
      simp only [realize_sentence_equal, realize_closed_term] at Hcd Hde,
      simp [Hcd, Hde] },
  end }

namespace bounded_model_of_infinite_model

variables (T)

def M := @quotient L.constants (@fol.equality_of_constants _ T _)

variables [hwit : fact (has_enough_constants T)]
include hwit

lemma fun_map_on_L_constants : Π {n : ℕ} (f : L.functions n) (xs : dvector L.constants n),
  ∃ c : L.constants,
  (bd_equal (bd_apps (bd_func f) (dvector.map bd_const xs)) (bd_const c)) ∈ T :=
λ n f xs, classical.choice
begin
  obtain ⟨ M , hM0 , hMT ⟩ := (model_existence _).1 hcompl.1.1,
  set ϕ := (bd_apps (bd_func f) (dvector.map bd_const xs) ≃ x_ 0) with hϕ,
  have hex : bd_ex ϕ ∈ T,
  { apply or.resolve_right (hcompl.1.2 _),
    intro hmem,
    set x := realize_bounded_term (dvector.nil : dvector M 0)
      (bd_apps (bd_func f) (dvector.map bd_const xs)) dvector.nil with hx,
    have hbot := hMT hmem,
    simp only [realize_bounded_term, realize_sentence_not, realize_bounded_formula, realize_sentence_ex, dvector.nth, fin.val_zero',
      not_exists] at hbot,
    apply hbot x,
    simpa [realize_bounded_term_bd_apps, hx] },
  cases hwit.1 with w hw,
  split,
  use w ϕ,
  apply or.resolve_right (hcompl.1.2 _),
  intro hmem,
  have hbot := hMT hmem,
  simp at hbot, -- fix
  apply hbot,
  sorry
  -- specialize hw ϕ,
  -- rw completeness at hw,
  -- have hMϕ := hw hM0 hMT,
  -- simp at hMϕ, --FIX


end

/-- The map on functions uses choice twice, once to find representatives from the
  quotient terms, once to find constant a symbol using witness property / henkin / enough constants
-/
noncomputable def fun_map_on_M : Π {n : ℕ}, L.functions n → dvector (M T) n → M T :=
λ n f xs, quotient.mk (fun_map_on_L_constants T f (dvector.map quotient.out xs)).some

variable [L.is_algebraic]

noncomputable def bounded_model_of_infinite_model.model :
  Structure L :=
{ carrier := M T,
  fun_map := λ _, fun_map_on_M T,
  rel_map := λ _ r, false.elim $ Language.is_algebraic.empty_relations _ r }

end bounded_model_of_infinite_model

/-- If a theory `T` is complete (i.e. maximal) and consistent
  then `T` has a model `M` with `#M ≤ |constant symbols of the language|` -/
theorem bounded_model_of_infinite_model :
  ∃ M : Structure L, M ⊨ T ∧ #M ≤ #L.constants :=
begin
  sorry

end


#check Language.constants

end fol
