import set_theory.cardinal
import fol
import completeness
import Rings.Notation
import Rings.ToMathlib.fol

noncomputable theory

namespace fol
open_locale cardinal

variables {L : Language}

lemma realize_lift_bounded_term (M : Structure L) {n} :
  Π {l} (t : bounded_preterm L n l) (xs : dvector M n) (v : dvector M l) (a : M),
  realize_bounded_term (dvector.cons a xs) (t ↑ 1) v =
    realize_bounded_term xs t v
| _ (bd_var k) _ _ _ :=
begin
  have hle : 0 ≤ (k : ℕ) := nat.zero_le _,
  dsimp [lift_bounded_term],
  rw [if_pos hle],
  congr',
end
| _ (bd_func f) _ _ _ := by { dsimp only [lift_bounded_term], simp }
| _ (bd_app t s) xs v _ :=
begin
  dsimp only [lift_bounded_term],
  simp only [lift_bounded_term_at, realize_bounded_term_bd_app],
  have hinds := realize_lift_bounded_term s xs,
  rw hinds,
  have hind := realize_lift_bounded_term t xs
    (dvector.cons (realize_bounded_term xs s dvector.nil) v),
  rw hind,
end

/-- The formula that will give rise to a witness for function symbols -/
abbreviation wit_bd_func {n : ℕ} (f : L.functions n) (xs : dvector L.constants n) :
  bounded_formula L 1 := bd_apps (bd_func f) (dvector.map bd_const xs) ≃ x_ 0

-- /-- The formula that will give rise to a witness for terms -/
-- abbreviation wit_bd_preterm {n l} (t : bounded_preterm L n l) (v : dvector ) :
--   bounded_preformula L (n+1) l := bd_equal (lift_bounded_term1 t) x_ 0

/-- The formula that will give rise to a witness for terms -/
abbreviation wit_bd_term (t : bounded_term L 0) :
  bounded_formula L 1 := (lift_bounded_term1 t : bounded_term L 1) ≃ x_ 0

variables (T : Theory L) [hcompl : fact (is_complete T)]

include hcompl

-- namespace is_complete

-- def M : Structure L := classical.some $ (model_existence _).1 hcompl.1.1

-- def hM0 : nonempty (M T) := (classical.some_spec $ (model_existence _).1 hcompl.1.1).1

-- def hMT : (M T) ⊨ T := (classical.some_spec $ (model_existence _).1 hcompl.1.1).2

-- end is_complete

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

def model_carrier := @quotient L.constants (@fol.equality_of_constants _ T _)

variables [hwit : fact (has_enough_constants T)]
include hwit

def w : bounded_formula L 1 → L.constants := classical.some hwit.1

lemma hw : ∀ (f : bounded_formula L 1), T ⊢' (∃' f) ⟹ f[bd_const ((w T) f) /0] :=
classical.some_spec hwit.1

variable {T}

lemma all_realize_wit_of_mem (ϕ : bounded_formula L 1) : (∃' ϕ) ∈ T → T ⊨ ϕ[bd_const (w T ϕ) /0] :=
begin
  intro hmem,
  have hTϕ := hw T ϕ,
  rw completeness at hTϕ,
  intros M hM0 hMT,
  exact hTϕ hM0 hMT (hMT hmem),
end


variable (T)

/-- The action of a function symbol on the set of constant symbols is given by the witness property:
  if `xs` is a list of constant symbols then we take the formula `∃ v, f(xs) = v ∈ T`.
  The witness property gives us `c : L.constants` such that `f(xs) = c ∈ T`.
  Proving these formulas are in `T` repeatedly uses completeness and (hence) consistency of `T`.
-/
abbreviation fun_map_on_L_constants {n : ℕ} (f : L.functions n) (xs : dvector L.constants n) :
  L.constants := w T (wit_bd_func f xs)

lemma fun_map_on_L_constants_all_realize_sentence {n : ℕ} (f : L.functions n)
  (xs : dvector L.constants n) : T ⊨ (wit_bd_func f xs)[bd_const (w T (wit_bd_func f xs)) /0] :=
begin
  obtain ⟨ M , hM0 , hMT ⟩ := (model_existence _).1 hcompl.1.1,
  set x := realize_bounded_term (dvector.nil : dvector M 0)
    (bd_apps (bd_func f) (dvector.map bd_const xs)) dvector.nil with hx,
  apply all_realize_wit_of_mem,
  apply or.resolve_right (hcompl.1.2 _),
  intro hmem,
  have hbot := hMT hmem,
  simp only [realize_bounded_term, realize_sentence_not, realize_bounded_formula,
    realize_sentence_ex, dvector.nth, fin.val_zero', not_exists] at hbot,
  apply hbot x,
  simpa [realize_bounded_term_bd_apps, hx],
end

lemma bd_func_on_L_constants_mem {n : ℕ} (f : L.functions n) (xs : dvector L.constants n) :
  -- T ⊨ (wit_bd_func f xs)[bd_const (w T (wit_bd_func f xs)) /0] →
  ((bd_apps (bd_func f) (dvector.map bd_const xs)) ≃ (bd_const (w T (wit_bd_func f xs)))) ∈ T :=
begin
  obtain ⟨ M , hM0 , hMT ⟩ := (model_existence _).1 hcompl.1.1,
  apply or.resolve_right (hcompl.1.2 _),
  intro hmem,
  have hbot := hMT hmem,
  apply hbot,
  simp [realize_sentence_equal, realize_closed_term, bd_const, realize_bounded_term_bd_apps],
  have hMϕ := fun_map_on_L_constants_all_realize_sentence T f xs hM0 hMT,
  simp [realize_subst_formula0] at hMϕ, -- cannot fix
  convert hMϕ,
  simp [bd_const, realize_bounded_term_bd_apps],
end


/-- The map on functions uses choice twice, once to find representatives from the
  quotient terms, once to find constant a symbol using witness property / henkin / enough constants
  (since `fol.bounded_model_of_infinite_model.w` uses choice)
-/
def fun_map_on_M : Π {n : ℕ}, L.functions n → dvector (model_carrier T) n →
  model_carrier T :=
λ n f xs, quotient.mk (fun_map_on_L_constants T f (dvector.map quotient.out xs))

variable [L.is_algebraic]

def model :
  Structure L :=
{ carrier := model_carrier T,
  fun_map := λ _, fun_map_on_M T,
  rel_map := λ _ r, false.elim $ Language.is_algebraic.empty_relations _ r }

lemma realize_term_all_realize_sentence (t : bounded_term L 0) :
  T ⊨ (wit_bd_term t)[bd_const (w T (wit_bd_term t)) /0] :=
begin
  apply all_realize_wit_of_mem,
  obtain ⟨ M , hM0 , hMT ⟩ := (model_existence _).1 hcompl.1.1,
  apply or.resolve_right (hcompl.1.2 _),
  intro hmem,
  apply hMT hmem,
  simp only [realize_bounded_formula, lift_bounded_term1,
    realize_bounded_term, realize_bounded_formula_ex, dvector.nth, fin.val_zero'],
  use (realize_closed_term M t),
  rw realize_lift_bounded_term,
end

-- lemma realize_bounded_term {n l} (xs : dvector (model T) n) (t : bounded_preterm L n l)
--   (v : dvector (model T) l) :
--   realize_bounded_term xs t v
--   = realize_closed_term (model T) (bd_const (w T (wit_bd_term t))) :=


lemma realize_term' (t : bounded_term L 0) : realize_closed_term (model T) t
  = realize_closed_term (model T) (bd_const (w T (wit_bd_term t))) :=
begin
  sorry
  -- let ϕ := (lift_bounded_term1 t : bounded_term L 1) ≃ -- x_ 0,
  -- have hex : (∃' ϕ) ∈ T,
  -- {
  --   obtain ⟨ M , hM0 , hMT ⟩ := (model_existence _).1 hcompl.1.1,
  --   apply or.resolve_right (hcompl.1.2 _),
  --   intro hmem,
  --   apply hMT hmem,
  --   simp only [realize_bounded_formula, lift_bounded_term1,
  --     realize_bounded_term, realize_bounded_formula_ex, dvector.nth, fin.val_zero'],
  --   use (realize_closed_term M t),
  --   rw realize_lift_bounded_term },
  -- use w T ϕ,
  -- simp only [realize_closed_term],
  -- have hTϕ := all_realize_wit_of_mem ϕ hex,

  -- cases t with k,
  -- { apply fin_zero_elim k },
  -- {
    -- simp [bd_const],
    -- sorry
  -- },
  -- {sorry},
end

lemma realize_sentence_iff (ϕ : sentence L) : model T ⊨ ϕ ↔ ϕ ∈ T :=
begin
  obtain ⟨ M , hM0 , hMT ⟩ := (model_existence _).1 hcompl.1.1,
  cases ϕ,
  { simp only [false_of_satisfied_false, false_iff],
    intro hbot,
    apply hMT hbot },
  {
    simp [realize_sentence_equal, realize_closed_term],
    sorry
  },
  {
    sorry
  },
  {
    sorry
  },
  {
    sorry
  },
  {
    sorry
  },
end

lemma all_realize_sentence : model T ⊨ T :=
begin
  obtain ⟨ M , hM0 , hMT ⟩ := (model_existence _).1 hcompl.1.1,
  intro ϕ,
  cases ϕ,
  { intro hbot,
    exfalso,
    apply hMT hbot },
  {
    intro hmem,
    sorry
  },
  {
    sorry
  },
  {
    sorry
  },
  {
    sorry
  },
  {
    sorry
  },
end

lemma cardinality : #(model T) ≤ #L.constants := sorry

end bounded_model_of_infinite_model

/-- If a theory `T` is complete (i.e. maximal) and consistent
  then `T` has a model `M` with `#M ≤ |constant symbols of the language|` -/
theorem bounded_model_of_infinite_model
  [hwit : fact (has_enough_constants T)] [L.is_algebraic] :
  ∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ #M ≤ #L.constants :=
⟨ bounded_model_of_infinite_model.model T,
    sorry,
    bounded_model_of_infinite_model.all_realize_sentence T ,
    bounded_model_of_infinite_model.cardinality T ⟩


#check Language.constants

end fol
