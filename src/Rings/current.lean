import Rings.Lefschetz
import data.zmod.basic

open Lefschetz
open fol
open Fields

namespace fol

open_locale cardinal

variable {L : Language}

def no_finite_model (T : Theory L) : Prop :=
∀ (M : Model T), infinite M.1

localized "notation A ` ≃[`:25 L `] ` B := L.equiv A B" in fol

namespace Language
namespace equiv

/-- Isomorphic structures realize the same formulas -/
lemma realize_sentence {M N : Structure L} (ϕ : sentence L) :
(M ≃[L] N) → (M ⊨ ϕ ↔ N ⊨ ϕ) := sorry

/-- Isomorphic structures model the same theories -/
lemma all_realize_sentence (M N : Structure L) (T : Theory L) :
(M ≃[L] N) → (M ⊨ T ↔ N ⊨ T) :=
λ H, by simp only [all_realize_sentence, Language.equiv.realize_sentence _ H]

end equiv
end Language

/-- Categoricity states any two models of the same cardinality κ are isomorphic -/
def categorical (κ : cardinal) (T : Theory L) :=
∀ (M N : Structure L) (hM : M ⊨ T) (hN : N ⊨ T), #M = #N → M ≃[L] N

/-- The theory doesn't deduce ϕ ↔ there is a model satisfying its negation -/
lemma not_ssatisfied {T : Theory L} {ϕ : sentence L} :
¬ T ⊨ ϕ ↔ ∃ M : Structure L, nonempty M ∧ M ⊨ set.insert (∼ ϕ) T :=
begin
  simp only [ssatisfied, not_forall, not_imp, all_realize_sentence_insert,
    realize_sentence_not],
  tauto,
end

/-- Theories with big models have arbitrarily large models -/
lemma has_sized_model_of_has_infinite_model {T : Theory L} {κ : cardinal}
(hκ : max (#(L.functions 0)) cardinal.omega ≤ κ) :
(Σ' M : Structure L, nonempty M ∧ M ⊨ T ∧ infinite M) →
Σ' M : Structure L, nonempty M ∧ M ⊨ T ∧ #M = κ :=
sorry

/-- Vaught's test for showing a theory is complete -/
lemma is_complete'_of_no_finite_model_of_categorical
{T : Theory L} (M : Structure L) (hM : M ⊨ T)
(hinf : no_finite_model T) {κ : cardinal}
(hκ : max (#(L.functions 0)) cardinal.omega ≤ κ) (hcat : categorical κ T) :
is_complete' T :=
begin
  intro ϕ,
  by_contra hbot,
  simp only [not_or_distrib, not_ssatisfied] at hbot,
  obtain ⟨ ⟨ M , hM0 , hM ⟩ , ⟨ N , hN0 , hN ⟩ ⟩ := hbot,
  obtain ⟨ M' , hM'0 , hM' , hcard ⟩ := has_sized_model_of_has_infinite_model hκ
    ⟨
      M , hM0 , hM ,
      hinf ⟨ M , all_realize_sentence_of_subset hM (set.subset_insert _ _) ⟩
    ⟩,
  obtain ⟨ N' , hN'0 , hN' , hNcard ⟩ := has_sized_model_of_has_infinite_model hκ
    ⟨
      N , hN0 , hN ,
      hinf ⟨ N , all_realize_sentence_of_subset hN (set.subset_insert _ _) ⟩
    ⟩,
  clear hM0 hM M hN0 hN N,
  rw ← hNcard at hcard,
  have hiso := hcat M' N'
    (all_realize_sentence_of_subset hM' (set.subset_insert _ _))
    (all_realize_sentence_of_subset hN' (set.subset_insert _ _)) hcard,
  rw all_realize_sentence_insert at hM' hN',
  rw Language.equiv.realize_sentence _ hiso at hM',
  exact hN'.1 hM'.1,
end

end fol

namespace Lefschetz_current

/-- Lefschetz part 1. Any sentence or its negation can be deduced in ACF₀-/
theorem is_complete'_ACF₀ : is_complete' ACF₀ :=
begin
  sorry
end

end Lefschetz_current
