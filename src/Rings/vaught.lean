import Rings.ToMathlib.fol
import set_theory.cardinal

universe u

open fol

namespace fol

open_locale cardinal fol

variable {L : Language}

/-- Theories with big models have arbitrarily large models -/
lemma has_sized_model_of_has_infinite_model {T : Theory L} {κ : cardinal}
(hκ : max (#(L.functions 0)) cardinal.omega ≤ κ) :
(Σ' M : Structure L, nonempty M ∧ M ⊨ T ∧ infinite M) →
Σ' M : Structure L, nonempty M ∧ M ⊨ T ∧ #M = κ :=
sorry

/-- Vaught's test for showing a theory is complete -/
lemma is_complete'_of_only_infinite_of_categorical
{T : Theory L} (M : Structure L) (hM : M ⊨ T)
(hinf : only_infinite T) {κ : cardinal}
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
    (all_realize_sentence_of_subset hN' (set.subset_insert _ _)) (hcard.trans hNcard) hNcard,
  rw all_realize_sentence_insert at hM' hN',
  rw Language.equiv.realize_sentence _ (classical.choice hiso) at hN',
  exact hN'.1 hM'.1,
end

end fol

