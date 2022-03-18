import Rings.ToMathlib.fol
import set_theory.cardinal
import completeness
import language_extension

universe u

open fol

namespace fol

open_locale cardinal fol

variables {L : Language.{u}} {T : Theory L}

theorem compactness' : is_consistent T ↔
  ∀ fs : finset (sentence L), ↑fs ⊆ T → is_consistent (↑fs : Theory L) :=
begin
  split,
  { simp only [model_existence],
    rintros ⟨ M , hM0 , hMT ⟩ fs hfsT,
    exact ⟨ M , hM0 , all_realize_sentence_of_subset hMT hfsT ⟩},
  { intros h hbot,
    rw theory_proof_compactness_iff at hbot,
    obtain ⟨ fs , hfsbot , hfsT ⟩ := hbot,
    exact h fs hfsT hfsbot},
end

namespace Language

variables (L) (α : Type u)

@[reducible] def of_constants : Language :=
{ functions := λ n, match n with | 0 := α | (n+1) := pempty end,
  relations := λ _, pempty }

def of_constants.to_term (x : α) : bounded_term (of_constants α) 0 :=
bd_const x

end Language

variables {α : Type u}

def distinct_constants : Theory (Language.of_constants α) :=
set.image (λ x , ∼ (bd_const (prod.fst x) ≃ bd_const x.snd)) { x : α × α | x.fst ≠ x.snd }

open Language Lhom

def add_distinct_constants : Theory $ L.sum (of_constants α) :=
Theory_induced Lhom.sum_inr distinct_constants



/-- Theories with big models have arbitrarily large models -/
lemma has_sized_model_of_has_infinite_model {T : Theory L} {κ : cardinal}
(hκ : max (#(L.functions 0)) cardinal.omega ≤ κ) :
(Σ' M : Structure L, nonempty M ∧ M ⊨ T ∧ infinite M) →
Σ' M : Structure L, nonempty M ∧ M ⊨ T ∧ κ ≤ #M :=
begin
  rintro ⟨ M , hM0, hMT, hMinf ⟩,
  sorry

end

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

