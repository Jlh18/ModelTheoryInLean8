import Rings.Lefschetz
import data.zmod.basic
import field_theory.is_alg_closed.classification

open Lefschetz
open fol
open Fields

namespace fol

open_locale cardinal

variable {L : Language}

/-- Theory T only has infinitely large models -/
def only_infinite (T : Theory L) : Prop :=
∀ (M : Model T), infinite M.1

lemma only_infinite_subset {T₀ T₁ : Theory L} (hsub : T₀ ⊆ T₁) :
only_infinite T₀ → only_infinite T₁ :=
λ hinf M, hinf ⟨ M.1 , all_realize_sentence_of_subset M.2 hsub ⟩

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
∀ (M N : Structure L) (hM : M ⊨ T) (hN : N ⊨ T), #M = κ → #N = κ → M ≃[L] N

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
  rw Language.equiv.realize_sentence _ hiso at hM',
  exact hN'.1 hM'.1,
end

end fol

namespace Lefschetz_current

open_locale fol cardinal

lemma equiv_of_ring_equiv (M N : Structure Rings.ring_signature) (h : M ≃+* N) :
  M ≃[Rings.ring_signature] N := sorry


/-- Two uncountable algebraically closed fields of characteristic zero are isomorphic
if they have the same cardinality. -/
@[nolint def_lemma] lemma ring_equiv_of_cardinal_eq_of_char_zero
  {K L : Type*} [field K] [field L] [is_alg_closed K] [is_alg_closed L]
  [char_zero K] [char_zero L]
  (hK : ω < #K) (hKL : #K = #L) : K ≃+* L := sorry

#check is_alg_closed.ring_equiv_of_cardinal_eq_of_char_zero

lemma categorical_ACF₀ {κ} (hκ : ω < κ) : fol.categorical κ ACF₀ :=
begin
  intros M N hM hN hMκ hNκ,
  apply equiv_of_ring_equiv,
  haveI : field M.1,
  sorry,
  have h : char_zero M.1,
  sorry,
  haveI : is_alg_closed M.1,
  sorry,
  haveI : field N.1,
  sorry,
  have h1 : char_zero N.1,
  sorry,
  haveI : is_alg_closed N.1,
  sorry,
  sorry,
end

open cardinal

lemma omega_lt_aleph_one : ω < aleph 1 := sorry

lemma functions_le_omega : # (Rings.ring_signature.functions 0) ≤ ω := sorry

lemma max_card_functions_omega_le_aleph_one :
max (# (Rings.ring_signature.functions 0)) ω ≤ aleph 1 :=
max_le (functions_le_omega.trans $ omega_le_aleph _) $ omega_le_aleph _

/-- Lefschetz part 1. Any sentence or its negation can be deduced in ACF₀-/
theorem is_complete'_ACF₀ : is_complete' ACF₀ :=
fol.is_complete'_of_only_infinite_of_categorical
    instances.algebraic_closure_of_rat
    instances.algebraic_closure_of_rat_models_ACF₀ -- ℚ̅ is a model of ACF₀
    (fol.only_infinite_subset ACF_subset_ACF₀ sorry) -- alg closed fields are infinite
    max_card_functions_omega_le_aleph_one -- pick the cardinal κ := aleph 1
    sorry

end Lefschetz_current
