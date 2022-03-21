import Rings.ToMathlib.fol
import set_theory.cardinal
import completeness
import language_extension

universes u v

open fol

namespace fol

open_locale cardinal fol

variables {L : Language.{u}} {T : Theory L}

def Structure.constants (S : Structure L) (c : L.constants) : S :=
Structure.fun_map S c dvector.nil

namespace Lhom

variables {L' : Language.{u}} {ϕ : L →ᴸ L'}

/-- restatement of `Lhom.reduct_all_ssatisfied` -/
def reduct_Theory_induced {S : Structure L'} {T : Theory L} (hϕ : ϕ.is_injective)
  (h : S ⊨ Theory_induced ϕ T) : S[[ϕ]] ⊨ T :=
reduct_all_ssatisfied hϕ h

namespace sum

lemma is_injective_inl : (@Lhom.sum_inl L L').is_injective :=
{ on_function := λ n x y hxy, sum.inl.inj hxy,
  on_relation := λ n x y hxy, sum.inl.inj hxy, }

lemma is_injective_inr : (@Lhom.sum_inr L L').is_injective :=
{ on_function := λ n x y hxy, sum.inr.inj hxy,
  on_relation := λ n x y hxy, sum.inr.inj hxy, }

end sum
end Lhom

/-- A version of compactness theorem: a theory is consistent (a.k.a satisfiable)
  if and only if it is finitely consistent -/
theorem compactness' : is_consistent T ↔
  ∀ fs : finset (sentence L), ↑fs ⊆ T → is_consistent (↑fs : Theory L) :=
begin
  split,
  { rintros hT fs hfsT ⟨hbot⟩,
    exact hT ⟨sweakening hfsT hbot⟩ },
  { intros h hbot,
    rw theory_proof_compactness_iff at hbot,
    obtain ⟨ fs , hfsbot , hfsT ⟩ := hbot,
    exact h fs hfsT hfsbot },
end

namespace Language

variables (L) (α : Type u)

/-- The language with `α` indexing its constant symbols and nothing else -/
@[reducible] def of_constants : Language :=
{ functions := λ n, match n with | 0 := α | (n+1) := pempty end,
  relations := λ _, pempty }

/-- Making terms out of constant symbols in `fol.Language.of_constants` -/
def of_constants.to_term (x : α) : bounded_term (of_constants α) 0 :=
bd_const x

end Language

variables (α : Type u)

/-- The theory that says there are `α` many distinct constants -/
@[reducible] def distinct_constants : Theory (Language.of_constants α) :=
set.image (λ x , ∼ (bd_const (prod.fst x) ≃ bd_const x.snd)) { x : α × α | x.fst ≠ x.snd }

open Language Lhom

/-- The `(L + of_constants α)`-theory induced from `fol.distinct_constants` -/
def add_distinct_constants : Theory $ L.sum (of_constants α) :=
Theory_induced Lhom.sum_inr $ distinct_constants _

def all_realize_sentence_distinct_constants (M : Structure _) (hM : M ⊨ distinct_constants α) :
  #α ≤ #M :=
begin
  rw all_realize_sentence_image at hM,
  have hf : function.injective (λ a, M.constants a),
  { intros x y hfxy,
    by_cases hxy : x = y, exact hxy,
    exfalso, apply hM ⟨x,y⟩ hxy,
    simp only [Structure.constants] at hfxy,
    simp [bd_const, hfxy] },
  apply cardinal.mk_le_of_injective hf,
end

/-- Theories with big models have arbitrarily large models (lower bound to cardinality) -/
lemma has_sized_model_of_has_infinite_model_lower {T : Theory L} {κ : cardinal}
(hκ : max (#(L.functions 0)) cardinal.omega ≤ κ) :
(∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ infinite M) →
∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ κ ≤ #M :=
begin
  rintro ⟨ M , hM0, hMT, hMinf ⟩,
  set Tκ := (Theory_induced Lhom.sum_inl T : Theory $ L.sum (of_constants κ.out))
    ∪ add_distinct_constants κ.out with hTκ,
  have hTκ_consis : is_consistent Tκ,
  { rw compactness',
    intros fs hfsTκ,
    rw model_existence,
    rw hTκ at hfsTκ,
    classical,
    obtain ⟨fT, f_of_constants, hfs, hfT, hf_of_constants⟩ := finset.subset_union_elim hfsTκ,
    sorry,

  }, -- by compactness'
  rw model_existence at hTκ_consis,
  obtain ⟨ M , hM0, hMTκ ⟩ := hTκ_consis,
  rw hTκ at hMTκ,
  rw all_realize_sentence_union at hMTκ,
  refine ⟨ ( M[[(Lhom.sum_inl : L →ᴸ L.sum (of_constants κ.out))]] ), (by simp [hM0]),
    Lhom.reduct_Theory_induced Lhom.sum.is_injective_inl hMTκ.1 , _ ⟩,
  have hMκ := Lhom.reduct_Theory_induced Lhom.sum.is_injective_inr hMTκ.2,
  have hM := all_realize_sentence_distinct_constants κ.out _ hMκ,
  simp only [reduct_coe, cardinal.mk_out κ] at *,
  exact hM,
end

/-- Theories with big models have arbitrarily large models -/
lemma has_sized_model_of_has_infinite_model {T : Theory L} {κ : cardinal}
(hκ : max (#(L.functions 0)) cardinal.omega ≤ κ) :
(∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ infinite M) →
∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ #M = κ :=
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
  obtain ⟨ M' , hM'0 , hM' , hMcard ⟩ := has_sized_model_of_has_infinite_model hκ
    ⟨
      M , hM0 , hM ,
      hinf ⟨ M , all_realize_sentence_of_subset hM (set.subset_insert _ _) ⟩
    ⟩,
  obtain ⟨ N' , hN'0 , hN' , hNcard ⟩ := has_sized_model_of_has_infinite_model hκ
    ⟨
      N , hN0 , hN ,
      hinf ⟨ N , all_realize_sentence_of_subset hN (set.subset_insert _ _) ⟩
    ⟩,
  have hiso := hcat M' N'
    (all_realize_sentence_of_subset hM' (set.subset_insert _ _))
    (all_realize_sentence_of_subset hN' (set.subset_insert _ _)) hMcard hNcard,
  rw all_realize_sentence_insert at hM' hN',
  rw Language.equiv.realize_sentence _ (classical.choice hiso) at hN',
  exact hN'.1 hM'.1,
end

end fol

