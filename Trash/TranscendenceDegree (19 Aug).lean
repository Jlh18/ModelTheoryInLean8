import ring_theory.algebraic
-- import data.finset
-- import algebra.field
-- import field_theory.subfield
import field_theory.algebraic_closure
-- import order.zorn
import Rings.ToMathlib
-- import data.mv_polynomial.equiv
-- import data.equiv.fin

open classical
local attribute [instance] prop_decidable

universes u v


section nttn

variables
  (K : Type u)

@[simp] def algebra.image (L : Type v) [comm_semiring K] [semiring L] [algebra K L] : set L :=
set.range (algebra_map K L)

@[simp] def subfield_generated {L : Type v} [field K] [field L] [algebra K L] (S : set L)
  : subfield L :=
subfield.closure (S ∪ algebra.image K L)

lemma subfield_generated.subset_closure
  {K : Type u} {L : Type v} [field K] [field L] [algebra K L] {S : set L} :
  S ⊆ subfield_generated K S :=
begin
  intros _ hs,
  simp only [algebra.image, subfield_generated, set_like.mem_coe],
  apply subfield.subset_closure,
  left,
  exact hs,
end

end nttn

namespace transcendent

variables
  (K : Type u) {L : Type u} [field K] [field L] [algebra K L]

def indep (S : set L) : Prop :=
Π (n : ℕ) (f : mv_polynomial (fin n) K) (as : fin n → L),
(Π k, as k ∈ S) → mv_polynomial.eval as (f : mv_polynomial (fin n) L) = 0 → f = 0

lemma indep_subset (S T : set L) (hST : S ⊆ T) : indep K T → indep K S :=
begin
  intros hT _ f as has hf,
  have has' : Π k, as k ∈ T := λ k, hST (has k),
  exact hT _ f as has' hf,
end


lemma indep_empty : indep K (∅ : set L)
| nat.zero f as has hf :=
begin
  apply @mv_polynomial.map_injective K L (fin 0) _ _ (algebra_map K L) (ring_hom.injective _),
  simp,
  rw mv_polynomial.is_empty (fin.is_empty) (mv_polynomial.map (algebra_map K L) f) as,
  rw ← mv_polynomial.C_0,
  rw (mv_polynomial.C_inj L),
  rw ← hf,
  simp only [mv_polynomial.eval, mv_polynomial.eval_map],
  unfold_coes,
end
| (nat.succ n) f as has hf :=
begin
  exfalso,
  rw ← set.mem_empty_eq (as 0),
  {apply has},
end

lemma indep_sUnion_chain {c : set (set L)} (hchain : zorn.chain has_subset.subset c)
  (h0 : c.nonempty)
  (hc : Π (S : set L) (hS : S ∈ c), indep K S) :
  indep K ⋃₀ c :=
begin
  intros k f as has hf,
  cases zorn.fin_range_sub_mem_chain_of_sub_union hchain h0 as has with S hS,
  cases hS with hSc hS,
  apply hc S hSc _ _ as _ hf,
  exact hS,
end

def basis (B : set L) : Prop := indep K B ∧ Π (S : set L), indep K S → B ⊆ S → S = B

lemma extend_to_basis_aux (S : set L) (hindS : indep K S) :
  ∃ (B : set L) (H : B ∈ {T : set L | S ⊆ T ∧ indep K T}),
  S ⊆ B ∧ Π (T : set L), T ∈ {T : set L | S ⊆ T ∧ indep K T} → B ⊆ T → T = B :=
(@zorn.zorn_subset_nonempty L { T : set L | S ⊆ T ∧ indep K T }
  (λ c hcsub hchain hc0,
    ⟨
      -- the upper bound by taking union
      ⋃₀ c ,
      ⟨
        let hScup : S ⊆ ⋃₀ c :=
        begin
          cases hc0 with T hT,
          cases hcsub hT with hST hand,
          have hTcup : T ⊆ ⋃₀ c := λ t ht , ⟨ T , hT , ht ⟩,
          exact set.subset.trans hST hTcup,
        end in
        ⟨ -- the upper bound is in the set
          hScup ,
          indep_sUnion_chain K hchain hc0 (λ S hs, (hcsub hs).2)
        ⟩ ,
        (λ S hS s hs, ⟨ S , hS , hs ⟩) -- showing the maximal element is in the set
      ⟩
    ⟩
  )
  S -- give U for the set being non-empty
  ⟨ set.subset.refl _ , hindS ⟩)

#check is_algebraic_algebra_map

lemma subfield_mem (a : L) (K : subfield L) (haK : a ∈ K) :
  a = algebra_map K L (⟨ a , haK ⟩ : K) := rfl

lemma is_algebraic_subfield {a : L} {K : subfield L} (haK : a ∈ K) : is_algebraic K a :=
⟨
  polynomial.X - polynomial.C (⟨ a , haK ⟩ : K) ,
  polynomial.X_sub_C_ne_zero _ ,
  begin
    simp only [polynomial.aeval_X, polynomial.aeval_C, alg_hom.map_sub],
    rw ← subfield_mem a K haK,
    simp,
  end
⟩

#check ite

lemma algebraic_over_basis (B : set L) (hB : basis K B) :
  algebra.is_algebraic (subfield_generated K B) L :=
begin
  intro x,
  by_cases hind : indep K (B ∪ {x}),
  {
    have hBx := hB.2 (B ∪ {x}) hind (by simp),
    have hxBx : x ∈ subfield_generated K B,
    {apply subfield.subset_closure, left, rw ← hBx, right, exact set.mem_singleton x},
    apply is_algebraic_subfield hxBx,
  },
  {
    simp only [indep, not_forall] at hind,
    cases hind with n hind,
    cases hind with f hind,
    cases hind with as hind,
    cases hind with has hind,
    cases hind with hf hf0,
    have bs : fin n → polynomial (subfield_generated K B) :=
    λ k, @decidable.rec_on (as k ∈ B) (λ k, polynomial (subfield_generated K B)) _
      (λ _, polynomial.X)
      (λ h, polynomial.C (⟨ as k , subfield_generated.subset_closure h ⟩ : subfield_generated K B)),

    -- have p : polynomial (subfield_generated K B) := mv_polynomial.eval₂ _ _,

  }
end

variables (K) (L)

lemma extend_to_basis (S : set L) (hindS : indep K S) :
    ∃ (B : set L), S ⊆ B ∧ basis K B :=
begin
  cases extend_to_basis_aux K S hindS with B hB,
  cases hB with hmem hB,
  cases hB with hSB hbasis,
  use B,
  split,
  {exact hSB},
  {
    split,
    {exact hmem.2},
    {
      intros T hindT hBT,
      apply hbasis T _ hBT,
      exact ⟨ set.subset.trans hSB hBT , hindT ⟩,
    }
  }
end

lemma basis_ex : ∃ (B : set L), basis K B :=
begin
  cases extend_to_basis K L ∅ (indep_empty K) with B hB,
  use B,
  exact hB.2,
end

lemma basis_some : set L := @classical.some (set L) (λ S, basis K S) (basis_ex K L)

lemma degree : cardinal.{u} := cardinal.mk (basis_some K L)


end transcendent


namespace field_theory

variables
  {K L0 L1 : Type u}
  [field K] [field L0] [field L1]
  [algebra K L0] [algebra K L1]

open transcendent algebra

lemma iso_of_bij_indep (S0 : set L0) (S1 : set L1) :
  indep K S0 → indep K S1 → equiv S0 S1 →
  subfield_generated K S0 ≃+* subfield_generated K S1 :=
sorry

lemma iso_of_alg_closed_algebraic
  {K0 K1 L0 L1: Type u} [field K0] [field K1] [field L0] [field L1]
  [is_alg_closed L0] [is_alg_closed L1]
  [algebra K0 L0] [algebra K1 L1] : K0 ≃+* K1 →
  is_algebraic K0 L0 → is_algebraic K1 L1 → L0 ≃+* L1 := sorry

lemma iso_of_alg_closed_of_eq_trans_deg [is_alg_closed L0] [is_alg_closed L1]
  (B0 : set L0) (B1 : set L1) : transcendent.basis K B0 → transcendent.basis K B1 →
  equiv B0 B1
  → L0 ≃+* L1 :=
begin
  intros hB0 hB1 htdeg,
  apply iso_of_alg_closed_algebraic _
  (algebraic_over_basis K B0 hB0)
  (algebraic_over_basis K B1 hB1),
  apply iso_of_bij_indep B0 B1 hB0.1 hB1.1 htdeg,
end



end field_theory
