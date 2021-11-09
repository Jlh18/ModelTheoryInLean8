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

universes u v v0


section nttn


@[simp] def algebra.image
  (K : Type u) (L : Type v) [comm_semiring K] [semiring L] [algebra K L] : set L :=
set.range (algebra_map K L)

@[simp] def subfield_generated
  (K : Type u) {L : Type v} [field K] [field L] [algebra K L] (S : set L)
  : subfield L :=
subfield.closure (S ∪ algebra.image K L)

namespace subfield_generated

variables
  (K : Type*) {L : Type*} [field K] [field L] [algebra K L] (S : set L)

lemma subset_closure_set : S ⊆ subfield_generated K S :=
begin
  intros _ hs,
  simp only [subfield_generated, set_like.mem_coe],
  apply subfield.subset_closure,
  left,
  exact hs,
end

lemma subset_closure_base (a : K) : algebra_map K L a ∈ subfield_generated K S :=
begin
  simp only [subfield_generated, set_like.mem_coe],
  apply subfield.subset_closure,
  right,
  simp only [set.mem_range_self, algebra.image]
end

@[simp] def ring_hom : K →+* subfield_generated K S :=
⟨
  (λ a, ⟨ algebra_map K L a , subset_closure_base K S a⟩ ),
  begin simp only [ring_hom.map_one], refl end,
  begin intros, simp only [ring_hom.map_mul], refl end,
  begin simp only [ring_hom.map_zero], refl end,
  begin intros, simp only [ring_hom.map_add], refl end
⟩

instance has_scalar : has_scalar K (subfield_generated K S) :=
⟨ λ a r, (ring_hom K S a) * r ⟩
-- #check algebra

@[simp] instance algebra : algebra K (subfield_generated K S) :=
⟨
  ring_hom K S ,
  λ r, field.mul_comm (ring_hom K S r),
  (λ r x, rfl) ,
⟩

@[simp] noncomputable def eval {n : ℕ} (as : fin n → L) (has : Π k, as k ∈ S) :
  mv_polynomial (fin n) K →+* subfield_generated K S :=
  mv_polynomial.eval₂_hom (algebra_map K (subfield_generated K S))
    (λ k, ⟨ as k , subfield_generated.subset_closure_set K S (has k) ⟩)

lemma eval_proj {n : ℕ} (as : fin n → L) (has : Π k, as k ∈ S) (p : mv_polynomial (fin n) K) :
  ((subfield_generated.eval K S as has) p).val
    = mv_polynomial.eval as (p : mv_polynomial (fin n) L) :=
-- lemma eval_proj {n : ℕ} (as : fin n → L) (has : Π k, as k ∈ S) (p : mv_polynomial (fin n) K) :
--   ((subfield_generated.eval K S as has) p).val
--     = mv_polynomial.eval as (mv_polynomial.map (algebra_map K L) p) :=
-- mv_polynomial.induction_on p _ _ _

@mv_polynomial.induction_on K (fin n) _
  (λ q, ((subfield_generated.eval K S as has) q).val
    = mv_polynomial.eval as (q : mv_polynomial (fin n) L))
  p
(begin
  intro a,
  simp only [eval, mv_polynomial.map_C, mv_polynomial.eval_C, ring_hom.to_fun_eq_coe,
    mv_polynomial.eval₂_hom_C, subtype.val_eq_coe, algebra_map],
  unfold_coes,
  simpa,
end)
(begin
  intros p q hp hq,
  simp only [eval, mv_polynomial.coe_eval₂_hom, subfield.coe_add, ring_hom.to_fun_eq_coe,
     mv_polynomial.eval₂_add, mv_polynomial.eval_map, subtype.val_eq_coe],
  simp only [eval, mv_polynomial.coe_eval₂_hom, subfield.coe_add, ring_hom.to_fun_eq_coe,
     mv_polynomial.eval₂_add, mv_polynomial.eval_map, subtype.val_eq_coe] at hp hq,
  rw [hp, hq],
  unfold_coes,
  simp,
end)
(begin
  intros p n hp,
  unfold_coes,
  simp only [mv_polynomial.eval_X, eval, subfield.coe_mul, ring_hom.to_fun_eq_coe,
    mv_polynomial.coe_eval₂_hom, subfield_generated,
    mv_polynomial.eval_map, subfield_generated.algebra,
    subtype.coe_mk, mul_eq_mul_right_iff, mv_polynomial.eval₂_X,
    ring_hom.map_mul, subtype.val_eq_coe, mv_polynomial.map_X],
  left,
  unfold_coes at hp,
  simp only [eval, mv_polynomial.coe_eval₂_hom, ring_hom.to_fun_eq_coe,
    mv_polynomial.eval_map, subtype.val_eq_coe] at hp,
  exact hp,
end)

end subfield_generated

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

-- #check @mv_polynomial.map_injective
-- -- mv_polynomial.eval₂ polynomial.C bs (⇑(mv_polynomial.map (subfield_generated.ring_hom K B)) f)

-- #check @ring_hom.injective

-- #check @mv_polynomial.eval₂

-- #check mv_polynomial.eval₂_zero
-- --
-- #check polynomial.as_sum_range

lemma mv_polynomial.zero_iff {K : Type u} {R : Type v} {σ : Type v0} [field K] [comm_semiring R]
  [nontrivial R] (f : K →+* R) (p : mv_polynomial σ K) : p = 0 ↔ mv_polynomial.map f p = 0 :=
begin
  split,
  {intro hp, rw hp, simp,},
  {
    intro hp,
    apply mv_polynomial.map_injective f (ring_hom.injective f),
    simpa using hp,
  },
end

-- #check mv_polynomial.fin_succ_equiv

-- #check mv_polynomial.eval₂

-- #check mv_polynomial.mv_polynomial_equiv_mv_polynomial

lemma insert_dependent_to_is_algebraic_aux {n : ℕ} {S : set L} {a : L} :
  (∃ (p : mv_polynomial (fin n.succ) K) (as : fin n.succ → L) (has : ∀ (k : fin n.succ), as k ∈ S ∪ {a})
    (hp : (mv_polynomial.eval as) p = 0), p ≠ 0)
  →
  (∃ (p : polynomial (mv_polynomial (fin n) K)) (as : fin n → L)
    (has : ∀ (k : fin n), as k ∈ S)
    (hp : (polynomial.aeval a) (polynomial.map (subfield_generated.eval K S as has) p) = 0), p ≠ 0) :=
sorry

-- should really be iff
lemma insert_dependent_to_is_algebraic (S : set L) (hS : indep K S) (a : L) :
  ¬ indep K (S ∪ {a}) → is_algebraic (subfield_generated K S) a :=
begin
  intro hdep,
  simp only [indep, not_forall] at hdep,
  cases hdep with n hdep,
  cases n,
  {
    cases hdep with f hdep,
    cases hdep with as hdep,
    cases hdep with has hdep,
    cases hdep with hf hf0,
    exfalso,
    apply hf0,
    have h := mv_polynomial.is_empty fin.is_empty (f : mv_polynomial (fin 0) L) as,
    rw (congr_arg (@mv_polynomial.C L (fin 0) _) hf) at h,
    simp only [mv_polynomial.C_0] at h,
    rw mv_polynomial.zero_iff (algebra_map K L) f,
    exact h,
  },
  {
    have hf := insert_dependent_to_is_algebraic_aux K hdep,
    cases hf with f hf,
    cases hf with as hf,
    cases hf with has hf,
    cases hf with hf hf0,
    -- evaluate f at the terms in S to produce a polynomial in K(S)[X]
    -- (subfield_generated.eval K S as has) : mv_polynomial (fin n) K →+* subfield_generated K S
    use polynomial.map (subfield_generated.eval K S as has) f,
    split,
    {
      intro hp,
      apply hf0,
      apply polynomial.ext,
      intro m,
      rw polynomial.coeff_zero,
      rw polynomial.ext_iff at hp,
      have hpm := hp m,
      rw polynomial.coeff_zero at hpm,
      rw polynomial.coeff_map at hpm,
      -- we use that S is independent to show each `f.coeff m` is 0 ~ they evaluate to 0 via
      -- elements of S
      apply hS n (f.coeff m) as has,
      -- it remains to show that evaluating at `as` in K(S) is the same as evaluating at `as` in L
      rw ← subfield_generated.eval_proj K S as has (f.coeff m),
      rw hpm,
      simp only [subfield.coe_zero, subtype.val_eq_coe],
    },
    {exact hf,},
  },
end

-- lemma insert_dependent_iff_is_algebraic (S : set L) (a : L) :
--   ¬ indep K (S ∪ {a}) → is_algebraic (subfield_generated K S) a :=
-- begin
--   intro hdep,
--   simp only [indep, not_forall] at hdep,
--     cases hdep with n hdep,
--     cases hdep with f hdep,
--     cases hdep with as hdep,
--     cases hdep with has hdep,
--     cases hdep with hf hf0,
--     let bs : fin n → polynomial (subfield_generated K S) :=
--     λ k, @decidable.by_cases (as k ∈ S) (polynomial (subfield_generated K S)) _
--       (λ h, polynomial.C
--         (⟨ as k , subfield_generated.subset_closure_set K S h ⟩ : subfield_generated K S))
--       (λ _, polynomial.X),
--     let p : polynomial (subfield_generated K S) :=
--       mv_polynomial.eval₂ polynomial.C bs
--       (mv_polynomial.map (subfield_generated.ring_hom K S) f),
--     use p,
--     split,
--     {
--       intro hp,
--       apply hf0,
--       rw mv_polynomial.zero_iff (subfield_generated.ring_hom K S),

--       sorry,
--     },
--     {
--       simp only [p],
--       rw ← hf,
--       simp,
--       sorry,
--     },
-- end

lemma algebraic_over_basis (B : set L) (hB : basis K B) :
  algebra.is_algebraic (subfield_generated K B) L :=
begin
  intro x,
  by_cases hind : indep K (B ∪ {x}),
  {
    -- if B ∪ {x} is independent then x ∈ B since B is a basis
    have hBx := hB.2 (B ∪ {x}) hind (by simp),
    -- hence x ∈ K(B) and is independent over K(B)
    have hxBx : x ∈ subfield_generated K B,
    {apply subfield.subset_closure, left, rw ← hBx, right, exact set.mem_singleton x},
    apply is_algebraic_subfield hxBx,
  },
  {
    apply insert_dependent_to_is_algebraic K B hB.1 x hind,
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
