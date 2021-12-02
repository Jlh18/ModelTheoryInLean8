import fol
import Rings.Notation
import Rings.Rings
import field_theory.algebraic_closure

universe u

notation h :: t  := dvector.cons h t
notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

local infix ` ≃ `:64 := fol.bounded_preformula.bd_equal

-- open classical
-- local attribute [instance] prop_decidable


namespace Fields
open fol
open Rings
open Rings.ring_signature

def mul_inv : sentence ring_signature :=
∀' (x_ 1 ≃ 0) ⊔ (∃' x_ 1 * x_ 0 ≃ 1)

def non_triv : sentence ring_signature := 0 ≄ 1

def field_theory : Theory ring_signature := ring_theory ∪ {mul_inv , non_triv}

lemma mul_inv_in_field_theory : mul_inv ∈ field_theory := begin right, left, refl end

lemma non_triv_in_field_theory : non_triv ∈ field_theory :=
begin right, right, exact set.mem_singleton _ end

lemma ring_theory_sub_field_theory : ring_theory ⊆ field_theory :=
begin intros f hf, left, exact hf end

namespace field_to
  variables
    {K : Type u} [field K]

  lemma K_is_field : is_field K := field.to_is_field K

open Rings.models_ring_theory_to_comm_ring

  lemma realize_field_theory :
    (struc_to_ring_struc.Structure K) ⊨ field_theory := -- squeeze_simp, val_zero
  begin
    intros ϕ h,
    cases h,
    {apply (comm_ring_to_model.realize_ring_theory K h)},
    repeat {cases h},
     {
       intro,
       unfold fol.bd_or,
       simp only [realize_one, ring_signature.mul, struc_to_ring_struc.func_map,
         fin.val_zero', realize_bounded_formula_not, struc_to_ring_struc.binaries_map,
         fin.val_eq_coe, dvector.last, realize_bounded_formula_ex, realize_bounded_term_bd_app,
         realize_bounded_formula, realize_bounded_term, fin.val_one, dvector.nth,
         realize_zero],
       apply is_field.mul_inv_cancel,
       apply K_is_field,
     },
    {unfold fol.realize_sentence, simp},
  end

  /-- Fields are models of the theory of fields -/
  def models_field_theory : Model field_theory.{u} :=
  ⟨ struc_to_ring_struc.Structure K ,  realize_field_theory ⟩

end field_to

namespace models_theory_of_fields_to_is_field

  variables {M : Structure ring_signature} (h : M ⊨ field_theory)
  -- M inherits instances of 0 1 - + * from Rings.ModelTo

  include h

  lemma ring_model : M ⊨ ring_theory :=
  begin
    intros f hf,
    apply h,
    apply ring_theory_sub_field_theory,
    exact hf
  end

  instance comm_ring : comm_ring M :=
  models_ring_theory_to_comm_ring.comm_ring (ring_model h)

  instance ring : ring M := @comm_ring.to_ring M (models_theory_of_fields_to_is_field.comm_ring h)

  lemma zero_ne_one : (0 : M) ≠ 1 := by simpa using (h non_triv_in_field_theory)

  lemma mul_inv (a : M) (ha : a ≠ 0) : (∃ (b : M), a * b = 1) :=
  let hmulinv := h mul_inv_in_field_theory in by simpa using hmulinv a ha

  lemma is_field : @is_field M (models_theory_of_fields_to_is_field.ring h) :=
  begin
    split,
    {exact ⟨ 0 , 1 , zero_ne_one h ⟩},
    {exact (models_theory_of_fields_to_is_field.comm_ring h).mul_comm},
    {exact mul_inv h},
  end
  -- ⟨
  --   ⟨ 0 , 1 , zero_ne_one ⟩,
  --   models_ring_theory_to_comm_ring.mul_comm,
  --   mul_inv
  -- ⟩
  noncomputable instance field : field M :=
  @is_field.to_field M (models_theory_of_fields_to_is_field.ring h)
  (models_theory_of_fields_to_is_field.is_field h)

end models_theory_of_fields_to_is_field

/-- GenPoly n is the polynomial aₙ₊₁ xⁿ + ⋯ + a₂ x + a₁
 where aₖ = x_ k and x = x_ 0, i.e. we are seeing the variables x_ k with 0 < k as coefficients
 and x_ 0 as the indeterminate -/
@[simp] def gen_poly : Π (n : ℕ), bounded_term ring_signature (n + 2)
| 0       := x_ 1
| (n + 1) := (x_ (fin.succ n.succ)) * ((x_ 0) ^ (n + 1)) +
  bounded_preterm.lift_succ (gen_poly n)

/-- Adds a monic term at the beginning of gen_poly.
 We will require that these polynomials have solutions for `algebraically closed`.
 We cannot just use gen_poly as we need the polynomials to have 0 < deg -/
@[simp] def gen_monic_poly (n : ℕ) : bounded_term ring_signature (n + 2) :=
(x_ 0) ^ (n + 2) + gen_poly n

section poly_lemmas

variables {A : Type u} [hcomm : comm_ring A] [hnt : nontrivial A] [hde : decidable_eq A]

include hcomm hnt hde

/-- xᵐ has degree m -/
lemma deg_pow {n m : ℕ} {as : dvector A (n + 1)} :
(polynomial.term_evaluated_at_coeffs as (x_ 0 ^ m)).degree = m :=
begin
  rw polynomial.term_evaluated_at_coeffs_pow,
  apply polynomial.degree_X_pow,
end

/-- degree of gen_poly n < n + 1 -/
lemma gen_poly_degree : Π {n} {as : dvector A (n + 1)},
  (polynomial.term_evaluated_at_coeffs as (gen_poly n)).degree < n.succ
| nat.zero as :=
begin
  simp only [gen_poly],
  have h : polynomial.term_evaluated_at_coeffs as x_ 1 = polynomial.C (as.nth' 0),
  {rw ← polynomial.term_evaluated_at_coeffs_coeff, simp,},
  rw h,
  by_cases h0 : as.nth' 0 = 0,
  {
    rw h0,
    rw polynomial.C_0,
    rw polynomial.degree_zero,
    exact dec_trivial,
  },
  {
    rw polynomial.degree_C h0,
    exact dec_trivial,
  }
end
| (nat.succ n) as :=
begin
  simp only [gen_poly, polynomial.term_evaluated_at_coeffs_add],
  rw polynomial.term_evaluated_at_coeffs_monomial,
  rw polynomial.lift_succ_remove_last,
  -- have am : dvector A n.succ := dvector.remove_mth (n + 2) as,
  apply has_le.le.trans_lt (polynomial.degree_add_le _ _),
  apply max_lt,
  {
    apply has_le.le.trans_lt (polynomial.degree_monomial_le _ _),
    exact with_bot.succ_lt_succ_succ,
  },
  {
    apply lt_trans (@gen_poly_degree n (dvector.remove_mth (n.succ + 2) as)),
    exact with_bot.succ_lt_succ_succ,
  },
end

/-- gen_monic_poly has non-zero degree -/
lemma gen_monic_poly_non_const {n} {as : dvector A (n + 1)} :
  polynomial.degree (polynomial.term_evaluated_at_coeffs as (gen_monic_poly n)) ≠ 0 :=
begin
  unfold gen_monic_poly,
  apply ne_of_gt,
  have hp : (polynomial.term_evaluated_at_coeffs as (x_ 0 ^ (n + 2))).degree = n + 2,
  {apply deg_pow},
  have hq : (polynomial.term_evaluated_at_coeffs as (gen_poly n)).degree < n + 2,
  {
    apply lt_trans gen_poly_degree,
    exact with_bot.succ_lt_succ_succ,
    exact hnt, -- why??
    exact hde, -- why??
  },
  have hle : (polynomial.term_evaluated_at_coeffs as (gen_poly n)).degree
    < (polynomial.term_evaluated_at_coeffs as (x_ 0 ^ (n + 2))).degree,
  { rw hp, exact hq },
  rw polynomial.term_evaluated_at_coeffs_add,
  rw (polynomial.degree_add_eq_left_of_degree_lt hle),
  rw hp,
  exact dec_trivial,
end

end poly_lemmas

/-- ∀ a₁ ⋯ ∀ aₙ, ∃ x₀, (aₙ x₀ⁿ⁻¹ + ⋯ + a₂ x₀+ a₁ = 0) -/
@[simp] def all_gen_monic_poly_has_root (n : ℕ) : sentence ring_signature :=
fol.bd_alls (n + 1) (∃' gen_monic_poly n ≃ 0)

def ACF : Theory ring_signature := field_theory ∪ (set.range all_gen_monic_poly_has_root)
-- the latter stands for {gen_monic_polyHasSolution n | n : ℕ}

/-- ACF with p = 0 chucked in -/
def ACFₚ (p : ℕ) : Theory ring_signature := set.insert (p ≃ 0) ACF

/-- ACF with p ≠ 0 chucked in for every natural p -/
def ACF₀ : Theory ring_signature := ACF ∪ (set.range (λ p : ℕ, p ≄ 0))

namespace is_alg_closed_to

  variables {K : Type u} [field K] [is_alg_closed K] [decidable_eq K]

  -- should be in the library
  theorem is_alg_closed.exists_root (f : polynomial K) (h : f.degree ≠ 0) :
    ∃ x : K, f.eval x = 0 := polynomial.exists_root_of_splits _ (is_alg_closed.splits f) h

  /-- Algebraically closed fields model the theory ACF-/
  lemma realize_ACF : struc_to_ring_struc.Structure K ⊨ ACF :=
  begin
    intros ϕ h,
    cases h,
    {apply field_to.realize_field_theory h},
    {
      cases h with n hϕ,
      rw ← hϕ,
      unfold all_gen_monic_poly_has_root,
      rw realize_sentence_bd_alls,
      simp only [realize_bounded_formula_ex, realize_bounded_formula,
        models_ring_theory_to_comm_ring.realize_zero, zero],
      intro as,
      have root := is_alg_closed.exists_root
        (polynomial.term_evaluated_at_coeffs as (gen_monic_poly n)) gen_monic_poly_non_const,
      cases root with x hx,
      use x,
      rw polynomial.eval_term_evaluated_at_coeffs_eq_realize_bounded_term at hx,
      exact hx,
    },
  end

end is_alg_closed_to



end Fields

-- #lint
