import fol
import Rings.Notation
import Rings.Rings
import field_theory.algebraic_closure
import Rings.ToMathlib.algebraic_closure

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
open Rings.struc_to_ring_struc

def mul_inv : sentence ring_signature :=
∀' (x_ 1 ≃ 0) ⊔ (∃' x_ 1 * x_ 0 ≃ 1)

def non_triv : sentence ring_signature := 0 ≄ 1

def field_theory : Theory ring_signature := ring_theory ∪ {mul_inv , non_triv}

lemma mul_inv_in_field_theory : mul_inv ∈ field_theory :=
begin right, left, refl end

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
    Structure K ⊨ field_theory := -- squeeze_simp, val_zero
  begin
    intros ϕ h,
    cases h,
    {apply (comm_ring_to_model.realize_ring_theory K h)},
    repeat {cases h},
     {
       intro,
       unfold fol.bd_or,
       simp only [models_ring_theory_to_comm_ring.realize_one,
         ring_signature.mul, struc_to_ring_struc.func_map,
         fin.val_zero', realize_bounded_formula_not,
         struc_to_ring_struc.binaries_map,
         fin.val_eq_coe, dvector.last,
         realize_bounded_formula_ex, realize_bounded_term_bd_app,
         realize_bounded_formula, realize_bounded_term,
         fin.val_one, dvector.nth,
         models_ring_theory_to_comm_ring.realize_zero],
       apply is_field.mul_inv_cancel,
       apply K_is_field,
     },
    { unfold fol.realize_sentence,
      simp only [forall_false_left, ring_signature.one, realize_bounded_formula,
        realize_bounded_term, struc_to_ring_struc.realize_one, func_map, const_map,
        zero_ne_one, struc_to_ring_struc.realize_zero, ring_signature.zero] },
  end

  /-- Fields are models of the theory of fields -/
  def models_field_theory : Model field_theory.{u} :=
  ⟨ Structure K ,  realize_field_theory ⟩

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
| 0       := x_ ⟨ 1 , by exact dec_trivial ⟩
| (n + 1) :=
  (x_ ⟨ n + 2 , add_lt_add_right (nat.lt_succ_self _) _ ⟩)
  * (npow_rec (n + 1) (x_ ⟨ 0 , nat.zero_lt_succ _ ⟩)) +
  bounded_preterm.lift_succ (gen_poly n)

/-- Adds a monic term at the beginning of gen_poly.
 We will require that these polynomials have solutions for `algebraically closed`.
 We cannot just use gen_poly as we need the polynomials to have 0 < deg -/
@[simp] def gen_monic_poly (n : ℕ) : bounded_term ring_signature (n + 2) :=
npow_rec (n + 1) (x_ 0) + gen_poly n

section poly_lemmas

variables {A : Type u} [hcomm : comm_ring A] [hnt : nontrivial A] [hde : decidable_eq A]

include hcomm hnt hde

/-- xᵐ has degree m -/
lemma deg_pow {n m : ℕ} {as : dvector A (n + 1)} :
  (polynomial.term_evaluated_at_coeffs as
    (npow_rec m x_ ⟨ 0 , nat.zero_lt_succ _ ⟩)).degree
  = m :=
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
  have h : polynomial.term_evaluated_at_coeffs as x_ ⟨ 1 , _ ⟩
    = polynomial.C (as.nth' 0),
  {rw ← polynomial.term_evaluated_at_coeffs_coeff, simp only [fin.val_zero'] },
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
  rw polynomial.term_evaluated_at_coeffs_monomial' (nat.lt_succ_self _),
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
  have hp : (polynomial.term_evaluated_at_coeffs as (npow_rec (n + 1) x_ 0)).degree = n + 1,
  {apply deg_pow},
  have hq : (polynomial.term_evaluated_at_coeffs as (gen_poly n)).degree < (n + 1),
  {
    apply lt_of_lt_of_le gen_poly_degree,
    {
      rw le_iff_eq_or_lt,
      left, refl,
    },
    exact hnt, -- why??
    exact hde, -- why??
  },
  have hle : (polynomial.term_evaluated_at_coeffs as (gen_poly n)).degree
    < (polynomial.term_evaluated_at_coeffs as (npow_rec (n + 1) x_ 0)).degree,
  { rw hp, exact hq },
  rw polynomial.term_evaluated_at_coeffs_add,
  rw (polynomial.degree_add_eq_left_of_degree_lt hle),
  rw hp,
  exact dec_trivial,
end

end poly_lemmas

/-- ∀ a₁ ⋯ ∀ aₙ, ∃ x₀, (aₙ x₀ⁿ⁻¹ + ⋯ + a₂ x₀+ a₁ = 0) -/
@[simp] def all_gen_monic_poly_has_root (n : ℕ) :
  sentence ring_signature :=
fol.bd_alls (n + 1) (∃' gen_monic_poly n ≃ 0)

/-- The thoery of algebraically closed fields -/
def ACF : Theory ring_signature :=
field_theory ∪ (set.range all_gen_monic_poly_has_root)
-- the latter stands for {gen_monic_polyHasSolution n | n : ℕ}

/-- The theory of algebraically closed fields of prime characteristic -/

def ACFₚ {p : ℕ} (h : prime p) : Theory ring_signature :=
set.insert (p ≃ 0) ACF

@[reducible] def plus_one_ne_zero (p : ℕ) : sentence ring_signature :=
p + 1 ≄ 0

/-- The theory of algebraically closed fields of characterstic zero -/
def ACF₀ : Theory ring_signature := ACF ∪ (set.range plus_one_ne_zero)

lemma ACF_subset_ACFₚ {p} {h : prime p} : ACF ⊆ ACFₚ h :=
set.subset_insert _ _

lemma ACF_subset_ACF₀ : ACF ⊆ ACF₀ :=
set.subset_union_left _ _

lemma realize_plus_one_ne_zero {M : Structure ring_signature} {p} :
  (M ⊨ plus_one_ne_zero p) ↔ (p.succ : M) ≠ 0 :=
begin
  simp only [plus_one_ne_zero],
  have hrw : add (p : bounded_ring_term 0) one = ↑(p.succ) := rfl,
  rw hrw,
  simp only [bd_notequal, realize_sentence_not,
    realize_sentence_equal, realize_closed_term,
    models_ring_theory_to_comm_ring.realize_nat,
    not_iff_not],
  refl,
end

namespace is_alg_closed_to

variables {K : Type u} [field K] [is_alg_closed K] [decidable_eq K]

open Rings.struc_to_ring_struc

  -- should be in the library
theorem is_alg_closed.exists_root (f : polynomial K) (h : f.degree ≠ 0) :
  ∃ x : K, f.eval x = 0 :=
polynomial.exists_root_of_splits _ (is_alg_closed.splits f) h

/-- Algebraically closed fields model the theory ACF-/
lemma realize_ACF : Structure K ⊨ ACF :=
begin
  intros ϕ h,
  cases h,
  {apply field_to.realize_field_theory h},
  {
    cases h with n hϕ,
    rw ← hϕ,
    simp only [all_gen_monic_poly_has_root, realize_sentence_bd_alls,
      realize_bounded_formula_ex, realize_bounded_formula,
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

lemma realize_ACF₀ [char_zero K] : Structure K ⊨ ACF₀ :=
begin
  simp only [ACF₀, all_realize_sentence_union, all_realize_sentence_range,
    bd_notequal, realize_sentence_not, realize_sentence_equal],
  refine ⟨ realize_ACF , λ n, _ ⟩,
  simp only [realize_plus_one_ne_zero],
  intro hbot,
  have hbot1 : (n.succ : K) = ((0 : ℕ) : K) := hbot,
  have hbot2 := char_zero.cast_injective hbot1,
  exact nat.succ_ne_zero _ hbot2,
end

end is_alg_closed_to

namespace models_ACF_to
noncomputable theory

variables {M : Structure ring_signature} [hM : fact (M ⊨ ACF)]


include hM

instance Field : field M :=
  models_theory_of_fields_to_is_field.field
(begin
  rw [ACF, all_realize_sentence_union] at hM,
  exact hM.1.1,
end)

-- @[reducible] noncomputable def term_evaluated_at_coeffs {n} (as : dvector M n)
--   (t : bounded_ring_term n.succ) : polynomial M :=
-- let σ : fin n.succ → polynomial M :=
-- @fin.cases n (λ _, polynomial M) polynomial.X (λ i, polynomial.C (dvector.nth' as i)) in
-- mv_polynomial.eval σ (mv_polynomial.term t)

-- /-- terms realized at values in A are the corresponding polynomials -/
-- /- evaluated at those values -/
-- lemma realized_term_is_evaluated_poly {n} {as : dvector M n} :
-- Π (t : bounded_ring_term n),
--   @realize_bounded_term _ M _ as _ t dvector.nil
--   = mv_polynomial.eval (dvector.fin_val as) (mv_polynomial.term t) :=
-- @ring_term_rec n (λ (t : bounded_ring_term n),
--   @realize_bounded_term _ M _ as _ t dvector.nil
--     = mv_polynomial.eval (dvector.fin_val as) (mv_polynomial.term t))
--   (begin intro k, simpa, end) -- variables
--   (begin -- zero
--     simpa only [struc_to_ring_struc.apps_zero, dvector.fin_val,
--       realize_bounded_term,
--       struc_to_ring_struc.realize_zero, mv_polynomial.term_zero, zero],
--   end)
--   (by simp)
--   -- simp only [struc_to_ring_struc.apps_one, dvector.fin_val, realize_bounded_term,
--   --   struc_to_ring_struc.realize_one, term_one, one,
--   --   mv_polynomial.coe_mv_poly_one, ring_hom.map_one],
--   (begin -- neg
--     intros t h,
--     unfold_coes,
--     unfold_coes at h,
--     simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map] at h,
--     rw mv_polynomial.term_neg,
--     simp only [struc_to_ring_struc.unaries_map, struc_to_ring_struc.func_map,
--       dvector.last, realize_bounded_term, neg, dvector.nth,
--       mv_polynomial.coe_mv_poly_neg, h, ring_hom.to_fun_eq_coe,
--       ring_hom.map_neg, models_ring_theory_to_comm_ring.realize_neg,
--       mv_polynomial.eval_map, neg_inj, struc_to_ring_struc.apps_neg],
--   end)
--   (begin -- add
--     intros s t hs ht,
--     unfold_coes,
--     rw mv_polynomial.term_add,
--     simp only [add, struc_to_ring_struc.binaries_map, dvector.last, struc_to_ring_struc.func_map,
--       dvector.last, realize_bounded_term, dvector.nth, mv_polynomial.coe_mv_poly_neg],
--     rw [hs, ht],
--     unfold_coes,
--     simp,
--   end)
--   (begin -- mul
--     intros s t hs ht,
--     unfold_coes,
--     rw mv_polynomial.term_mul,
--     simp only [mul, struc_to_ring_struc.binaries_map, dvector.last, struc_to_ring_struc.func_map,
--       dvector.last, realize_bounded_term, dvector.nth, mv_polynomial.coe_mv_poly_neg],
--     rw [hs, ht],
--     unfold_coes,
--     simp,
--   end)

-- lemma eval_term_evaluated_at_coeffs_eq_realize_bounded_term
--   {n} {as : dvector M n} {x : M} (t : bounded_term ring_signature n.succ) :
--   (polynomial.eval x (term_evaluated_at_coeffs as t)
--     = @realize_bounded_term _ M n.succ (x::as) _ t dvector.nil) :=
-- begin
--   rw realized_term_is_evaluated_poly,
--   rw dvector.fin_val_eq_x_val,
--   rw mv_polynomial.eval_eq_poly_eval_mv_coeffs,
--   simp only [dvector.fin_val, function.comp_app, fin.x_val,
--     mv_polynomial.to_polynomial, term_evaluated_at_coeffs],
--   have hcoes : polynomial.C.comp (int.cast_ring_hom M) =
--     int.cast_ring_hom (polynomial M) :=
--   by simp,
--   unfold_coes,
--   rw ← hcoes,
--   simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval₂_map,
--     mv_polynomial.eval_map],
-- end

-- lemma idk {p : polynomial M} :
--   p =
--   (@mv_polynomial.eval
--     (@fin.cases
--       _
--       (λ _, polynomial M)
--       polynomial.X
--       (λ (i : fin (p.nat_degree + 1)), polynomial.C (p.coeff i))
--     )
--   )
--       (mv_polynomial.term (gen_monic_poly p.nat_degree))


lemma realize_npow_rec
  {m n} {as : dvector M m} {t : bounded_term ring_signature m} :
  realize_bounded_term as (npow_rec n t) dvector.nil =
  (realize_bounded_term as t dvector.nil) ^ n :=
begin
  induction n with n hn,
  { simpa only [npow_rec, one, realize_one, realize_bounded_term,
    _root_.pow_zero] },
  { simpa only [npow_rec, mul, models_ring_theory_to_comm_ring.realize_mul,
      realize_bounded_term, hn] },
end

lemma realize_gen_poly {n : ℕ} {root} {c : ℕ → M} :
realize_bounded_term
  (dvector.cons root (dvector.of_fn (λ (i : fin (n + 1)), c i)))
  (gen_poly n) dvector.nil =
(finset.range (n + 1)).sum (λ (x : ℕ), c x * root ^ x)
     :=
begin
  induction n with n hn,
  {
    simp only [finset.sum_range_one, _root_.pow_zero, mul_one,
      gen_poly, dvector.nth_of_fn,
      realize_bounded_term, dvector.nth_cons _ _ _ (nat.zero_lt_one)],
    refl,
  },
  {
    simp only [finset.sum_range_add, hn, finset.sum_range_one, mul_one,
      gen_poly, dvector.nth_of_fn, add_zero, fin.mk_zero, fin.val_zero',
      models_ring_theory_to_comm_ring.realize_add, add,
      models_ring_theory_to_comm_ring.realize_mul, realize_bounded_term,
      dvector.nth, realize_lift_succ, dvector.remove_mth],
    rw [dvector.remove_mth_of_fn_last, hn,
      add_comm ((finset.range (n + 1)).sum (λ (x : ℕ), c x * root ^ x))],
    congr1,
    simp only [mul, fin.val_zero', models_ring_theory_to_comm_ring.realize_mul,
      realize_bounded_term, dvector.nth, dvector.nth_of_fn,
      fin.coe_mk, realize_npow_rec],
  }
end

instance is_alg_closed : is_alg_closed M :=
begin
  apply is_alg_closed.of_monic_nat_degree_ne_zero_exists_root,
  intros p hmonic hdeg,
  simp only [ACF, all_realize_sentence_union, all_realize_sentence_range,
    all_gen_monic_poly_has_root, realize_sentence_bd_alls,
    realize_bounded_formula, models_ring_theory_to_comm_ring.realize_zero, zero,
    realize_bounded_formula_ex] at hM,
  obtain ⟨ _ , halg_closed ⟩ := hM.1,
  set n := polynomial.nat_degree p - 1 with hn,
  set xs := dvector.of_fn (λ (i : fin (n + 1)), polynomial.coeff p i) with hxs,
  obtain ⟨ root , hroot ⟩ := halg_closed n xs,
  use root,
  convert hroot,
  rw polynomial.eval_eq_finset_sum,
  simp only [gen_monic_poly],
  simp only [mul, fin.val_zero',
    models_ring_theory_to_comm_ring.realize_add, add,
    models_ring_theory_to_comm_ring.realize_mul,
    realize_bounded_term, dvector.nth,
    models_ring_theory_to_comm_ring.realize_pow],
  simp only [polynomial.monic, polynomial.leading_coeff] at hmonic,
  simp only [finset.sum_range_add, finset.sum_range_one, add_zero, hmonic,
    one_mul],
  have hpow : npow_rec (n + 1) root = root ^ p.nat_degree,
  { simp only [pow, hn], rw nat.sub_add_cancel, refl,
    rw ← nat.one_lt_bit0_iff, exact nat.one_lt_bit0 hdeg },
  rw [add_comm _ (root ^ p.nat_degree), hpow, hxs, hn],
  congr,
  rw realize_gen_poly,
  rw nat.sub_add_cancel,
  rw ← nat.one_lt_bit0_iff, exact nat.one_lt_bit0 hdeg,
end

end models_ACF_to



variables {M : Structure ring_signature} {h : M ⊨ ACF} {p : ℕ}

lemma models_ACFₚ_iff {hp : prime p} :
  M ⊨ ACFₚ hp ↔ (p : M) = 0 ∧ M ⊨ ACF :=
by simp only [ACFₚ, all_realize_sentence_insert, realize_sentence_equal, zero,
    realize_closed_term, models_ring_theory_to_comm_ring.realize_nat,
    models_ring_theory_to_comm_ring.realize_zero]



end Fields

