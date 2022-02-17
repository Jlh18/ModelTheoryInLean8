import fol
import Rings.Notation
import Rings.Rings
import field_theory.is_alg_closed.algebraic_closure
import Rings.ToMathlib.algebraic_closure
import Rings.ToMathlib.char_p

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

variables (K : Type u) [field K]

lemma K_is_field : is_field K := field.to_is_field K

open Rings.models_ring_theory_to_comm_ring

lemma realize_field_theory :
  Structure K ⊨ field_theory :=
begin
  intros ϕ h,
  cases h,
  {apply (comm_ring_to_model.realize_ring_theory K h)},
  repeat {cases h},
   { intro,
     simp only [fol.bd_or, models_ring_theory_to_comm_ring.realize_one,
       struc_to_ring_struc.func_map, fin.val_zero', realize_bounded_formula_not,
       struc_to_ring_struc.binaries_map, fin.val_eq_coe, dvector.last,
       realize_bounded_formula_ex, realize_bounded_term_bd_app,
       realize_bounded_formula, realize_bounded_term,
       fin.val_one, dvector.nth, models_ring_theory_to_comm_ring.realize_zero],
     apply is_field.mul_inv_cancel (K_is_field K) },
  { simp [fol.realize_sentence] },
end

/-- Fields are models of the theory of fields -/
def models_field_theory : Model field_theory.{u} :=
⟨ Structure K ,  realize_field_theory _ ⟩

end field_to

namespace models_theory_of_fields_to_is_field

variables {M : Structure ring_signature} (h : M ⊨ field_theory)
-- M inherits instances of 0 1 - + * from Rings.ModelTo

include h

lemma ring_model : M ⊨ ring_theory :=
all_realize_sentence_of_subset h ring_theory_sub_field_theory

instance comm_ring : comm_ring M :=
models_ring_theory_to_comm_ring.comm_ring (ring_model h)

instance ring : ring M := @comm_ring.to_ring M (models_theory_of_fields_to_is_field.comm_ring h)

lemma zero_ne_one : (0 : M) ≠ 1 := by simpa using h non_triv_in_field_theory

lemma mul_inv (a : M) (ha : a ≠ 0) : (∃ (b : M), a * b = 1) :=
let hmulinv := h mul_inv_in_field_theory in by simpa using hmulinv a ha

lemma is_field : @is_field M (models_theory_of_fields_to_is_field.ring h) :=
{ exists_pair_ne := ⟨ 0 , 1 , zero_ne_one h ⟩,
  mul_comm := (models_theory_of_fields_to_is_field.comm_ring h).mul_comm,
  mul_inv_cancel := mul_inv h }

noncomputable instance field : field M :=
@is_field.to_field M (models_theory_of_fields_to_is_field.ring h)
(models_theory_of_fields_to_is_field.is_field h)

end models_theory_of_fields_to_is_field

/-- GenPoly n is the polynomial aₙ₊₁ xⁿ + ⋯ + a₂ x + a₁
 where aₖ = x_ k and x = x_ 0, i.e. we are seeing the variables x_ k with 0 < k as coefficients
 and x_ 0 as the indeterminate -/
@[simp] def gen_poly : Π (n : ℕ), bounded_ring_term (n + 2)
| 0       := x_ ⟨ 1 , dec_trivial ⟩
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
    (npow_rec m x_ ⟨ 0 , nat.zero_lt_succ _ ⟩)).degree = m :=
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
  { rw [h0, polynomial.C_0, polynomial.degree_zero],
    dec_trivial },
  { rw polynomial.degree_C h0,
    dec_trivial }
end
| (nat.succ n) as :=
begin
  simp only [gen_poly, polynomial.term_evaluated_at_coeffs_add,
    polynomial.term_evaluated_at_coeffs_monomial' (nat.lt_succ_self _),
    polynomial.lift_succ_remove_last],
  apply has_le.le.trans_lt (polynomial.degree_add_le _ _),
  apply max_lt,
  { apply has_le.le.trans_lt (polynomial.degree_monomial_le _ _),
    exact with_bot.succ_lt_succ_succ },
  { apply lt_trans (@gen_poly_degree n (dvector.remove_mth (n.succ + 2) as)),
    exact with_bot.succ_lt_succ_succ },
end

/-- gen_monic_poly has non-zero degree -/
lemma gen_monic_poly_non_const {n} {as : dvector A (n + 1)} :
  polynomial.degree (polynomial.term_evaluated_at_coeffs as (gen_monic_poly n)) ≠ 0 :=
begin
  apply ne_of_gt,
  have hp : (polynomial.term_evaluated_at_coeffs as (npow_rec (n + 1) x_ 0)).degree = n + 1,
  {apply deg_pow},
  have hq : (polynomial.term_evaluated_at_coeffs as (gen_poly n)).degree < (n + 1),
  { apply lt_of_lt_of_le gen_poly_degree,
    { rw le_iff_eq_or_lt,
      left, refl },
    exact hnt,
    exact hde },
  have hle : (polynomial.term_evaluated_at_coeffs as (gen_poly n)).degree
    < (polynomial.term_evaluated_at_coeffs as (npow_rec (n + 1) x_ 0)).degree,
  { rw hp, exact hq },
  rw [gen_monic_poly, polynomial.term_evaluated_at_coeffs_add,
    (polynomial.degree_add_eq_left_of_degree_lt hle), hp],
  dec_trivial,
end

end poly_lemmas

/-- ∀ a₁ ⋯ ∀ aₙ, ∃ x₀, (aₙ x₀ⁿ⁻¹ + ⋯ + a₂ x₀+ a₁ = 0) -/
@[simp] def all_gen_monic_poly_has_root (n : ℕ) :
  sentence ring_signature :=
fol.bd_alls (n + 1) (∃' gen_monic_poly n ≃ 0)

/-- The theory of algebraically closed fields -/
def ACF : Theory ring_signature :=
field_theory ∪ (set.range all_gen_monic_poly_has_root)
-- the latter stands for {gen_monic_polyHasSolution n | n : ℕ}

/-- The theory of algebraically closed fields of prime characteristic -/

def ACFₚ {p : ℕ} (h : nat.prime p) : Theory ring_signature :=
set.insert (p ≃ 0) ACF

@[reducible] def plus_one_ne_zero (p : ℕ) : sentence ring_signature :=
p + 1 ≄ 0

lemma injective_plus_one_ne_zero : function.injective plus_one_ne_zero :=
begin
  intros n m himage,
  simp only [plus_one_ne_zero] at himage,
  have h := (bd_app.inj (bd_app.inj (bd_notequal.inj himage).1).1).2,
  apply instances.nat_cast_bd_ring_term_inj h,
end

/-- The theory of algebraically closed fields of characterstic zero -/
def ACF₀ : Theory ring_signature := ACF ∪ (set.range plus_one_ne_zero)

lemma ACF_subset_ACFₚ {p} {h : nat.prime p} : ACF ⊆ ACFₚ h :=
set.subset_insert _ _

lemma ACF_subset_ACF₀ : ACF ⊆ ACF₀ :=
set.subset_union_left _ _

lemma realize_plus_one_ne_zero {M : Structure ring_signature} {p} :
  (M ⊨ plus_one_ne_zero p) ↔ (p.succ : M) ≠ 0 :=
by simpa only [plus_one_ne_zero, bd_notequal, realize_sentence_not,
    realize_sentence_equal, realize_closed_term,
    models_ring_theory_to_comm_ring.realize_nat,
    not_iff_not, Rings.models_ring_theory_to_comm_ring.realize_zero,
    models_ring_theory_to_comm_ring.realize_one,
    realize_bounded_term_bd_app, nat.cast_succ,
    realize_bounded_term.equations._eqn_2,
    models_ring_theory_to_comm_ring.realize_add]

namespace is_alg_closed_to

variables {K : Type u} [field K] [is_alg_closed K] [decidable_eq K]

open Rings.struc_to_ring_struc

lemma is_alg_closed.exists_root (f : polynomial K) (h : f.degree ≠ 0) :
  ∃ x : K, f.eval x = 0 :=
polynomial.exists_root_of_splits _ (is_alg_closed.splits f) h

/-- Algebraically closed fields model the theory ACF-/
lemma realize_ACF : Structure K ⊨ ACF :=
begin
  intros ϕ h,
  cases h,
  { apply field_to.realize_field_theory _ h },
  { cases h with n hϕ,
    rw ← hϕ,
    simp only [all_gen_monic_poly_has_root, realize_sentence_bd_alls,
      realize_bounded_formula_ex, realize_bounded_formula,
      models_ring_theory_to_comm_ring.realize_zero],
    intro as,
    have root := is_alg_closed.exists_root
      (polynomial.term_evaluated_at_coeffs as (gen_monic_poly n)) gen_monic_poly_non_const,
    cases root with x hx,
    rw polynomial.eval_term_evaluated_at_coeffs_eq_realize_bounded_term at hx,
    exact ⟨ x , hx ⟩ },
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

lemma realize_npow_rec
  {m n} {as : dvector M m} {t : bounded_term ring_signature m} :
  realize_bounded_term as (npow_rec n t) dvector.nil =
  (realize_bounded_term as t dvector.nil) ^ n :=
begin
  induction n with n hn,
  { simpa only [npow_rec, realize_one, realize_bounded_term,
    _root_.pow_zero] },
  { simpa only [npow_rec, models_ring_theory_to_comm_ring.realize_mul,
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
  { simpa only [finset.sum_range_one, _root_.pow_zero, mul_one,
      gen_poly, dvector.nth_of_fn,
      realize_bounded_term, dvector.nth_cons _ _ _ (nat.zero_lt_one)] },
  { simp only [finset.sum_range_add, hn, finset.sum_range_one, mul_one,
      gen_poly, dvector.nth_of_fn, add_zero, fin.mk_zero, fin.val_zero',
      models_ring_theory_to_comm_ring.realize_add,
      models_ring_theory_to_comm_ring.realize_mul, realize_bounded_term,
      dvector.nth, realize_lift_succ, dvector.remove_mth,
      dvector.remove_mth_of_fn_last, hn,
      add_comm ((finset.range (n + 1)).sum (λ (x : ℕ), c x * root ^ x))],
    congr1,
    simp only [fin.val_zero', models_ring_theory_to_comm_ring.realize_mul,
      realize_bounded_term, dvector.nth, dvector.nth_of_fn,
      fin.coe_mk, realize_npow_rec] }
end

instance is_alg_closed : is_alg_closed M :=
begin
  apply is_alg_closed.of_exists_root_nat_degree,
  intros p hmonic hirr hdeg,
  simp only [ACF, all_realize_sentence_union, all_realize_sentence_range,
    all_gen_monic_poly_has_root, realize_sentence_bd_alls,
    realize_bounded_formula, models_ring_theory_to_comm_ring.realize_zero,
    realize_bounded_formula_ex] at hM,
  obtain ⟨ _ , halg_closed ⟩ := hM.1,
  set n := polynomial.nat_degree p - 1 with hn,
  set xs := dvector.of_fn (λ (i : fin (n + 1)), polynomial.coeff p i) with hxs,
  obtain ⟨ root , hroot ⟩ := halg_closed n xs,
  use root,
  convert hroot,
  rw polynomial.eval_eq_finset_sum,
  simp only [
    gen_monic_poly, models_ring_theory_to_comm_ring.realize_add,
    fin.val_zero', models_ring_theory_to_comm_ring.realize_mul,
    realize_bounded_term, dvector.nth, models_ring_theory_to_comm_ring.realize_pow],
  simp only [polynomial.monic, polynomial.leading_coeff] at hmonic,
  have hpow : npow_rec (n + 1) root = root ^ p.nat_degree,
  { simp only [pow, hn], rw nat.sub_add_cancel, refl,
    rw ← nat.one_lt_bit0_iff, exact nat.one_lt_bit0 hdeg },
  simp only [finset.sum_range_add, finset.sum_range_one,
    add_zero, hmonic, one_mul, add_comm _ (root ^ p.nat_degree), hpow, hxs, hn],
  congr,
  rw [realize_gen_poly, nat.sub_add_cancel],
  rw ← nat.one_lt_bit0_iff,
  exact nat.one_lt_bit0 hdeg,
end

variables {p : ℕ}

end models_ACF_to

variables {M : Structure ring_signature} {p : ℕ}

lemma models_ACFₚ_iff {hp : nat.prime p} :
  M ⊨ ACFₚ hp ↔ (p : M) = 0 ∧ M ⊨ ACF :=
by simp only [ACFₚ, all_realize_sentence_insert, realize_sentence_equal,
    realize_closed_term, models_ring_theory_to_comm_ring.realize_nat,
    models_ring_theory_to_comm_ring.realize_zero]

lemma models_ACFₚ_char [hM : fact (M ⊨ ACF)] {hp : nat.prime p} :
  M ⊨ ACFₚ hp → ring_char M = p :=
begin
  rw models_ACFₚ_iff,
  intro hmodel,
  apply char_p.ring_char_of_prime_eq_zero hp hmodel.1,
end


namespace instances

@[reducible] def algebraic_closure_of_zmod {p : ℕ} (hp : nat.prime p) :
  Structure ring_signature :=
Rings.struc_to_ring_struc.Structure (@algebraic_closure.of_ulift_zmod p ⟨ hp ⟩)

theorem algebraic_closure_of_zmod_models_ACFₚ {p : ℕ} (hp : nat.prime p) :
  algebraic_closure_of_zmod hp ⊨ ACFₚ hp :=
begin
  rw models_ACFₚ_iff,
  split,
  { have h := @algebraic_closure.of_ulift_zmod.char_p p ⟨ hp ⟩,
    rw ← ring_char.eq_iff at h,
    rw ring_char.spec,
    have hrw : ring_char (@algebraic_closure.of_ulift_zmod p ⟨ hp ⟩) =
      ring_char ↥(Structure (@algebraic_closure.of_ulift_zmod p ⟨ hp ⟩)),
    { refl },
    rw hrw at h,
    rw h },
  { classical,
    apply is_alg_closed_to.realize_ACF },
end

end instances


end Fields

