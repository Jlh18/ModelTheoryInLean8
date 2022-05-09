import fol
import Rings.Notation
import Rings.Rings
import Rings.ToMathlib.algebraic_closure
import Rings.ToMathlib.char_p
import field_theory.is_alg_closed.classification
import set_theory.continuum
import Rings.vaught

universe u

notation h :: t  := dvector.cons h t
notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

local infix ` ≃ `:64 := fol.bounded_preformula.bd_equal

namespace Fields

open fol Rings Rings.ring_signature Rings.struc_to_ring_struc

/-- The sentence "every non-zero element has a multiplicative inverse" -/
def mul_inv : sentence ring_signature :=
∀' (x_ 1 ≃ 0) ⊔ (∃' x_ 1 * x_ 0 ≃ 1)

/-- The sentence "zero is not equal to one", implying the ring is non-trivial -/
def non_triv : sentence ring_signature := 0 ≄ 1

/-- The theory of fields in the language of rings -/
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

variables {M : Structure ring_signature} [h : fact (M ⊨ field_theory)]
-- M inherits instances of 0 1 - + * from Rings.ModelTo

include h

instance ring_model : fact (M ⊨ ring_theory) :=
⟨ all_realize_sentence_of_subset h.1 ring_theory_sub_field_theory ⟩

lemma zero_ne_one : (0 : M) ≠ 1 :=
by { have h1 := h.1, have h2 := h1 non_triv_in_field_theory, simpa [h2] }

lemma mul_inv (a : M) (ha : a ≠ 0) : (∃ (b : M), a * b = 1) :=
by { have h1 := h.1, have hmulinv := h1 mul_inv_in_field_theory, by simpa using hmulinv a ha }

lemma is_field : is_field M :=
{ exists_pair_ne := ⟨ 0 , 1 , zero_ne_one ⟩,
  mul_comm := mul_comm,
  mul_inv_cancel := mul_inv }

noncomputable instance field : field M :=
is_field.to_field M is_field

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

/-- The sentence "`p + 1` is non-zero" for a natural p -/
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

instance models_field_theory : fact (M ⊨ field_theory) :=
by { rw [ACF, all_realize_sentence_union] at hM, exact ⟨ hM.1.1 ⟩ }

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
(finset.range (n + 1)).sum (λ (x : ℕ), c x * root ^ x) :=
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

lemma models_ACFₚ_iff' {hp : nat.prime p} :
  M ⊨ ACFₚ hp ↔ (p : M) = 0 ∧ M ⊨ ACF :=
by simp only [ACFₚ, all_realize_sentence_insert, realize_sentence_equal,
    realize_closed_term, models_ring_theory_to_comm_ring.realize_nat,
    models_ring_theory_to_comm_ring.realize_zero]

lemma models_ACFₚ_iff [hM : fact (M ⊨ ACF)] {hp : nat.prime p} :
  M ⊨ ACFₚ hp ↔ ring_char M = p :=
begin
  rw models_ACFₚ_iff',
  split,
  { intro hmodel, apply char_p.ring_char_of_prime_eq_zero hp hmodel.1 },
  { intro hchar, refine ⟨ _ , hM.1 ⟩, rw [← hchar, ring_char.spec] },
end

instance models_ACFₚ_to_models_ACF [hp : fact (nat.prime p)] [hM : fact (M ⊨ ACFₚ hp.1)] :
  fact (M ⊨ ACF) := by { rw [models_ACFₚ_iff'] at hM, exact ⟨ hM.1.2 ⟩ }

lemma models_ACFₚ_char_p [hp : fact (nat.prime p)] [hM : fact (M ⊨ ACFₚ hp.1)] : char_p M p :=
by { convert ring_char.char_p M, rw ((@models_ACFₚ_iff _ _ _ hp.1).1 hM.1) }

instance models_ACF₀_to_models_ACF [hM : fact (M ⊨ ACF₀)] : fact (M ⊨ ACF) :=
by { rw [ACF₀, all_realize_sentence_union] at hM, exact ⟨ hM.1.1 ⟩ }

lemma models_ACF₀_char_zero [hM : fact (M ⊨ ACF)] (hM : M ⊨ ACF₀) : char_zero M :=
begin
  simp only [ACF₀, all_realize_sentence_union,
  all_realize_sentence_range, realize_plus_one_ne_zero] at hM,
  split,
  intros n,
  induction n with n hn,
  { intro m, induction m with m hm,
    { intro, refl },
    { intro hnm, exfalso, apply hM.2 m, simpa only [← realize_nat_succ, ← hnm] }},
  { intro m, induction m with m hm,
    { intro hnm, exfalso, exact hM.2 n hnm },
    { intro hnm, rw nat.succ_inj', apply hn, simp only [realize_nat_succ] at hnm,
      apply add_right_cancel hnm }}
end

instance models_ACF₀_char_zero' [hM : fact (M ⊨ ACF₀)] : char_zero M :=
models_ACF₀_char_zero hM.1

lemma models_ACF₀_iff [hM : fact (M ⊨ ACF)] :
  M ⊨ ACF₀ ↔ ring_char M = 0 :=
begin
  split,
  { intro hmodel, apply @ring_char.eq_zero _ _ (models_ACF₀_char_zero hmodel) },
  { intro hchar,
    simp only [ACF₀, all_realize_sentence_union, all_realize_sentence_range,
      plus_one_ne_zero, realize_bounded_formula_not],
    refine ⟨ hM.1 , _ ⟩, intros n hn,
    rw ring_char.eq_iff at hchar, have hchar1 := hchar.1, have hcharn := hchar1 (n + 1),
    simp only [zero_dvd_iff, nat.succ_ne_zero, nat.cast_add, nat.cast_one, iff_false] at hcharn,
    apply hcharn, convert hn, convert (@realize_nat M _ _ _ _ _ dvector.nil n).symm,
    rw Structure_structure_eq_self },
end

namespace instances

/-- alg_cl (ℤ/p) : Type* as a ring structure -/
@[reducible] def algebraic_closure_of_zmod {p : ℕ} (hp : nat.prime p) :
  Structure ring_signature :=
Rings.struc_to_ring_struc.Structure (@algebraic_closure.of_ulift_zmod p ⟨ hp ⟩)

/-- alg_cl (ℤ/p) : Type* is algebraically closed of characteristic p -/
theorem algebraic_closure_of_zmod_models_ACFₚ {p : ℕ} (hp : nat.prime p) :
  algebraic_closure_of_zmod hp ⊨ ACFₚ hp :=
begin
  rw models_ACFₚ_iff',
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

/-- ℚ̅ : Type* as a ring structure -/
@[reducible] def algebraic_closure_of_rat :
  Structure ring_signature :=
Rings.struc_to_ring_struc.Structure algebraic_closure.of_ulift_rat

instance algebraic_closure_of_rat_models_ACF : fact (algebraic_closure_of_rat ⊨ ACF) :=
by {split, classical, apply is_alg_closed_to.realize_ACF }

instance : char_zero algebraic_closure_of_rat :=
{ cast_injective :=
begin
  intros n m hnm,
  apply algebraic_closure.of_ulift_rat.char_zero.1,
  exact hnm,
end }

/-- ℚ̅ : Type* is algebraically closed of characteristic zero -/
theorem algebraic_closure_of_rat_models_ACF₀ :
  algebraic_closure_of_rat ⊨ ACF₀ :=
models_ACF₀_iff.2 ring_char.eq_zero

end instances

namespace is_complete_ACF₀

open_locale fol cardinal
open Rings dvector fol cardinal

@[reducible] def comm_ring_ulift : comm_ring (ulift.{u} ℤ) := equiv.comm_ring equiv.ulift
local attribute [instance] comm_ring_ulift

def ulift.down_ring_hom_int : ulift.{u} ℤ →+* ℤ :=
{ to_fun := equiv.ulift.to_fun,
  map_one' := rfl,
  map_mul' := by finish,
  map_zero' := rfl,
  map_add' := by finish }

def ulift.down_ring_hom_zmod {p : ℕ} [fact p.prime] : ulift.{u} (zmod p) →+* zmod p :=
{ to_fun := equiv.ulift.to_fun,
  map_one' := rfl,
  map_mul' := by finish,
  map_zero' := rfl,
  map_add' := by finish }

@[reducible] def algebra_ulift_int {A : Type u} [comm_ring A] : algebra (ulift.{u} ℤ) A :=
ring_hom.to_algebra (ring_hom.comp (algebra_map ℤ A) ulift.down_ring_hom_int)
local attribute [instance] algebra_ulift_int

lemma injective_alg_map_int {K : Type u} [field K] (hK : char_zero K) :
  function.injective (algebra_map (ulift.{u} ℤ) K) :=
function.injective.comp (@int.cast_injective _ _ _ hK) equiv.ulift.injective

@[reducible] def algebra_ulift_zmod {A : Type u} [comm_ring A] {p : ℕ}
  [fact p.prime] [char_p A p] : algebra (ulift.{u} (zmod p)) A :=
ring_hom.to_algebra (ring_hom.comp (algebra_map (zmod p) A) ulift.down_ring_hom_zmod)
local attribute [instance] algebra_ulift_int

lemma injective_alg_map_zmod {K : Type u} [field K] {p : ℕ} [fact p.prime]
  [char_p K p] :
  function.injective (@algebra_map (ulift.{u} (zmod p)) K _ _ algebra_ulift_zmod) :=
function.injective.comp ((algebra_map (zmod p) _).injective) equiv.ulift.injective

/-- Two uncountable algebraically closed fields of characteristic zero are isomorphic
if they have the same cardinality. -/ --credit to Chris Hughes
lemma ring_equiv_of_cardinal_eq_of_char_zero
  {K L : Type u} (hKf : field K) (hLf : field L)
  (hK1 : is_alg_closed K) (hL1 : is_alg_closed L)
  (hK2 : char_zero K) (hL2 : char_zero L)
  (hK : ω < #K) (hKL : #K = #L) : nonempty (K ≃+* L) :=
begin
  have hinjK := injective_alg_map_int hK2,
  have hinjL := injective_alg_map_int hL2,
  have mk_ulift_int : #(ulift.{u} ℤ) = ω := by simp,
  cases exists_is_transcendence_basis (ulift.{u} ℤ)
    (show function.injective (algebra_map (ulift.{u} ℤ) K),
      from hinjK) with s hs,
  cases exists_is_transcendence_basis (ulift.{u} ℤ)
    (show function.injective (algebra_map (ulift.{u} ℤ) L),
      from hinjL) with t ht,
  have : #s = #t,
  { rw [← is_alg_closed.cardinal_eq_cardinal_transcendence_basis_of_omega_lt _ hs (le_of_eq mk_ulift_int) hK,
      ← is_alg_closed.cardinal_eq_cardinal_transcendence_basis_of_omega_lt _ ht (le_of_eq mk_ulift_int), hKL],
    rwa ← hKL },
  cases cardinal.eq.1 this with e,
  exact ⟨is_alg_closed.equiv_of_transcendence_basis _ _ e hs ht⟩,
end

lemma ring_equiv_of_cardinal_eq_of_char_p -- credit to Chris Hughes
  {K L : Type u} (hKf : field K) (hLf : field L)
  (hK1 : is_alg_closed K) (hL1 : is_alg_closed L) (p : ℕ) [fact p.prime]
  [char_p K p] [char_p L p] (hK : ω < #K) (hKL : #K = #L) : nonempty (K ≃+* L) :=
begin
  cases @exists_is_transcendence_basis (ulift.{u} (zmod p)) _ _ _ algebra_ulift_zmod
    (show function.injective (@algebra_map (ulift.{u} (zmod p)) K _ _ algebra_ulift_zmod),
      from injective_alg_map_zmod) with s hs,
  cases @exists_is_transcendence_basis (ulift.{u} (zmod p)) _ _ _ algebra_ulift_zmod
    (show function.injective (@algebra_map (ulift.{u} (zmod p)) L _ _ algebra_ulift_zmod),
      from injective_alg_map_zmod) with t ht,
  have : #s = #t,
  { rw [← @is_alg_closed.cardinal_eq_cardinal_transcendence_basis_of_omega_lt
          (ulift.{u} (zmod p)) K _ _ algebra_ulift_zmod _ _ _ _ hs
      (le_of_lt $ lt_omega_iff_fintype.2 ⟨infer_instance⟩) hK,
        ← @is_alg_closed.cardinal_eq_cardinal_transcendence_basis_of_omega_lt
          (ulift.{u} (zmod p)) L _ _ algebra_ulift_zmod _ _ _ _ ht
      (le_of_lt $ lt_omega_iff_fintype.2 ⟨infer_instance⟩), hKL],
    rwa ← hKL },
  cases cardinal.eq.1 this with e,
  exact ⟨@is_alg_closed.equiv_of_transcendence_basis
   (ulift.{u} (zmod p)) L K _ _ algebra_ulift_zmod _ algebra_ulift_zmod
     _ _ _ _ _ _ e hs ht⟩,
end

/-- Two uncountable algebraically closed fields are isomorphic
if they have the same cardinality and the same characteristic. -/
lemma ring_equiv_of_cardinal_eq_of_char_eq
  {K L : Type u} [hKf : field K] [hLf : field L]
  (hKalg : is_alg_closed K) (hLalg : is_alg_closed L)
  (p : ℕ) [char_p K p] [char_p L p]
  (hKω : ω < #K) (hKL : #K = #L) : nonempty (K ≃+* L) :=
begin
  rcases char_p.char_is_prime_or_zero K p with hp | hp,
  { haveI : fact p.prime := ⟨hp⟩,
    exact ⟨(ring_equiv_of_cardinal_eq_of_char_p hKf hLf hKalg hLalg p hKω hKL).some⟩ },
  { rw [hp] at *,
    resetI,
    letI : char_zero K := char_p.char_p_to_char_zero K,
    letI : char_zero L := char_p.char_p_to_char_zero L,
    exact ⟨(ring_equiv_of_cardinal_eq_of_char_zero hKf hLf hKalg hLalg _inst _inst_3 hKω hKL).some⟩ }
end

lemma categorical_ACF₀ {κ} (hκ : ω < κ) : fol.categorical κ ACF₀ :=
begin
  intros M N hM hN hMκ hNκ,
  haveI : fact (M ⊨ ACF₀) := ⟨ hM ⟩, haveI : fact (N ⊨ ACF₀) := ⟨ hN ⟩,
  split,
  apply equiv_of_ring_equiv,
  apply classical.choice,
  apply ring_equiv_of_cardinal_eq_of_char_zero,
  repeat { apply_instance },
  repeat { cc },
end

lemma categorical_ACFₚ {κ} (hκ : ω < κ) {p : ℕ} (hp : nat.prime p) :
  fol.categorical κ (ACFₚ hp) :=
begin
  intros M N hM hN hMκ hNκ,
  haveI : fact (nat.prime p) := ⟨ hp ⟩,
  haveI : fact (M ⊨ ACFₚ hp) := ⟨ hM ⟩, haveI : fact (N ⊨ ACFₚ hp) := ⟨ hN ⟩,
  split,
  apply equiv_of_ring_equiv,
  apply classical.choice,
  subst hMκ,
  refine @ring_equiv_of_cardinal_eq_of_char_eq _ _ _ _ _ _ p
    models_ACFₚ_char_p models_ACFₚ_char_p hκ hNκ.symm,
  { apply_instance },
  { apply_instance },
end


def unit_equiv_ring_unaries : _root_.equiv unit ring_unaries :=
{ to_fun := λ x, match x with | unit.star := ring_unaries.neg end,
  inv_fun := λ x, match x with | ring_unaries.neg := unit.star end,
  left_inv := λ x, match x with | unit.star := rfl end,
  right_inv := λ x, match x with | ring_unaries.neg := rfl end }

def bool_equiv_ring_binaries : _root_.equiv bool ring_binaries :=
{ to_fun := λ x, match x with | ff := ring_binaries.add | tt := ring_binaries.mul end,
  inv_fun := λ c, match c with | ring_binaries.add := ff | ring_binaries.mul := tt end,
  left_inv := λ x, match x with | ff := rfl | tt := rfl end,
  right_inv := λ c, match c with | ring_binaries.add := rfl | ring_binaries.mul := rfl end }


lemma ring_signature.fintype_functions : ∀ n, fintype (ring_signature.functions n)
| 0 := fintype.of_equiv bool bool_equiv_ring_consts
| 1 := fintype.of_equiv unit unit_equiv_ring_unaries
| 2 := fintype.of_equiv bool bool_equiv_ring_binaries
| (n+3) := by { dsimp [ring_signature, ring_funcs], exact fintype.of_is_empty }

lemma functions_le_omega : ∀ n, # (Rings.ring_signature.functions n) ≤ ω :=
begin
  intro n,
  apply le_of_lt,
  simp only [lt_omega_iff_fintype, ring_signature, ring_funcs],
  exact ⟨ ring_signature.fintype_functions _ ⟩,
end

lemma card_functions_omega_le_continuum : ∀ (n : ℕ), mk (ring_signature.functions n) ≤ continuum :=
λ n, (functions_le_omega _).trans omega_le_continuum

lemma only_infinite_ACF : only_infinite ACF :=
by { intro M, haveI : fact (M.1 ⊨ ACF) := ⟨ M.2 ⟩, exact is_alg_closed.infinite }

end is_complete_ACF₀

open is_complete_ACF₀ cardinal

/-- a.k.a Lefschetz part 1. Any sentence or its negation can be deduced in ACF₀-/
theorem is_complete'_ACF₀ : is_complete' ACF₀ :=
is_complete'_of_only_infinite_of_categorical
    instances.algebraic_closure_of_rat
    instances.algebraic_closure_of_rat_models_ACF₀ -- ℚ̅ is a model of ACF₀
    (only_infinite_subset ACF_subset_ACF₀ only_infinite_ACF) -- alg closed fields are infinite
    -- pick the cardinal κ := 𝔠
    card_functions_omega_le_continuum
    omega_le_continuum
    -- (max_le (functions_le_omega.trans $ omega_le_continuum) omega_le_continuum)
    (categorical_ACF₀ omega_lt_continuum)

/-- a.k.a Lefschetz part 3. Any sentence or its negation can be deduced in ACF₀-/
theorem is_complete'_ACFₚ {p : ℕ} (hp : nat.prime p) : is_complete' (ACFₚ hp) :=
is_complete'_of_only_infinite_of_categorical
    (instances.algebraic_closure_of_zmod hp)
    (instances.algebraic_closure_of_zmod_models_ACFₚ hp) -- alg_closure (ℤ / p) is a model of ACFₚ
    (only_infinite_subset ACF_subset_ACFₚ only_infinite_ACF) -- alg closed fields are infinite
    -- pick the cardinal κ := 𝔠
    card_functions_omega_le_continuum
    omega_le_continuum
    -- (max_le (functions_le_omega.trans $ omega_le_continuum) omega_le_continuum)
    (categorical_ACFₚ omega_lt_continuum hp)

end Fields
