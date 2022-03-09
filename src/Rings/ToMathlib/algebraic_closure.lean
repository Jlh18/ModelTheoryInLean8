import field_theory.is_alg_closed.algebraic_closure
import data.zmod.basic
import data.equiv.transfer_instance
import Rings.ToMathlib.char_p
import algebra.char_p.algebra
import field_theory.separable

universes u v

namespace is_alg_closed

open polynomial

lemma of_exists_root_nat_degree {k : Type*} [field k] (H : ∀ p : polynomial k, p.monic → irreducible p → nat_degree p ≠ 0 → ∃ x, p.eval x = 0) :
  is_alg_closed k :=
begin
  apply of_exists_root,
  intros p hmonic hirr,
  by_cases hdeg : nat_degree p = 0,
  {
    rw monic.nat_degree_eq_zero_iff_eq_one hmonic at hdeg,
    rw hdeg at hirr,
    exfalso,
    apply hirr.1,
    exact ⟨ 1 , rfl ⟩,
  },
  apply H p hmonic hirr hdeg,
end

lemma of_nat_degree_ne_zero_exists_root {k : Type*} [field k]
  (H : ∀ p : polynomial k, nat_degree p ≠ 0 → ∃ x, p.eval x = 0) :
  is_alg_closed k :=
of_exists_root_nat_degree $ λ _ _ hdeg, H _

lemma infinite {K : Type*} [field K] [is_alg_closed K] : infinite K :=
begin
  split,
  intro hfin, haveI := hfin,
  set n := fintype.card K with hn,
  set f : polynomial K := polynomial.monomial n.succ 1 - 1 with hf,
  have hfsep : f.separable,
  { rw polynomial.separable_def',
    refine ⟨ -1, (polynomial.monomial 1 (n.succ : K)⁻¹), _⟩,
    simp only [hf, polynomial.derivative_sub, polynomial.derivative_monomial,
      neg_one_mul, neg_sub, one_mul, polynomial.derivative_one, sub_zero,
      polynomial.monomial_mul_monomial],
    have hrw0 : (1 + (n.succ - 1)) = n.succ, ring,
    rw hrw0,
    have hrw1 : (n.succ : K)⁻¹ * n.succ = 1, simp,
    -- char_p.cast_card_eq_zero, nice simp lemma!
    rw hrw1,
    ring },
  apply nat.not_succ_le_self (fintype.card K),
  have hroot : fintype.card (f.root_set K) = n.succ,
  { rw [polynomial.card_root_set_eq_nat_degree hfsep (is_alg_closed.splits_domain _),
      hf, polynomial.nat_degree, polynomial.degree_sub_eq_left_of_degree_lt],
    { simp },
    { simpa [← cmp_eq_lt_iff] } },
  rw ← hroot,
  apply fintype.card_le_of_injective coe subtype.coe_injective,
end

end is_alg_closed

section ulift

variables {K : Type} [field K]

instance : field (ulift K) := equiv.ulift.field

lemma nat_down_eq : Π {n : ℕ}, (n : ulift K).down = (n : K)
| nat.zero := rfl
| (nat.succ n) := by { simp only [nat.cast_succ], rw ← nat_down_eq, refl }

lemma nat_up_eq : Π {n : ℕ}, ulift.up (n : K) = (n : ulift K)
| nat.zero := rfl
| (nat.succ n) := by { simp only [nat.cast_succ], rw ← nat_up_eq, refl }

lemma ulift_char_p (p : ℕ) [hp : fact (nat.prime p)] (hp : char_p K p) :
  char_p (ulift K) p :=
begin
  split,
  intro n,
  rw ← hp.cast_eq_zero_iff,
  split,
  {
    intro hn,
    convert congr_arg ulift.down hn,
    rw nat_down_eq,
  },
  {
    intro hn,
    rw ← ulift.up_down ↑n,
    rw ← ulift.up_down 0,
    apply congr_arg ulift.up,
    convert hn,
    rw nat_down_eq,
  },
end

lemma ulift_char_zero (h0 : char_zero K) : char_zero (ulift K) :=
begin
  split,
  intros n m hnm,
  apply h0.1,
  apply equiv.injective equiv.ulift.symm,
  convert hnm,
  repeat { simp [nat_up_eq] },
end

end ulift

namespace algebraic_closure

section instances

variables (p : ℕ) [hp : fact (nat.prime p)]

/-- algebraic closure of finite fields with char p lifted to any universe -/
@[reducible] def of_ulift_zmod (p : ℕ) [hp : fact (nat.prime p)] :=
algebraic_closure (ulift (zmod p))

/-- algebraic closure of zmod is still characteristic p -/
lemma of_ulift_zmod.char_p (p : ℕ) [hp : fact (nat.prime p)] : char_p (of_ulift_zmod.{u} p) p :=
(ring_hom.char_p_iff_char_p (algebra_map (ulift.{u} (zmod p))
  (of_ulift_zmod.{u} p)) p).1 $ ulift_char_p p (zmod.char_p p)

/-- algebraic closure of finite fields with char p lifted to any universe -/
@[reducible] def of_ulift_rat := algebraic_closure (ulift rat)

/-- algebraic closure of zmod is still characteristic p -/
lemma of_ulift_rat.char_zero : char_zero of_ulift_rat.{u} :=
(ring_hom.char_zero_iff (ring_hom.injective (algebra_map (ulift.{u} rat) _))).1
  (ulift_char_zero linear_ordered_semiring.to_char_zero)

end instances

end algebraic_closure
