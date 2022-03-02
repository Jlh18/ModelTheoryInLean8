import field_theory.is_alg_closed.algebraic_closure
import data.zmod.basic
import data.equiv.transfer_instance
import Rings.ToMathlib.char_p
import algebra.char_p.algebra

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
