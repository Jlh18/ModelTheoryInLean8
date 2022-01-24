import field_theory.algebraic_closure
import data.zmod.basic
import Rings.ToMathlib.char_p

namespace ulift.equiv

variables {k : Type*} [field k]

open ulift

def zero : ulift k := up 0

lemma zero_add (a : ulift k) :
  up (down (up 0) + down a) = a :=
begin
  rw ← up_down a,
  apply congr_arg up,
  simp only [down_up, zero_add],
end

lemma add_zero (a : ulift k) :
  up (down a + down (up 0)) = a :=
begin
  rw ← up_down a,
  apply congr_arg up,
  simp only [down_up, add_zero],
end

lemma add_comm (a b : ulift k) :
  up (down a + down b) = up (down b + down a) :=
congr_arg up (add_comm _ _)

lemma add_assoc (a b c : ulift k) :
  up (down (up (down a + down b)) + down c) =
  up (down a + down (up (down b + down c))) :=
begin
  apply congr_arg up,
  simp only [down_up, add_assoc],
end

lemma add_left_neg (a : ulift k) :
  up (down (up (- down a)) + down a) = up 0 :=
begin
  apply congr_arg up,
  simp only [down_up, add_left_neg],
end

lemma mul_one (a : ulift k) :
  up (down a * down (up 1)) = a :=
begin
  rw ← up_down a,
  apply congr_arg up,
  simp only [down_up, mul_one],
end

lemma one_mul (a : ulift k) :
  up (down (up 1) * down a) = a :=
begin
  rw ← up_down a,
  apply congr_arg up,
  simp only [down_up, one_mul],
end

lemma mul_comm (a b : ulift k) :
  up (down a * down b) = up (down b * down a) :=
congr_arg up (mul_comm _ _)

lemma mul_assoc (a b c : ulift k) :
  up (down (up (down a * down b)) * down c) =
  up (down a * down (up (down b * down c))) :=
begin
  apply congr_arg up,
  simp only [down_up, mul_assoc],
end

lemma left_distrib (a b c : ulift k) :
  down a * (down b + down c)
  = down a * down b + down a * down c :=
begin
  sorry
end


def field [field k] : field (ulift k) :=
equiv.field (equiv.ulift)

-- { zero             := up 0,
--   add              := λ a b, up (down a + down b),
--   neg              := λ a, up (- down a),
--   one              := up 1,
--   mul              := λ a b, up (down a * down b),
--   inv              := λ a, up ((down a)⁻¹),
--   zero_add         := zero_add,
--   add_zero         := add_zero,
--   add_comm         := add_comm,
--   add_assoc        := add_assoc,
--   add_left_neg     := add_left_neg,
--   mul_one          := mul_one,
--   one_mul          := one_mul,
--   mul_comm         := mul_comm,
--   mul_assoc        := mul_assoc,
--   left_distrib     := sorry,
--   right_distrib    := sorry,
--   exists_pair_ne   := sorry,
--   mul_inv_cancel   := sorry,
--   inv_zero         := sorry }

end ulift

namespace is_alg_closed

open polynomial

lemma of_exists_root_nat_degree {k : Type*} [field k] (H : ∀ p : polynomial k, p.monic → irreducible p → nat_degree p ≠ 0 → ∃ x, p.eval x = 0) :
  is_alg_closed k :=
begin
  apply of_exists_root,
  intros p hmonic hirr,
  by_cases hdeg : nat_degree p = 0,
  {
    rw monic.degree_eq_zero_iff_eq_one hmonic at hdeg,
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

namespace algebraic_closure

section zmod

variables (p : ℕ) [hp : fact (nat.prime p)]

include hp

@[reducible] def of_zmod := algebraic_closure (zmod p)

-- noncomputable lemma of_zmod.field : field (of_zmod p) :=
-- by apply_instance

-- noncomputable lemma of_zmod_algebra : (zmod p) →+* (of_zmod p) :=
-- algebra_map _ _

lemma of_zmod.char_p :
  char_p (of_zmod p) p :=
(ring_hom.char_p_iff_char_p (algebra_map (zmod p) (of_zmod p)) p).1 $ zmod.char_p p


@[reducible] def ulift_of_zmod : Type* := ulift (of_zmod p)

end zmod

end algebraic_closure
