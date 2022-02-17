import field_theory.is_alg_closed.algebraic_closure
import data.zmod.basic
import data.equiv.transfer_instance
import Rings.ToMathlib.char_p


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


section zmod

variables (p : ℕ) [hp : fact (nat.prime p)]

include hp

/-- lift zmod up to any universe -/
def ulift_zmod := ulift (zmod p)

instance ulift_zmod.field : field (ulift_zmod p) := equiv.ulift.field

lemma down_nat_coe_ulift_of_zmod :
  Π {n : ℕ}, (n : ulift_zmod p).down = (n : zmod p)
| nat.zero := rfl
| (nat.succ n) :=
begin
  simp only [nat.cast_succ],
  rw ← down_nat_coe_ulift_of_zmod,
  refl,
end

lemma ulift_zmod.char_p : char_p (ulift_zmod p) p :=
begin
  split,
  intro n,
  rw ← (zmod.char_p p).cast_eq_zero_iff,
  split,
  {
    intro hn,
    have hn' := congr_arg ulift.down hn,
    convert hn',
    rw down_nat_coe_ulift_of_zmod,
  },
  {
    intro hn,
    rw ← ulift.up_down ↑n,
    rw ← ulift.up_down 0,
    apply congr_arg ulift.up,
    convert hn,
    rw down_nat_coe_ulift_of_zmod,
  },
end

end zmod


namespace algebraic_closure

section zmod

variables (p : ℕ) [hp : fact (nat.prime p)]

include hp

/-- algebraic closure of finite fields with char p lifted to any universe -/
@[reducible] def of_ulift_zmod := algebraic_closure (ulift_zmod p)

-- noncomputable instance fields : field (of_zmod p) := by apply_instance

universe u

-- noncomputable instance :
--  algebra (ulift_zmod.{u} p) (of_ulift_zmod.{u} p) := by apply_instance

/-- algebraic closure of zmod is still characteristic p -/
lemma of_ulift_zmod.char_p : char_p (of_ulift_zmod.{u} p) p :=
(ring_hom.char_p_iff_char_p (algebra_map (ulift_zmod.{u} p) (of_ulift_zmod.{u} p)) p).1 $ ulift_zmod.char_p p


-- @[reducible] def ulift_of_zmod : Type* := ulift (of_zmod p)

-- noncomputable instance of_zmod.field : field (ulift (of_zmod p)) := equiv.ulift.field

-- #check equiv.iff

-- lemma difjsij {α β : Type*} (hequiv : α ≃ β) (p : Type* → Prop) :
--   p α ↔ p β :=
-- by library_search

instance of_zmod.is_alg_closed : is_alg_closed (of_ulift_zmod p) :=
by apply_instance

-- lemma down_nat_coe_ulift_of_zmod :
--   Π {n : ℕ}, (n : ulift_of_zmod p).down = (n : of_zmod p)
-- | nat.zero := rfl
-- | (nat.succ n) :=
-- begin
--   simp only [nat.cast_succ],
--   rw ← down_nat_coe_ulift_of_zmod,
--   refl,
-- end

-- lemma ulift_of_zmod.char_p :
--   char_p (ulift_of_zmod p) p :=
-- begin
--   split,
--   intro n,
--   rw ← (of_zmod.char_p p).cast_eq_zero_iff,
--   split,
--   {
--     intro hn,
--     have hn' := congr_arg ulift.down hn,
--     convert hn',
--     rw down_nat_coe_ulift_of_zmod,
--   },
--   {
--     intro hn,
--     rw ← ulift.up_down ↑n,
--     rw ← ulift.up_down 0,
--     apply congr_arg ulift.up,
--     convert hn,
--     rw down_nat_coe_ulift_of_zmod,
--   },
-- end



end zmod

end algebraic_closure
