import field_theory.algebraic_closure
import data.zmod.basic
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

end zmod

end algebraic_closure
