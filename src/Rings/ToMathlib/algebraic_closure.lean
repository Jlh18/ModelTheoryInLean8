import field_theory.algebraic_closure

namespace is_alg_closed

open polynomial

lemma of_monic_nat_degree_ne_zero_exists_root {k : Type*} [field k]
  (H : ∀ p : polynomial k, p.monic → nat_degree p ≠ 0 → ∃ x, p.eval x = 0) :
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
  apply H p hmonic hdeg,
end

lemma of_nat_degree_ne_zero_exists_root {k : Type*} [field k]
  (H : ∀ p : polynomial k, nat_degree p ≠ 0 → ∃ x, p.eval x = 0) :
  is_alg_closed k :=
of_monic_nat_degree_ne_zero_exists_root $ λ _ _ hdeg, H _ hdeg

end is_alg_closed
