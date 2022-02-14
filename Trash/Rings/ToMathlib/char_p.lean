import algebra.char_p.basic
import ring_theory.localization
import algebra.free_algebra

namespace ring_char

lemma of_prime_eq_zero
  {A : Type*} [non_assoc_semiring A] [nontrivial A]
  {p : ℕ} (hprime : nat.prime p) (hp0 : (p : A) = 0) :
  ring_char A = p :=
begin
  have hchar : ring_char A ∣ p := ring_char.dvd hp0,
  unfold nat.prime at hprime,
  have heq := hprime.2 (ring_char A) hchar,
  cases heq,
  { exfalso,
    exact char_p.ring_char_ne_one heq },
  { exact heq },
end

lemma lt_char {A : Type*} [non_assoc_semiring A]
  {n : ℕ} : (n : A) = 0 → n < ring_char A → n = 0 :=
begin
  rw spec A n,
  exact nat.eq_zero_of_dvd_of_lt,
end

lemma lt_char_field {A : Type*} [field A]
  {n : ℕ} : (n : A) = 0 → n < ring_char A → n = 0 :=
begin
  rw spec A n,
  exact nat.eq_zero_of_dvd_of_lt,
end


end ring_char

/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
lemma char_p_of_injective_algebra_map {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (h : function.injective (algebra_map R A)) (p : ℕ) [char_p R p] : char_p A p :=
{ cast_eq_zero_iff := λx,
  begin
    rw ←char_p.cast_eq_zero_iff R p x,
    change algebra_map ℕ A x = 0 ↔ algebra_map ℕ R x = 0,
    rw is_scalar_tower.algebra_map_apply ℕ R A x,
    refine iff.trans _ h.eq_iff,
    rw ring_hom.map_zero,
  end }
