import algebra.char_p.basic
import ring_theory.localization
import algebra.free_algebra
import algebra.char_p.algebra

-- namespace char_p

-- lemma ring_char_of_prime_eq_zero {R : Type*} [non_assoc_semiring R]
--   [nontrivial R] {p : ℕ}
--   (hprime : nat.prime p) (hp0 : (p : R) = 0) : ring_char R = p :=
-- or.resolve_left ((nat.dvd_prime hprime).1 (ring_char.dvd hp0)) ring_char_ne_one

-- end char_p

namespace ring_char

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

