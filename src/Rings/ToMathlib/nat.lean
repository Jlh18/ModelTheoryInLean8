import data.nat.basic
import Rings.ToMathlib

namespace nat

variables {A B : Type*}

@[simp] def natlist : Π (n : ℕ) (as : ℕ → list A), list A
| nat.zero := λ as, []
| (nat.succ n) := λ as, (as n) ++ (natlist n as)

section

variables [has_mul A] [has_one A] [mul_one_class B]

-- def sum [has_add A] [has_zero A] : Π (n : ℕ) (as : ℕ → A), A
-- | nat.zero := λ as, 0
-- | (nat.succ n) := λ as, sum n as + as n

def prod [has_mul A] [has_one A] : Π (n : ℕ) (as : ℕ → A), A
| nat.zero := λ as, 1
| (nat.succ n) := λ as, prod n as * as n

lemma map_prod (f : mul_one_hom A B) : Π {n : ℕ} {as : ℕ → A},
f.to_fun (prod n as) = prod n (f.to_fun ∘ as)
| nat.zero as := f.map_one
| (nat.succ n) as :=
begin
  simp only [prod, f.map_mul],
  rw map_prod,
end

end

end nat
