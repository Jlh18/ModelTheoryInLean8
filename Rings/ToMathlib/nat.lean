import data.nat.basic
import Rings.ToMathlib.list
-- import Rings.ToMathlib

namespace nat

variables {A B : Type*}

@[simp] def natlist : Π (n : ℕ) (as : ℕ → list A), list A
| nat.zero := λ as, []
| (nat.succ n) := λ as, (as n) ++ (natlist n as)

section mul_one_class

variables [has_mul A] [has_one A] [mul_one_class B]

-- def sum [has_add A] [has_zero A] : Π (n : ℕ) (as : fin n → A), A
-- | nat.zero := λ as, 0
-- | (nat.succ n) := λ as, sum n (λ n, as n) + as n

@[simp] def non_comm_prod [has_mul A] [has_one A] :
  Π (n : ℕ) (as : fin n → A), A
| nat.zero := λ as, 1
| (nat.succ n) := λ as, non_comm_prod n (λ n, as n) * as n

lemma map_non_comm_prod (f : mul_one_hom A B) : Π {n : ℕ} {as : fin n → A},
f.to_fun (non_comm_prod n as) = non_comm_prod n (f.to_fun ∘ as)
| nat.zero as := f.map_one
| (nat.succ n) as :=
begin
  simp only [non_comm_prod, f.map_mul],
  rw map_non_comm_prod,
end

end mul_one_class

section comm_monoid

variables [comm_monoid B]

lemma non_comm_prod_eq_prod {n : ℕ} {as : fin n → B} :
  n.non_comm_prod as = finset.univ.prod as :=
begin
  induction n with n hn,
  {simp},
  {
    simp only [fin.coe_eq_cast_succ, non_comm_prod, fin.univ_cast_succ],
    rw finset.prod_insert,
    {
      rw mul_comm,
      congr,
      {
        apply fin.eq_of_veq,
        simp only [fin.val_eq_coe, fin.coe_last, fin.coe_of_nat_eq_mod],
        apply mod_eq_of_lt (lt_succ_self _),
      },
      {
        rw hn,
        simp only [imp_self, implies_true_iff,
          order_embedding.eq_iff_eq, finset.prod_image],
      },
    },
    {
      simp only [not_exists, finset.mem_univ, finset.mem_image,
        forall_true_left],
      intro i,
      apply ne_of_lt,
      apply fin.cast_succ_lt_last,
    },
  }
end

end comm_monoid

end nat
