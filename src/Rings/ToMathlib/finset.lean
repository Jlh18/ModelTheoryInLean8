import data.finset
import data.finsupp
import algebra.big_operators.order

namespace finsupp

lemma le_sum {σ : Type*}
  (f : σ →₀ ℕ) (x : σ) :
  f x ≤ f.support.sum f :=
dite (f x = 0)
(λ h, by simp [h])
(λ h, finset.single_le_sum (λ s hs, nat.zero_le _) (finsupp.mem_support_iff.2 h))

end finsupp
