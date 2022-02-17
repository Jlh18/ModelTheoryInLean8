import data.finset
import data.finsupp
import algebra.big_operators.order

namespace finset

lemma filter_mem_set_of_subset_set {α} {s : set α} [decidable_pred (λ x, x ∈ s)]
  {fs : finset α} (h : ↑fs ⊆ s) :
  filter (λ x, x ∈ s) fs = fs :=
begin
  ext x,
  split,
  { apply filter_subset },
  { intro hmem, rw mem_filter, exact ⟨ hmem , h hmem ⟩ },
end

end finset

namespace finsupp

lemma le_sum {σ : Type*}
  (f : σ →₀ ℕ) (x : σ) :
  f x ≤ f.support.sum f :=
dite (f x = 0)
(λ h, by simp [h])
(λ h, finset.single_le_sum (λ s hs, nat.zero_le _) (finsupp.mem_support_iff.2 h))

end finsupp
