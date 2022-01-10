import data.finset
import data.finsupp
import algebra.big_operators.order

namespace finset

section to_list

variables {α : Type*} {β : Type*} {γ : Type*}
/-- Produce a list of the elements in the finite set using choice. -/
@[reducible] noncomputable def to_list (s : finset α) : list α := s.1.to_list

lemma nodup_to_list (s : finset α) : s.to_list.nodup :=
by { rw [to_list, ←multiset.coe_nodup, multiset.coe_to_list], exact s.nodup }

@[simp] lemma mem_to_list {a : α} (s : finset α) : a ∈ s.to_list ↔ a ∈ s :=
by { rw [to_list, ←multiset.mem_coe, multiset.coe_to_list], exact iff.rfl }

@[simp] lemma length_to_list (s : finset α) : s.to_list.length = s.card :=
by { rw [to_list, ←multiset.coe_card, multiset.coe_to_list], refl }

@[simp] lemma to_list_empty : (∅ : finset α).to_list = [] :=
by simp [to_list]

@[simp, norm_cast]
lemma coe_to_list (s : finset α) : (s.to_list : multiset α) = s.val :=
by { classical, ext, simp }

@[simp] lemma to_list_to_finset [decidable_eq α] (s : finset α) : s.to_list.to_finset = s :=
by { ext, simp }

@[to_additive] lemma prod_to_list [comm_monoid β]
  (s : finset α) (f : α → β) :
  (list.map f s.to_list).prod = finset.prod s f :=
begin
  delta finset.prod,
  rw [← multiset.coe_prod, ← multiset.coe_map, finset.coe_to_list],
end

lemma to_list_cons {a : α} {s : finset α} (h : a ∉ s) : (cons a s h).to_list ~ a :: s.to_list :=
(list.perm_ext (nodup_to_list _) (by simp [h, nodup_to_list s])).2 $
  λ x, by simp only [list.mem_cons_iff, finset.mem_to_list, finset.mem_cons]

lemma to_list_insert [decidable_eq α] {a : α} {s : finset α} (h : a ∉ s) :
  (insert a s).to_list ~ a :: s.to_list :=
cons_eq_insert _ _ h ▸ to_list_cons _

end to_list

end finset

namespace finsupp

lemma le_sum {σ : Type*}
  (f : σ →₀ ℕ) (x : σ) :
  f x ≤ f.support.sum f :=
dite (f x = 0)
(λ h, by simp [h])
(λ h, finset.single_le_sum (λ s hs, nat.zero_le _) (finsupp.mem_support_iff.2 h))

end finsupp
