import data.list
import data.fintype.card

structure add_zero_hom (M N : Type*) [has_zero M] [has_zero N] [has_add M] [has_add N] :=
(to_fun : M → N)
(map_zero : to_fun 0 = 0)
(map_add : Π a b : M, to_fun (a + b) = to_fun a + to_fun b)

structure mul_one_hom (M N : Type*) [has_one M] [has_one N] [has_mul M] [has_mul N] :=
(to_fun : M → N)
(map_one : to_fun 1 = 1)
(map_mul : Π a b : M, to_fun (a * b) = to_fun a * to_fun b)


namespace list

variables {A B C : Type*}

section sumr
variables [has_zero A] [has_add A] [has_zero B] [has_add B]

@[simp] def sumr : list A → A
| nil := 0
| (cons hd tl) := hd + sumr tl

def eval_sumr (f : add_zero_hom A B) : Π (l : list A),
  f.to_fun (sumr l) = sumr (list.map f.to_fun l)
| nil := by simpa using f.map_zero
| (cons hd tl) :=
begin
  simp only [sumr, map, add_zero_hom.map_add],
  rw eval_sumr,
end

end sumr

@[simp] lemma sumr_append [add_comm_group B] :
  Π (l1 l2 : list B), sumr (l1 ++ l2) = sumr l1 + sumr l2
| nil l2 := by simp
| (cons hd tl) l2 :=
begin
  simp only [cons_append, sumr],
  rw sumr_append,
  rw add_assoc,
end

lemma mapr_sumr
  [has_zero A] [has_add A] [add_comm_group B] (f : add_zero_hom A B) (as : list A) :
  f.to_fun as.sumr = (map f.to_fun as).sumr :=
begin
  induction as with a as hind,
  {
    simp only [sumr, map],
    exact f.map_zero,
  },
  {
    simp only [sumr, map],
    rw f.map_add,
    rw hind,
  }
end

lemma sumr_eq_sum
  [add_comm_group A] (as : list A) :
  as.sumr = as.sum :=
begin
  induction as with a as hind,
  {simp},
  {
    simp only [sumr, map, sum_cons, add_right_inj],
    exact hind,
  }
end

/-- if all the lists from fin n → list α are the same length m then
  the whole thing has length n * m
-/
lemma map_length_of_fn_const {α} {n m : ℕ} (f : fin n → list α)
  (h : ∀ i : fin n, (f i).length = m) :
  (list.map list.length (list.of_fn f)).sum = n * m :=
begin
 rw list.map_of_fn,
 rw list.sum_of_fn,
 have h' : (λ (i : fin n), (list.length ∘ f) i) = λ (i : fin n), m,
 {funext, exact h i},
 rw h',
 simp,
end

@[simp] def index_of' {A : Type*} [decidable_eq A] (a : A) (l : list A) : ℕ :=
ite (a ∈ l) (index_of a l) 0

lemma index_of'_lt_length {A : Type*} [decidable_eq A] {a : A} {l : list A}
  (h0 : 0 < l.length) :
  index_of' a l < l.length :=
begin
  by_cases h : a ∈ l,
  {simp only [h, if_true, index_of', index_of_lt_length]},
  {simp only [h, if_false, index_of', h0]},
end


-- lemma realize_bounded_term_mapr_append
--   [has_zero A] [has_add A] [add_comm_group B] (f : A → B) {as l2 : list A} :
--   f (as ++ l2).sumr = (mapr f as).sumr + (mapr f l2).sumr :=
-- begin
--   induction as,
--   {
--     simp,

--   },
--   sorry
-- end

end list

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


end to_list

end finset
