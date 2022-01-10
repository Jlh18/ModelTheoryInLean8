import data.list
import data.fintype.card

-- not list things but these are needed for this file,
-- hence are kept here (to avoid mutual imports)

structure add_zero_hom (M N : Type*) [has_zero M] [has_zero N] [has_add M] [has_add N] :=
(to_fun : M → N)
(map_zero : to_fun 0 = 0)
(map_add : Π a b : M, to_fun (a + b) = to_fun a + to_fun b)

structure mul_one_hom (M N : Type*) [has_one M] [has_one N] [has_mul M] [has_mul N] :=
(to_fun : M → N)
(map_one : to_fun 1 = 1)
(map_mul : Π a b : M, to_fun (a * b) = to_fun a * to_fun b)

namespace finset

lemma card_filter_fin_lt {n k : ℕ} (hkn : k < n) :
  (finset.filter (λ (j : fin n), ↑j < k) finset.univ).card = k :=
begin
  -- have h := finset.card_range k,
  refine finset.card_eq_of_bijective
    (λ i hik, ⟨ i , lt_trans hik hkn ⟩) _ _ _,
  {
    intros i hi,
    use i.1,
    have h : i.1 < k,
    {
      simp only [true_and, finset.mem_univ, finset.mem_filter] at hi,
      exact hi,
    },
    use h,
    simp,
  },
  {
    intros i hik,
    simp [hik],
  },
  {
    intros i j hi hj,
    exact fin.mk.inj_iff.mp,
  }
end

end finset

-- all the list lemmas

namespace list

variables {α β : Type*}

section sumr
variables [has_zero α] [has_add α] [has_zero β] [has_add β]

@[simp] def sumr : list α → α
| nil := 0
| (cons hd tl) := hd + sumr tl

def add_zero_hom_sumr (f : add_zero_hom α β) : Π (l : list α),
  f.to_fun (sumr l) = sumr (list.map f.to_fun l)
| nil := by simpa using f.map_zero
| (cons hd tl) :=
begin
  simp only [sumr, map, add_zero_hom.map_add],
  rw add_zero_hom_sumr,
end

end sumr

@[simp] lemma sumr_append [add_comm_group β] :
  Π (l1 l2 : list β), sumr (l1 ++ l2) = sumr l1 + sumr l2
| nil l2 := by simp
| (cons hd tl) l2 :=
begin
  simp only [cons_append, sumr],
  rw sumr_append,
  rw add_assoc,
end

-- lemma mapr_sumr
--   [has_zero α] [has_add α] [add_comm_group β] (f : add_zero_hom α β) (as : list α) :
--   f.to_fun as.sumr = (map f.to_fun as).sumr :=
-- begin
--   induction as with a as hind,
--   {
--     simp only [sumr, map],
--     exact f.map_zero,
--   },
--   {
--     simp only [sumr, map],
--     rw f.map_add,
--     rw hind,
--   }
-- end

lemma sumr_eq_sum
  [add_comm_group α] (as : list α) :
  as.sumr = as.sum :=
begin
  induction as with a as hind,
  {simp},
  {
    simp only [sumr, map, sum_cons, add_right_inj],
    exact hind,
  }
end

lemma map_length_of_fn {n : ℕ} (f : fin n → list α) :
  list.map list.length (list.of_fn f)
  = list.of_fn (λ i : fin n, (f i).length) := by simp

/-- if all the lists from fin n → list α are the same length m then
  the whole thing has length n * m
-/
lemma sum_map_length_of_fn_const_length {n l : ℕ} (f : fin n → list α)
  (h_const_length : ∀ i : fin n, (f i).length = l) :
  (list.map list.length (list.of_fn f)).sum = n * l :=
by rw [list.map_of_fn, list.sum_of_fn, funext (λ i, h_const_length i)]; simp

lemma length_join_of_fn_const_length {n l : ℕ} (f : fin n → list α)
  (h_const_length : ∀ i : fin n, (f i).length = l) :
  (list.of_fn f).join.length = n * l :=
by rw [list.length_join, sum_map_length_of_fn_const_length f h_const_length]

@[simp] def index_of' [decidable_eq α] (a : α) (l : list α) : ℕ :=
ite (a ∈ l) (index_of a l) 0

lemma index_of'_lt_length [decidable_eq α] {a : α} {l : list α}
  (h0 : 0 < l.length) :
  index_of' a l < l.length :=
begin
  by_cases h : a ∈ l,
  {simp only [h, if_true, index_of', index_of_lt_length]},
  {simp only [h, if_false, index_of', h0]},
end

lemma index_of'_nth_le [decidable_eq α]
  {a : α} {l : list α} (h : a ∈ l) :
  l.nth_le (index_of' a l) (index_of'_lt_length (length_pos_of_mem h)) = a :=
by simp only [index_of', h, index_of_nth_le, if_true]

lemma nth_le_join_of_fn_const_length_aux
  {n l k i : ℕ} (as : fin n → list α)
  (h_const_length : ∀ i : fin n, (as i).length = l)
  (hkn : k < n) (hil : i < l) :
  i + k * l < (list.of_fn as).join.length :=
begin
  rw list.length_join_of_fn_const_length as h_const_length,
  have h1 : (1 + k) * l ≤ n * l,
  {
    apply mul_le_mul_right' _ l,
    rw [nat.one_add, nat.succ_le_iff],
    exact hkn,
  },
  apply lt_of_lt_of_le _ h1,
  rw [add_mul, one_mul],
  exact add_lt_add_right hil _,
end

lemma nth_le_join_of_fn_const_length {n l k i : ℕ} (as : fin n → list α)
  (h_const_length : ∀ i : fin n, (as i).length = l)
  (hkn : k < n) (hil : i < l) :
  (list.of_fn as).join.nth_le (i + k * l)
    (list.nth_le_join_of_fn_const_length_aux as h_const_length hkn hil)
  =
  (as ⟨ k , hkn ⟩).nth_le i (by simp [hil, h_const_length]) :=
begin
  have hkn' : k < (list.of_fn as).length := by simp [hkn],
  have hil' : i < ((list.of_fn as).nth_le k (by simp [hkn])).length :=
    by simp [hil, h_const_length],
  have hrw : i + k * l = ((list.take k (list.map list.length (list.of_fn as))).sum + i),
  {
    rw nat.add_comm i,
    congr,
    rw list.map_length_of_fn,
    simp only [h_const_length],
    rw list.sum_take_of_fn,
    simp only [nat.cast_id, nsmul_eq_mul, fin.val_eq_coe,
      finset.sum_const, finset.filter_congr_decidable, mul_eq_mul_right_iff],
    left,
    rw finset.card_filter_fin_lt hkn,
  },
  simp only [hrw, list.nth_le_of_fn',
    list.nth_le_join (list.of_fn as) hkn' hil'],
end



end list

