import to_mathlib
import data.fin
import Rings.ToMathlib.fin

namespace dvector

variables {α : Type*} {n : ℕ}


lemma nil_append (as : dvector α n) :
  dvector.append dvector.nil as = as :=
by simp

/-- Converts a dvector into an n-ary tuple -/
@[simp] def fin_val (as : dvector α n) : fin n → α :=
λ k, dvector.nth' as k
 @[simp] lemma cons_nth'_succ_eq_nth' {n} {x : α} {as : dvector α n} {k : fin n} :
(dvector.cons x as).nth' (k.succ) = as.nth' k :=
begin
  unfold dvector.nth',
  simp,
end

/-- x_val is the same data as concatenation of dvectors -/
lemma fin_val_eq_x_val {x : α} {as : dvector α n} :
  fin_val (dvector.cons x as) = fin.x_val x (fin_val as) :=
funext (
  @fin.cases n
  (λ k, fin_val (dvector.cons x as) k = fin.x_val x (fin_val as) k)
  rfl
  (λ k, begin unfold fin_val, simp, end)
  )

lemma nth_eq_succ_nth : Π {k n : ℕ} {as : dvector α (n + 1)} {h : k < n},
as.nth k (lt_trans h (by simp)) = (dvector.remove_mth (n + 2) as).nth k h
| k nat.zero (dvector.cons a _) h := by {exfalso, simpa using h}
| nat.zero (nat.succ n) (dvector.cons a as) h := by simp
| (nat.succ k) (nat.succ n) (dvector.cons a as) h :=
  by {simpa using nth_eq_succ_nth}

def of_list : Π (as : list α), dvector α (list.length as)
| list.nil := dvector.nil
| (list.cons a as) := dvector.cons a (of_list as)

def reverse : Π {n : ℕ} (v : dvector α n),
  dvector α n
| nat.zero _ := dvector.nil
| (nat.succ n) (dvector.cons a v) := dvector.concat (reverse v) a

/-- if you append and take nth its the same as just taking nth for small n-/
lemma nth_append_small : Π {xl yl : ℕ}
  {xs : dvector α xl} {ys : dvector α yl} {n : ℕ} (h : n < xl),
  (dvector.append xs ys).nth n (nat.lt_of_lt_of_le h (nat.le_add_left _ _))
  = xs.nth n h
| 0             yl xs                  ys n h := by simpa using h
| (nat.succ xl) yl (dvector.cons x xs) ys 0 h := by simp
| (nat.succ xl) yl (dvector.cons x xs) ys (nat.succ n) h :=
begin
  simp only [dvector.nth, dvector.append],
  rw ← (@nth_append_small xl yl xs ys n (nat.succ_lt_succ_iff.1 h)),
  refl,
end

/-- if you append and take nth its the same as just taking n - kth for big n-/
lemma nth_append_big : Π {xl yl : ℕ}
  {xs : dvector α xl} {ys : dvector α yl} {n : ℕ}
  (hbig : xl ≤ n) (h : n < yl + xl),
  (dvector.append xs ys).nth n h
  = ys.nth (n - xl) ((nat.sub_lt_right_iff_lt_add hbig).2 h)
| 0             yl nil                 ys n hbig h := by simpa
| (nat.succ xl) yl (dvector.cons x xs) ys 0 hbig h :=
begin
  exfalso,
  exact nat.not_succ_le_zero _ hbig,
end
| (nat.succ xl) yl (dvector.cons x xs) ys (nat.succ n) hbig h :=
begin
  simp only [nat.succ_sub_succ_eq_sub, dvector.append, dvector.nth],
  apply nth_append_big (nat.le_of_succ_le_succ hbig),
end

lemma nth_cast : Π {xl yl k : ℕ}
  {xs : dvector α xl}
  (heq : xl = yl) (hk : k < yl),
  (dvector.cast heq xs).nth k hk = xs.nth k (by simp [heq, hk])
| 0             yl            k nil          heq hk :=
  (k.not_lt_zero (by simp [heq, hk])).elim
| (nat.succ xl) 0             k (cons x xs) heq hk :=
  (nat.succ_ne_zero _ heq).elim
| (nat.succ xl) (nat.succ yl) k (cons x xs) heq hk :=
begin
  rw dvector.cast_cons heq x xs,
  induction k with k hk,
  {simp},
  rw dvector.nth_cons _ _ _ (nat.lt_of_succ_lt_succ hk),
  exact nth_cast (nat.succ_injective heq) (nat.lt_of_succ_lt_succ hk),
end

lemma nth_of_list : Π (l : list α) (k : ℕ) (h : k < l.length),
  (dvector.of_list l).nth k h = list.nth_le l k h
| list.nil k h :=
begin
  exfalso,
  rw list.length at h,
  exact nat.not_lt_zero _ h,
end
| (a :: l) k h :=
begin
  rw of_list,
  induction k with k hk,
  {rw [dvector.nth, list.nth_le]},
  {simpa [dvector.nth, list.nth_le, nth_of_list l]},
end

end dvector
