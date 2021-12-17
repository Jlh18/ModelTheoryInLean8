import to_mathlib
import data.fin
import Rings.ToMathlib.fin

namespace dvector
  variable {A : Type*}


  lemma nil_append {A} {n} (f : dvector A n) :
    dvector.append dvector.nil f = f :=
  by simp

  /-- Converts a dvector into an n-ary tuple -/
  @[simp] def fin_val {n} (as : dvector A n) : fin n → A :=
  λ k, dvector.nth' as k

    @[simp] lemma cons_nth'_succ_eq_nth' {n} {x : A} {as : dvector A n} {k : fin n} :
  (dvector.cons x as).nth' (k.succ) = as.nth' k :=
  begin
    unfold dvector.nth',
    simp,
  end

  /-- x_val is the same data as concatenation of dvectors -/
  lemma fin_val_eq_x_val {n} {x : A} {as : dvector A n} :
    fin_val (dvector.cons x as) = fin.x_val x (fin_val as) :=
  funext (
    @fin.cases n
    (λ k, fin_val (dvector.cons x as) k = fin.x_val x (fin_val as) k)
    rfl
    (λ k, begin unfold fin_val, simp, end)
    )

  lemma nth_eq_succ_nth : Π {k n : ℕ} {as : dvector A (n + 1)} {h : k < n},
  as.nth k (lt_trans h (by simp)) = (dvector.remove_mth (n + 2) as).nth k h
  | k nat.zero (dvector.cons a _) h := by {exfalso, simpa using h}
  | nat.zero (nat.succ n) (dvector.cons a as) h := by simp
  | (nat.succ k) (nat.succ n) (dvector.cons a as) h := by {simpa using nth_eq_succ_nth}

  def of_list {A : Type*} : Π (as : list A), dvector A (list.length as)
  | list.nil := dvector.nil
  | (list.cons a as) := dvector.cons a (of_list as)


  def reverse {A : Type*} : Π {n : ℕ} (v : dvector A n),
    dvector A n
  | nat.zero _ := dvector.nil
  | (nat.succ n) (dvector.cons a v) := dvector.concat (reverse v) a

  /-- if you append and take nth its the same as just taking nth for small n-/
  def nth_append_small {α : Type*} : Π {xl yl : ℕ}
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
def nth_append_big {α : Type*} : Π {xl yl : ℕ}
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

end dvector
