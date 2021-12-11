import to_mathlib
import data.fin
import Rings.ToMathlib.fin

namespace dvector
  variable {A : Type*}

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

  def of_list {A : Type} : Π (as : list A), dvector A (list.length as)
  | list.nil := dvector.nil
  | (list.cons a as) := dvector.cons a (of_list as)


  def reverse {A : Type*} : Π {n : ℕ} (v : dvector A n),
    dvector A n
  | nat.zero _ := dvector.nil
  | (nat.succ n) (dvector.cons a v) := dvector.concat (reverse v) a

end dvector
