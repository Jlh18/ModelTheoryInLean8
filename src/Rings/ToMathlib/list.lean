import data.list
import Rings.ToMathlib

namespace list

variables {A B C : Type*}

@[simp] def mapr (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: mapr l

lemma comp_mapr (f : A → B) (g : B → C) : Π (as : list A),
  mapr (g ∘ f) as = mapr g (mapr f as)
| nil := rfl
| (cons hd tl) :=
begin
  simp only [true_and, eq_self_iff_true, mapr],
  rw comp_mapr,
end

@[simp] lemma mapr_append (f : A → B) : Π (l1 l2 : list A),
  mapr f (append l1 l2) = append (mapr f l1) (mapr f l2)
| nil l2 := by simp
| (cons hd tl) l2 :=
begin
  simp only [true_and, cons_append, eq_self_iff_true, mapr],
  rw mapr_append,
end

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
  f.to_fun as.sumr = (mapr f.to_fun as).sumr :=
begin
  induction as with a as hind,
  {
    simp only [sumr, mapr],
    exact f.map_zero,
  },
  {
    simp only [sumr, mapr],
    rw f.map_add,
    rw hind,
  }
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
