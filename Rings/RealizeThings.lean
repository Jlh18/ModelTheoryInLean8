import Rings.ToMathlib.fol
import Rings.ToMathlib.list
import Rings.ToMathlib.nat
import Rings.Rings

open Rings fol

namespace realize_ring_term

variables
  {A : Type*} [comm_ring A]
  {c : ℕ} (xs : dvector (struc_to_ring_struc.Structure A) c)

@[simp] lemma list_sumr :
  Π {l : list (bounded_ring_term c)},
  realize_bounded_term xs (list.sumr l) dvector.nil
  =
  list.sumr (list.map (λ t, realize_bounded_term xs t dvector.nil) l)
| list.nil := by simp
| (list.cons t ts) :=
begin
  simp only [list.map, models_ring_theory_to_comm_ring.realize_add,
    ring_signature.add, list.sumr, realize_bounded_term],
  simp only [struc_to_ring_struc.func_map, dvector.last,
    struc_to_ring_struc.binaries_map, add_right_inj, dvector.nth],
  rw list_sumr,
end

def add_zero_hom :
  add_zero_hom (bounded_ring_term c) A :=
⟨ λ t, realize_bounded_term xs t dvector.nil ,
  models_ring_theory_to_comm_ring.realize_zero ,
  λ t s, models_ring_theory_to_comm_ring.realize_add ⟩

lemma sumr
  {ts : list (bounded_ring_term c)} :
  realize_bounded_term xs (ts).sumr dvector.nil
  =
  (list.map (add_zero_hom xs).to_fun ts).sumr :=
begin
  rw ← list.add_zero_hom_sumr (add_zero_hom xs) ts,
  refl,
end

lemma nat_non_comm_prod :
  Π (n : ℕ) (ts : fin n → bounded_ring_term c),
  realize_bounded_term xs (nat.non_comm_prod _ ts) dvector.nil
  =
  nat.non_comm_prod n (λ i, realize_bounded_term xs (ts i) dvector.nil)
| nat.zero ts :=
begin
  simp only [nat.non_comm_prod],
  refl,
end
| (nat.succ n) ts :=
begin
  simp only [nat.non_comm_prod, struc_to_ring_struc.func_map,
    dvector.last, struc_to_ring_struc.binaries_map, realize_bounded_term,
    ring_signature.mul, dvector.nth],
  rw nat_non_comm_prod n,
end

lemma pow (t : bounded_ring_term c) : Π (n : ℕ),
  realize_bounded_term xs (npow_rec n t) dvector.nil
  =
  (realize_bounded_term xs t dvector.nil) ^ n
| nat.zero := by simp only [nat.nat_zero_eq_zero, ring_signature.pow_zero,
    realize_bounded_term, models_ring_theory_to_comm_ring.realize_one,
    ring_signature.one, models_ring_theory_to_comm_ring.realize_one, pow_zero]
| (nat.succ n) := by simp only [struc_to_ring_struc.func_map,
  dvector.last, ring_signature.pow_succ, struc_to_ring_struc.binaries_map,
  realize_bounded_term, ring_signature.mul, dvector.nth, pow n, pow_succ]

end realize_ring_term
