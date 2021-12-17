import Rings.Rings
import Rings.Fields
import Rings.ToMathlib.list
import Rings.ToMathlib.nat
import Rings.ToMathlib.fol
import Rings.ToMathlib.mv_polynomial
import Rings.ToMathlib.finset
import Rings.ToMathlib.dvector
import Rings.RealizeThings
import algebra.big_operators.finprod
import data.finset.basic
import Rings.AxGroth

open Rings
open AxGroth

noncomputable theory

lemma poly_map_data.coeffs_dvector'_nth_aux
  {A : Type*} [comm_ring A] {n d : ℕ}
  {ps : poly_map_data A n} (j : fin n) (f : fin n → ℕ)
    (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d) :
  list.index_of' f (monom_deg_le_finset n d).to_list + ↑j * (monom_deg_le_finset n d).to_list.length <
    n * monom_deg_le_length n d :=
begin
  have h1 : (1 + ↑j) * monom_deg_le_length n d ≤ n * monom_deg_le_length n d,
  {
    rw [mul_le_mul_right (zero_lt_monom_deg_le_length n d),
      nat.one_add, nat.succ_le_iff],
    exact j.2,
  },
  apply lt_of_lt_of_le _ h1,
  rw add_mul,
  apply add_lt_add_right,
  rw one_mul,
  apply list.index_of'_lt_length (zero_lt_monom_deg_le_length n d),
end

lemma poly_map_data.coeffs_dvector'_nth
  {A : Type*} [comm_ring A] {n d : ℕ}
  {ps : poly_map_data A n} (j : fin n) (f : fin n → ℕ)
    (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d) :
  (ps j).to_fun (finsupp_of_fin_dom_emb f) =
    (poly_map_data.coeffs_dvector' d ps).nth
      (list.index_of' f (monom_deg_le_finset n d).to_list +
        ↑j * (monom_deg_le_finset n d).to_list.length)
      (poly_map_data.coeffs_dvector'_nth_aux j f hdeg) :=
sorry




lemma realize_poly_map_data_coeffs_ys
  {A : Type*} [comm_ring A] {n d : ℕ}
  [decidable_eq (mv_polynomial (fin n) ↥(struc_to_ring_struc.Structure A))]
  (ps : poly_map_data A n)
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d)
  (xs ys : dvector ↥(struc_to_ring_struc.Structure A) n)
  (j : fin n)
  :
  mv_polynomial.eval (λ (i : fin n), ys.nth i i.2) (ps j)
  =
  list.sumr (list.map
    (λ (f : fin n → ℕ),
      (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth
        (list.index_of' f (monom_deg_le_finset n d).to_list +
           (j * (monom_deg_le_finset n d).to_list.length + n + n))
        (poly_indexed_by_monoms_aux0 n d _ _ inj_formula_aux0 f)
        *
        (n.non_comm_prod
          (λ (i : fin n),
            (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth
            (i + 0) inj_formula_aux3 ^ f i))
        )
    (monom_deg_le n d))
  :=
begin
  rw mv_polynomial.eval_eq',
  -- rw ← realize_poly_map_data_coeffs_ys_aux_prod ps xs ys,
  rw mv_polynomial_sum_eq_finset_map_monom_deg_le_finset_sum (ps j) (hdeg j),
  rw finset.sum_map,
  rw monom_deg_le,
  rw list.sumr_eq_sum,
  rw finset.sum_to_list,
  congr,
  funext f,
  rw realize_poly_map_data_coeffs_ys_aux_prod ps xs ys f,
  congr,
  rw mv_polynomial.coeff,
  rw dvector.nth_append_big,
  {
    rw dvector.nth_append_big,
    {
      simp only [add_assoc],
      simp only [symm (add_assoc (list.index_of' f (monom_deg_le_finset n d).to_list)
        (j * (monom_deg_le_finset n d).to_list.length ) (n + n))],
      simp only [symm (add_assoc (list.index_of' f (monom_deg_le_finset n d).to_list
        + j * (monom_deg_le_finset n d).to_list.length) n n)],
      simp only [nat.add_sub_cancel],
      sorry,
    },
    {
      rw ← add_assoc,
      rw nat.add_sub_cancel,
      rw ← add_assoc,
      apply nat.le_add_left,
    },
  },
  {
    rw ← add_assoc,
    apply nat.le_add_left,
  },


  -- have h : ∀ i : fin n, (finsupp_of_fin_dom_emb f) i = f i
  -- := congr_fun (to_fun_finsupp_of_fin_dom_emb f),
end

