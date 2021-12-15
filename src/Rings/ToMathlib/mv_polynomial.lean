import data.mv_polynomial
import data.mv_polynomial.comm_ring
import Rings.ToMathlib.list
import Rings.ToMathlib.finset

namespace mv_polynomial

lemma support_le_total_degree
  {A σ : Type*} [comm_ring A]
  {p : mv_polynomial σ A} (x : σ)
  (f : σ →₀ ℕ) (hf : f ∈ p.support) :
  f x ≤ mv_polynomial.total_degree p :=
begin
  apply le_trans _ (finset.le_sup hf),
  simp only [finsupp.sum],
  apply finsupp.le_sum,
end


-- variables
--   {σ S₁ R : Type*}
--   [comm_semiring R] [comm_semiring S₁]
--   {p q : mv_polynomial σ R}

-- lemma sum_support_eq_sumr {n : ℕ} (p : mv_polynomial (fin n) R) {as : (fin n → ℕ) → R} :
-- (p).support.sum
--       (λ f, as f) =
--     (list.mapr as
--        -- (λ (f : fin n → ℕ),
--        --    (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth
--        --        (list.index_of' f (n_var_monom_of_deg_le_d_finset n d).to_list +
--        --           (↑i * (n_var_monom_of_deg_le_d_finset n d).to_list.length + n + n))
--        --        _ *
--        --      n.non_comm_prod
--        --        (λ (i : fin n),
--        --           (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth (↑i + 0) inj_formula_aux3 ^ f i))
--        (n_var_monom_of_deg_le n d)).sumr

end mv_polynomial
