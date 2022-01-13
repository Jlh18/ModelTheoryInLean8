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

lemma total_degree_sum
  {A : Type*} {ι : Type*} {σ} [comm_semiring A] (s : finset ι)
  [decidable_eq ι]
  (ps : ι → mv_polynomial σ A) :
  (finset.sum s ps).total_degree
  ≤
  finset.sup s (mv_polynomial.total_degree ∘ ps) :=
finset.induction_on s (zero_le _)
(λ a s has hind, by rw finset.sum_insert has;
  exact le_trans (mv_polynomial.total_degree_add _ _)
    ( by rw [max_le_iff, finset.sup_insert];
      exact ⟨ le_sup_iff.mpr $ or.inl (le_of_eq rfl) , le_sup_iff.mpr $ or.inr hind ⟩))

lemma total_degree_monomial
  {A : Type*} [comm_semiring A] [decidable_eq A]
  {σ : Type*} (f : σ →₀ ℕ) (a : A) :
  (mv_polynomial.monomial f a).total_degree
  =
  ite (a = 0) ⊥ (f.sum (λ _ n, n)) :=
dite (a = 0)
(λ h, by rw [mv_polynomial.total_degree, mv_polynomial.support_monomial,
  if_pos h, if_pos h, finset.sup_empty])
(λ h, by rw [mv_polynomial.total_degree, mv_polynomial.support_monomial,
  if_neg h, if_neg h, finset.sup_singleton])

noncomputable def finsupp_coeff_add_zero_hom
  (A : Type*) [comm_semiring A] {σ} (f : σ →₀ ℕ) :
  add_zero_hom (mv_polynomial σ A) A :=
⟨ (λ p, mv_polynomial.coeff f p) , rfl , λ a b, rfl ⟩

lemma finsupp_coeff_sumr
  {A : Type*} [comm_semiring A] {σ} (f : σ →₀ ℕ)
  (ps : list (mv_polynomial σ A)) :
  mv_polynomial.coeff f ps.sumr
  =
  list.sumr (list.map (λ p : mv_polynomial σ A, mv_polynomial.coeff f p) ps) :=
list.add_zero_hom_sumr (mv_polynomial.finsupp_coeff_add_zero_hom A f) ps


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
