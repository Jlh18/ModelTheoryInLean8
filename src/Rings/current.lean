import Rings.Rings
import Rings.Fields
import Rings.ToMathlib.list
import Rings.ToMathlib.nat
import Rings.ToMathlib.fol
import Rings.ToMathlib.mv_polynomial
import Rings.RealizeThings
import algebra.big_operators.finprod
import data.finset.basic

noncomputable theory

/-- composition by coe : fin d → ℕ -/
def monom_of_bd_monom {n d : ℕ} :
  (fin n → fin d) ↪ fin n → ℕ :=
⟨
  λ f, coe ∘ f ,
  λ f g h,
  begin
    funext i,
    have h' := congr_fun h i,
    apply fin.coe_injective h',
  end
⟩

/-- converts map from fin n to same map with finite support -/
def finsupp_of_fin_dom {A : Type*} [has_zero A] {n : ℕ}
  (f : fin n → A) :
  fin n →₀ A :=
finsupp.on_finset finset.univ f (λ a h, finset.mem_univ _)

def finsupp_of_fin_dom_emb {A : Type*} [has_zero A] {n : ℕ} :
  (fin n → A) ↪ fin n →₀ A :=
⟨
  finsupp_of_fin_dom ,
  λ _ _ h, congr_arg finsupp.to_fun h,
⟩

lemma finsupp_of_fin_dom_to_fun {A : Type*} [has_zero A] {n : ℕ}
  (f : fin n →₀ A) : finsupp_of_fin_dom f.to_fun = f :=
begin
  simp only [finsupp_of_fin_dom],
  apply finsupp.ext,
  intro k,
  simpa,
end

/-- {f : fin n → ℕ | ∀ i, f i < d.succ }-/
@[simp] def n_var_bd_monom (n d : ℕ) : finset (fin n → ℕ) :=
finset.map (@monom_of_bd_monom n d.succ)
finset.univ

-- then convert these to maps f : fin n → ℕ
/-- { f : fin n → ℕ | sum f ≤ d } -/
@[simp] def n_var_monom_of_deg_le_finset (n d : ℕ) : finset (fin n → ℕ) :=
finset.filter
  (λ f : fin n → ℕ, (finsupp_of_fin_dom f).support.sum f ≤ d)
  (n_var_bd_monom n d)


/-- list of all n-variable monomials of degree ≤ d -/
def n_var_monom_of_deg_le (n d : ℕ) : list (fin n → ℕ) :=
(n_var_monom_of_deg_le_finset n d).to_list

/-- counts all n-variable monomials of degree ≤ d -/
def n_var_monom_of_deg_le_length (n d : ℕ) : ℕ :=
list.length $ n_var_monom_of_deg_le n d



def support_sub_n_var_monom_of_deg_le_finset
  {A : Type*} [comm_ring A] {n d : ℕ}
  (p : mv_polynomial (fin n) A)
  (hdeg : p.total_degree ≤ d)
  :
  p.support ⊆
  finset.map finsupp_of_fin_dom_emb (n_var_monom_of_deg_le_finset n d) :=
begin
  intros f hf,
  simp only [true_and, exists_prop, finset.mem_univ,
    finset.mem_map, n_var_monom_of_deg_le_finset, finset.mem_filter],
  exact ⟨ f.to_fun,
  begin
    have hf_img_lt : ∀ i : fin n, f i < d.succ,
    {
      intro i,
      rw nat.lt_succ_iff,
      apply le_trans _ hdeg,
      exact mv_polynomial.support_le_total_degree i f hf,
    },
    refine ⟨ ⟨ _ , _ ⟩ , _ ⟩ ,
    {
      simp only [n_var_bd_monom, monom_of_bd_monom, finset.mem_map,
        finset.mem_univ],
      refine ⟨ λ k, ⟨ f k, hf_img_lt k⟩, _ , _ ⟩,
      {simp},
      {funext, simpa},
    },
    {
      apply le_trans _ hdeg,
      rw finsupp_of_fin_dom_to_fun,
      apply finset.le_sup hf,
    },
    {
      simp only [finsupp_of_fin_dom_emb, finsupp_of_fin_dom_to_fun,
        function.embedding.coe_fn_mk],
    }
  end ⟩,
end

lemma support_union_compl_eq_n_var_monom_of_deg_le_finset
  {A : Type*} [comm_ring A] {n d : ℕ}
  (p : mv_polynomial (fin n) A)
  (hdeg : p.total_degree ≤ d)
  :
  p.support ∪
  (finset.map finsupp_of_fin_dom_emb (n_var_monom_of_deg_le_finset n d)
    \ p.support) =
  finset.map finsupp_of_fin_dom_emb (n_var_monom_of_deg_le_finset n d) :=
finset.union_sdiff_of_subset $ support_sub_n_var_monom_of_deg_le_finset _ hdeg

lemma mv_polynomial_sum_eq_finset_map_n_var_monom_of_deg_le_finset_sum
  {A : Type*} [comm_ring A] {n d : ℕ}
  (p : mv_polynomial (fin n) A)
  (hdeg : p.total_degree ≤ d)
  (as : (fin n →₀ ℕ) → A)
  :
  p.support.sum (λ (f : fin n →₀ ℕ), mv_polynomial.coeff f p * as f)
  =
  (finset.map finsupp_of_fin_dom_emb (n_var_monom_of_deg_le_finset n d)).sum
  (λ (f : fin n →₀ ℕ), mv_polynomial.coeff f p * as f)
  :=
begin
  rw ← support_union_compl_eq_n_var_monom_of_deg_le_finset p hdeg,
  rw finset.sum_union,
  {
    set LHS :=
      p.support.sum (λ (f : fin n →₀ ℕ), mv_polynomial.coeff f p * as f)
      with hLHS,
    rw ← add_zero LHS,
    rw ← hLHS,
    congr,
    symmetry,
    apply finset.sum_eq_zero,
    intros f hf,
    rw finset.mem_sdiff at hf,
    cases hf with hfl hfr,
    unfold mv_polynomial.coeff,
    rw finsupp.not_mem_support_iff.1 hfr,
    exact zero_mul _,
  },
  {exact disjoint_sdiff_self_right},
end
