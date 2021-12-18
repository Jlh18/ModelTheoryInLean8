import Rings.Rings
import Rings.Fields
import Rings.ToMathlib.list
import Rings.ToMathlib.nat
import Rings.ToMathlib.fol
import Rings.ToMathlib.mv_polynomial
import Rings.RealizeThings
import algebra.big_operators.finprod
import data.finset.basic

namespace AxGroth

noncomputable theory

universe u

open fol
open Rings

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
def finsupp_of_fin_dom {A : Type*} [has_zero A] {n : ℕ} :
  (fin n → A) → fin n →₀ A :=
finsupp.equiv_fun_on_fintype.inv_fun

def finsupp_of_fin_dom_emb {A : Type*} [has_zero A] {n : ℕ} :
  (fin n → A) ↪ (fin n →₀ A) :=
equiv.to_embedding finsupp.equiv_fun_on_fintype.symm

@[simp] lemma to_fun_finsupp_of_fin_dom {A : Type*} [has_zero A] {n : ℕ}
  (f : fin n → A) : (finsupp_of_fin_dom f).to_fun = f :=
begin
  simp only [finsupp_of_fin_dom],
  funext k,
  simpa,
end

@[simp] lemma finsupp_of_fin_dom_to_fun {A : Type*} [has_zero A] {n : ℕ}
  (f : fin n →₀ A) : finsupp_of_fin_dom f.to_fun = f :=
begin
  simp only [finsupp_of_fin_dom],
  apply finsupp.ext,
  intro k,
  simpa,
end

lemma to_fun_finsupp_of_fin_dom_emb {A : Type*} [has_zero A] {n : ℕ}
  (f : fin n → A) : (finsupp_of_fin_dom_emb f).to_fun = f :=
begin
  simp only [finsupp_of_fin_dom_emb],
  exact to_fun_finsupp_of_fin_dom f,
end


/-- {f : fin n → ℕ | ∀ i, f i < d.succ }-/
@[simp] def n_var_bd_monom (n d : ℕ) : finset (fin n → ℕ) :=
finset.map (@monom_of_bd_monom n d.succ)
finset.univ

-- then convert these to maps f : fin n → ℕ
/-- { f : fin n → ℕ | sum f ≤ d } -/
@[simp] def monom_deg_le_finset (n d : ℕ) : finset (fin n → ℕ) :=
finset.filter
  (λ f : fin n → ℕ, (finsupp_of_fin_dom f).support.sum f ≤ d)
  (n_var_bd_monom n d)


/-- list of all n-variable monomials of degree ≤ d -/
def monom_deg_le (n d : ℕ) : list (fin n → ℕ) :=
(monom_deg_le_finset n d).to_list

/-- counts all n-variable monomials of degree ≤ d -/
-- def monom_deg_le_length (n d : ℕ) : ℕ :=
-- list.length $ monom_deg_le n d

/-- lists all n-variable monomials of degree ≤ d as finsupp maps-/
@[simp] def monom_deg_le₀ (n d : ℕ) : list (fin n →₀ ℕ) :=
list.map (finsupp_of_fin_dom) $ monom_deg_le n d

-- no restriction on degree
/-- takes a polynomial in n variables and gives a list of its coefficients-/
@[simp] def coeffs_list_of_mv_polynomial
  {K : Type*} [comm_semiring K] {n : ℕ} (d : ℕ)
  (p : mv_polynomial (fin n) K) : list K :=
list.map (λ m, mv_polynomial.coeff m p) (monom_deg_le₀ n d)

/-- there is always a monomial of degree ≤ d,
  namely the constant polynomial 0 -/
lemma monom_deg_le_length_ne_zero (n d : ℕ) :
  (monom_deg_le n d).length ≠ 0 :=
begin
  simp only [monom_deg_le,
    finset.length_to_list, finset.card_map,
    monom_deg_le_finset],
  apply finset.card_ne_zero_of_mem _,
  {exact λ i, 0},
  {
    simp only [finset.mem_univ, finset.sum_const_zero,
      finset.mem_filter, n_var_bd_monom, and_true, finset.mem_map,
      zero_le', exists_true_left],
    exact ⟨ (λ _, 0), by simp,
    (begin
      simp only [monom_of_bd_monom],
      funext,
      refl,
    end)⟩,
  },
end

lemma zero_lt_monom_deg_le_length (n d : ℕ) :
  0 < (monom_deg_le n d).length :=
  nat.pos_of_ne_zero (monom_deg_le_length_ne_zero n d)

lemma monom_deg_le₀_nth_le {n d k : ℕ}
  (hk : k < (monom_deg_le n d).length) :
  (monom_deg_le₀ n d).nth_le k (by simp [hk]) =
  finsupp_of_fin_dom_emb ((monom_deg_le n d).nth_le k hk) :=
begin
  simp only [list.length_map, list.length,
    list.nth_le, monom_deg_le₀, list.map, finsupp_of_fin_dom_emb,
    finsupp_of_fin_dom],
  simp,
end

lemma index_of_monom_deg_le_lt_length {n d : ℕ} (f : fin n → ℕ) :
  list.index_of' f (monom_deg_le_finset n d).to_list
  < (monom_deg_le n d).length :=
list.index_of'_lt_length (zero_lt_monom_deg_le_length n d)

lemma index_of_monom_deg_le₀_lt_length {n d : ℕ} (f : fin n → ℕ) :
  list.index_of' f (monom_deg_le_finset n d).to_list
  < (monom_deg_le₀ n d).length :=
begin
  rw monom_deg_le₀,
  rw list.length_map,
  apply list.index_of'_lt_length (zero_lt_monom_deg_le_length n d),
end

/-- the bound hndc is enough in poly_indexed_by_monoms -/
lemma poly_indexed_by_monoms_aux0 (n d s c : ℕ)
  (hndc : (monom_deg_le n d).length + s ≤ c) (f : fin n → ℕ) :
  list.index_of' f (monom_deg_le n d) + s < c :=
begin
  apply nat.lt_of_lt_of_le _ hndc,
  apply nat.add_lt_add_right,
  apply list.index_of'_lt_length,
  apply nat.pos_of_ne_zero (monom_deg_le_length_ne_zero n d),
end

/-- if i ∈ fin n and n + p ≤ c then i + p < c -/
lemma fin_add_lt_of_add_le (n p c : ℕ) (hnpc : n + p ≤ c) (i : fin n) :
(i : ℕ) + p < c :=
begin
  apply nat.lt_of_lt_of_le _ hnpc,
  apply nat.add_lt_add_right i.2,
end

/-- ∑_{f ∈ monom_deg_le n d} xⱼ₊ₛ ∏ {0 ≤ i < n} xᵢ₊ₚᶠ⁽ⁱ⁾ in "context c"
 where j is the index of f in monom_deg_le n d
 the context should at least include the variables xⱼ₊ₛ -- this is hndc
 the context should at least include the variables xᵢ₊ₚ -- this is hpc -/
@[simp] def poly_indexed_by_monoms (n d s p c : ℕ)
  (hndsc : (monom_deg_le n d).length + s ≤ c)
  (hnpc : n + p ≤ c) :
  bounded_ring_term c :=
-- sum indexed by the n-variable monom of degree < d
list.sumr
(list.map
  (λ f : (fin n → ℕ),
    let
      x_js : bounded_ring_term c :=
      x_ ⟨(list.index_of' f (monom_deg_le n d) + s) ,
      poly_indexed_by_monoms_aux0 n d s c hndsc f ⟩,
      x_ip (i : fin n) : bounded_ring_term c :=
      x_ ⟨ (i : ℕ) + p , fin_add_lt_of_add_le n p c hnpc i ⟩
    in
    x_js * (n.non_comm_prod $ λ i, npow_rec (f i) (x_ip i))
    )
  (monom_deg_le n d)
)

lemma realize_poly_indexed_by_monoms
  {A : Type*} [comm_ring A] {n d s p c : ℕ}
  (hndsc : (monom_deg_le n d).length + s ≤ c)
  (hnpc : n + p ≤ c)
  {xs : dvector (struc_to_ring_struc.Structure A) c}  :
  realize_bounded_term xs
    (poly_indexed_by_monoms n d s p c hndsc hnpc) dvector.nil
  =
  list.sumr
  (list.map
    (λ f,
    (dvector.nth xs (list.index_of' f (monom_deg_le n d) + s)
      (poly_indexed_by_monoms_aux0 n d s c hndsc f))
    *
    (n.non_comm_prod $ λ i,
    ((dvector.nth xs (i + p) (fin_add_lt_of_add_le n p c hnpc i)) ^ (f i) ))
    )
  (monom_deg_le n d)
  ) :=
begin
  simp only [poly_indexed_by_monoms],
  rw realize_ring_term.sumr,
  rw ← list.comp_map,
  congr,
  funext f,
  simp only [realize_ring_term.add_zero_hom, function.comp_app],
  simp only [struc_to_ring_struc.func_map, fin.val_eq_coe, dvector.last,
    struc_to_ring_struc.binaries_map, realize_bounded_term,
    ring_signature.mul, dvector.nth],
  congr,
  rw realize_ring_term.nat_non_comm_prod,
  congr,
  funext i,
  rw realize_ring_term.pow,
  simp,
end

lemma inj_formula_aux0 {n d : ℕ} {j : fin n} :
  (monom_deg_le n d).length +
    (j * ((monom_deg_le n d).length) + n + n)
  ≤
  n * (monom_deg_le n d).length + n + n :=
begin
  let c := n * ((monom_deg_le n d).length) + n + n,
  let monom := (monom_deg_le n d).length,
  repeat {rw ← nat.add_assoc, apply nat.add_le_add_right},
  cases nat.exists_eq_succ_of_ne_zero (ne_zero_of_lt j.2) with k hk,
  have hrw : n * (monom_deg_le n d).length = (monom_deg_le n d).length + k * (monom_deg_le n d).length,
  {
    rw hk,
    rw nat.succ_mul,
    rw nat.add_comm,
  },
  rw hrw,
  apply nat.add_le_add_left,
  apply nat.mul_le_mul_of_nonneg_right,
  apply nat.le_of_lt_succ,
  rw ← hk,
  exact j.2,
end

lemma inj_formula_aux1 {n d : ℕ} :
  n + 0
  ≤
  n * (monom_deg_le n d).length + n + n :=
begin
  rw add_comm,
  apply nat.add_le_add_right,
  apply nat.zero_le,
end

lemma inj_formula_aux2 {n d : ℕ} :
  n + n
  ≤
  n * (monom_deg_le n d).length + n + n :=
begin
  rw nat.add_assoc,
  apply nat.le_add_left,
end

lemma inj_formula_aux3 {n d : ℕ} {i : fin n} :
  (i : ℕ)
  <
  n * (monom_deg_le n d).length + n + n :=
begin
  apply nat.lt_of_lt_of_le i.2,
  apply nat.le_add_left,
end

lemma inj_formula_aux4 {n d : ℕ} {i : fin n} :
  (i : ℕ) + n < n * (monom_deg_le n d).length + n + n :=
begin
  rw nat.add_assoc,
  apply nat.lt_add_left,
  apply nat.add_lt_add_right,
  exact i.2,
end

-- in the context of having n polynomials pⱼ indexed by
-- their monomial coefficients,
-- if for all xᵢ and all yᵢ, every polynomial satisfies pⱼ xᵢ = pⱼ yᵢ
-- then each xᵢ = yᵢ.
-- This says the polynomial map formed by the pⱼs is injective
/-- Injectivity of polynomial maps stated model-theoretically-/
def inj_formula (n d : ℕ) :
  bounded_ring_formula (n * (monom_deg_le n d).length) :=
  let monom := (monom_deg_le n d).length in
-- for all pairs in the domain x₋ ∈ Kⁿ and ...
bd_alls' n _
$
-- ... y₋ ∈ Kⁿ
bd_alls' n _
$
-- if at each pⱼ
(bd_big_and n
-- pⱼ xᵢ = pⱼ yᵢ
  (λ j,
    (poly_indexed_by_monoms n d (j * monom + n + n) n _ -- note n
      inj_formula_aux0 inj_formula_aux2)
    ≃
    (poly_indexed_by_monoms n d (j * monom + n + n) 0 _ -- note 0
      inj_formula_aux0 inj_formula_aux1)
  )
)
-- then
⟹
-- at each 0 ≤ i < n,
(bd_big_and n $ λ i,
-- xᵢ = yᵢ (where yᵢ is written as xᵢ₊ₙ₊₁)
  x_ ⟨ i , inj_formula_aux3 ⟩ ≃ x_ (⟨ i + n , inj_formula_aux4 ⟩)
)

-- in the context of having n polynomials pⱼ indexed by
-- their monomial coefficients,
-- for all z₋ ∈ Kⁿ, there exists x₋ ∈ Kⁿ such that each zⱼ = pⱼ x₋
-- This says the polynomial map formed by the pⱼs is surjective
/-- Surjectivity of polynomial maps stated model-theoretically-/
def surj_formula (n d : ℕ) :
  bounded_ring_formula (n * (monom_deg_le n d).length) :=
let monom := (monom_deg_le n d).length in
-- for all x₋ ∈ Kⁿ in the codomain
bd_alls' n _
$
-- there exists y₋ ∈ Kⁿ in the domain such that
bd_exs' n _
$
-- at each 0 ≤ j < n
bd_big_and n
$
-- pⱼ y₋ = xⱼ
λ j,
  poly_indexed_by_monoms n d (j * monom + n + n) 0 _
    inj_formula_aux0 inj_formula_aux1
  ≃
  x_ ⟨ j + n , inj_formula_aux4 ⟩

/-- Ax-Grothendieck stated model-theoretically -/
def Ax_Groth_formula (n d : ℕ) : sentence ring_signature :=
-- quantify over n many (n-variable polynomials) called ps;
-- i.e. the data of a polynomial map
-- by quantifying over (n * monom_of_bounded_degree) monomial coefficients
bd_alls (n * ((monom_deg_le n d).length))
-- if the polynomial function is injective then it is surjective
$ inj_formula n d ⟹ surj_formula n d

/-- the data of a polynomial map consists of n polynomials in n variables -/
@[simp] def poly_map_data (K : Type*) [comm_semiring K] (n : ℕ) : Type* :=
fin n → mv_polynomial (fin n) K

/-- a polynomial map evaluates those polynomials that it consists of -/
def poly_map {K : Type*} [comm_semiring K] {n : ℕ} :
  poly_map_data K n → (fin n → K) → (fin n → K) :=
λ ps as k, mv_polynomial.eval as (ps k)

/-- The main result: algebraically closed fields of characteristic zero
   satisfy Ax-Grothendieck formula -/
lemma realize_Ax_Groth_formula {K : Type*} [field K] [is_alg_closed K]
  (h0 : char_zero K) (n d : ℕ) :
  struc_to_ring_struc.Structure K ⊨ Ax_Groth_formula n d :=
sorry

section semiring

variables {A : Type*} [comm_semiring A] {n : ℕ}

/-- takes a polynomial map
  (preferably of total deg < d) and gives list of coeffs of each polynomial -/
@[simp] def poly_map_data.coeffs_list
  {n : ℕ} (d : ℕ) (ps : poly_map_data A n) : list A :=
list.join (list.of_fn (λ i : fin n, coeffs_list_of_mv_polynomial d (ps i)))

/- Writes polynomial map into a dvector of its coefficients -/
def poly_map_data.coeffs_dvector
  {n : ℕ} (d : ℕ) (ps : poly_map_data A n) :
  dvector A (poly_map_data.coeffs_list d ps).length :=
dvector.of_list (poly_map_data.coeffs_list d ps)

/-- the number of coefficients of mv_polynomial = number of monomials -/
lemma coeffs_list_length_eq_monom_deg_le_length {d : ℕ}
  (p : mv_polynomial (fin n) A) :
  (coeffs_list_of_mv_polynomial d p).length
  =
  (monom_deg_le n d).length := by simp

/-- lemma for matching up lengths of contexts for mv_polynomials -/
lemma variable_bound_equal {n : ℕ} (d : ℕ) (ps : poly_map_data A n) :
  (n * (monom_deg_le n d).length)
  =
  (poly_map_data.coeffs_list d ps).length :=
begin
  simp only [poly_map_data.coeffs_list, list.length_join],
  rw list.sum_map_length_of_fn_const_length,
  intro i,
  apply coeffs_list_length_eq_monom_deg_le_length,
end

/-- Writes polynomial map into a dvector of its coefficients
  (with a replaced variable context) -/
def poly_map_data.coeffs_dvector' {n : ℕ} (d : ℕ)
  (ps : poly_map_data A n) :
  dvector A (n * (monom_deg_le n d).length) :=
dvector.cast (symm (variable_bound_equal d ps))
  (poly_map_data.coeffs_dvector d ps)

end semiring

-- ⇑(mv_polynomial.eval (λ (i : fin n), ys.reverse.nth ↑i _)) (ps i) =
--     realize_bounded_term (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps)))
--      (poly_indexed_by_monoms n d (↑i * (monom_deg_le_finset n d).to_list.length + n + n) 0
--          (n * (monom_deg_le n d).length + n + n)
--          _
--          _)
--       dvector.nil

-- {A : Type*} [comm_ring A] {n d s p c : ℕ}
--   (hndsc : (monom_deg_le n d).length + s ≤ c)
--   (hnpc : n + p ≤ c)
--   {xs : dvector (struc_to_ring_struc.Structure A) c}  :
--   realize_bounded_term xs
--     (poly_indexed_by_monoms hndsc hnpc) dvector.nil
--   =
--

section realize_poly_map_data_coeffs_xs_and_ys

variables {A : Type*} [comm_ring A] {n d : ℕ}
  (p : mv_polynomial (fin n) A)

/-- the support of a polynomial of degree ≤ d is contained in the set of monomials of degree ≤ d -/
lemma support_sub_monom_deg_le_finset (hdeg : p.total_degree ≤ d) :
  p.support ⊆ finset.map finsupp_of_fin_dom_emb (monom_deg_le_finset n d) :=
begin
  intros f hf,
  simp only [true_and, exists_prop, finset.mem_univ,
    finset.mem_map, monom_deg_le_finset, finset.mem_filter],
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
    {exact finsupp_of_fin_dom_to_fun f},
  end ⟩,
end

/-- the support union its complement (in monom_deg_le_finset) is equal to the whole thing-/
lemma support_union_compl_eq_monom_deg_le_finset
  [decidable_eq (mv_polynomial (fin n) A)] (hdeg : p.total_degree ≤ d) :
  p.support ∪
    (finset.map finsupp_of_fin_dom_emb (monom_deg_le_finset n d)
      \ p.support) =
  finset.map finsupp_of_fin_dom_emb (monom_deg_le_finset n d) :=
finset.union_sdiff_of_subset $ support_sub_monom_deg_le_finset _ hdeg

lemma mv_polynomial_sum_eq_finset_map_monom_deg_le_finset_sum
  [decidable_eq (mv_polynomial (fin n) A)]
  (hdeg : p.total_degree ≤ d)
  (as : (fin n →₀ ℕ) → A)
  :
  p.support.sum (λ (f : fin n →₀ ℕ), mv_polynomial.coeff f p * as f)
  =
  (finset.map finsupp_of_fin_dom_emb (monom_deg_le_finset n d)).sum
  (λ (f : fin n →₀ ℕ), mv_polynomial.coeff f p * as f)
  :=
begin
  rw ← support_union_compl_eq_monom_deg_le_finset p hdeg,
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

variables (ps : poly_map_data A n)
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d)
  (xs ys : dvector ↥(struc_to_ring_struc.Structure A) n)

lemma realize_poly_map_data_coeffs_xs_aux_prod
  (f : fin n → ℕ) :
  n.non_comm_prod
  (λ (i : fin n),
    (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth
    (i + n) inj_formula_aux4 ^ f i) =
  finset.univ.prod (λ (i : fin n), xs.nth i i.2 ^ f i) :=
begin
  rw nat.non_comm_prod_eq_prod,
  congr,
  funext i,
  rw dvector.nth_append_big
    (nat.le_add_left n _) inj_formula_aux4,
  simp only [nat.add_sub_cancel i n],
  rw dvector.nth_append_small,
end

lemma realize_poly_map_data_coeffs_ys_aux_prod
  (f : fin n → ℕ) :
  n.non_comm_prod
  (λ (i : fin n),
    (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth
    (i + 0) inj_formula_aux3 ^ f i) =
  finset.univ.prod (λ (i : fin n), ys.nth i i.2 ^ f i) :=
begin
  rw nat.non_comm_prod_eq_prod,
  congr,
  funext i,
  simp only [add_zero],
  rw ← @dvector.nth_append_small _ _ _ ys,
end

lemma poly_map_data.coeffs_dvector'_nth_aux0
  (j : fin n) (f : fin n → ℕ) :
  list.index_of' f (monom_deg_le_finset n d).to_list
    + ↑j * (monom_deg_le_finset n d).to_list.length
  <
    n * (monom_deg_le n d).length :=
begin
  have h1 : (1 + ↑j) * (monom_deg_le n d).length ≤ n * (monom_deg_le n d).length,
  {
    rw [mul_le_mul_right (zero_lt_monom_deg_le_length _ _),
      nat.one_add, nat.succ_le_iff],
    exact j.2,
  },
  apply lt_of_lt_of_le _ h1,
  rw add_mul,
  apply add_lt_add_right,
  rw one_mul,
  apply list.index_of'_lt_length (zero_lt_monom_deg_le_length _ _),
end

lemma poly_map_data.coeffs_dvector'_nth_aux1
  {ps : poly_map_data A n} :
  ∀ (i : fin n),
  ((λ (i : fin n), coeffs_list_of_mv_polynomial d (ps i)) i).length
  = (monom_deg_le n d).length :=
λ i, coeffs_list_length_eq_monom_deg_le_length (ps i)

lemma poly_map_data.coeffs_dvector'_nth_aux2
  (j : fin n) (f : fin n → ℕ)
  (hf : f ∈ monom_deg_le n d) :
  finsupp_of_fin_dom_emb.to_fun f
  =
  (monom_deg_le₀ n d).nth_le
    (list.index_of' f (monom_deg_le_finset n d).to_list)
    (index_of_monom_deg_le₀_lt_length f) :=
begin
  rw monom_deg_le₀_nth_le (index_of_monom_deg_le_lt_length f),
  apply congr_arg,
  simp only,
  delta monom_deg_le,
  have h := @list.index_of'_nth_le _ _
    f (monom_deg_le_finset n d).to_list hf,
  funext i,
  rw ← congr_fun h i,
  congr,
end

lemma poly_map_data.coeffs_dvector'_nth
  {A : Type*} [comm_ring A] {n d : ℕ}
  {ps : poly_map_data A n} (j : fin n) (f : fin n → ℕ)
  (hf : f ∈ monom_deg_le_finset n d) :
  (ps j).to_fun (finsupp_of_fin_dom_emb f) =
    (poly_map_data.coeffs_dvector' d ps).nth
      (list.index_of' f (monom_deg_le_finset n d).to_list +
        ↑j * (monom_deg_le n d).length)
      (poly_map_data.coeffs_dvector'_nth_aux0 j f) :=
begin
  rw [poly_map_data.coeffs_dvector', dvector.nth_cast,
    poly_map_data.coeffs_dvector, dvector.nth_of_list],
  delta poly_map_data.coeffs_list,
  unfold_coes,
  rw list.nth_le_join_of_fn_const_length
    (λ (i : fin n), coeffs_list_of_mv_polynomial d (ps i))
    poly_map_data.coeffs_dvector'_nth_aux1
    j.2
    (index_of_monom_deg_le_lt_length _),
  have h :
    ((λ (i : fin n), coeffs_list_of_mv_polynomial d (ps i)) ⟨ j.1 , j.2⟩)
    =
    coeffs_list_of_mv_polynomial d (ps ⟨ j.1 , j.2 ⟩),
  {refl},
  simp only [h],
  delta coeffs_list_of_mv_polynomial,
  delta mv_polynomial.coeff,
  rw list.nth_le_map,
  have hj : (⟨ j.1, j.2 ⟩ : fin n) = j := fin.eta j j.2,
  rw [hj],
  apply congr_arg,
  have hf' : f ∈ (monom_deg_le_finset n d).to_list :=
  (finset.mem_to_list _).2 hf,
  exact poly_map_data.coeffs_dvector'_nth_aux2 j f hf',
  -- {exact index_of_monom_deg_le₀_lt_length _},
end

lemma realize_poly_map_data_coeffs_xs
  [decidable_eq (mv_polynomial (fin n) A)]
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d) (j : fin n) :
  mv_polynomial.eval (λ (i : fin n), xs.nth i i.2) (ps j)
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
             (i + n) inj_formula_aux4 ^ f i))
         )
    (monom_deg_le n d))
  :=
begin
  rw mv_polynomial.eval_eq',
  rw mv_polynomial_sum_eq_finset_map_monom_deg_le_finset_sum (ps j) (hdeg j),
  rw finset.sum_map,
  rw list.sumr_eq_sum,
  delta monom_deg_le,
  rw finset.sum_to_list,
  apply finset.sum_congr rfl,
  intros f hf,
  rw realize_poly_map_data_coeffs_xs_aux_prod ps xs ys f,
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
      exact poly_map_data.coeffs_dvector'_nth _ f hf,
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
end

lemma realize_poly_map_data_coeffs_ys
  [decidable_eq (mv_polynomial (fin n) ↥(struc_to_ring_struc.Structure A))]
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d) (j : fin n) :
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
    (monom_deg_le_finset n d).to_list)
  :=
begin
  rw mv_polynomial.eval_eq',
  -- rw ← realize_poly_map_data_coeffs_ys_aux_prod ps xs ys,
  rw mv_polynomial_sum_eq_finset_map_monom_deg_le_finset_sum (ps j) (hdeg j),
  rw finset.sum_map,
  delta monom_deg_le,
  rw list.sumr_eq_sum,
  rw finset.sum_to_list,
  apply finset.sum_congr rfl,
  intros f hf,
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
      exact poly_map_data.coeffs_dvector'_nth _ f hf,
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
end


end realize_poly_map_data_coeffs_xs_and_ys

section max_total_deg

variables {K : Type*} [comm_semiring K]

@[simp] def max_total_deg :
  Π {n m : ℕ}, (fin n → mv_polynomial (fin m) K) → ℕ
| 0 _ ps := 0
| (n + 1) _ ps :=
  max (max_total_deg (λ (i : fin n), ps i)) (mv_polynomial.total_degree (ps n))


def total_deg_le_max_total_deg :
  Π {n m : ℕ} (ps : fin n → mv_polynomial (fin m) K) (i : fin n),
  mv_polynomial.total_degree (ps i) ≤ max_total_deg ps
| 0 _ ps i := fin_zero_elim i
| (n + 1) _ ps i :=
begin
  simp only [max_total_deg],
  rw le_max_iff,
  cases fin.lt_or_eq_fin i with h,
  {
    left,
    have hlt : (i : ℕ) < n,
    {
      rw fin.lt_coe_iff_val_lt i (nat.lt_succ_self _),
      exact h,
    },
    have hind :=
    @total_deg_le_max_total_deg n _ (λ j, ps j.val.cast) ⟨ i , hlt ⟩,
    simp only [fin.coe_eq_cast_succ, fin.cast_succ_mk, fin.eta] at hind,
    rw ← fin.coe_coe_eq_self i,
    exact hind,
  },
  {
    right,
    rw h,
  },
end

end max_total_deg

section alg_closed_field
open classical
local attribute [instance] prop_decidable

variables {K : Type*} [field K] [is_alg_closed K]

lemma Ax_Groth_inj_aux
  {n d : ℕ}
  (ps : poly_map_data K n)
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d)
  (hinj : function.injective (poly_map ps))
  : @realize_bounded_formula _ (struc_to_ring_struc.Structure K)
    _ _ (@poly_map_data.coeffs_dvector' K _ n d ps)
    (inj_formula n d) dvector.nil :=
begin
  let xs0 := poly_map_data.coeffs_dvector' d ps,
  -- open up the definition of inj_formula and what it means to realize it
  simp only [inj_formula,
    realize_bounded_formula_bd_alls',
    realize_bounded_formula_bd_alls',
    realize_bounded_formula_imp,
    realize_bounded_formula_bd_big_and],
  intros xs ys, -- n tuples in the domain
  -- we are showing that ps xs = ps yx implies xs = ys
  intro hImage, -- assume the images are all equal (expressed model theoretically)
  -- we must translate this to the images are equal
  -- (expressed algebraically / in the ring)
  have himage : poly_map ps (λ i, dvector.nth xs i i.2)
               = poly_map ps (λ i, dvector.nth ys i i.2),
  {
    funext j, -- for each i < n (... the tuples at i are equal)
    simp only [poly_map],
    have hImagei := hImage j,
    simp only [realize_bounded_formula,
      monom_deg_le, realize_poly_indexed_by_monoms] at hImagei,
    convert hImagei,
    {rw realize_poly_map_data_coeffs_xs ps xs ys hdeg j, refl },
    {rw realize_poly_map_data_coeffs_ys ps xs ys hdeg j, refl },
  },
  -- by injectivity of poly_map ps we have the preimages are equal (pointwise)
  intro i, -- for each input (... they are equal)
  have hpreimage : dvector.nth xs i i.2 = dvector.nth ys i i.2,
  {apply congr_fun (hinj himage) i},
  simp only [realize_bounded_formula,
    realize_bounded_term,
    @dvector.nth_append_small _ _ _ ys _ i i.2,
    dvector.nth_append_big (nat.le_add_left _ _),
    nat.add_sub_cancel,
    @dvector.nth_append_small _ _ _ xs _ i i.2,
    hpreimage],
end

lemma Ax_Groth_surj_aux
  {n d : ℕ}
  (ps : poly_map_data K n)
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d)
  (hSurj : @realize_bounded_formula _ (struc_to_ring_struc.Structure K)
    _ _ (@poly_map_data.coeffs_dvector' K _ n d ps)
    (surj_formula n d) dvector.nil) :
  function.surjective (poly_map ps)
  :=
begin
  simp only [surj_formula,
    realize_bounded_formula_bd_alls',
    realize_bounded_formula_bd_exs',
    realize_bounded_formula_bd_big_and,
    realize_bounded_formula] at hSurj,
  intro xs, -- for any n tuple xs in the codomain
  cases hSurj (dvector.of_fn xs) with ys hys,
  use (dvector.nth' ys), -- there exists an n tuple ys in the domain
  funext k,
  delta poly_map,
  delta dvector.nth',
  have hysk := hys k,
  have hrw0 : realize_bounded_term
    (ys.append ((dvector.of_fn xs).append (poly_map_data.coeffs_dvector' d ps)))
    x_⟨ k + n , inj_formula_aux4 ⟩ dvector.nil = xs k,
  {
    simp only [realize_bounded_term, symm (fin.val_eq_coe _)],
    rw dvector.nth_append_big (nat.le_add_left _ _) _,
    rw dvector.nth_append_small,
    {
      simp only [nat.add_sub_cancel],
      rw dvector.nth_of_fn,
      congr,
      simp only [fin.val_eq_coe, fin.eta],
    },
    {
      rw nat.add_sub_cancel,
      exact k.2
    },
  },
  rw hrw0 at hysk,
  simp only [realize_bounded_formula,
      monom_deg_le, realize_poly_indexed_by_monoms] at hysk,
  have hrw1 := realize_poly_map_data_coeffs_ys ps (dvector.of_fn xs) ys hdeg k,
  have hrw2 := symm (eq.trans hrw1 hysk),
  have hrw3 : ⇑(mv_polynomial.eval (λ (i : fin n), ys.nth i.1 i.2)) (ps k)
    = ⇑(mv_polynomial.eval (λ (i : fin n), ys.nth i i.2)) (ps k),
  {simpa only [fin.val_eq_coe]},
  rw [hrw3, ← hrw2],
end

lemma Ax_Groth_aux
  (h0 : char_zero K) {n d : ℕ}
  (ps : poly_map_data K n)
  (hdeg : ∀ (i : fin n), mv_polynomial.total_degree (ps i) ≤ d)
  (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps) :=
begin
  let xs0 := poly_map_data.coeffs_dvector' d ps,
  have hAG := realize_Ax_Groth_formula h0 n d,
  simp only [realize_sentence_bd_alls,
    Ax_Groth_formula, realize_bounded_formula] at hAG,
  -- injective -> realize inj_formula
  have hInj : @realize_bounded_formula _ (struc_to_ring_struc.Structure K) _ _
    (poly_map_data.coeffs_dvector' d ps) (inj_formula n d) dvector.nil,
  {exact Ax_Groth_inj_aux ps hdeg hinj},
  -- apply realize_Ax_Groth to ps, i.e. apply hAG to its coefficients
  have hSurj := hAG xs0 hInj,
  exact Ax_Groth_surj_aux ps hdeg hSurj,
end

theorem Ax_Groth
  (h0 : char_zero K) {n : ℕ}
  (ps : poly_map_data K n) (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps) :=
Ax_Groth_aux h0 ps (total_deg_le_max_total_deg ps) hinj

end alg_closed_field
end AxGroth
