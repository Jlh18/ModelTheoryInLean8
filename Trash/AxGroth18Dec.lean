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
def monom_deg_le_length (n d : ℕ) : ℕ :=
list.length $ monom_deg_le n d

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
  monom_deg_le_length n d ≠ 0 :=
begin
  simp only [monom_deg_le, monom_deg_le_length,
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
  0 < monom_deg_le_length n d :=
  nat.pos_of_ne_zero (monom_deg_le_length_ne_zero n d)

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
  monom_deg_le_length n d +
    (j * (monom_deg_le_length n d) + n + n)
  ≤
  n * monom_deg_le_length n d + n + n :=
begin
  let c := n * (monom_deg_le_length n d) + n + n,
  let monom := monom_deg_le_length n d,
  repeat {rw ← nat.add_assoc, apply nat.add_le_add_right},
  cases nat.exists_eq_succ_of_ne_zero (ne_zero_of_lt j.2) with k hk,
  have hrw : n * monom_deg_le_length n d = monom_deg_le_length n d + k * monom_deg_le_length n d,
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
  n * monom_deg_le_length n d + n + n :=
begin
  rw add_comm,
  apply nat.add_le_add_right,
  apply nat.zero_le,
end

lemma inj_formula_aux2 {n d : ℕ} :
  n + n
  ≤
  n * monom_deg_le_length n d + n + n :=
begin
  rw nat.add_assoc,
  apply nat.le_add_left,
end

lemma inj_formula_aux3 {n d : ℕ} {i : fin n} :
  (i : ℕ)
  <
  n * monom_deg_le_length n d + n + n :=
begin
  apply nat.lt_of_lt_of_le i.2,
  apply nat.le_add_left,
end

lemma inj_formula_aux4 {n d : ℕ} {i : fin n} :
  (i : ℕ) + n < n * monom_deg_le_length n d + n + n :=
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
  bounded_ring_formula (n * monom_deg_le_length n d) :=
  let monom := monom_deg_le_length n d in
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
  bounded_ring_formula (n * monom_deg_le_length n d) :=
let monom := monom_deg_le_length n d in
-- for all z₋ ∈ Kⁿ in the codomain
bd_alls' n _
$
-- there exists x₋ ∈ Kⁿ in the domain such that
bd_exs' n _
$
-- at each 0 ≤ j < n
bd_big_and n
$
-- zⱼ = pⱼ x₋
λ j,
  x_ ⟨ j , inj_formula_aux3 ⟩
  ≃
  poly_indexed_by_monoms n d (j * monom + n + n) 0 _
    inj_formula_aux0 inj_formula_aux1

/-- Ax-Grothendieck stated model-theoretically -/
def Ax_Groth_formula (n d : ℕ) : sentence ring_signature :=
-- quantify over n many (n-variable polynomials) called ps;
-- i.e. the data of a polynomial map
-- by quantifying over (n * monom_of_bounded_degree) monomial coefficients
bd_alls (n * (monom_deg_le_length n d))
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
  monom_deg_le_length n d :=
begin
  unfold monom_deg_le_length,
  simp,
end

/-- lemma for matching up lengths of contexts for mv_polynomials -/
lemma variable_bound_equal {n : ℕ} (d : ℕ) (ps : poly_map_data A n) :
  (n * monom_deg_le_length n d)
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
  dvector A (n * monom_deg_le_length n d) :=
dvector.cast (symm (variable_bound_equal d ps))
  (poly_map_data.coeffs_dvector d ps)

end semiring

-- ⇑(mv_polynomial.eval (λ (i : fin n), ys.reverse.nth ↑i _)) (ps i) =
--     realize_bounded_term (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps)))
--      (poly_indexed_by_monoms n d (↑i * (monom_deg_le_finset n d).to_list.length + n + n) 0
--          (n * monom_deg_le_length n d + n + n)
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

lemma realize_poly_map_data_coeffs_xs
  (ps : poly_map_data A n)
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d)
  (xs ys : dvector ↥(struc_to_ring_struc.Structure A) n)
  (i : fin n)
  :
  mv_polynomial.eval (λ (i : fin n), xs.nth i i.2) (ps i)
  =
  list.sumr (list.map
    (λ (f : fin n → ℕ),
       (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth
         (list.index_of' f (monom_deg_le_finset n d).to_list +
            (↑i * (monom_deg_le_finset n d).to_list.length + n + n))
         (poly_indexed_by_monoms_aux0 n d _ _ inj_formula_aux0 f)
         *
         (n.non_comm_prod
           (λ (i : fin n),
             (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth
             (↑i + n) inj_formula_aux4 ^ f i))
         )
    (monom_deg_le n d))
  :=
begin
  sorry
end
--   rw realize_poly_indexed_by_monoms,
--   { sorry },
--   {
--     intro f, -- f is a monomial
--     simp only [monom_deg_le],
--     sorry,
--   },
--   {
--     sorry
--   },
-- end\
--
--n.non_comm_prod
--(λ (i : fin n),
--   (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps))).nth (↑i + 0)
--   inj_formula_aux3 ^ f i))

lemma realize_poly_map_data_coeffs_ys_aux_prod
  (ps : poly_map_data A n)
  (xs ys : dvector ↥(struc_to_ring_struc.Structure A) n)
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

-- lemma sum_support_eq_list_sum_aux
--   {A : Type*} [comm_ring A] {n d : ℕ}
--   (p : mv_polynomial (fin n) A) {as : (fin n → ℕ) → A}
--   (hdeg : ∀ (i : fin n), p.total_degree ≤ d) :
--   p.support.sum (λ (f : fin n →₀ ℕ), as ⇑f)
--   =
--   sorry
--   -- p.support.sum (λ (f : fin n →₀ fin d.succ), as (coe ∘ f))
--   :=
-- sorry

-- #check @finsupp.support_sum

-- lemma sum_support_eq_list_sum
--   {A : Type*} [comm_ring A] {n d : ℕ}
--   (p : mv_polynomial (fin n) A) {as : (fin n → ℕ) → A}
--   (hdeg : ∀ (i : fin n), p.total_degree ≤ d) :
--   p.support.sum (λ f, as f)
--   =
--   (list.map as (monom_deg_le n d)).sum :=
-- begin
--   unfold monom_deg_le,
--   unfold monom_deg_le_finset,
--   unfold monom_of_bd_monom,

-- end

-- #check list.map


-- lemma sum_support_eq_list_sumr
--   {A : Type*} [comm_ring A] {n d : ℕ}
--   (p : mv_polynomial (fin n) A) {as : (fin n → ℕ) → A}
--   (hdeg : ∀ (i : fin n), p.total_degree ≤ d) :
--   p.support.sum (λ f, as f)
--   =
--   (list.map as (monom_deg_le n d)).sumr :=
-- begin
--   rw list.sumr_eq_sum,
--   unfold monom_deg_le,
--   unfold monom_deg_le_finset,

-- end




lemma mv_polynomial_sum_eq_finset_map_monom_deg_le_finset_sum
  {A : Type*} [comm_ring A] {n d : ℕ}
  [decidable_eq (mv_polynomial (fin n) A)]
  (p : mv_polynomial (fin n) A)
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

lemma realize_poly_map_data_coeffs_ys
  {A : Type*} [comm_ring A] {n d : ℕ}
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

  sorry

end

end realize_poly_map_data_coeffs_xs_and_ys


lemma Ax_Groth_inj_aux {K : Type*} [field K] [is_alg_closed K]
  (h0 : char_zero K)
  {n d : ℕ}
  (ps : poly_map_data K n)
  (hdeg : ∀ (i : fin n), (ps i).total_degree ≤ d)
  (hinj : function.injective (poly_map ps))
  : @realize_bounded_formula _ (struc_to_ring_struc.Structure K)
    _ _ (@poly_map_data.coeffs_dvector' K _ n d ps)
    (inj_formula n d) dvector.nil :=
begin
  let xs0 := poly_map_data.coeffs_dvector' d ps,
  -- open up the definition of inj_formula
  simp only [inj_formula],
  rw realize_bounded_formula_bd_alls',
  intro xs, -- an n tuple in the domain
  rw realize_bounded_formula_bd_alls',
  intro ys, -- an n tuple in the domain
  simp only [realize_bounded_formula_imp],
  -- we are showing that ps xs = ps yx implies xs = ys
  -- assume the images are all equal (expressed model theoretically)
  intro hImage,
  rw realize_bounded_formula_bd_big_and,
  rw realize_bounded_formula_bd_big_and at hImage,
  -- translate this to the images are equal
  -- (expressed algebraically / in the ring)
  have himage : (poly_map ps (λ i, dvector.nth xs i i.2))
               = poly_map ps (λ i, dvector.nth ys i i.2),
  -- note that i need to reverse the index since de bruijn index
  {
    funext j, -- for each i < n (... the tuples at i are equal)
    simp only [poly_map],
    have hImagei := hImage j,
    simp only [monom_deg_le_length, realize_bounded_formula,
      monom_deg_le, realize_poly_indexed_by_monoms] at hImagei,
    convert hImagei,
    {rw realize_poly_map_data_coeffs_xs ps hdeg xs ys j, refl },
    {rw realize_poly_map_data_coeffs_ys ps hdeg xs ys j, refl },
  },
  intro k, -- for each input (... they are equal)
  -- ... they are equal
  {sorry},
end

-- realize_bounded_term (ys.append (xs.append xs0))
      -- (poly_indexed_by_monoms n d (2 * n + ↑i * (nat.natlist d (monom_deg_le_of_deg n)).length) 0
      --    (n * monom_deg_le_length n d + n + n)
      --    inj_formula_aux)
      -- dvector.nil
      --
-- ⇑(mv_polynomial.eval (λ (i : fin n), xs.nth ↑i _)) (ps i)

lemma Ax_Groth_aux {K : Type*} [field K] [is_alg_closed K]
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
  {exact Ax_Groth_inj_aux h0 ps hdeg hinj},
  -- apply realize_Ax_Groth to ps, i.e. apply hAG to its coefficients
  have hSurj := hAG xs0 hInj,
  sorry,
end

@[simp] def max_total_deg {K : Type*} [comm_semiring K] :
  Π {n m : ℕ}, (fin n → mv_polynomial (fin m) K) → ℕ
| 0 _ ps := 0
| (n + 1) _ ps :=
  max (max_total_deg (λ (i : fin n), ps i)) (mv_polynomial.total_degree (ps n))


def total_deg_le_max_total_deg {K : Type*} [comm_semiring K] :
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

theorem Ax_Groth {K : Type*} [field K] [is_alg_closed K]
  (h0 : char_zero K) {n : ℕ}
  (ps : poly_map_data K n) (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps) :=
Ax_Groth_aux h0 ps (total_deg_le_max_total_deg ps) hinj


end AxGroth
