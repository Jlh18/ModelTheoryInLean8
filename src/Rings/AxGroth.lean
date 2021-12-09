import Rings.Rings
import Rings.Fields
import Rings.ToMathlib.list
import Rings.ToMathlib.nat
import Rings.ToMathlib.fol
import Rings.RealizeThings
import algebra.big_operators.finprod
import data.finset.basic

namespace AxGroth

noncomputable theory

universe u

open fol
open Rings

/-- composition by coe : fin d → ℕ -/
def monom_of_bd_monom (n d : ℕ) :
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

/-- { f : fin n → ℕ | finsum f ≤ d } -/
@[simp] def n_var_monom_of_deg_le_d_finset (n d : ℕ) : finset (fin n → ℕ) :=
finset.map (monom_of_bd_monom n d.succ) finset.univ

/-- list of all n-variable monomials of degree ≤ d -/
def n_var_monom_of_deg_le (n d : ℕ) : list (fin n → ℕ) :=
(n_var_monom_of_deg_le_d_finset n d).to_list

/-- counts all n-variable monomials of degree ≤ d -/
def n_var_monom_of_deg_le_length (n d : ℕ) : ℕ :=
list.length $ n_var_monom_of_deg_le n d

def finsupp_to_nat_of_fin_to_nat {n : ℕ} (p : fin n → ℕ) :
  fin n →₀ ℕ :=
⟨ { k ∈ finset.fin_range n | p k ≠ 0 } , p ,
begin
  intro a,
  split,
  {intro ha, simpa using ha},
  {intro ha, simpa using ha}
end ⟩

/-- lists all n-variable monomials of degree ≤ d as finsupp maps-/
@[simp] def n_var_monom_of_deg_le₀ (n d : ℕ) : list (fin n →₀ ℕ) :=
list.map (finsupp_to_nat_of_fin_to_nat) $ n_var_monom_of_deg_le n d

-- no restriction on degree
/-- takes a polynomial in n variables and gives a list of its coefficients-/
@[simp] def coeffs_list_of_mv_polynomial
  {K : Type} [comm_semiring K] {n : ℕ} (d : ℕ)
  (p : mv_polynomial (fin n) K) : list K :=
list.map (λ m, mv_polynomial.coeff m p) (n_var_monom_of_deg_le₀ n d)

section prop_decidable

local attribute [instance] classical.prop_decidable

/-- there is always a monomial of degree ≤ d,
  namely the constant polynomial 1 -/
lemma n_var_monoms_of_deg_le_length_ne_zero (n d : ℕ) :
  n_var_monom_of_deg_le_length n d ≠ 0 :=
begin
  simp only [n_var_monom_of_deg_le, n_var_monom_of_deg_le_length,
    finset.length_to_list, finset.card_map,
    n_var_monom_of_deg_le_d_finset],
  apply @finset.card_ne_zero_of_mem _,
  {apply finset.mem_univ},
  {exact λ i, 1},
end

/-- the bound hndc is enough in poly_indexed_by_monoms -/
lemma poly_indexed_by_monoms_aux0 (n d s c : ℕ)
  (hndc : (n_var_monom_of_deg_le n d).length + s ≤ c) (f : fin n → ℕ) :
  list.index_of' f (n_var_monom_of_deg_le n d) + s < c :=
begin
  apply nat.lt_of_lt_of_le _ hndc,
  apply nat.add_lt_add_right,
  apply list.index_of'_lt_length,
  apply nat.pos_of_ne_zero (n_var_monoms_of_deg_le_length_ne_zero n d),
end

/-- if i ∈ fin n and n + p ≤ c then i + p < c -/
lemma fin_add_lt_of_add_le (n p c : ℕ) (hnpc : n + p ≤ c) (i : fin n) :
(i : ℕ) + p < c :=
begin
  apply nat.lt_of_lt_of_le _ hnpc,
  apply nat.add_lt_add_right i.2,
end

-- NOTE s = 2 * n
-- NOTE c = n * n_var_monom_of_deg_lt n d + 2 * n
/-- ∑_{f ∈ n_var_monom_of_deg n d} xⱼ₊ₛ ∏ {0 ≤ i < n} xᵢ₊ₚᶠ⁽ⁱ⁾ in "context c"
 where j is the index of f in n_var_monom_of_deg n d
 the context should at least include the variables xⱼ₊ₛ -- this is hndc
 the context should at least include the variables xᵢ₊ₚ -- this is hpc -/
@[simp] def poly_indexed_by_monoms (n d s p c : ℕ)
  (hndsc : (n_var_monom_of_deg_le n d).length + s ≤ c)
  (hnpc : n + p ≤ c) :
  bounded_ring_term c :=
-- sum indexed by the n-variable monom of degree < d
list.sumr
(list.mapr
  (λ f : (fin n → ℕ),
    let
      x_js : bounded_ring_term c :=
      x_ ⟨(list.index_of' f (n_var_monom_of_deg_le n d) + s) ,
      poly_indexed_by_monoms_aux0 n d s c hndsc f ⟩,
      x_ip (i : fin n) : bounded_ring_term c :=
      x_ ⟨ (i : ℕ) + p , fin_add_lt_of_add_le n p c hnpc i ⟩
    in
    x_js * (nat.prod n $ λ i, (x_ip i) ^ (f i) )
    )
  (n_var_monom_of_deg_le n d)
)

lemma realize_poly_indexed_by_monoms
  {A : Type*} [comm_ring A] {n d s p c : ℕ}
  (hndsc : (n_var_monom_of_deg_le n d).length + s ≤ c)
  (hnpc : n + p ≤ c)
  {xs : dvector (struc_to_ring_struc.Structure A) c}  :
  realize_bounded_term xs
    (poly_indexed_by_monoms n d s p c hndsc hnpc) dvector.nil
  =
  list.sumr
  (list.mapr
    (λ f,
    (dvector.nth xs (list.index_of' f (n_var_monom_of_deg_le n d) + s)
      (poly_indexed_by_monoms_aux0 n d s c hndsc f))
    *
    (nat.prod n $ λ i,
    ((dvector.nth xs (i + p) (fin_add_lt_of_add_le n p c hnpc i)) ^ (f i) ))
    )
  (n_var_monom_of_deg_le n d)
  ) :=
begin
  simp only [poly_indexed_by_monoms],
  rw realize_ring_term.sumr,
  rw ← list.comp_mapr,
  congr,
  funext f,
  simp only [realize_ring_term.add_zero_hom, function.comp_app],
  simp only [struc_to_ring_struc.func_map, fin.val_eq_coe, dvector.last,
    struc_to_ring_struc.binaries_map, realize_bounded_term,
    ring_signature.mul, dvector.nth],
  congr,
  rw realize_ring_term.nat_prod,
  congr,
  funext i,
  rw realize_ring_term.pow,
  simp,
end

end prop_decidable

lemma inj_formula_aux0 (n d : ℕ) (j : fin n) :
  n_var_monom_of_deg_le_length n d +
    (j * (n_var_monom_of_deg_le_length n d) + n + n)
  ≤
  n * n_var_monom_of_deg_le_length n d + n + n :=
begin
  let c := n * (n_var_monom_of_deg_le_length n d) + n + n,
  let monom := n_var_monom_of_deg_le_length n d,
  repeat {rw ← nat.add_assoc, apply nat.add_le_add_right},
  cases nat.exists_eq_succ_of_ne_zero (ne_zero_of_lt j.2) with k hk,
  have hrw : n * n_var_monom_of_deg_le_length n d = n_var_monom_of_deg_le_length n d + k * n_var_monom_of_deg_le_length n d,
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

lemma inj_formula_aux1 (n d : ℕ) :
  n + 0
  ≤
  n * n_var_monom_of_deg_le_length n d + n + n :=
begin
  rw add_comm,
  apply nat.add_le_add_right,
  apply nat.zero_le,
end

lemma inj_formula_aux2 (n d : ℕ) :
  n + n
  ≤
  n * n_var_monom_of_deg_le_length n d + n + n :=
begin
  rw nat.add_assoc,
  apply nat.le_add_left,
end

lemma inj_formula_aux3 (n d : ℕ) (i : fin n) :
  (i : ℕ)
  <
  n * n_var_monom_of_deg_le_length n d + n + n :=
begin
  apply nat.lt_of_lt_of_le i.2,
  apply nat.le_add_left,
end

lemma inj_formula_aux4 (n d : ℕ) (i : fin n) :
  (i : ℕ) + n
  <
  n * n_var_monom_of_deg_le_length n d + n + n :=
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
  bounded_ring_formula (n * n_var_monom_of_deg_le_length n d) :=
  let c := n * (n_var_monom_of_deg_le_length n d) + 2 * n,
  monom := n_var_monom_of_deg_le_length n d in
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
    (poly_indexed_by_monoms n d (j * monom + n + n) 0 _ -- note 0
      (inj_formula_aux0 n d j) (inj_formula_aux1 n d))
    ≃
    (poly_indexed_by_monoms n d (j * monom + n + n) n _ -- note n
      (inj_formula_aux0 n d j) (inj_formula_aux2 n d))
  )
)
-- then
⟹
-- at each 0 ≤ i < n,
(bd_big_and n $ λ i,
-- xᵢ = yᵢ (where yᵢ is written as xᵢ₊ₙ₊₁)
  x_ ⟨ i , inj_formula_aux3 n d i ⟩ ≃ x_ (⟨ i + n , inj_formula_aux4 n d i ⟩)
)

-- in the context of having n polynomials pⱼ indexed by
-- their monomial coefficients,
-- for all z₋ ∈ Kⁿ, there exists x₋ ∈ Kⁿ such that each zⱼ = pⱼ x₋
-- This says the polynomial map formed by the pⱼs is surjective
/-- Surjectivity of polynomial maps stated model-theoretically-/
def surj_formula (n d : ℕ) :
  bounded_ring_formula (n * n_var_monom_of_deg_le_length n d) :=
let monom := n_var_monom_of_deg_le_length n d in
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
  x_ ⟨ j , inj_formula_aux3 n d j ⟩
  ≃
  poly_indexed_by_monoms n d (j * monom + n + n) 0 _
    (inj_formula_aux0 n d j) (inj_formula_aux1 n d)

/-- Ax-Grothendieck stated model-theoretically -/
def Ax_Groth_formula (n d : ℕ) : sentence ring_signature :=
-- quantify over n many (n-variable polynomials) called ps;
-- i.e. the data of a polynomial map
-- by quantifying over (n * monom_of_bounded_degree) monomial coefficients
bd_alls (n * (n_var_monom_of_deg_le_length n d))
-- if the polynomial function is injective then it is surjective
$ inj_formula n d ⟹ surj_formula n d

/-- the data of a polynomial map consists of n polynomials in n variables -/
@[simp] def poly_map_data (K : Type) [comm_semiring K] (n : ℕ) : Type :=
fin n → mv_polynomial (fin n) K

/-- a polynomial map evaluates those polynomials that it consists of -/
def poly_map {K : Type} [comm_semiring K] {n : ℕ} :
  poly_map_data K n → (fin n → K) → (fin n → K) :=
λ ps as k, mv_polynomial.eval as (ps k)

/-- The main result: algebraically closed fields of characteristic zero
   satisfy Ax-Grothendieck formula -/
lemma realize_Ax_Groth_formula {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) (n d : ℕ) :
  struc_to_ring_struc.Structure K ⊨ Ax_Groth_formula n d :=
sorry

section semiring

variables {A : Type} [comm_semiring A] {n : ℕ}

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
lemma coeffs_list_length_eq_n_var_monom_length {d : ℕ}
  (p : mv_polynomial (fin n) A) :
  (coeffs_list_of_mv_polynomial d p).length
  =
  n_var_monom_of_deg_le_length n d :=
begin
  unfold n_var_monom_of_deg_le_length,
  simp,
end

/-- lemma for matching up lengths of contexts for mv_polynomials -/
lemma variable_bound_equal {n : ℕ} (d : ℕ) (ps : poly_map_data A n) :
  (n * n_var_monom_of_deg_le_length n d)
  =
  (poly_map_data.coeffs_list d ps).length :=
begin
  simp only [poly_map_data.coeffs_list, list.length_join],
  rw list.map_length_of_fn_const,
  intro i,
  apply coeffs_list_length_eq_n_var_monom_length,
end

/-- Writes polynomial map into a dvector of its coefficients
  (with a replaced variable context) -/
lemma poly_map_data.coeffs_dvector' {n : ℕ} (d : ℕ)
  (ps : poly_map_data A n) :
  dvector A (n * n_var_monom_of_deg_le_length n d) :=
begin
  have xs0 := poly_map_data.coeffs_dvector d ps,
  rw ← variable_bound_equal d ps at xs0,
  exact xs0,
end

end semiring

-- lemma realize_poly_map_data_coeffs_xs
--   {A : Type*} [comm_ring A] {n d : ℕ}
--   (ps : poly_map_data A n)
--   (hdeg : ∀ (i : fin n), (ps i).total_degree < d)
--   (xs ys : dvector ↥(struc_to_ring_struc.Structure A) n)
--   (i : fin n)
--   :
--   realize_bounded_term (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps)))
--       (poly_indexed_by_monoms n d
--         (2 * n + ↑i * (d.natlist (n_var_monom_of_deg n)).length)
--         0
--         (n * n_var_monom_of_deg_le_length n d + n + n))
--       dvector.nil
--   =
--   mv_polynomial.eval (λ (i : fin n), xs.nth i i.2) (ps i) :=
-- begin
--   rw realize_poly_indexed_by_monoms,
--   { sorry },
--   {
--     intro f, -- f is a monomial
--     simp only [n_var_monom_of_deg_le],
--     sorry,
--   },
--   {
--     sorry
--   },
-- end

lemma Ax_Groth_inj_aux {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K)
  {n d : ℕ}
  (ps : poly_map_data K n)
  (hdeg : ∀ (i : fin n), (ps i).total_degree < d)
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
  -- translate this to the images are equal (expressed algebraically / in the ring)
  have himage : (poly_map ps (λ i, dvector.nth xs i i.2))
               = poly_map ps (λ i, dvector.nth ys i i.2),
  {
    funext i, -- for each i < n (... the tuples at i are equal)
    simp only [poly_map],
    have hImagei := hImage i,
    simp only [n_var_monom_of_deg_le_length, realize_bounded_formula,
      n_var_monom_of_deg_le] at hImagei,
    convert hImagei,
    sorry,
    sorry,
  },
  intro k, -- for each input (... they are equal)
  -- ... they are equal
  {sorry},
end

-- realize_bounded_term (ys.append (xs.append xs0))
      -- (poly_indexed_by_monoms n d (2 * n + ↑i * (nat.natlist d (n_var_monom_of_deg n)).length) 0
      --    (n * n_var_monom_of_deg_le_length n d + n + n)
      --    inj_formula_aux)
      -- dvector.nil
      --
-- ⇑(mv_polynomial.eval (λ (i : fin n), xs.nth ↑i _)) (ps i)

lemma Ax_Groth_aux {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) {n d : ℕ}
  (ps : poly_map_data K n)
  (hdeg : ∀ (i : fin n), mv_polynomial.total_degree (ps i) < d)
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

@[simp] def max_total_deg {K : Type} [comm_semiring K] :
  Π {n m : ℕ}, (fin n → mv_polynomial (fin m) K) → ℕ
| 0 _ ps := 0
| (n + 1) _ ps :=
  max (max_total_deg (λ (i : fin n), ps i)) (mv_polynomial.total_degree (ps n))


def total_deg_le_max_total_deg {K : Type} [comm_semiring K] :
  Π {n m : ℕ} (ps : fin n → mv_polynomial (fin m) K) (i : fin n),
  mv_polynomial.total_degree (ps i) < max_total_deg ps + 1
| 0 _ ps i := fin_zero_elim i
| (n + 1) _ ps i :=
begin
  rw nat.lt_add_one_iff,
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
    nat.le_of_lt_succ (@total_deg_le_max_total_deg n _ (λ j, ps j.val.cast) ⟨ i , hlt ⟩),
    simp only [fin.coe_eq_cast_succ, fin.cast_succ_mk, fin.eta] at hind,
    rw ← fin.coe_coe_eq_self i,
    exact hind,
  },
  {
    right,
    rw h,
  },
end


theorem Ax_Groth {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) {n : ℕ}
  (ps : poly_map_data K n) (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps) :=
Ax_Groth_aux h0 ps (total_deg_le_max_total_deg ps) hinj


end AxGroth
