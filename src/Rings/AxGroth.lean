import Rings.Rings
import Rings.Fields

namespace AxGroth

noncomputable theory

universe u

open fol
open Rings

def list_image_append {A : Type u} [decidable_eq A] {n} :
  A → list (fin n → A) → list (fin n.succ → A) :=
λ x, list.map (λ xs k, dite (↑k < n) (λ h, xs ⟨ k , h ⟩) (λ _ , x))

/-- lists all n-variable monomials of degree d -/
@[simp] def n_var_monomials_of_deg : Π (n d : ℕ), list (fin n → ℕ)
| 0 d := [fin_zero_elim]
| 1 d := [λ k, d]
| (n + 2) 0 := [λ k, 0]
| (n + 2) (d + 1) := list.join $ list.of_fn $
  λ i : fin (d + 2), list_image_append i (n_var_monomials_of_deg (n + 1) (d + 1 - i))

/-- lists all n-variable monomials of degree < d -/
@[simp] def n_var_monomials_of_deg_lt (n d : ℕ) : list (fin n.succ → ℕ) :=
nat.natlist d (λ d', n_var_monomials_of_deg n.succ d')

-- counts all n-variable monomials of degree < d
@[simp] def n_var_monomials_of_deg_lt_length (n d : ℕ) : ℕ :=
list.length $ n_var_monomials_of_deg_lt n d
-- def n_var_monomials_of_deg_lt (n d : ℕ) : ℕ :=
-- finset.sum (finset.range d) (λ d', list.length $ n_var_monomials_of_deg n d')

def finsupp_to_nat_of_fin_to_nat {n : ℕ} (p : fin n.succ → ℕ) : fin n.succ →₀ ℕ :=
⟨ {k ∈ finset.fin_range n.succ | p k ≠ 0 } , p ,
begin
  intro a,
  split,
  {intro ha, simpa using ha},
  {intro ha, simpa using ha}
end ⟩

/-- lists all n-variable monomials of degree < d as finsupp maps-/
@[simp] def n_var_monomials_of_deg_lt₀ (n d : ℕ) : list (fin n.succ →₀ ℕ) :=
list.map (finsupp_to_nat_of_fin_to_nat) $ n_var_monomials_of_deg_lt n d

-- no restriction on degree
/-- takes a polynomial in n.succ variables and gives a list of its coefficients-/
@[simp] def coeffs_list_of_mv_polynomial {K : Type} [comm_semiring K] {n : ℕ} (d : ℕ)
  (p : mv_polynomial (fin n.succ) K) : list K :=
list.map (λ m, mv_polynomial.coeff m p) (n_var_monomials_of_deg_lt₀ n d)

section prop_decidable

local attribute [instance] classical.prop_decidable

namespace list

def fin_index_of {α : Type u} (a : α) : Π (l : list α), (a ∈ l) → fin (list.length l)
| [] h :=
begin
  exfalso,
  rw ← list.mem_nil_iff a,
  apply h,
end
| (hd :: l) h := ⟨ list.index_of a (hd :: l) , begin rw list.index_of_lt_length, apply h end ⟩

-- λ a f, ⟨ list.index_of a f , (by rw list.index_of_lt_length; simp) ⟩

end list

-- ∑ {f ∈ n_var_monomials_of_deg n.succ d} x₍ⱼ₊ₛ₎ ∏ {0 ≤ i < n} x₍ᵢ₊ₚ₎ᶠ⁽ⁱ⁾ in "context c.succ"
-- where j is the index of f in n_var_monomials_of_deg n.succ d
def poly_indexed_by_monos' (n d s p c : ℕ) :
  bounded_ring_term c.succ :=
-- sum indexed by the n-variable monomials of degree < d
list.sum
(list.map
  (λ f : (fin n.succ → ℕ),
    (x_ (list.index_of f (n_var_monomials_of_deg_lt n d) + s))
    *
    (nat.prod n.succ $ λ i, (x_ (i + p)) ^ (f i) )
    )
  (n_var_monomials_of_deg_lt n d)
)

-- ∑ {f ∈ n_var_monomials_of_deg n.succ d} x₍ⱼ₊ₛ₎ ∏ {0 ≤ i < n} x₍ᵢ₊ₚ₎ᶠ⁽ⁱ⁾ in "context c"
-- where j is the index of f in n_var_monomials_of_deg n.succ d
def poly_indexed_by_monos (n d s p c : ℕ) (h : 0 < c) :
  bounded_ring_term c :=
begin
  rw ← nat.succ_pred_eq_of_pos h,
  apply poly_indexed_by_monos' n d s p,
end


-- NOTE s = 2 * n.succ
-- NOTE c = n.succ * n_var_monomials_of_deg_lt n.succ d + 2 * n.succ

end prop_decidable

lemma inj_formula_aux {n d : ℕ} :
  0 < n.succ * n_var_monomials_of_deg_lt_length n d + n.succ + n.succ :=
begin
  apply nat.lt_add_left 0 (n.succ) _ ,
  simp,
end

-- in the context of having n.succ polynomials pⱼ indexed by
-- their monomial coefficients,
-- if for all xᵢ and all yᵢ, every polynomial satisfies pⱼ xᵢ = pⱼ yᵢ
-- then each xᵢ = yᵢ.
-- This says the polynomial map formed by the pⱼs is injective
def inj_formula (n d : ℕ) :
  bounded_ring_formula (n.succ * (n_var_monomials_of_deg_lt_length n d)) :=
let c := n.succ * (n_var_monomials_of_deg_lt_length n d) + 2 * n.succ,
    monom := n_var_monomials_of_deg_lt_length n d in
-- for all pairs in the domain x₋ ∈ Kⁿ⁺¹ and ...
bd_alls' n.succ _
$
-- ... y₋ ∈ Kⁿ⁺¹
bd_alls' n.succ _
$
-- if at each pⱼ
(bd_big_and n.succ
-- pⱼ xᵢ = pⱼ yᵢ
  (λ j,
    (poly_indexed_by_monos n.succ d (2 * n.succ + j * monom) 0 _ inj_formula_aux)
    ≃
    (poly_indexed_by_monos n.succ d (2 * n.succ + j * monom) (n.succ) _ inj_formula_aux)
  )
)
-- then
⟹
-- at each 0 ≤ i < n.succ,
(bd_big_and n.succ $ λ i,
-- xᵢ = yᵢ (where yᵢ is written as xᵢ₊ₙ₊₁)
  x_ i ≃ x_ (i + n.succ)
)

def surj_formula (n d : ℕ) :
  bounded_ring_formula (n.succ * n_var_monomials_of_deg_lt_length n d) :=
let monom := n_var_monomials_of_deg_lt_length n d in
-- for all z₋ ∈ Kⁿ⁺¹ in the codomain
bd_alls' n.succ _
$
-- there exists x₋ ∈ Kⁿ⁺¹ in the domain such that
bd_exs' n.succ _
$
-- at each 0 ≤ j < n.succ
bd_big_and n.succ
$
-- zⱼ = pⱼ x₋
λ j, x_ j ≃ poly_indexed_by_monos n.succ d (n.succ + n.succ + j * monom) 0 _ inj_formula_aux

def Ax_Groth_formula (n d : ℕ) : sentence ring_signature :=
-- quantify over (n.succ) many (n.succ-variable polynomials) called ps;
-- i.e. the data of a polynomial map
-- by quantifying over (n.succ * monomials_of_bounded_degree) monomial coefficients
bd_alls (n.succ * (n_var_monomials_of_deg_lt_length n d))
-- if the polynomial function is injective then it is surjective
$ inj_formula n d ⟹ surj_formula n d

@[simp] def poly_map_data (K : Type) [comm_semiring K] (n : ℕ) : Type :=
fin n → mv_polynomial (fin n) K

def poly_map {K : Type} [comm_semiring K] {n : ℕ} :
  poly_map_data K n → (fin n → K) → (fin n → K) :=
λ ps as k, mv_polynomial.eval as (ps k)

lemma realize_Ax_Groth_formula {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) (n d : ℕ) : struc_to_ring_struc.Structure K ⊨ Ax_Groth_formula n d := sorry

------------
def dvector.of_list {A : Type} : Π (as : list A), dvector A (list.length as)
| list.nil := []
| (list.cons a as) := dvector.cons a (dvector.of_list as)

-- #check list.length_map

-- def coeffs_dvector_of_mv_polynomial {K : Type} [comm_semiring K] {n d : ℕ}
--   (p : mv_polynomial (fin n.succ) K) (hdeg : mv_polynomial.total_degree p < d) :
--   dvector K (list.length (coeffs_list_of_mv_polynomial d p)) :=
-- dvector.of_list (coeffs_list_of_mv_polynomial d p)
-- ------------

-- #check @list.of_fn
-- #eval list.join (list.cons (list.cons 0 list.nil) (list.cons (list.cons 1 list.nil) list.nil))

section semiring

variables {K : Type} [comm_semiring K] {n : ℕ}

-- takes a polynomial map (preferably of total deg < d) and gives list of coeffs of each polynomial
@[simp] def poly_map_data.coeffs_list
  {n : ℕ} (d : ℕ) (ps : poly_map_data K n.succ) : list K :=
list.join (list.of_fn (λ i : fin n.succ, coeffs_list_of_mv_polynomial d (ps i)))

def poly_map_data.coeffs_dvector {n : ℕ} (d : ℕ) (ps : poly_map_data K n.succ) :
  dvector K (poly_map_data.coeffs_list d ps).length :=
dvector.of_list (poly_map_data.coeffs_list d ps)

open mv_polynomial

-- (X₀ + 1 , X₁ + 1)
-- def example_poly_map : poly_map_data ℤ 2 := λ k, X k + 1

lemma list.map_length_of_fn_const {α} {m : ℕ} (f : fin n → list α)
  (h : ∀ i : fin n, (f i).length = m) :
  (list.map list.length (list.of_fn f)).sum = n * m :=
begin
 rw list.map_of_fn,
 rw list.sum_of_fn,
 have h' : (λ (i : fin n), (list.length ∘ f) i) = λ (i : fin n), m,
 {funext, exact h i},
 rw h',
 simp,
end

lemma coeffs_list_of_mv_polynomial_const {d : ℕ}
  (ps : poly_map_data K n.succ) (i : fin n.succ) :
  (coeffs_list_of_mv_polynomial d (ps i)).length = n_var_monomials_of_deg_lt_length n d :=
by simp

lemma variable_bound_equal {K : Type} [comm_semiring K] : Π {n d : ℕ}
  (ps : poly_map_data K n.succ),
  (n.succ * n_var_monomials_of_deg_lt_length n d) = (poly_map_data.coeffs_list d ps).length :=
begin
  intros n d ps,
  simp only [poly_map_data.coeffs_list, list.length_join],
  rw list.map_length_of_fn_const _ (coeffs_list_of_mv_polynomial_const ps),
end

end semiring

-- -- move to ToMathlib
-- def bd_pis {A : Type u} : Π (n : ℕ) (P : (fin n → A) → Prop), Prop
-- | nat.zero P := P fin_zero_elim
-- | (nat.succ n) P := Π (a : A), bd_pis n $ λ as, P $ fin.cons a as

-- lemma realize_bounded_formula_bd_big_and' {L} {S : Structure L} {n m : ℕ}
--   {v : dvector S n} (f : fin m.succ → bounded_formula L n) :
--   realize_bounded_formula v (bd_big_and m.succ f) dvector.nil
--   ↔
--   (realize_bounded_formula v (bd_big_and m (λ k, f k)) dvector.nil
--   ∧
--   realize_bounded_formula v (f m) dvector.nil) :=
-- begin
--   simp only [bd_big_and, realize_bounded_formula_and],
-- end

@[simp] lemma realize_bounded_formula_bd_big_and {L} {S : Structure L} {n : ℕ}
  {v : dvector S n} : Π {m : ℕ} (f : fin m → bounded_formula L n),
  realize_bounded_formula v (bd_big_and m f) dvector.nil
  ↔
  (Π k : fin m, realize_bounded_formula v (f k) dvector.nil)
| nat.zero f :=
begin
  simp only [bd_big_and, realize_bounded_formula_not,
    realize_bounded_formula, true_iff, not_false_iff],
  exact fin_zero_elim,
end
| (nat.succ m) f :=
begin
  simp only [bd_big_and, realize_bounded_formula_and],
  split,
  {
    intros hf k,
    rw realize_bounded_formula_bd_big_and at hf,
    cases fin.lt_or_eq_fin k with hk,
    -- by_cases hk : (k : ℕ) < m,
    {
      have h :=  hf.1 ⟨ k , _ ⟩,
      {simpa using h},
      {
        rw fin.lt_coe_iff_val_lt,
        exact hk,
        exact lt_add_one m,
      },
    },
    {rw h, exact hf.2}
  },
  {
    intro hf,
    split,
    {
      rw realize_bounded_formula_bd_big_and,
      intro k,
      apply hf k,
    },
    {exact hf m}
  },
end

lemma Ax_Groth_inj_aux {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K)
  {n d : ℕ}
  (ps : poly_map_data K n.succ)
  (hdeg : ∀ (i : fin n.succ), (ps i).total_degree < d)
  (hinj : function.injective (poly_map ps))
  (xs0 : dvector (struc_to_ring_struc.Structure K)
    (n.succ * n_var_monomials_of_deg_lt_length n d))
  : realize_bounded_formula xs0 (inj_formula n d) dvector.nil :=
begin
  simp only [inj_formula],
  rw realize_bounded_formula_bd_alls',
  intro xs,
  rw realize_bounded_formula_bd_alls',
  intro ys,
  simp only [realize_bounded_formula_imp],
  intro hImage,
  rw realize_bounded_formula_bd_big_and,
  rw realize_bounded_formula_bd_big_and at hImage,
  intro k,
  have himage : (poly_map ps (λ i, dvector.nth xs i i.2)) = poly_map ps (λ i, dvector.nth ys i i.2),
  {sorry},
  {sorry},
end

lemma Ax_Groth_aux {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) {n d : ℕ}
  (ps : poly_map_data K n.succ) (hdeg : ∀ (i : fin n.succ), mv_polynomial.total_degree (ps i) < d)
  (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps) :=
begin
  have hAG := realize_Ax_Groth_formula h0 n d,
  simp only [realize_sentence_bd_alls,
    Ax_Groth_formula, realize_bounded_formula] at hAG,
  -- write ps into a dvector of its coefficients
  have xs0 := poly_map_data.coeffs_dvector d ps,
  rw ← variable_bound_equal ps at xs0,
  -- injective -> realize inj_formula
  have hInj : @realize_bounded_formula _ (struc_to_ring_struc.Structure K) _ _
    xs0 (inj_formula n d) dvector.nil,
  {
    apply Ax_Groth_inj_aux h0 ps hdeg hinj,
  },
  -- apply realize_Ax_Groth to ps, i.e. apply hAG to its coefficients
  have hSurj := hAG xs0 hInj,

  sorry,
end

@[simp] def max_total_deg {K : Type} [comm_semiring K] :
  Π {n m : ℕ}, (fin n → mv_polynomial (fin m) K) → ℕ
| 0 _ ps := 0
| (n + 1) _ ps := max (max_total_deg (λ (i : fin n), ps i)) (mv_polynomial.total_degree (ps n))

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
  (ps : poly_map_data K n.succ) (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps) :=
Ax_Groth_aux h0 ps (total_deg_le_max_total_deg ps) hinj


end AxGroth
