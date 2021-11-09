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
@[simp] def homog_basis_list : Π (n d : ℕ), list (fin n → ℕ)
| 0 d := [fin_zero_elim]
| 1 d := [λ k, d]
| (n + 2) 0 := [λ k, 0]
| (n + 2) (d + 1) := list.join $ list.of_fn $
  λ i : fin (d + 2), list_image_append i (homog_basis_list (n + 1) (d + 1 - i))

/-- lists all n-variable monomials of degree < d -/
@[simp] def n_var_monomials_of_deg (n d : ℕ) : list (fin n → ℕ) :=
nat.natlist d (λ d', homog_basis_list n d')

-- counts all n-variable monomials of degree < d
@[simp] def n_var_monomials_of_deg_lt (n d : ℕ) : ℕ :=
list.length $ homog_basis_list n d
-- def n_var_monomials_of_deg_lt (n d : ℕ) : ℕ :=
-- finset.sum (finset.range d) (λ d', list.length $ homog_basis_list n d')

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
    (x_ (list.index_of f (n_var_monomials_of_deg n.succ d) + s))
    *
    (nat.prod n.succ $ λ i, (x_ (i + p)) ^ (f i) )
    )
  (n_var_monomials_of_deg n.succ d)
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
  0 < n.succ * n_var_monomials_of_deg_lt n.succ d + n.succ + n.succ :=
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
  bounded_ring_formula (n.succ * (n_var_monomials_of_deg_lt n.succ d)) :=
let c := n.succ * (n_var_monomials_of_deg_lt n.succ d) + 2 * n.succ,
    monom := n_var_monomials_of_deg_lt n.succ d in
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
  bounded_ring_formula (n.succ * n_var_monomials_of_deg_lt n.succ d) :=
let monom := n_var_monomials_of_deg_lt n.succ d in
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
bd_alls (n.succ * (n_var_monomials_of_deg_lt n.succ d))
-- if the polynomial function is injective then it is surjective
$ inj_formula n d ⟹ surj_formula n d

@[simp] def poly_map_data (K : Type) [comm_semiring K] (n : ℕ) : Type :=
fin n → mv_polynomial (fin n) K

def poly_map {K : Type} [comm_semiring K] {n : ℕ} :
  poly_map_data K n → (fin n → K) → (fin n → K) :=
λ ps as k, mv_polynomial.eval as (ps k)

namespace inj_formula

----------------

end inj_formula

lemma realize_Ax_Groth_formula {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) (n d : ℕ) : struc_to_ring_struc.Structure K ⊨ Ax_Groth_formula n d := sorry

#check realize_sentence

lemma Ax_Groth_aux {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) {n d : ℕ}
  (ps : poly_map_data K n.succ) (hdeg : ∀ (i : fin n.succ), mv_polynomial.total_degree (ps i) < d)
  (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps) :=
begin
  have h := realize_Ax_Groth_formula h0 n d,
  simp only [realize_sentence_bd_alls, Ax_Groth_formula] at h,


  sorry
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
