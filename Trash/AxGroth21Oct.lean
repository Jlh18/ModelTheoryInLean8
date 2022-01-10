import Rings.Rings
import Rings.Fields

-- import data.polynomial.eval
-- import data.mv_polynomial

namespace AxGroth

noncomputable theory

universe u

@[simp] def poly_map_data (K : Type) [comm_semiring K] (n : ℕ) : Type :=
fin n → mv_polynomial (fin n) K

def poly_map {K : Type} [comm_semiring K] {n : ℕ} :
  poly_map_data K n → (fin n → K) → (fin n → K) :=
λ ps as k, mv_polynomial.eval as (ps k)

open fol
open Rings

/-
-- takes x : A and for each xs : fin n → A appends x at the end,
-- then take the image
def image_append {A : Type u} [decidable_eq A] {n} :
  A → finset (fin n → A) → finset (fin n.succ → A) :=
λ x, finset.image (λ xs k, dite (↑k < n) (λ h, xs ⟨ k , h ⟩) (λ _ , x))
-/

def list_image_append {A : Type u} [decidable_eq A] {n} :
  A → list (fin n → A) → list (fin n.succ → A) :=
λ x, list.map (λ xs k, dite (↑k < n) (λ h, xs ⟨ k , h ⟩) (λ _ , x))

/-
def homog_basis (n d : ℕ) : set (fin n → ℕ) :=
{ f | finset.sum (finset.range n) (λ k, dite (k < n) (λ h, f ⟨ k , h ⟩) (λ h, 0)) = d }

-- #check finset.sum_fin_eq_sum_range
def homog_basis' (n d : ℕ) : set (fin n → ℕ) :=
{ f | finset.univ.sum (λ (k : fin n), f k) = d }
-/

/-
-- takes number of variables n and degree d and returns finite set
-- {f : fin n → ℕ | Σᵢ f i = d}
-- for each i : fin n, we read (f i) as the degree of the variable xᵢ
-- hence each f represents a monomial of degree d
def homog_basis'' : Π (n d : ℕ), finset (fin n → ℕ)
| 0 d := {fin_zero_elim}
| 1 d := {λ k, d}
| (n + 2) 0 := {λ k, 0}
| (n + 2) (d + 1) :=
  finset.bUnion (finset.range (d + 2)) (λ i, image_append i (homog_basis'' (n + 1) (d + 1 - i)))
-/

-- takes number of variables n and degree d and returns list representing the set
-- {f : fin n → ℕ | Σᵢ f i = d}
-- for each i : fin n, we read (f i) as the degree of the variable xᵢ
-- hence each f represents a monomial of degree d

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

/-
def homog_dim'' (n d : ℕ) : ℕ := finset.card (homog_basis'' n d)

@[simp] def homog_dim : Π (n d : ℕ), ℕ
| 0 d := 0
| 1 d := 1
| (n + 2) 0 := 1
| (n + 2) (d + 1) :=
  finset.sum (finset.range (d + 2)) (λ i, homog_dim (n + 1) (d + 1 - i))
-/

/-
section

local attribute [instance] classical.prop_decidable

-- set of monomials (in n variables) of degree d.
def homog_basis''' (n d : ℕ) : finset (mv_polynomial (fin n) ℤ) :=
@finset.image (fin n → ℕ) (mv_polynomial (fin n) ℤ) _
  (λ ms : fin n → ℕ, big_mul (λ k : fin n, mv_polynomial.X k))
  (homog_basis'' n d)

-- set of monomials (in n variables) of degree < d
def monomials_of_bounded_degree'
  (n d : ℕ) : finset (mv_polynomial (fin n) ℤ) :=
finset.bUnion (finset.range d) (λ d', homog_basis''' n d')

-- indexing the set of monomials (in n variables) of degree at most d.
def monomials_of_bounded_degree (n d : ℕ) : ℕ :=
finset.card (monomials_of_bounded_degree' n d)

end
-/

-- TRIED LIST INSTEAD BECAUSE bounded_ring_term NOT COMMUTATIVE
-- def homog_poly_indexed_by_monos {n d : ℕ} (i : ℕ) :
--   bounded_ring_term (n * monomials_of_bounded_degree n d + 2 * n) :=
-- finset.sum (homog_basis'' n d)
--   (λ p, big_mul (λ j : fin n, x_ ⟨ j , _ ⟩))

#eval list.index_of 5 ([1,2])

#check list.mem_nil_iff


section

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

-- #check nat.succ_le

-- def lemma_idk {α : Type u} {n d : ℕ} (l : list α) (x : ℕ) :
--  x
--  ≤ (n.succ * x + 2 * n.succ) :=
-- begin
--   induction n,
--   {
--     induction x with x hx,
--     {simp},
--     have hx' := nat.succ_le_succ hx,
--     apply nat.le_trans hx',
--     simp,

--   },
--   sorry




-- end



-- ∑ {f ∈ n_var_monomials_of_deg n.succ d} x₍ⱼ₊ₛ₎ ∏ {0 ≤ i < n} x₍ᵢ₊ₚ₎ᶠ⁽ⁱ⁾ in "context c"
-- where j is the index of f in n_var_monomials_of_deg n.succ d
def poly_indexed_by_monos (n d s p c : ℕ) (h : 0 < c) :
  bounded_ring_term c :=
-- sum indexed by the n-variable monomials of degree < d
list.sum
(list.map
  (λ f : (fin n.succ → ℕ),
    (x_ ⟨ (list.index_of f (n_var_monomials_of_deg n.succ d) + s) % c , nat.mod_lt _ h ⟩)
    *
    (nat.prod n.succ $ λ i, (x_ ⟨ (i + p) % c , nat.mod_lt _ h ⟩) ^ (f i) )
    )
(n_var_monomials_of_deg n.succ d))

-- NOTE s = 2 * n.succ
-- NOTE c = n.succ * n_var_monomials_of_deg_lt n.succ d + 2 * n.succ

end

-- finset.sum (homog_basis'' n d)
--  (λ p, big_mul (λ j : fin n, x_ ⟨ j , _ ⟩))

lemma inj_formula_aux {n d : ℕ} :
  0 < n.succ * n_var_monomials_of_deg_lt n.succ d + 2 * n.succ :=
begin
  apply nat.lt_add_left 0 (2 * n.succ) _ ,
  simp,
end

lemma inj_formula_aux' {n d : ℕ} :
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
-- for all pairs in the domain x₋ ∈ Kⁿ⁺¹ and y₋ ∈ Kⁿ⁺¹
bd_alls' (2 * n.succ) _
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
(bd_big_and n.succ $
-- xᵢ = yᵢ (where yᵢ is written as xᵢ₊ₙ₊₁)
  λ i, x_ ⟨ i % c , nat.mod_lt _ inj_formula_aux ⟩
  ≃
  x_ ⟨ (i + n.succ) % c , nat.mod_lt _ inj_formula_aux ⟩
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
λ j, x_ j ≃ poly_indexed_by_monos n.succ d (n.succ + n.succ + j * monom) 0 _ inj_formula_aux'

def Ax_Groth_Formula {n d : ℕ} : sentence ring_signature :=
-- quantify over (n.succ) many (n.succ-variable polynomials) called ps;
-- i.e. the data of a polynomial map
-- by quantifying over (n.succ * monomials_of_bounded_degree) monomial coefficients
bd_alls (n.succ * (n_var_monomials_of_deg_lt n.succ d))
-- if the polynomial function is injective then it is surjective
$ inj_formula n d ⟹ surj_formula n d




theorem Ax_Grothendieck {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) {n : ℕ}
  (ps : poly_map_data K n) (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps) := sorry



end AxGroth
