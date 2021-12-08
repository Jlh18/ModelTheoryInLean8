import Rings.Rings
import Rings.Fields
import Rings.ToMathlib.list
import Rings.ToMathlib.nat
import algebra.big_operators.finprod

namespace AxGroth

noncomputable theory

universe u

open fol
open Rings

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

/-- {{ f : fin n → ℕ | finsum f ≤ d }}-/
def n_var_monom_of_deg_le_d (n d : ℕ) : finset (fin n → ℕ) :=
finset.map (monom_of_bd_monom n d.succ) finset.univ

-- @[simp] def n_var_monom_of_deg_d (n d : ℕ) : finset (fin n → ℕ) :=
-- finset.filter (λ f, finsum f = d) $ n_var_monom_of_deg_le_d n d

#exit

/-- lists all n-variable monomials of degree d -/
@[simp] def n_var_monomials_of_deg : Π (n d : ℕ), list (fin n → ℕ)
| 0 d := [fin_zero_elim]
| 1 d := [λ k, d]
| (n + 2) 0 := [λ k, 0]
| (n + 2) (d + 1) :=
  list.join $ list.of_fn $
  λ i : fin (d + 2), list_image_append (i : ℕ)
  (n_var_monomials_of_deg (n + 1) (d + 1 - i))

lemma list.lt_length_join_of_lt_length_mem
  {A : Type*} {ls : list (list A)} (n : ℕ) (l : list A) (hmem : l ∈ ls) :
  n < l.length → n < ls.join.length :=
begin
  intro hl,
  induction ls with _ _ hind,
  {simpa using hmem},
  cases hmem,
  {
    rw ← hmem,
    simp only [list.join, list.length_append, list.length_join],
    apply nat.lt_add_right _ _ _ hl,
  },
  {
    simp only [list.join, list.length_append, list.length_join],
    apply nat.lt_add_left,
    simpa using hind hmem,
  }
end

#check list.join

lemma mem_n_var_monomials_of_deg : Π (n d : ℕ),
  fin n → ℕ
| 0 d := fin_zero_elim
| 1 d := λ k, d
| (n + 2) 0 := λ k, 0
| (n + 2) (d + 1) :=
  λ i : fin (d + 2), list_image_append (i : ℕ)
  (n_var_monomials_of_deg (n + 1) (d + 1 - i))
 -- list.join $ list.of_fn $
 --  λ i : fin (d + 2), list_image_append i
 --  (n_var_monomials_of_deg (n + 1) (d + 1 - i))

-- lemma zero_lt_n_var_monomials_of_deg_length : Π (n d : ℕ),
--   0 < (n_var_monomials_of_deg n d).length
-- | 0 d := by simp
-- | 1 d := by simp
-- | (n + 2) 0 := by simp
-- | (n + 2) (d + 1) :=
-- begin
--   simp only [n_var_monomials_of_deg],
--   apply list.lt_length_join_of_lt_length_mem 0,

-- end

/-- lists all n-variable monomials of degree ≤ d -/
@[simp] def n_var_monomials_of_deg_le (n d : ℕ) : list (fin n → ℕ) :=
nat.natlist d.succ (λ d', n_var_monomials_of_deg n d')

-- counts all n-variable monomials of degree ≤ d
@[simp] def n_var_monomials_of_deg_le_length (n d : ℕ) : ℕ :=
list.length $ n_var_monomials_of_deg_le n d

def finsupp_to_nat_of_fin_to_nat {n : ℕ} (p : fin n → ℕ) :
  fin n →₀ ℕ :=
⟨ {k ∈ finset.fin_range n | p k ≠ 0 } , p ,
begin
  intro a,
  split,
  {intro ha, simpa using ha},
  {intro ha, simpa using ha}
end ⟩

/-- lists all n-variable monomials of degree ≤ d as finsupp maps-/
@[simp] def n_var_monomials_of_deg_le₀ (n d : ℕ) : list (fin n →₀ ℕ) :=
list.map (finsupp_to_nat_of_fin_to_nat) $ n_var_monomials_of_deg_le n d

-- no restriction on degree
/-- takes a polynomial in n.succ variables and gives a list of its coefficients-/
@[simp] def coeffs_list_of_mv_polynomial
  {K : Type} [comm_semiring K] {n : ℕ} (d : ℕ)
  (p : mv_polynomial (fin n) K) : list K :=
list.map (λ m, mv_polynomial.coeff m p) (n_var_monomials_of_deg_le₀ n d)

section prop_decidable

local attribute [instance] classical.prop_decidable

lemma zero_le_n_var_monomials_of_deg_le_length (n d : ℕ) :
  0 < n_var_monomials_of_deg_le_length n d :=
begin
  simp only [list.length_append, n_var_monomials_of_deg_le,
    nat.natlist, n_var_monomials_of_deg_le_length],
  apply nat.lt_add_right,
  sorry,
end

-- namespace list

-- def fin_index_of {α : Type u} (a : α) :
--   Π (l : list α), (a ∈ l) → fin (list.length l)
-- | [] h :=
-- begin
--   exfalso,
--   rw ← list.mem_nil_iff a,
--   apply h,
-- end
-- | (hd :: l) h := ⟨ list.index_of a (hd :: l) ,
-- begin rw list.index_of_lt_length, apply h end ⟩

-- end list

#exit

lemma poly_indexed_by_monos_aux (n d s c : ℕ)
  (hndc : (n_var_monomials_of_deg_le n d).length + s < c) (f : fin n → ℕ) :
  list.index_of f (n_var_monomials_of_deg_le n d) + s < c :=
begin
  apply nat.lt_of_le_of_lt _ hndc,
  apply nat.add_le_add_right list.index_of_le_length,
end


lemma fin_add_lt_of_add_le (n p c : ℕ) (hnpc : n + p ≤ c) (i : fin n) : (i : ℕ) + p < c :=
begin
  apply nat.lt_of_lt_of_le _ hnpc,
  apply nat.add_lt_add_right i.2,
end

-- ∑_{f ∈ n_var_monomials_of_deg n d} xⱼ₊ₛ ∏ {0 ≤ i < n} xᵢ₊ₚᶠ⁽ⁱ⁾ in "context c"
-- where j is the index of f in n_var_monomials_of_deg n d
-- the context should at least include the variables xⱼ₊ₛ -- this is hndc
-- the context should at least include the variables xᵢ₊ₚ -- this is hpc
@[simp] def poly_indexed_by_monos (n d s p c : ℕ)
  (hndc : (n_var_monomials_of_deg_le n d).length + s < c)
  (hnpc : n + p ≤ c) :
  bounded_ring_term c :=
-- sum indexed by the n-variable monomials of degree < d
list.sumr
(list.mapr
  (λ f : (fin n → ℕ),
    let
      x_js : bounded_ring_term c :=
      x_ ⟨(list.index_of f (n_var_monomials_of_deg_le n d) + s) ,
      poly_indexed_by_monos_aux n d s c hndc f ⟩,
      x_ip (i : fin n) : bounded_ring_term c :=
      x_ (⟨ (i : ℕ) + p , fin_add_lt_of_add_le n p c hnpc i ⟩)
    in
    x_js * (nat.prod n $ λ i, (x_ip i) ^ (f i) )
    )
  (n_var_monomials_of_deg_le n d)
)


#exit
-- -- ∑ {f ∈ n_var_monomials_of_deg n.succ d} x₍ⱼ₊ₛ₎ ∏ {0 ≤ i < n} x₍ᵢ₊ₚ₎ᶠ⁽ⁱ⁾ in "context c"
-- -- where j is the index of f in n_var_monomials_of_deg n.succ d
-- @[simp] def poly_indexed_by_monos (n d s p c : ℕ) (h : 0 < c) :
--   bounded_ring_term c :=
-- begin
--   rw ← nat.succ_pred_eq_of_pos h,
--   apply poly_indexed_by_monos' n d s p,
-- end


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
    (poly_indexed_by_monos n.succ d (2 * n.succ + j * monom) 0 _)
    ≃
    (poly_indexed_by_monos n.succ d (2 * n.succ + j * monom) (n.succ) _)
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
λ j, x_ j ≃ poly_indexed_by_monos n.succ d (n.succ + n.succ + j * monom) 0 _

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

variables {A : Type} [comm_semiring A] {n : ℕ}

-- takes a polynomial map (preferably of total deg < d) and gives list of coeffs of each polynomial
@[simp] def poly_map_data.coeffs_list
  {n : ℕ} (d : ℕ) (ps : poly_map_data A n.succ) : list A :=
list.join (list.of_fn (λ i : fin n.succ, coeffs_list_of_mv_polynomial d (ps i)))

/- Writes polynomial map into a dvector of its coefficients -/
def poly_map_data.coeffs_dvector {n : ℕ} (d : ℕ) (ps : poly_map_data A n.succ) :
  dvector A (poly_map_data.coeffs_list d ps).length :=
dvector.of_list (poly_map_data.coeffs_list d ps)

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
  (ps : poly_map_data A n.succ) (i : fin n.succ) :
  (coeffs_list_of_mv_polynomial d (ps i)).length = n_var_monomials_of_deg_lt_length n d :=
by simp

lemma variable_bound_equal {n : ℕ} (d : ℕ) (ps : poly_map_data A n.succ) :
  (n.succ * n_var_monomials_of_deg_lt_length n d) = (poly_map_data.coeffs_list d ps).length :=
begin
  simp only [poly_map_data.coeffs_list, list.length_join],
  rw list.map_length_of_fn_const _ (coeffs_list_of_mv_polynomial_const ps),
end

/- Writes polynomial map into a dvector of its coefficients (with a better variable context) -/
lemma poly_map_data.coeffs_dvector' {n : ℕ} (d : ℕ)
  (ps : poly_map_data A n.succ) :
  dvector A (n.succ * n_var_monomials_of_deg_lt_length n d) :=
begin
  have xs0 := poly_map_data.coeffs_dvector d ps,
  rw ← variable_bound_equal d ps at xs0,
  exact xs0,
end

open mv_polynomial

-- (X₀ + 1 , X₁ + 1)
-- def example_poly_map : poly_map_data ℤ 2 := λ k, X k + 1



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

-- #check list.sum

@[simp] lemma realize_bounded_term_list_sumr
  {A : Structure ring_signature} {c : ℕ} {xs : dvector A c} :
  Π {l : list (bounded_ring_term c)},
  realize_bounded_term xs (list.sumr l) dvector.nil
  =
  list.sumr (list.mapr (λ t, realize_bounded_term xs t dvector.nil) l)
| list.nil := by simp
| (list.cons t ts) :=
begin
  simp only [list.mapr, models_ring_theory_to_comm_ring.realize_add,
    ring_signature.add, list.sumr, realize_bounded_term],
  rw realize_bounded_term_list_sumr,
end

-- list.sumr
-- (list.mapr
--   (λ f : (fin n.succ → ℕ),
--     (x_ (list.index_of f (n_var_monomials_of_deg_lt n d) + s))
--     *
--     (nat.prod n.succ $ λ i, (x_ (i + p)) ^ (f i) )
--     )
--   (n_var_monomials_of_deg_lt n d)
-- )


def realize_add_zero_hom {A : Type*} [comm_ring A]
  {c : ℕ} (xs : dvector (struc_to_ring_struc.Structure A) c):
  add_zero_hom (bounded_ring_term c) A :=
⟨ λ t, realize_bounded_term xs t dvector.nil ,
  models_ring_theory_to_comm_ring.realize_zero ,
  λ t s, models_ring_theory_to_comm_ring.realize_add ⟩

lemma realize_sumr {A : Type*} [comm_ring A]
  {c : ℕ} (xs : dvector (struc_to_ring_struc.Structure A) c)
  {ts : list (bounded_ring_term c)} :
  realize_bounded_term xs (ts).sumr dvector.nil
  =
  (list.mapr (realize_add_zero_hom xs).to_fun ts).sumr :=
begin
  rw ← list.mapr_sumr (realize_add_zero_hom xs) ts,
  refl,
end

lemma realize_nat_prod {A : Type*} [comm_ring A]
  {c : ℕ} (xs : dvector (struc_to_ring_struc.Structure A) c)
  (ts : ℕ → bounded_ring_term c) : Π n,
  realize_bounded_term xs (nat.prod n ts) dvector.nil
  =
  nat.prod n (λ n, realize_bounded_term xs (ts n) dvector.nil)
| nat.zero :=
begin
  simp only [nat.prod],
  refl,
end
| (nat.succ n) :=
begin
  simp only [nat.prod, struc_to_ring_struc.func_map, dvector.last, struc_to_ring_struc.binaries_map, realize_bounded_term,
  ring_signature.mul, dvector.nth],
  rw realize_nat_prod n,
end

lemma realize_pow {A : Type*} [comm_ring A]
  {c : ℕ} (xs : dvector (struc_to_ring_struc.Structure A) c)
  (t : bounded_ring_term c) : Π (n : ℕ),
  realize_bounded_term xs (t ^ n) dvector.nil
  =
  (realize_bounded_term xs t dvector.nil) ^ n
| nat.zero := by
  simpa only [nat.nat_zero_eq_zero, ring_signature.pow_zero,
    realize_bounded_term, models_ring_theory_to_comm_ring.realize_one,
    ring_signature.one, models_ring_theory_to_comm_ring.realize_one]
| (nat.succ n) :=
begin
  simp only [struc_to_ring_struc.func_map, dvector.last, ring_signature.pow_succ, struc_to_ring_struc.binaries_map,
  realize_bounded_term, ring_signature.mul, dvector.nth],
  rw realize_pow n,
  refl,
end

lemma realize_poly_indexed_by_monos
  {A : Type*} [comm_ring A] {n d s p c : ℕ}
  (hcf : Π (f : fin n.succ → ℕ), list.index_of f (n_var_monomials_of_deg_lt n d) + s < c.succ)
  (hci : Π (i : ℕ), i + p < c.succ)
  {xs : dvector (struc_to_ring_struc.Structure A) c.succ}  :
  realize_bounded_term xs (poly_indexed_by_monos n d s p c) dvector.nil
  =
  list.sumr
  (list.mapr
    (λ f,
    (dvector.nth xs (list.index_of f (n_var_monomials_of_deg_lt n d) + s) (hcf f))
    *
    (nat.prod n.succ $ λ i, ((dvector.nth xs (i + p) (hci i)) ^ (f i) ))
    )
  (n_var_monomials_of_deg_lt n d)
  ) :=
begin
  simp only [poly_indexed_by_monos],
  rw realize_sumr,
  rw ← list.comp_mapr,
  congr,
  funext f,
  simp only [realize_add_zero_hom, function.comp_app],
  simp only [struc_to_ring_struc.func_map, fin.val_eq_coe, dvector.last,
    struc_to_ring_struc.binaries_map, realize_bounded_term,
    ring_signature.mul, dvector.nth],
  congr,
  {
    norm_cast,
    simp only [fin.val_eq_coe, fin.coe_of_nat_eq_mod],
    rw ← nat.mod_eq_of_lt (hcf f),
    congr,
  },
  {
    rw realize_nat_prod,
    congr,
    funext i,
    rw realize_pow,
    simp,
    norm_cast,
    congr,
    simp only [fin.val_eq_coe, fin.coe_of_nat_eq_mod],
    rw nat.mod_eq_of_lt (hci i),
  },
end

lemma realize_poly_map_data_coeffs_xs
  {A : Type*} [comm_ring A] {n d : ℕ}
  (ps : poly_map_data A n.succ)
  (hdeg : ∀ (i : fin n.succ), (ps i).total_degree < d)
  (xs ys : dvector ↥(struc_to_ring_struc.Structure A) n.succ)
  (i : fin n.succ)
  :
  realize_bounded_term (ys.append (xs.append (poly_map_data.coeffs_dvector' d ps)))
      (poly_indexed_by_monos n.succ d
        (2 * n.succ + ↑i * (d.natlist (n_var_monomials_of_deg n.succ)).length)
        0
        (n.succ * n_var_monomials_of_deg_lt_length n d + n.succ + n))
      dvector.nil
  =
  mv_polynomial.eval (λ (i : fin n.succ), xs.nth i i.2) (ps i) :=
begin
  rw realize_poly_indexed_by_monos,
  { sorry },
  {
    intro f, -- f is a monomial
    simp only [n_var_monomials_of_deg_lt],
    sorry,
  },
  {
    sorry
  },
end

lemma Ax_Groth_inj_aux {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K)
  {n d : ℕ}
  (ps : poly_map_data K n.succ)
  (hdeg : ∀ (i : fin n.succ), (ps i).total_degree < d)
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
  have himage : (poly_map ps (λ i, dvector.nth xs i i.2)) = poly_map ps (λ i, dvector.nth ys i i.2),
  {
    funext i, -- for each i < n (... the tuples at i are equal)
    simp only [poly_map],
    have hImagei := hImage i,
    simp only [n_var_monomials_of_deg_lt_length, realize_bounded_formula,
      n_var_monomials_of_deg_lt] at hImagei,
    convert hImagei,
    sorry,
    sorry,
  },
  intro k, -- for each input (... they are equal)
  -- ... they are equal
  {sorry},
end

-- realize_bounded_term (ys.append (xs.append xs0))
      -- (poly_indexed_by_monos n.succ d (2 * n.succ + ↑i * (nat.natlist d (n_var_monomials_of_deg n.succ)).length) 0
      --    (n.succ * n_var_monomials_of_deg_lt_length n d + n.succ + n.succ)
      --    inj_formula_aux)
      -- dvector.nil
      --
-- ⇑(mv_polynomial.eval (λ (i : fin n.succ), xs.nth ↑i _)) (ps i)

lemma Ax_Groth_aux {K : Type} [field K] [is_alg_closed K]
  (h0 : char_zero K) {n d : ℕ}
  (ps : poly_map_data K n.succ) (hdeg : ∀ (i : fin n.succ), mv_polynomial.total_degree (ps i) < d)
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
