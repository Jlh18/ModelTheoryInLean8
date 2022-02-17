import data.finset
import algebra.group.defs
import to_mathlib
import data.mv_polynomial
import Rings.Notation
import field_theory.subfield
import data.mv_polynomial.rename
import data.equiv.fin
import data.polynomial.algebra_map
import data.list
import Rings.ToMathlib.fin

universes u v

lemma with_bot.succ_lt_succ_succ {n : ℕ} : (n + 1 : with_bot ℕ) < ↑n.succ + 1 := by tidy

-- More general version of monoid.has_pow
-- instance has_pow_of_has_one_has_mul (A : Type u) [has_one A] [has_mul A] :
--   has_pow A ℕ := ⟨ λ t k, npow_rec k t ⟩

namespace mv_polynomial
  variables
    {A B : Type*}
    [comm_ring A] [comm_ring B] [algebra A B] {σ : Type*}

  open dvector

  noncomputable instance coe_mv_poly_A_to_mv_poly_B :
  has_coe (mv_polynomial σ A) (mv_polynomial σ B) :=
  ⟨ mv_polynomial.map (algebra_map A B)⟩

  noncomputable instance coe_mv_poly_Z_to_mv_poly_A :
  has_coe (mv_polynomial σ ℤ) (mv_polynomial σ A) :=
  ⟨ mv_polynomial.map (int.cast_ring_hom A) ⟩

  noncomputable instance coe_mv_poly_A_to_mv_poly_poly_A :
  has_coe (mv_polynomial σ A) (mv_polynomial σ (polynomial A)) :=
  ⟨ @mv_polynomial.map A (polynomial A) σ _ _ polynomial.C ⟩

  @[simp] lemma coe_mv_poly_X {k : σ} :
    ↑(mv_polynomial.X k : mv_polynomial σ ℤ) = (mv_polynomial.X k : mv_polynomial σ A) :=
  begin unfold_coes, simp, end

  @[simp] lemma coe_mv_poly_one : ↑ (1 : mv_polynomial σ ℤ) = (1 : mv_polynomial σ A) :=
  begin unfold_coes, simp, end

  @[simp] lemma coe_mv_poly_neg {t}: ↑ - (t : mv_polynomial σ ℤ) = - (↑t : mv_polynomial σ A) :=
  begin unfold_coes, simp, end

  @[simp] noncomputable def to_polynomial {n} (val : fin n → A)
    (p : mv_polynomial (fin n.succ) A) :
    polynomial A :=
  mv_polynomial.eval (fin.x_val polynomial.X (polynomial.C ∘ val)) p

  lemma eval_eq_poly_eval_mv_coeffs_X
  {n : ℕ} {val : fin n → A} (x : A) : Π {k},
    @mv_polynomial.eval A (fin n.succ) _ (fin.x_val x val) (mv_polynomial.X k)
    = polynomial.eval x (to_polynomial val (mv_polynomial.X k)) :=
  @fin.cases n
  (λ k, @mv_polynomial.eval A (fin n.succ) _ (fin.x_val x val) (mv_polynomial.X k)
    = polynomial.eval x (to_polynomial val (mv_polynomial.X k)))
  (begin
    simp only [mv_polynomial.eval_X, fin.cases_zero,
      function.comp_app, fin.x_val, to_polynomial],
    unfold_coes,
    simp,
  end)
  (begin
    simp only [mv_polynomial.eval_X, fin.cases_succ,
      function.comp_app, fin.x_val, to_polynomial],
    unfold_coes,
    simp,
  end)

  lemma eval_eq_poly_eval_mv_coeffs
  {n : ℕ} {p : mv_polynomial (fin n.succ) A} {val : fin n → A} (x : A) :
    @mv_polynomial.eval A (fin n.succ) _ (fin.x_val x val) p
    = polynomial.eval x (to_polynomial val p) :=
  @mv_polynomial.induction_on A (fin n.succ) _
    (λ q, @mv_polynomial.eval A (fin n.succ) _ (fin.x_val x val) q
    = polynomial.eval x (to_polynomial val q))
    p
  (begin
    intro a,
    simp only [mv_polynomial.eval_C, function.comp_app, fin.x_val, to_polynomial],
    unfold_coes,
    simp,
  end)
  (begin
    intros p q,
    simp only [to_polynomial],
    intros hp hq,
    unfold_coes,
    simp only [ring_hom.map_add, ring_hom.to_fun_eq_coe,
    function.comp_app, fin.x_val, polynomial.eval_add],
    simp only [ring_hom.to_fun_eq_coe, function.comp_app, fin.x_val] at hp hq,
    rw [hp, hq],
    refl,
  end)
  (begin
    intros p k,
    simp only [to_polynomial],
    unfold_coes,
    simp only [mv_polynomial.eval_X, ring_hom.to_fun_eq_coe,
      function.comp_app, polynomial.eval_mul, fin.x_val, mv_polynomial.eval_map,
      ring_hom.map_mul, mv_polynomial.map_X],
    intro hp,
    rw ← hp,
    have hx := @mv_polynomial.eval_eq_poly_eval_mv_coeffs_X _ _ _ val x k,
    simp only [mv_polynomial.eval_X, function.comp_app, fin.x_val, to_polynomial] at hx,
    rw hx,
    unfold_coes,
    simp,
  end)

  lemma eval_add {val : σ → A} {p q : mv_polynomial σ A} :
  mv_polynomial.eval val (p + q) = mv_polynomial.eval val p + mv_polynomial.eval val q :=
  by simp


  -- section equiv

  /-- The algebra isomorphism between multivariable polynomials in no variables
  and the ground ring. -/

  -- LIBRARY ---- mv_polynomial.rename_equiv
  --
  -- variables {R : Type u} [comm_semiring R]

  -- @[simp] noncomputable def var_equiv {σ τ : Type v} (hequiv : equiv σ τ) :
  --   mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R :=
  -- let f : mv_polynomial σ R →+* mv_polynomial τ R :=
  --     ring_hom.of (eval₂ C (λ s,X (hequiv.to_fun s))),
  --     g : mv_polynomial τ R →+* mv_polynomial σ R :=
  --     ring_hom.of (eval₂ C (λ s, X (hequiv.inv_fun s)))
  -- in
  -- { to_fun    := eval₂ C (λ s, X (hequiv.to_fun s)),
  --   inv_fun   := eval₂ C (λ t, X (hequiv.inv_fun t)),
  --
  --left_inv  :=
  --   begin
  --     show ∀ p, g.comp f p = p,
  --     apply is_id,
  --     { intro a, simp },
  --     { intro n, simp }
  --   end,
  --   right_inv :=
  --   begin
  --     show ∀ p, f.comp g p = p,
  --     apply is_id,
  --     { intro a, simp },
  --     { intro n, simp }
  --   end,
  --   map_mul'  := λ _ _, eval₂_mul _ _,
  --   map_add'  := λ _ _, eval₂_add _ _,
  --   commutes' := λ _, eval₂_C _ _ _ }
  -- end equiv

  lemma is_empty {R : Type u} {σ : Type v} [comm_ring R] (h : is_empty σ)
    (f : mv_polynomial σ R) (as : σ → R) :
    f = mv_polynomial.C (mv_polynomial.eval as f) :=
  @mv_polynomial.induction_on R σ _
  (λ p, p = mv_polynomial.C (mv_polynomial.eval as p))
  f
  (begin
    intro a,
    rw (mv_polynomial.C_inj R),
    simp,
  end)
  (begin
    intros p q hp hq,
    rw [hp, hq],
    simp,
  end)
  (
  begin
    intros p n hp,
    apply is_empty.elim h n,
  end
  )

end mv_polynomial

namespace zorn

-- open classical
-- local attribute [instance] prop_decidable

--   lemma fin_range_sub_mem_chain_of_sub_union
--     {α : Type u} {c : set (set α)} (hchain : zorn.chain has_subset.subset c) (hc0 : c.nonempty) :
--     Π {n : ℕ} (F : fin n → α), (Π k, F k ∈ ⋃₀ c)
--       → ∃ (Y : set α), Y ∈ c ∧ (Π k, F k ∈ Y)
--   | nat.zero :=
--   begin
--     intros F hF,
--     cases hc0 with Y hY,
--     use Y,
--     split,
--     {exact hY},
--     {exact is_empty.elim fin.is_empty}
--   end
--   | (nat.succ n) :=
--   begin
--     intros Fsucc hFsucc,
--     have F : fin n → α := λ k, Fsucc (k.succ),
--     have hF : Π (k : fin n), Fsucc k.succ ∈ ⋃₀ c := λ k, hFsucc (fin.succ k),
--     cases fin_range_sub_mem_chain_of_sub_union (λk, Fsucc (k.succ)) hF with Y hY,
--     have h0cup : Fsucc 0 ∈ ⋃₀ c := hFsucc 0,
--     rw set.mem_sUnion at h0cup,
--     cases h0cup with Y0 hY0,
--     cases hY0 with hY0c hY0,
--     cases hY with hYc hY,
--     by_cases hYY0 : Y = Y0,
--     {
--       use Y,
--       split,
--       {exact hYc},
--       {
--         intro k,
--         apply @fin.cases n (λ l, Fsucc l ∈ Y),
--         {rw hYY0, exact hY0},
--         {intro i, apply hY i},
--       }
--     },
--     {
--       cases hchain Y hYc Y0 hY0c hYY0 with hsub hsub,
--       {
--         use Y0,
--         split,
--         {exact hY0c},
--         {
--           intro k,
--           apply @fin.cases n (λ l, Fsucc l ∈ Y0),
--           {exact hY0},
--           {intro i, apply hsub, apply hY i},
--         }
--       },
--       {
--         use Y,
--         split,
--         {exact hYc},
--         {
--           intro k,
--           apply @fin.cases n (λ l, Fsucc l ∈ Y),
--           {apply hsub, exact hY0},
--           {intro i, apply hY i},
--         },
--       },
--     }
--   end

--   lemma fin_sub_mem_chain_of_sub_union
--     {α : Type u} {c : set (set α)} (hchain : zorn.chain has_subset.subset c) (hc0 : c.nonempty) :
--     Π (F : finset α), (↑F ⊆ ⋃₀ c) → ∃ (Y : set α), Y ∈ c ∧ ↑F ⊆ Y :=
--   @finset.induction α (λ (F : finset α), (↑F ⊆ ⋃₀ c) → ∃ (Y : set α), Y ∈ c ∧ ↑F ⊆ Y)
--   _
--   (begin
--     intro h0sub,
--     cases hc0 with Y hY,
--     use Y,
--     split,
--     exact hY,
--     simp,
--   end)
--   (begin
--     intros a F haF hind hFasub,
--     have hacup : a ∈ ⋃₀ c,
--     {apply hFasub, simp},
--     rw set.mem_sUnion at hacup,
--     cases hacup with Z hZ,
--     cases hZ with hZc haZ,
--     have hFsub : ↑F ⊆ ⋃₀ c,
--     {apply set.subset.trans _ hFasub, simp},
--     have Y := (hind hFsub),
--     cases Y with Y hY,
--     by_cases hYZ : Y = Z,
--     {
--       use Y,
--       split,
--       {exact hY.1},
--       {
--         simp only [finset.coe_insert, set.insert_subset],
--         split,
--         {rw hYZ, exact haZ,},
--         {exact hY.2}
--       }
--     },
--     cases hY with hYc hFY,
--     cases hchain Y hYc Z hZc hYZ with hl hr,
--     {
--       use Z,
--       split,
--       {exact hZc},
--       simp only [finset.coe_insert, set.insert_subset],
--       split,
--       {exact haZ},
--       {exact set.subset.trans hFY hl},
--     },
--     {
--       use Y,
--       split,
--       {exact hYc},
--       {
--         simp only [finset.coe_insert, set.insert_subset],
--         split,
--         {exact hr haZ},
--         {exact hFY}
--       },
--     }
--   end)

end zorn

namespace set
  lemma union_sdiff {α : Type u} {B : set α} {x y} :
    ¬x = y → (B ∪ {x}) \ {y} = B \ {y} ∪ {x} :=
  begin
    intro hxy,
    apply set.ext,
    intro b,
    split,
    {
      intro hb,
      by_cases hbx : b = x,
      {
        right,
        simpa,
      },
      {
        left,
        split,
        cases hb with hl hr,
        cases hl,
        {exact hl},
        {exfalso, apply hbx, simpa using hl},
        {exact hb.2},
      },
    },
    {
      intro hb,
      cases hb,
      {
        split,
        {left, exact hb.1},
        {simpa using hb.2},
      },
      {
        split,
        {right, exact hb},
        {intro hbot, apply hxy, tidy},
      },
    },
  end


  lemma remove_insert {α : Type u} {B : set α} {y} : y ∈ B → B \ {y} ∪ {y} = B :=
  begin
    intro hyB,
    apply set.ext,
    intro b,
    split,
    {
      intro hb,
      cases hb,
      {exact hb.1},
      {rw set.mem_singleton_iff at hb, rw hb, exact hyB},
    },
    {
      intro hbB,
      by_cases hby : b = y,
      {
        rw hby,
        right,
        simp,
      },
      {
        left,
        split,
        {exact hbB},
        {simpa using hby},
      },
    },
  end

  lemma remove_insert_not_mem {α : Type u} {B : set α} {x} : x ∉ B → B = (B ∪ {x}) \ {x} :=
  begin
    intro hxB,
    simp only [set.mem_singleton, set.insert_diff_of_mem, set.union_singleton],
    apply set.ext,
    intro b,
    split,
    {
      intro hb, split,
      {exact hb},
      {intro hbot,
      rw set.mem_singleton_iff at hbot,
      rw hbot at hb,
      exact hxB hb,}
    },
    {intro hb, cases hb, cc},
  end
end set

namespace subfield

  variables
    (L : Type u) [field L]

  -- lemma closure_subset (U V : set L) (hUV : U ⊆ V) :
  --   (subfield.closure U : set L) ⊆ subfield.closure V :=
  -- begin
  --   simp only [set_like.coe_subset_coe, closure_le],
  --   apply set.subset.trans hUV subset_closure,
  -- end

end subfield

-- couldn't find in the library
def big_add {A : Type u} [has_add A] [has_zero A] : Π {n : ℕ}, (fin n → A) → A
| nat.zero := 0
| (nat.succ n) := λ as, (big_add (λ k : fin n, as k)) + as n

def big_mul {A : Type u} [has_mul A] [has_one A] : Π {n : ℕ}, (fin n → A) → A
| nat.zero := 1
| (nat.succ n) := λ as, (big_mul (λ k : fin n, as k)) * as n
