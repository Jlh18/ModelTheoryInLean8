import data.finset
import algebra.group.defs
import to_mathlib
import data.mv_polynomial
import fol
import Rings.Notation
import field_theory.subfield
import data.mv_polynomial.rename
import data.equiv.fin
import data.polynomial.algebra_map
import data.list

universes u v

lemma with_bot.succ_lt_succ_succ {n : ℕ} : (n + 1 : with_bot ℕ) < ↑n.succ + 1 := by tidy

/-- More general version of monoid.has_pow -/
instance has_pow_of_has_one_has_mul (A : Type u) [has_one A] [has_mul A] :
  has_pow A ℕ := ⟨ λ t k, npow_rec k t ⟩

@[simp] lemma cons_nth'_succ_eq_nth' {A : Type u} {n} {x : A} {as : dvector A n} {k : fin n} :
  (dvector.cons x as).nth' (k.succ) = as.nth' k :=
begin
  unfold dvector.nth',
  simp,
end

namespace dvector
  variable {A : Type u}

  /-- Converts a dvector into an n-ary tuple -/
  @[simp] def fin_val {n} (as : dvector A n) : fin n → A :=
  λ k, dvector.nth' as k

  /-- converts an n-ary tuple to an n.succ-ary tuple -/
  @[simp] def x_val {n} (x : A) (val : fin n → A) : fin n.succ → A :=
  @fin.cases n (λ _, A) x (λ i, val i)

  /-- x_val is the same data as concatenation of dvectors -/
  lemma fin_val_eq_x_val {n} {x : A} {as : dvector A n} :
    fin_val (dvector.cons x as) = x_val x (fin_val as) :=
  funext (
    @fin.cases n
    (λ k, fin_val (dvector.cons x as) k = x_val x (fin_val as) k)
    rfl
    (λ k, begin unfold fin_val, simp, end)
    )

  lemma nth_eq_succ_nth : Π {k n : ℕ} {as : dvector A (n + 1)} {h : k < n},
  as.nth k (lt_trans h (by simp)) = (dvector.remove_mth (n + 2) as).nth k h
  | k nat.zero (dvector.cons a _) h := by {exfalso, simpa using h}
  | nat.zero (nat.succ n) (dvector.cons a as) h := by simp
  | (nat.succ k) (nat.succ n) (dvector.cons a as) h := by {simpa using nth_eq_succ_nth}

end dvector

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
  mv_polynomial.eval (x_val polynomial.X (polynomial.C ∘ val)) p

  lemma eval_eq_poly_eval_mv_coeffs_X
  {n : ℕ} {val : fin n → A} (x : A) : Π {k},
    @mv_polynomial.eval A (fin n.succ) _ (x_val x val) (mv_polynomial.X k)
    = polynomial.eval x (to_polynomial val (mv_polynomial.X k)) :=
  @fin.cases n
  (λ k, @mv_polynomial.eval A (fin n.succ) _ (x_val x val) (mv_polynomial.X k)
    = polynomial.eval x (to_polynomial val (mv_polynomial.X k)))
  (begin
    simp only [mv_polynomial.eval_X, fin.cases_zero,
      function.comp_app, x_val, to_polynomial],
    unfold_coes,
    simp,
  end)
  (begin
    simp only [mv_polynomial.eval_X, fin.cases_succ,
      function.comp_app, x_val, to_polynomial],
    unfold_coes,
    simp,
  end)

  lemma eval_eq_poly_eval_mv_coeffs
  {n : ℕ} {p : mv_polynomial (fin n.succ) A} {val : fin n → A} (x : A) :
    @mv_polynomial.eval A (fin n.succ) _ (x_val x val) p
    = polynomial.eval x (to_polynomial val p) :=
  @mv_polynomial.induction_on A (fin n.succ) _
    (λ q, @mv_polynomial.eval A (fin n.succ) _ (x_val x val) q
    = polynomial.eval x (to_polynomial val q))
    p
  (begin
    intro a,
    simp only [mv_polynomial.eval_C, function.comp_app, x_val, to_polynomial],
    unfold_coes,
    simp,
  end)
  (begin
    intros p q,
    simp only [to_polynomial],
    intros hp hq,
    unfold_coes,
    simp only [ring_hom.map_add, ring_hom.to_fun_eq_coe,
    function.comp_app, x_val, polynomial.eval_add],
    simp only [ring_hom.to_fun_eq_coe, function.comp_app, x_val] at hp hq,
    rw [hp, hq],
    refl,
  end)
  (begin
    intros p k,
    simp only [to_polynomial],
    unfold_coes,
    simp only [mv_polynomial.eval_X, ring_hom.to_fun_eq_coe,
      function.comp_app, polynomial.eval_mul, x_val, mv_polynomial.eval_map,
      ring_hom.map_mul, mv_polynomial.map_X],
    intro hp,
    rw ← hp,
    have hx := @mv_polynomial.eval_eq_poly_eval_mv_coeffs_X _ _ _ val x k,
    simp only [mv_polynomial.eval_X, function.comp_app, x_val, to_polynomial] at hx,
    rw hx,
    unfold_coes,
    simp,
  end)

  @[simp] lemma eval_add {val : σ → A} {p q : mv_polynomial σ A} :
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
  --   left_inv  :=
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

  -- lemma dvector.pmem_of_last {α : Type u} : Π {a_ : dvector α 1}, dvector.pmem a_.last a_
  -- | [a] := psum.inl rfl


namespace fol.bounded_preterm

-- I don't know if this is already in fol but
  @[simp] def lift_succ {L} {n : ℕ} : Π {l},
    fol.bounded_preterm L n l → fol.bounded_preterm L n.succ l
  | l (fol.bounded_preterm.bd_var k) := x_ k
  | l (fol.bounded_preterm.bd_func f) := fol.bounded_preterm.bd_func f
  | l (fol.bounded_preterm.bd_app t s) :=
    fol.bounded_preterm.bd_app (@lift_succ l.succ t) (@lift_succ 0 s)

  -- instance has_lift_succ {L} {n : ℕ} : Π l,
  --   has_lift (fol.bounded_preterm L n l) (fol.bounded_preterm L n.succ l) :=
  --   λ l, ⟨ lift_succ ⟩

  lemma lift_succ_x_k {L} {n : ℕ} {k : fin n} :
    lift_succ (x_ k : fol.bounded_preterm L n 0) = x_ k := rfl



end fol.bounded_preterm


namespace zorn

open classical
local attribute [instance] prop_decidable

  lemma fin_range_sub_mem_chain_of_sub_union
    {α : Type u} {c : set (set α)} (hchain : zorn.chain has_subset.subset c) (hc0 : c.nonempty) :
    Π {n : ℕ} (F : fin n → α), (Π k, F k ∈ ⋃₀ c)
      → ∃ (Y : set α), Y ∈ c ∧ (Π k, F k ∈ Y)
  | nat.zero :=
  begin
    intros F hF,
    cases hc0 with Y hY,
    use Y,
    split,
    {exact hY},
    {exact is_empty.elim fin.is_empty}
  end
  | (nat.succ n) :=
  begin
    intros Fsucc hFsucc,
    have F : fin n → α := λ k, Fsucc (k.succ),
    have hF : Π (k : fin n), Fsucc k.succ ∈ ⋃₀ c := λ k, hFsucc (fin.succ k),
    cases fin_range_sub_mem_chain_of_sub_union (λk, Fsucc (k.succ)) hF with Y hY,
    have h0cup : Fsucc 0 ∈ ⋃₀ c := hFsucc 0,
    rw set.mem_sUnion at h0cup,
    cases h0cup with Y0 hY0,
    cases hY0 with hY0c hY0,
    cases hY with hYc hY,
    by_cases hYY0 : Y = Y0,
    {
      use Y,
      split,
      {exact hYc},
      {
        intro k,
        apply @fin.cases n (λ l, Fsucc l ∈ Y),
        {rw hYY0, exact hY0},
        {intro i, apply hY i},
      }
    },
    {
      cases hchain Y hYc Y0 hY0c hYY0 with hsub hsub,
      {
        use Y0,
        split,
        {exact hY0c},
        {
          intro k,
          apply @fin.cases n (λ l, Fsucc l ∈ Y0),
          {exact hY0},
          {intro i, apply hsub, apply hY i},
        }
      },
      {
        use Y,
        split,
        {exact hYc},
        {
          intro k,
          apply @fin.cases n (λ l, Fsucc l ∈ Y),
          {apply hsub, exact hY0},
          {intro i, apply hY i},
        },
      },
    }
  end

  lemma fin_sub_mem_chain_of_sub_union
    {α : Type u} {c : set (set α)} (hchain : zorn.chain has_subset.subset c) (hc0 : c.nonempty) :
    Π (F : finset α), (↑F ⊆ ⋃₀ c) → ∃ (Y : set α), Y ∈ c ∧ ↑F ⊆ Y :=
  @finset.induction α (λ (F : finset α), (↑F ⊆ ⋃₀ c) → ∃ (Y : set α), Y ∈ c ∧ ↑F ⊆ Y)
  _
  (begin
    intro h0sub,
    cases hc0 with Y hY,
    use Y,
    split,
    exact hY,
    simp,
  end)
  (begin
    intros a F haF hind hFasub,
    have hacup : a ∈ ⋃₀ c,
    {apply hFasub, simp},
    rw set.mem_sUnion at hacup,
    cases hacup with Z hZ,
    cases hZ with hZc haZ,
    have hFsub : ↑F ⊆ ⋃₀ c,
    {apply set.subset.trans _ hFasub, simp},
    have Y := (hind hFsub),
    cases Y with Y hY,
    by_cases hYZ : Y = Z,
    {
      use Y,
      split,
      {exact hY.1},
      {
        simp only [finset.coe_insert, set.insert_subset],
        split,
        {rw hYZ, exact haZ,},
        {exact hY.2}
      }
    },
    cases hY with hYc hFY,
    cases hchain Y hYc Z hZc hYZ with hl hr,
    {
      use Z,
      split,
      {exact hZc},
      simp only [finset.coe_insert, set.insert_subset],
      split,
      {exact haZ},
      {exact set.subset.trans hFY hl},
    },
    {
      use Y,
      split,
      {exact hYc},
      {
        simp only [finset.coe_insert, set.insert_subset],
        split,
        {exact hr haZ},
        {exact hFY}
      },
    }
  end)

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

lemma dvector.nil_append {A} {n} (f : dvector A n) : dvector.append dvector.nil f = f :=
by simp

namespace fol

-- repeated and
def bd_big_and {L : Language} {d : ℕ} :
  Π (n : ℕ), (fin n → (bounded_formula L d)) → bounded_formula L d
| nat.zero fs := bd_not bd_falsum
| (nat.succ n) fs := bd_and (bd_big_and n (λ i, fs i)) (fs n)

lemma realize_bounded_formula_bd_alls'_aux {L} {n} : Π {k} {f : bounded_formula L (n + k)}
  {S : Structure L} (v : dvector S n),
  (realize_bounded_formula v (bd_alls' k n f) dvector.nil)
  →
  (∀ xs : dvector S k, realize_bounded_formula (dvector.append xs v) f dvector.nil)
| nat.zero  f S v hf (dvector.nil) :=
by simpa using hf
| (nat.succ n) f S v hf (dvector.cons x xs) :=
begin
  simp only [bd_alls'] at hf,
  have hf' := realize_bounded_formula_bd_alls'_aux v hf xs,
  simp only [realize_bounded_formula] at hf',
  simpa using hf' x,
end

lemma realize_bounded_formula_bd_alls' {L} {n} {k} {f : bounded_formula L (n + k)}
  {S : Structure L} (v : dvector S n) :
  (realize_bounded_formula v (bd_alls' k n f) dvector.nil)
  ↔
  (∀ xs : dvector S k, realize_bounded_formula (dvector.append xs v) f dvector.nil) :=
begin
  split, {apply realize_bounded_formula_bd_alls'_aux},
  intro hf,
  induction k with k hk,
  {simpa using hf dvector.nil},
  {
    simp only [bd_alls'],
    apply hk,
    simp only [realize_bounded_formula],
    intros xs x,
    apply hf (dvector.cons x xs),
  }
end



/-- copy of bd_alls with ∃'s instead--/
@[simp] def bd_exs' {L : Language} : Π k n : ℕ, bounded_formula L (n + k) → bounded_formula L n
| 0 n         f := f
| (k+1) n     f := bd_exs' k n (∃' f)

end fol

namespace fin

lemma lt_or_eq_nat {n : ℕ} (i : fin n.succ) : (i : ℕ) < n ∨ (i : ℕ) = n :=
begin
  cases nat.decidable_lt i n with h,
  {
    right,
    exact nat.eq_of_lt_succ_of_not_lt (fin.is_lt i) h,
  },
  {
    left,
    exact h,
  }
end

lemma lt_coe_iff_val_lt {n m : ℕ} (i : fin n.succ) (hle : m < n.succ) :
  (i : ℕ) < m ↔ i < (m : fin n.succ) :=
begin
  rw fin.lt_def,
  repeat {rw fin.val_eq_coe},
  rw fin.coe_coe_of_lt hle,
end

lemma lt_or_eq_fin {n : ℕ} (i : fin n.succ) : i < (n : fin n.succ) ∨ i = (n : fin n.succ) :=
begin
  cases fin.lt_or_eq_nat i with h,
  {
    left,
    rw ← fin.lt_coe_iff_val_lt i (nat.lt_succ_self _),
    exact h,
  },
  {
    right,
    rw ← fin.coe_coe_eq_self i,
    have f := @congr_arg _ _ (i : ℕ) n fin.of_nat h,
    simp only [fin.of_nat_eq_coe] at f,
    exact f,
  }
end

end fin

structure add_zero_hom (M N : Type*) [has_zero M] [has_zero N] [has_add M] [has_add N] :=
(to_fun : M → N)
(map_zero : to_fun 0 = 0)
(map_add : Π a b : M, to_fun (a + b) = to_fun a + to_fun b)

structure mul_one_hom (M N : Type*) [has_one M] [has_one N] [has_mul M] [has_mul N] :=
(to_fun : M → N)
(map_one : to_fun 1 = 1)
(map_mul : Π a b : M, to_fun (a * b) = to_fun a * to_fun b)
