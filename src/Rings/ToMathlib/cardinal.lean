import set_theory.cardinal
import Rings.ToMathlib.fol
import data.W.cardinal

universes u v

namespace fol

variables {L : Language.{u}}

open_locale cardinal

open fol.Language

def bounded_term.rec2_aux {n} {C : bounded_term L n → Sort v}
  (hvar : ∀(k : fin n), C &k)
  (hfunc : Π {l} (f : L.functions l) (ts : dvector (bounded_term L n) l)
    (ih_ts : ∀t, ts.pmem t → C t), C (bd_apps (bd_func f) ts)) :
  Π {l} (t : bounded_preterm L n l) (ts : dvector (bounded_term L n) l)
  (ih_ts : ∀s, ts.pmem s → C s), C (bd_apps t ts)
| l (bd_var k) dvector.nil := λ _, hvar k
| l (bd_func f)  ts := λ hs, hfunc f ts hs
| l (bd_app t s) ts := λ hs, bounded_term.rec2_aux t (dvector.cons s ts) $
  λ r hr, psum.cases_on hr
    (λ hrs, eq.rec_on hrs.symm (bounded_term.rec2_aux s dvector.nil $
      λ s₀ hs₀, false.elim $ by {cases hs₀}))
    (hs _)

def bounded_term.rec2 {n} {C : bounded_term L n → Sort v}
  (hvar : ∀(k : fin n), C &k)
  (hfunc : Π {l} (f : L.functions l) (ts : dvector (bounded_term L n) l)
    (ih_ts : ∀t, ts.pmem t → C t), C (bd_apps (bd_func f) ts)) :
  ∀(t : bounded_term L n), C t :=
λt, bounded_term.rec2_aux hvar (λ _, hfunc) t dvector.nil (λ s hs, false.elim $ by {cases hs})

-- have h : ∀{n l} (f : bounded_preformula L n l) (ts : dvector (bounded_term L n) l),
--   C n (bd_apps_rel f ts),
-- begin
--   intros, induction f; try {rw ts.zero_eq},
--   apply hfalsum, apply hequal, apply hrel, apply f_ih (f_t::ts),
--   exact himp (f_ih_f₁ ([])) (f_ih_f₂ ([])), exact hall (f_ih ([]))
-- end,
-- λn f, h f ([])

def bounded_formula.rec2_aux {C : Πn, bounded_formula L n → Sort v}
  (hfalsum : Π {n}, C n ⊥)
  (hequal : Π {n} (t₁ t₂ : bounded_term L n), C n (t₁ ≃ t₂))
  (hrel : Π {n l : ℕ} (R : L.relations l) (ts : dvector (bounded_term L n) l),
    C n (bd_apps_rel (bd_rel R) ts))
  (himp : Π {n} {f₁ f₂ : bounded_formula L n} (ih₁ : C n f₁) (ih₂ : C n f₂), C n (f₁ ⟹ f₂))
  (hall : Π {n} {f : bounded_formula L (n+1)} (ih : C (n+1) f), C n (∀' f)) :
  ∀{n l} (f : bounded_preformula L n l) (ts : dvector (bounded_term L n) l),
  C n (bd_apps_rel f ts)
| _ _ bd_falsum dvector.nil := hfalsum
| _ _ (t₁ ≃ t₂) dvector.nil := hequal _ _
| _ _ (bd_rel R)         ts := hrel _ _
| _ _ (bd_apprel f t)    ts := by {let x := bounded_formula.rec2_aux f (dvector.cons t ts),
  dsimp [bd_apps_rel] at x, exact x }
| _ _ (f₁ ⟹ f₂) dvector.nil := himp (bounded_formula.rec2_aux f₁ dvector.nil)
  (bounded_formula.rec2_aux f₂ dvector.nil)
| _ _ (∀' f)    dvector.nil := hall (bounded_formula.rec2_aux f dvector.nil)

def bounded_formula.rec2 {C : Πn, bounded_formula L n → Sort v}
  (hfalsum : Π {n}, C n ⊥)
  (hequal : Π {n} (t₁ t₂ : bounded_term L n), C n (t₁ ≃ t₂))
  (hrel : Π {n l : ℕ} (R : L.relations l) (ts : dvector (bounded_term L n) l),
    C n (bd_apps_rel (bd_rel R) ts))
  (himp : Π {n} {f₁ f₂ : bounded_formula L n} (ih₁ : C n f₁) (ih₂ : C n f₂), C n (f₁ ⟹ f₂))
  (hall : Π {n} {f : bounded_formula L (n+1)} (ih : C (n+1) f), C n (∀' f)) :
  ∀{n : ℕ} (f : bounded_formula L n), C n f :=
λ n f, bounded_formula.rec2_aux (λ _, hfalsum) (λ _, hequal) (λ _ _, hrel) (λ _ _ _, himp)
  (λ _ _, hall) f dvector.nil

-- lemma bounded_term.rec2_aux_bd_apps {n} {C : bounded_term L n → Sort v}
--   (hvar : ∀(k : fin n), C &k)
--   (hfunc : Π {l} (f : L.functions l) (ts : dvector (bounded_term L n) l)
--     (ih_ts : ∀t, ts.pmem t → C t), C (bd_apps (bd_func f) ts)) :
--   ∀ {l} (t : bounded_preterm L n l) (ts : dvector (bounded_term L n) l)
--     (ih_ts : ∀t, ts.pmem t → C t),
--   bounded_term.rec2_aux hvar (λ _, hfunc) (bd_apps t ts)
--     = sorry :=
-- begin
--   sorry
--   -- intros l t,
--   -- induction t,
--   -- {
--   --   intro ts,
--   --   -- induction ts,


--   -- },
--   -- {sorry},
-- end

lemma bounded_term.rec2_bd_var {n} {C : bounded_term L n → Sort v}
  (hvar : ∀(k : fin n), C &k)
  (hfunc : Π {l} (f : L.functions l) (ts : dvector (bounded_term L n) l)
    (ih_ts : ∀t, ts.pmem t → C t), C (bd_apps (bd_func f) ts)) :
  ∀ (k : fin n),
  bounded_term.rec2 hvar (λ _, hfunc) &k = hvar k := λ k, rfl

lemma bounded_term.rec2_bd_apps {n} {C : bounded_term L n → Sort v}
  (hvar : ∀(k : fin n), C &k)
  (hfunc : Π {l} (f : L.functions l) (ts : dvector (bounded_term L n) l)
    (ih_ts : ∀t, ts.pmem t → C t), C (bd_apps (bd_func f) ts)) :
  ∀ {l} (f : L.functions l) (ts : dvector (bounded_term L n) l)
    (ih_ts : ∀t, ts.pmem t → C t),
  bounded_term.rec2 hvar (λ _, hfunc) (bd_apps (bd_func f) ts)
    = hfunc f ts ih_ts :=
begin
  intros l f ts,
  induction ts with a b c hind e f g,
  { intro ih_ts,
    dsimp [bounded_term.rec2, bounded_term.rec2_aux],
    apply congr_arg,
    ext _ a,
    cases a },
  {
    intro ih_ts,
    dsimp [bd_apps, bounded_term.rec2, bounded_term.rec2_aux],
    sorry,

  },
end

namespace cardinal

variables (L) (n : ℕ)

/-- We make `bounded_term L n` as a `W_type`, viewing the `W_type` as an inductive type
  the constructors would be indexed by the following definition.
  For each `k < n` we have a variable `xₙ` (with arity zero given by `pempty`)
  For each `⟨ n , f ⟩ : Σ n : ℕ, L.functions n` we have a function application (with arity `n`) -/
@[reducible] def term_α := ulift.{u} (fin n) ⊕ Σ m : ulift.{u} ℕ, L.functions m.down

/-- To define the arities in the `W_type` for `closed_term`.
  For each `n : ℕ` we have a variable `xₙ` (with arity zero given by `pempty`)
  For each `⟨ n , f ⟩ : Σ n : ℕ, L.functions n` we have a function application (with arity `n`) -/
@[reducible] def term_β : Π (c : term_α.{u} L n), Type u
| (sum.inl m) := pempty.{u+1}
| (sum.inr ⟨ m , f ⟩) := ulift.{u} (fin m.down)

variable {L}

/-- The forward map of the equivalence `W_type_term_β_equiv_closed_term` -/
@[reducible] def bounded_term_of_W_type_term_β : W_type (term_β L n) → bounded_term L n
| ⟨ sum.inl m , b ⟩ := x_ m.down
| ⟨ sum.inr (⟨ n , f ⟩) , b ⟩ := bd_apps (bd_func f)
  (dvector.of_fn (λ k, bounded_term_of_W_type_term_β $ b (ulift.up k)))

/-- The forward map of the equivalence `W_type_term_β_equiv_closed_term` -/
@[reducible] def W_type_term_β_of_bounded_term : bounded_term L n → W_type (term_β L n) :=
  bounded_term.rec2
    (λ m, ⟨ sum.inl ⟨m⟩ , pempty.elim ⟩) $
    λ l f ts rec,
    ⟨ sum.inr ⟨ ulift.up l , f ⟩, λ k : ulift (fin l), rec (dvector.nth' ts $ k.down) dvector.pmem_nth' ⟩

lemma bounded_term_of_W_type_term_β_surjective' : ∀ t : bounded_term L n,
  bounded_term_of_W_type_term_β n (W_type_term_β_of_bounded_term n t) = t :=
begin
  apply bounded_term.rec2,
  { intro k, refl },
  { intros l f ts hind,
    dsimp only [W_type_term_β_of_bounded_term],
    rw bounded_term.rec2_bd_apps _ _ _ _ (λ t _, W_type_term_β_of_bounded_term n t),
    dsimp [bounded_term_of_W_type_term_β],
    congr,
    rw dvector.ext,
    intro i,
    simp [dvector.nth'_of_fn],
    apply hind,
    exact dvector.pmem_nth' },
end

/- This is really an equivalence, but we only need surjectivity -/
lemma bounded_term_of_W_type_term_β_surjective :
  function.surjective (@bounded_term_of_W_type_term_β L n) :=
begin
  intros t,
  use W_type_term_β_of_bounded_term n t,
  exact bounded_term_of_W_type_term_β_surjective' _ _,
end

lemma fintype_term_β : Π (a : term_α L n), fintype (term_β L n a)
| (sum.inl ⟨ m ⟩) := by apply_instance
| (sum.inr ⟨ m , f ⟩) := fintype.of_equiv (fin m.down) equiv.ulift.symm

local attribute [instance] fintype_term_β

lemma bounded_term_le_functions : #(bounded_term L n) ≤
  max (cardinal.sum (λ n : ulift.{u} (ℕ), #(L.functions n.down))) ω :=
calc #(bounded_term L n)
      ≤ #(W_type (term_β.{u} L n)) :
    cardinal.mk_le_of_surjective (bounded_term_of_W_type_term_β_surjective n)
  ... ≤ max (# (ulift.{u} (fin n) ⊕ Σ (m : ulift.{u} ℕ), L.functions m.down)) ω :
    W_type.cardinal_mk_le_max_omega_of_fintype
  ... ≤ max (#(Σ n : ulift.{u} ℕ, L.functions n.down)) ω :
  begin
    apply max_le _ (le_max_right _ _),
    simp only [cardinal.mk_sum],
    apply le_trans (cardinal.add_le_max _ _),
    apply max_le _ (le_max_right _ _),
    apply max_le (le_max_of_le_right _) (le_max_of_le_left _),
    { apply le_of_lt, simp [cardinal.lt_omega] },
    { simp },
  end
  ... = max (cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down))) ω :
    by {rw cardinal.mk_sigma _}

-- lemma bounded_preformula_le_bounded_term' (n l : ℕ) :
--   #(bounded_preformula L n l) ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(bounded_term L n.down))) ω := sorry

/- We show that the formulas are bounded above by the terms.
  We first construct a `W_type` for each `bounded_formula L n` as follows
  ```
  | constructor | multiplicity         | arity |
  |-------------+----------------------+-------|
  | ⊥           | unit                 | empty |
  | t₁ ≃ t₂     | (bounded_term L n)²  | empty |
  | ⟹           | unit                 | fin 2 |
  ```
  This gives us a way of injecting `bounded_formula L n`
  into `W_type β n ⊕ bounded_formula L (n+1)` (to account for `∀`).
  This ultimately gives us
  `bounded_formula L 0 ↪ Σ n : ℕ, W_type β n ` where instead of
  mapping into `bounded_formula L (n+1)` we map into the next `W_type β (n+1)`.
  We have bounds on each `W_type β n`, namely by `unit`, `(bounded_term L n)²` and `ω`.
  Finally we can remove `unit` and the squaring.

  The difference with the case of terms is captured in the following example
  ```
  inductive box : ℕ → Type u
  | base {n} : box n
  | all {n} (f : box (n+1)) : box n
  ```
-/

lemma bounded_formula_le_bounded_term :
  #(bounded_formula L 0) ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(bounded_term L n.down))) ω :=
sorry

lemma sentence_le_functions :
  #(bounded_formula L 0) ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down))) ω :=
begin
  apply le_trans (bounded_formula_le_bounded_term),
  apply max_le _ (le_max_right _ _),
  apply le_trans (cardinal.sum_le_sup _),
  simp only [cardinal.mk_denumerable],
  apply le_trans (cardinal.mul_le_max _ _),
  apply max_le _ (le_max_right _ _),
  apply max_le (le_max_right _ _),
  rw cardinal.sup_le,
  intro i,
  apply bounded_term_le_functions,
end

variable (L)

/-- Applying `∀` is an injection downwards. -/
def bounded_formula_bd_all : bounded_formula L (n+1) → (bounded_formula L n) :=
λ ϕ, ∀' ϕ

/-- Applying `∀` n times is an injection. "Dropbox" -/
def bounded_formula_bd_alls : Π n, bounded_formula L n → (bounded_formula L 0)
| 0 := id
| (n+1) := (bounded_formula_bd_alls n) ∘ bounded_formula_bd_all L n

variable {L}

lemma bounded_formula_bd_all_injective : function.injective (bounded_formula_bd_all L n) :=
λ ϕ ψ, bounded_preformula.bd_all.inj

lemma bounded_formula_bd_alls_injective : Π n, function.injective (bounded_formula_bd_alls L n)
| 0 := function.injective_id
| (n+1) := function.injective.comp (bounded_formula_bd_alls_injective n) (bounded_formula_bd_all_injective n)

/- Using ∀ we can embed `bounded_formula L (n+1)` into `bounded_formula L n`,
  hence showing they are all bounded by the function symbols
 -/
lemma bounded_formula_le_functions (n : ℕ) :
  #(bounded_formula L n) ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down))) ω :=
calc #(bounded_formula L n) ≤ #(bounded_formula L 0) : cardinal.mk_le_of_injective (bounded_formula_bd_alls_injective _)
                        ... ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down))) ω :
                        sentence_le_functions

end cardinal

end fol
