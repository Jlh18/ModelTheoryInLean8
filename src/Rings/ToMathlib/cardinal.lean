import set_theory.cardinal
import Rings.ToMathlib.fol
import data.W.cardinal

universes u v

namespace fol

variables {L : Language.{u}}

open_locale cardinal

open fol.Language

@[simp] def bounded_formula.rec2_aux {C : Πn, bounded_formula L n → Sort v}
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

@[simp] def bounded_formula.rec2 {C : Πn, bounded_formula L n → Sort v}
  (hfalsum : Π {n}, C n ⊥)
  (hequal : Π {n} (t₁ t₂ : bounded_term L n), C n (t₁ ≃ t₂))
  (hrel : Π {n l : ℕ} (R : L.relations l) (ts : dvector (bounded_term L n) l),
    C n (bd_apps_rel (bd_rel R) ts))
  (himp : Π {n} {f₁ f₂ : bounded_formula L n} (ih₁ : C n f₁) (ih₂ : C n f₂), C n (f₁ ⟹ f₂))
  (hall : Π {n} {f : bounded_formula L (n+1)} (ih : C (n+1) f), C n (∀' f)) :
  ∀{n : ℕ} (f : bounded_formula L n), C n f :=
λ n f, bounded_formula.rec2_aux (λ _, hfalsum) (λ _, hequal) (λ _ _, hrel) (λ _ _ _, himp)
  (λ _ _, hall) f dvector.nil

namespace cardinal

variables (L) (n : ℕ)

/-- Write preterms as lists of the following symbols -/
inductive preterm_symbol : Type u
| nat : ℕ → preterm_symbol
| var : Π {l}, fin l → preterm_symbol
| func : Π {l}, L.functions l → preterm_symbol
| app : preterm_symbol

instance : infinite (preterm_symbol L) :=
infinite.of_injective preterm_symbol.nat (λ _ _, preterm_symbol.nat.inj)

/-- Capture the cardinality of `preterm_symbol` by writing it equivalently in terms of a sum.
  The forward map of the equivalence. -/
def fin_sum_formula_sum_nat_of_preterm_symbol : preterm_symbol L →
  (Σ l : ulift.{u} ℕ, ulift.{u} (fin l.down)) ⊕ (Σ l : ulift.{u} ℕ, L.functions l.down) ⊕ ℕ
| (preterm_symbol.nat n) := sum.inr $ sum.inr $ n.succ
| (preterm_symbol.var k) := sum.inl $ ⟨ ⟨_⟩ , ulift.up k ⟩
| (preterm_symbol.func f) := sum.inr $ sum.inl ⟨ ⟨_⟩, f ⟩
| preterm_symbol.app := sum.inr $ sum.inr 0

/-- Capture the cardinality of `preterm_symbol` by writing it equivalently in terms of a sum.
  The backward map of the equivalence. -/
def preterm_symbol_of_fin_sum_formula_sum_nat :
  (Σ l : ulift.{u} ℕ, ulift.{u} (fin l.down)) ⊕ (Σ l : ulift.{u} ℕ, L.functions l.down) ⊕ ℕ → preterm_symbol L
| (sum.inl ⟨ l , ⟨k⟩ ⟩) := preterm_symbol.var k
| (sum.inr $ sum.inl ⟨ l , f ⟩) := preterm_symbol.func f
| (sum.inr $ sum.inr 0) := preterm_symbol.app
| (sum.inr $ sum.inr (n+1)) := preterm_symbol.nat n

/-- Capture the cardinality of `preterm_symbol` by writing it equivalently in terms of a sum. -/
def preterm_symbol_equiv_fin_sum_formula_sum_nat :
  _root_.equiv (preterm_symbol L) $
  (Σ l : ulift.{u} ℕ, ulift.{u} (fin l.down)) ⊕ (Σ l : ulift.{u} ℕ, L.functions l.down) ⊕ ℕ :=
{ to_fun := fin_sum_formula_sum_nat_of_preterm_symbol L,
  inv_fun := preterm_symbol_of_fin_sum_formula_sum_nat L,
  left_inv := λ x, match x with
    | (preterm_symbol.nat n)  := rfl
    | (preterm_symbol.var k)  := rfl
    | (preterm_symbol.func f) := rfl
    | preterm_symbol.app      := rfl end,
  right_inv := λ x, match x with
    | (sum.inl ⟨ ⟨l⟩ , ⟨k⟩ ⟩) := rfl
    | (sum.inr $ sum.inl ⟨ ⟨l⟩ , f ⟩) := rfl
    | (sum.inr $ sum.inr 0) := rfl
    | (sum.inr $ sum.inr (n+1)) := rfl end, }

/-- We inject `bounded_preterm L n l` into lists of symbols, keeping track
  of how the preterm is built.
  We always include the number of free variables, and number of missing applications,
  we keep track of the constructor,
  and then we keep the data of the any inductively attained list,
  even their lengths (useful in the proof of injectivity). -/
@[simp] def preterm_symbol_of_preterm {n} : ∀ {l},
  bounded_preterm L n l → list (preterm_symbol L)
| _ (&k)         := [ preterm_symbol.var k ]
| l (bd_func f)  := [ preterm_symbol.func f ]
| l (bd_app t s) := [ preterm_symbol.app,
  preterm_symbol.nat (preterm_symbol_of_preterm t).length ]
  ++ preterm_symbol_of_preterm t ++ preterm_symbol_of_preterm s

lemma preterm_symbol_of_preterm_injective {l} :
  function.injective (@preterm_symbol_of_preterm L n l) :=
begin
  intros x,
  induction x with k _ _ _ tx sx htx hsx,
  { intro y,
    cases y,
    { intro h,
      simp only [preterm_symbol_of_preterm, eq_self_iff_true, heq_iff_eq,
        true_and, and_true] at h,
      subst h },
    { intro h, cases h },
    { intro h, cases h } },
  { intro y,
    cases y,
    { intro h, cases h },
    { intro h,
      simp only [preterm_symbol_of_preterm, eq_self_iff_true, heq_iff_eq,
        true_and, and_true] at h,
      subst h },
    { intro h, cases h } },
  { intro y,
    cases y with _ _ _ _ ty sy,
    { intro h, cases h },
    { intro h, cases h },
    { intro h, simp only [preterm_symbol_of_preterm, list.cons_append,
      list.singleton_append, eq_self_iff_true, true_and] at h,
      obtain ⟨ ht , hs ⟩ := list.append_inj h.2 h.1,
      congr, { exact htx ht }, { exact hsx hs } } },
end

variable {L}

lemma bounded_preterm_le_functions {l} : #(bounded_preterm L n l) ≤
  max (cardinal.sum (λ n : ulift.{u} (ℕ), #(L.functions n.down))) ω :=
calc #(bounded_preterm L n l) ≤ # (list (preterm_symbol L)) :
    cardinal.mk_le_of_injective (@preterm_symbol_of_preterm_injective L n l)
  ... = # (preterm_symbol L) : cardinal.mk_list_eq_mk (preterm_symbol L)
  ... ≤ max (cardinal.sum (λ n : ulift.{u} (ℕ), #(L.functions n.down))) ω :
begin
  rw cardinal.mk_congr (preterm_symbol_equiv_fin_sum_formula_sum_nat L),
  simp only [cardinal.mk_sum, cardinal.mk_sigma, cardinal.mk_fintype, fintype.card_ulift,
    fintype.card_fin, cardinal.lift_id, cardinal.mk_denumerable, cardinal.lift_omega],
  apply le_trans (cardinal.add_le_max _ _) (max_le (max_le _ _) (le_max_right _ _)),
  { apply le_max_of_le_right,
    apply le_trans (cardinal.sum_le_sup.{u} (λ (i : ulift.{u} ℕ), (i.down : cardinal.{u}))),
    apply le_trans (cardinal.mul_le_max _ _) (max_le (max_le _ _) (le_of_eq rfl)),
    { simp },
    { rw cardinal.sup_le, intro i, apply le_of_lt, rw cardinal.lt_omega, simp, }
  },
  { apply le_trans (cardinal.add_le_max _ _) (max_le (max_le _ _) (le_max_right _ _)),
    { simp },
    { exact le_max_right _ _ } }
end

/-- Write formulas as lists of the following symbols -/
inductive formula_symbol (L : Language.{u}) : Type u
| bot : formula_symbol
| eq : formula_symbol
| imp : formula_symbol
| all : formula_symbol
| term : Π (l : ℕ), bounded_term L l → formula_symbol
| nat : ℕ → formula_symbol

instance : infinite (formula_symbol L) :=
infinite.of_injective formula_symbol.nat (λ x y, formula_symbol.nat.inj)

/-- Capture the cardinality of `formula_symbol` by writing it equivalently in terms of a sum.
  The forward map of the equivalence. -/
def bounded_term_sum_nat_of_formula_symbol : formula_symbol L →
  (Σ l : ulift.{u} ℕ, bounded_term L l.down) ⊕ ulift.{u} ℕ
| formula_symbol.bot := sum.inr ⟨0⟩
| formula_symbol.eq := sum.inr ⟨1⟩
| formula_symbol.imp := sum.inr ⟨2⟩
| formula_symbol.all := sum.inr ⟨3⟩
| (formula_symbol.term l f) := sum.inl ⟨ ⟨l⟩ , f ⟩
| (formula_symbol.nat n) := sum.inr ⟨ n+4 ⟩

/-- Capture the cardinality of `formula_symbol` by writing it equivalently in terms of a sum.
  The backward map of the equivalence. -/
def formula_symbol_of_bounded_term_sum_nat :
  (Σ l : ulift.{u} ℕ, bounded_term L l.down) ⊕ ulift.{u} ℕ → formula_symbol L
| (sum.inl ⟨ l , f ⟩) := formula_symbol.term l.down f
| (sum.inr ⟨0⟩) := formula_symbol.bot
| (sum.inr ⟨1⟩) := formula_symbol.eq
| (sum.inr ⟨2⟩) := formula_symbol.imp
| (sum.inr ⟨3⟩) := formula_symbol.all
| (sum.inr (⟨ n+4 ⟩)) := formula_symbol.nat n

/-- Capture the cardinality of `formula_symbol` by writing it equivalently in terms of a sum. -/
def formula_symbol_equiv_bounded_term_sum_nat :
  _root_.equiv (formula_symbol L) ((Σ l : ulift.{u} ℕ, bounded_term L l.down) ⊕ ulift.{u} ℕ) :=
{ to_fun := bounded_term_sum_nat_of_formula_symbol,
  inv_fun := formula_symbol_of_bounded_term_sum_nat,
  left_inv := λ x, match x with
    | formula_symbol.bot := rfl
    | formula_symbol.eq :=  rfl
    | formula_symbol.imp := rfl
    | formula_symbol.all := rfl
    | (formula_symbol.term l f) := rfl
    | (formula_symbol.nat n) := rfl end,
  right_inv := λ x, match x with
    | (sum.inl ⟨ ⟨l⟩ , f ⟩) := rfl
    | (sum.inr ⟨0⟩) :=       rfl
    | (sum.inr ⟨1⟩) :=       rfl
    | (sum.inr ⟨2⟩) :=       rfl
    | (sum.inr ⟨3⟩) :=       rfl
    | (sum.inr (⟨ n+4 ⟩)) := rfl end, }

/-- We inject `bounded_formula L n` into lists of symbols, keeping track
  of how the formula is built.
  We always include the number of variables of the formula at the beginning
  by adding `logic_symbo.nat l`,
  we then note the symbol for the constructor,
  and then we keep the data of the any inductively attained list. -/
@[simp] def formula_symbol_of_formula [is_algebraic L] {n} :
  bounded_formula L n → list (formula_symbol L) :=
bounded_formula.rec2
  (λ l, [formula_symbol.nat l, formula_symbol.bot]) -- ⊥
  (λ l t s, [ formula_symbol.nat l, formula_symbol.eq ,
    formula_symbol.term l t , formula_symbol.term l s ]) -- t ≃ s
  (λ _ _ r, false.elim $ Language.is_algebraic.empty_relations _ r) -- bd_rel
  (λ l ϕ ψ lϕ lψ, (formula_symbol.nat l) :: (formula_symbol.nat (list.length lϕ))
    :: (formula_symbol.nat (list.length lψ)) :: formula_symbol.imp :: lϕ.append lψ ) -- ϕ ⟹ ψ
  (λ l ϕ lϕ, (formula_symbol.nat l) :: formula_symbol.all :: lϕ) -- ∀ₗ ϕ

lemma formula_symbol_of_preformula_injective' [is_algebraic L] {n} : ∀ (x : bounded_formula L n)
  {m} (y : bounded_formula L m),
  formula_symbol_of_formula x = formula_symbol_of_formula y → x == y :=
begin
  -- apply bounded_formula.rec2,
  have hrel : ∀ {l} {p : Prop} (r : L.relations l), p,
  { intros _ _ r,
    exact false.elim (Language.is_algebraic.empty_relations _ r) },
  apply @bounded_formula.rec2 _ (λ _ x, ∀ {m} (y : bounded_formula L m),
    formula_symbol_of_formula x = formula_symbol_of_formula y → x == y),
  { intro l,
    apply @bounded_formula.rec2 _ (λ n y,
      formula_symbol_of_formula _ = formula_symbol_of_formula y → _ == y),
    { intros k h, simp only [formula_symbol_of_formula, bounded_formula.rec2_aux,
        bounded_formula.rec2, eq_self_iff_true, and_true] at h, subst h },
    { intros _ _ _ h, cases h },
    { intros _ _ r, apply hrel r },
    { intros _ _ _ _ _ h, cases h },
    { intros _ _ _ h, cases h } },
  { intros l t s,
    apply @bounded_formula.rec2 _ (λ n y,
      formula_symbol_of_formula _ = formula_symbol_of_formula y → _ == y),
    { intros k h, cases h },
    { intros _ _ _ h, simp at h, cases h with h h', subst h, cases h' with h h',
      cases h with h h1, subst h1, cases h' with h' h'1, subst h'1 },
    { intros _ _ r, apply hrel r },
    { intros _ _ _ _ _ h, cases h },
    { intros _ _ _ h, cases h } },
  { intros _ _ r, apply hrel r },
  { intros l f₁ f₂ hf₁ hf₂,
    apply @bounded_formula.rec2 _ (λ n y,
      formula_symbol_of_formula _ = formula_symbol_of_formula y → _ == y),
    { intros k h, cases h },
    { intros _ _ _ h, cases h },
    { intros _ _ r, apply hrel r },
    { intros l' f₁' f₂' hf₁' hf₂' h, simp at h, obtain ⟨ hll' , hlenϕ , hlenψ , h ⟩ := h,
      subst hll', obtain ⟨ hf₁f₁' , hf₂f₂'⟩ := list.append_inj h hlenϕ, congr,
      { simp at hf₁, specialize hf₁ f₁' hf₁f₁', subst hf₁ },
      { simp at hf₂, specialize hf₂ f₂' hf₂f₂', subst hf₂ } },
    { intros _ _ _ h, cases h } },
  { intros l f₁ hf₁ m, apply @bounded_formula.rec2 _
      (λ n y, formula_symbol_of_formula _ = formula_symbol_of_formula y → _ == y),
    { intros k h, cases h, },
    { intros _ _ _ h, cases h },
    { intros _ _ r, apply hrel r },
    { intros _ _ _ _ _ h, cases h },
    { intros k f₂ hf₂ h, simp only [formula_symbol_of_formula, bounded_formula.rec2_aux,
        bounded_formula.rec2, eq_self_iff_true, true_and] at h hf₁,
      cases h with hlk h, subst hlk, congr1, apply eq_of_heq, apply hf₁, exact h } },
end

lemma formula_symbol_of_preformula_injective [is_algebraic L] {n}:
  function.injective (@formula_symbol_of_formula L _ n) :=
begin
  intros x y hxy,
  have h := formula_symbol_of_preformula_injective' x y hxy,
  subst h,
end

variable (L)

lemma bounded_formula_le_bounded_term [is_algebraic L] {n} :
  #(bounded_formula L n) ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(bounded_term L n.down))) ω :=
calc #(bounded_formula L n) ≤ # (list (formula_symbol L)) :
    cardinal.mk_le_of_injective (formula_symbol_of_preformula_injective)
  ... = # (formula_symbol L) : cardinal.mk_list_eq_mk _
  ... = _ : cardinal.mk_congr formula_symbol_equiv_bounded_term_sum_nat
  ... ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(bounded_term L n.down))) ω : by {
  simp only [le_refl, and_true, cardinal.mk_denumerable, cardinal.mk_sum, cardinal.lift_omega,
    cardinal.mk_sigma, cardinal.lift_id],
  apply le_trans (cardinal.add_le_max _ _) (max_le (max_le _ _) (le_max_right _ _)),
  { exact le_max_left _ _ },
  { exact le_max_right _ _ } }

lemma bounded_formula_le_functions [is_algebraic L] {n} :
  #(bounded_formula L n) ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down))) ω :=
begin
  apply le_trans (bounded_formula_le_bounded_term L),
  apply max_le _ (le_max_right _ _),
  apply le_trans (cardinal.sum_le_sup _),
  simp only [cardinal.mk_denumerable],
  apply le_trans (cardinal.mul_le_max _ _),
  apply max_le _ (le_max_right _ _),
  apply max_le (le_max_right _ _),
  rw cardinal.sup_le,
  intro i,
  apply bounded_preterm_le_functions,
end

end cardinal

end fol
