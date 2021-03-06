import Rings.ToMathlib.fol
import set_theory.cardinal
import completeness
import language_extension
import data.W.cardinal
import Rings.ToMathlib.Lhom
import Rings.ToMathlib.completeness

noncomputable theory

universes u v

open fol fol.Language fol.Lhom

namespace fol

open_locale cardinal fol
variables {L : Language.{u}}

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

-- inductive box : ℕ → Type u
-- | base {n} : box n
-- | all {n} (f : box (n+1)) : box n

-- def drop : Π (n), box n → box 0
-- | 0 x := x
-- | (n+1) x := drop n (box.all x)

-- def box_zero_of_nat : ℕ → (box 0) := λ n, drop n box.base

-- def nat_of_box : ∀ n : ℕ, box n → ℕ
-- | n box.base := 0
-- | n (box.all f) := nat_of_box (n+1) f + 1

-- lemma left_inv : ∀ n, nat_of_box 0 (box_zero_of_nat n) = n
-- | 0 := rfl
-- | (n+1) :=
-- begin
--   have h := left_inv n,
--   dsimp [box_zero_of_nat, drop] at h,
--   sorry,

-- end

lemma bounded_preformula_le_bounded_term (n l : ℕ) :
  #(bounded_preformula L n l) ≤ #(Σ k : ℕ, bounded_term L k) := sorry

lemma bounded_preformula_of_bounded_formula (n : ℕ) :
  bounded_formula L n → (bounded_preformula L n 0) := λ x, x

lemma bounded_term_of_bounded_formula [is_algebraic L] (n : ℕ) :
  bounded_formula L n → (bounded_term L n) :=
sorry

lemma bounded_formula_le_bounded_term [is_algebraic L] (n : ℕ) :
  #(bounded_formula L 0) ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(bounded_term L n.down))) ω :=
sorry

lemma bounded_formula_card [is_algebraic L] (n : ℕ) :
  #(bounded_formula L 0) ≤ cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down)) :=
sorry

namespace term_model

/- `term_model` is the structure on terms built from a complete henkin theory.
  David Marker takes the elements of the model to be constant symbols
  up to equality in the theory (i.e. `c ≃ d ∈ T` or equivalently `T ⊢ c ≃ d`).
  In practice it is more sensible to take the model as 0-variable terms
  (closed terms) up to equality in the theory. -/

/- In this section we show that the cardinality of `term_model` is bounded
  by the function symbols in the language-/

variable (T : Theory L)

lemma card_le_closed_term : #(term_model T) ≤ #(closed_term L) :=
cardinal.mk_le_of_surjective quotient.surjective_quotient_mk'

/-- We make `closed_term` as a `W_type`, viewing the `W_type` as an inductive type
  the constructors would be indexed by the following definition.
  For each `n : ℕ` we have a variable `xₙ` (with arity zero given by `pempty`)
  For each `⟨ n , f ⟩ : Σ n : ℕ, L.functions n` we have a function application (with arity `n`) -/
def term_α (L : Language) := Σ n : ulift.{u} ℕ, L.functions n.down

/-- To define the arities in the `W_type` for `closed_term`.
  For each `n : ℕ` we have a variable `xₙ` (with arity zero given by `pempty`)
  For each `⟨ n , f ⟩ : Σ n : ℕ, L.functions n` we have a function application (with arity `n`) -/
def term_β (L : Language) : Π (c : term_α L), Type u
-- | (sum.inl n) := empty
| ⟨ n , f ⟩ := ulift (fin n.down)

/-- The forward map of the equivalence `W_type_term_β_equiv_closed_term` -/
def closed_term_of_W_type_term_β : W_type (term_β L) → closed_term L
-- | ⟨ n , b ⟩ := sorry
| ⟨ ⟨ n , f ⟩ , b ⟩ := bd_apps (bd_func f)
  (dvector.of_fn (λ k, closed_term_of_W_type_term_β $ b (ulift.up k)))

/-- The forward map of the equivalence `W_type_term_β_equiv_closed_term` -/
def W_type_term_β_of_closed_term : closed_term L → W_type (term_β L) :=
  bounded_term.rec2 fin_zero_elim $ λ l f ts rec,
    ⟨ ⟨ ulift.up l , f ⟩, λ k : ulift (fin l), rec (dvector.nth' ts $ k.down) dvector.pmem_nth' ⟩

lemma surj_lemma : ∀ t : closed_term L,
  closed_term_of_W_type_term_β (W_type_term_β_of_closed_term t) = t :=
begin
  apply bounded_term.rec2,
  { exact fin_zero_elim },
  { intros l f ts hind,
    dsimp [W_type_term_β_of_closed_term],
    rw bounded_term.rec2_bd_apps _ _ _ _ (λ t _, W_type_term_β_of_closed_term t),
    dsimp [closed_term_of_W_type_term_β],
    congr,
    rw dvector.ext,
    intro i,
    simp [dvector.nth'_of_fn],
    apply hind,
    exact dvector.pmem_nth' },
end

/- This is really an equivalence, but we only need surjectivity -/
lemma closed_term_of_W_type_term_β_surjective :
  function.surjective (@closed_term_of_W_type_term_β L) :=
begin
  intros t,
  use W_type_term_β_of_closed_term t,
  exact surj_lemma _,
end

lemma fintype_term_β : Π (a : term_α L), fintype (term_β L a) :=
λ ⟨ n , f ⟩, fintype.of_equiv (fin n.down) equiv.ulift.symm

local attribute [instance] fintype_term_β

lemma cardinal.closed_term_le_functions : #(closed_term L) ≤
  max (cardinal.sum (λ n : ulift.{u} (ℕ), #(L.functions n.down))) ω :=
calc #(closed_term L)
      ≤ #(W_type (term_β.{u u u} L)) :
    cardinal.mk_le_of_surjective closed_term_of_W_type_term_β_surjective
  ... ≤ max (#(Σ n : ulift.{u} ℕ, L.functions n.down)) ω :
    W_type.cardinal_mk_le_max_omega_of_fintype
  ... = max (cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down))) ω :
    by {rw cardinal.mk_sigma _}

lemma card_le_functions : #(term_model T) ≤
  max (cardinal.sum (λ n : ulift.{u} (ℕ), #(L.functions n.down))) ω :=
calc #(term_model T)
      ≤ #(closed_term L) : card_le_closed_term T
  ... ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down))) ω :
    cardinal.closed_term_le_functions

lemma card_le_cardinal {κ : cardinal.{u}} (hωκ : ω ≤ κ)
  (hκ : ∀ n : ulift.{u} ℕ, #(L.functions n.down) ≤ κ) : #(term_model T) ≤ κ :=
begin
  apply le_trans (card_le_functions T),
  apply max_le _ hωκ,
  apply le_trans (cardinal.sum_le_sup (λ n : ulift.{u} ℕ, #(L.functions n.down))),
  apply le_trans (cardinal.mul_le_max _ _),
  apply max_le _ hωκ,
  apply max_le,
  { simp [hωκ] },
  { rw cardinal.sup_le,
    exact hκ },
end

end term_model


namespace Language

variables (L) (α : Type u)

/-- The language with `α` indexing its constant symbols and nothing else -/
@[reducible] def of_constants : Language :=
{ functions := λ n, match n with | 0 := α | (n+1) := pempty end,
  relations := λ _, pempty }

lemma constants_of_constants : (of_constants α).constants = α := rfl

namespace of_constants

variables {L} {α}

def preimage (fs : finset $ sentence $ L.sum $ of_constants α) :
  finset $ sentence $ of_constants α :=
finset.preimage fs (on_sentence Lhom.sum_inr)
  (set.inj_on_of_injective (λ x y hxy, on_bounded_formula_inj Lhom.sum.is_injective_inr hxy) _)

-- /-- Making terms out of constant symbols in `fol.Language.of_constants` -/
-- def term (x : α) : bounded_term (of_constants α) 0 :=
-- bd_const x

@[reducible] protected def fun_map {S : Type*} (c : α → S) :
  Π {n : ℕ}, (of_constants α).functions n → dvector S n → S
| 0 f _ := c f
| (n+1) f _ := pempty.elim f


/-- To make a `fol.Structure` in `fol.Language.of_constants α`
  it suffices to give a map interpreting the constant symbols `α`-/
protected def Structure {S : Type*} (c : α → S) : Structure (of_constants α) :=
{ carrier := S,
  fun_map := λ _, of_constants.fun_map c,
  rel_map := λ n, pempty.elim }

variables {S : Structure L} (c : α → S)

/-- To make a `fol.Structure` in the `Lhom.sum` of a language and `fol.Language.of_constants α`,
  just give a structure in the first language and a map interpreting the constant symbols `α` -/
@[reducible] def sum_Structure : Structure (L.sum (of_constants α)) :=
{ carrier := S,
  fun_map := λ n f, sum.cases_on f (λ f, S.fun_map f) $ of_constants.fun_map c,
  rel_map := λ n r, sum.cases_on r (λ r, S.rel_map r) pempty.elim }

def sum_Structure_coe : S → sum_Structure c := λ x, x

/-- send dvectors on `S` to dvectors on `of_constants.sum_Structure c` -/
@[simp] def sum_Structure_dvector {n} (xs : dvector S n) :
  dvector (of_constants.sum_Structure c) n := dvector.map (sum_Structure_coe c) xs

variables {c} {T : Theory L}

lemma sum_Structure_on_term {n} :
  Π {l} (t : bounded_preterm L n l) {xs : dvector S n} {v : dvector S l},
  sum_Structure_coe c (realize_bounded_term xs t v) =
  realize_bounded_term (xs.map (sum_Structure_coe c))
    (on_bounded_term (Lhom.sum_inl : L →ᴸ L.sum (of_constants α)) t) (v.map (sum_Structure_coe c))
| _ &k           := by simp
| _ (bd_func f)  := by simp [sum_Structure_coe, Lhom.sum_inl]
| _ (bd_app t s) := by simp [realize_bounded_term, sum_Structure_on_term t,
  dvector.map, sum_Structure_on_term s]

lemma sum_Structure_on_formula :
  Π {n l} (f : bounded_preformula L n l) {xs : dvector S n} {v : dvector S l},
  realize_bounded_formula xs f v ↔
  realize_bounded_formula (xs.map (sum_Structure_coe c))
    (on_bounded_formula (Lhom.sum_inl : L →ᴸ L.sum (of_constants α)) f)
    (v.map (sum_Structure_coe c))
| _ _ bd_falsum        xs v := by simp
| _ _ (bd_equal t₁ t₂) xs v :=
begin
  simp only [← sum_Structure_on_term, realize_bounded_formula,
    sum_Structure_dvector, on_bounded_formula],
  simp [sum_Structure_coe],
end
| _ _ (bd_rel R)       xs v := by simp [Lhom.sum_inl, sum_Structure_coe]
| _ _ (bd_apprel f t)  xs v :=
by simp [realize_bounded_formula, sum_Structure_on_formula f,
    dvector.map, sum_Structure_on_term t]
| _ _ (bd_imp f₁ f₂)   xs v := by simp [sum_Structure_on_formula f₁, sum_Structure_on_formula f₂]
| _ _ (bd_all f)       xs v := by simpa [sum_Structure_on_formula f, sum_Structure_dvector]

lemma sum_Structure_on_sentence (f : sentence L) :
  S ⊨ f ↔ sum_Structure c ⊨ (on_sentence (Lhom.sum_inl : L →ᴸ L.sum (of_constants α)) f) :=
begin
  dsimp only [realize_sentence, on_sentence],
  rw @sum_Structure_on_formula _ _ _ c _ _ f,
  refl,
end

lemma sum_Structure_Theory_induced (hST : S ⊨ T) : of_constants.sum_Structure c ⊨
  Lhom.Theory_induced (Lhom.sum_inl : L →ᴸ L.sum (of_constants α)) T :=
begin
  intros ϕ hϕ,
  simp only [set.mem_image] at hϕ,
  obtain ⟨ ψ , hψT , hψ ⟩ := hϕ,
  subst hψ,
  rw ← sum_Structure_on_sentence,
  apply hST hψT,
end

end of_constants

end Language

variables (α : Type u)

/-- Takes a pair of terms `a b : α` and makes the sentence `a ≄ b` -/
@[simp] def distinct_constants_aux (x : α × α) : sentence (Language.of_constants α) :=
∼ (bd_const (prod.fst x) ≃ bd_const x.snd)

/-- The theory that says there are `α` many distinct constants -/
@[reducible] def distinct_constants : Theory (Language.of_constants α) :=
set.image (distinct_constants_aux _) { x : α × α | x.fst ≠ x.snd }

/-- The `(L + of_constants α)`-theory induced from `fol.distinct_constants` -/
def add_distinct_constants : Theory $ L.sum (Language.of_constants α) :=
Theory_induced Lhom.sum_inr $ distinct_constants _

variable {α}

lemma all_realize_sentence_distinct_constants (M : Structure _) (hM : M ⊨ distinct_constants α) :
  #α ≤ #M :=
begin
  rw all_realize_sentence_image at hM,
  have hf : function.injective (λ a, M.constants a),
  { intros x y hfxy,
    by_cases hxy : x = y, exact hxy,
    exfalso, apply hM ⟨x,y⟩ hxy,
    simp only [Structure.constants] at hfxy,
    simp [bd_const, hfxy] },
  apply cardinal.mk_le_of_injective hf,
end

lemma cardinal.finset_lt_infinite {fs : finset α} {β : Type u} (h : infinite β) : # fs < # β :=
calc # fs < ω : cardinal.finset_card_lt_omega _
    ... ≤ # β : cardinal.infinite_iff.1 h

lemma distinct_constants_aux_injective : function.injective (distinct_constants_aux α) :=
begin
  intros x y hxy,
  obtain ⟨ hfst, hsnd ⟩ := bounded_preformula.bd_equal.inj (bounded_preformula.bd_not.inj hxy),
  ext,
  { exact bounded_preterm.bd_func.inj hfst },
  { exact bounded_preterm.bd_func.inj hsnd },
end

open Language

/-- Collect all pairs `(a , b)` that appear as `a ≄ b` in a finset of sentences `fs` -/
def pairs_appearing_in (fs : finset (sentence $ of_constants α)) : finset (α × α) :=
finset.preimage fs (distinct_constants_aux α : α × α → sentence (of_constants α)) $
  set.inj_on_of_injective distinct_constants_aux_injective _

/-- Collect all `a` and `b` that appear in `a ≄ b` in a finset of sentences `fs` -/
def constants_appearing_in [decidable_eq α] (fs : finset (sentence $ of_constants α)) : finset α :=
(pairs_appearing_in fs).image prod.fst ∪ (pairs_appearing_in fs).image prod.snd

@[reducible] def union_add_distinct_constants (T : Theory L) (α : Type u) :=
(Theory_induced Lhom.sum_inl T : Theory $ L.sum (of_constants α)) ∪ add_distinct_constants α

lemma is_consistent_union_add_distinct_constants {T : Theory L} (α : Type u)
  {M : Structure L} (hMinf : infinite M) (hMT : M ⊨ T):
  is_consistent $ union_add_distinct_constants T α :=
begin
  have hM0 : nonempty M := infinite.nonempty _,
  rw compactness',
  intros fs hfsTκ,
  rw model_existence,
  classical,
  obtain ⟨Tfin, of_constants_fin, hfs, hTfin, h_of_constants_fin⟩ :=
    finset.subset_union_elim hfsTκ,
  classical,
  -- pick out constants that appear in f_of_constants
  set κfin : finset α := constants_appearing_in (of_constants.preimage of_constants_fin)
    with hκfin,
  let on_κfin : κfin ↪ M := classical.choice ((cardinal.le_def κfin M).1
    (le_of_lt $ cardinal.finset_lt_infinite hMinf)),
  -- send κfin to M injectively, map the rest to a point.
  set c : α → M :=
    λ x, dite (x ∈ κfin) (λ h, on_κfin ⟨x,h⟩) (λ _, classical.choice hM0) with hc,
  -- have hc : ∀ a b : κ.out, a ∈ κfin → b ∈ κfin → c a ≠ c b, sorry,
  refine ⟨ Language.of_constants.sum_Structure c , hM0 , _ ⟩,
  rw [← hfs, finset.coe_union, all_realize_sentence_union],
  split,
  { apply all_realize_sentence_of_subset _ hTfin,
    apply Language.of_constants.sum_Structure_Theory_induced hMT },
  { intros ϕ hϕ,
    have hϕ' := h_of_constants_fin hϕ,
    simp only [add_distinct_constants, set.mem_diff, on_sentence,
      set.mem_image, ne.def, prod.exists, not_exists, not_and] at hϕ',
    obtain ⟨⟨ψ, ⟨⟨ a, b, ⟨ hab, abrw ⟩⟩ , ψrw⟩⟩, _ ⟩ := hϕ',
    subst ψrw,
    subst abrw,
    simp only [← on_bounded_formula_not, on_bounded_formula, bd_const,
      on_bounded_term, realize_sentence_not, realize_sentence_equal,
      realize_closed_term, realize_bounded_term, Lhom.sum_inr,
      Language.of_constants.sum_Structure, Language.of_constants.fun_map,
      distinct_constants_aux] at hϕ ⊢,
    rw hc,
    have habκfin : a ∈ κfin ∧ b ∈ κfin,
    { rw hκfin,
      simp only [constants_appearing_in, pairs_appearing_in, bd_const,
        of_constants.preimage, ←on_bounded_formula_not, on_bounded_formula, Lhom.sum_inr,
        on_sentence, distinct_constants_aux, finset.mem_union, finset.mem_image,
        finset.mem_preimage, on_bounded_term, exists_prop, prod.exists,
        exists_and_distrib_right, exists_eq_right],
      exact ⟨or.inl ⟨ b , hϕ ⟩, or.inr ⟨ a , hϕ ⟩⟩ },
    simp only [dif_pos habκfin.1, dif_pos habκfin.2],
    intro hbot,
    have hbot' := (on_κfin.injective hbot),
    simp only [set.mem_set_of_eq] at hab,
      simp only [subtype.mk_eq_mk] at hbot',
  apply hab hbot' },
end

-- lemma cardinality_of_model_union_add_distinct_constants {T : Theory L} (α : Type u)
--   {M : Structure _} (hM0 : nonempty M) (hMT : M ⊨ union_add_distinct_constants T α) : #α ≤ #M :=
-- begin
--   rw all_realize_sentence_union at hMT,
--   have hMκ := Lhom.reduct_Theory_induced Lhom.sum.is_injective_inr hMT.2,
--   exact all_realize_sentence_distinct_constants _ hMκ,
-- end

-- /-- Theories with big models have arbitrarily large models (lower bound to cardinality) -/
-- lemma has_sized_model_of_has_infinite_model_lower {T : Theory L} {κ : cardinal}
-- (hκ : max (#(L.functions 0)) cardinal.omega ≤ κ) :
-- (∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ infinite M) →
-- ∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ κ ≤ #M :=
-- begin
--   rintro ⟨ M , hM0, hMT, hMinf ⟩,
--   set Tκ := union_add_distinct_constants T κ.out,
--   have hTκ_consis := is_consistent_union_add_distinct_constants κ.out hMinf hMT,
--   rw model_existence at hTκ_consis,
--   obtain ⟨ M , hM0, hMTκ ⟩ := hTκ_consis,
--   rw all_realize_sentence_union at hMTκ,
--   refine ⟨ ( M[[(Lhom.sum_inl : L →ᴸ L.sum (of_constants κ.out))]] ), (by simp [hM0]),
--     Lhom.reduct_Theory_induced Lhom.sum.is_injective_inl hMTκ.1 , _ ⟩,
--   have hMκ := Lhom.reduct_Theory_induced Lhom.sum.is_injective_inr hMTκ.2,
--   have hM := all_realize_sentence_distinct_constants _ hMκ,
--   simp only [reduct_coe, cardinal.mk_out κ] at *,
--   exact hM,
-- end

instance is_algebraic_henkin_language_chain_objects [is_algebraic L] {i} :
  is_algebraic (@henkin_language_chain_objects L i) :=
begin
  induction i with i hi,
  { dsimp only [henkin_language_chain_objects], cc },
  { dsimp only [henkin_language_chain_objects, henkin_language_step],
    split, intro n, apply hi.1 },
end

section le_cardinal

def henkin_language_functions_zero_fun :
  (henkin_language_functions L 0) → (L.functions 0 ⊕ bounded_formula L 1)
| (henkin_language_functions.inc f) := sum.inl f
| (henkin_language_functions.wit f) := sum.inr f


lemma henkin_language_functions_zero :
  _root_.equiv (henkin_language_functions L 0) (L.functions 0 ⊕ bounded_formula L 1) :=
{ to_fun := henkin_language_functions_zero_fun,
  inv_fun := λ f, sum.cases_on f henkin_language_functions.inc henkin_language_functions.wit,
  left_inv := λ f, match f with
    | (henkin_language_functions.inc f) := rfl
    | (henkin_language_functions.wit f) := rfl end,
  right_inv := λ f, sum.cases_on f (λ _, rfl) (λ _, rfl) }

lemma henkin_language_functions_succ {n : ℕ} :
  _root_.equiv (henkin_language_functions L (n+1)) (L.functions (n+1)) :=
{ to_fun := λ f, match f with
    | (henkin_language_functions.inc f) := f end,
  inv_fun := henkin_language_functions.inc,
  left_inv := λ f, match f with
    | (henkin_language_functions.inc f) := rfl end,
  right_inv := λ f, rfl }

lemma cardinal.sum_nat (f : ℕ → Type u) :
  cardinal.sum (λ (i : ℕ), # (f i)) = cardinal.sum (λ (i : ulift.{u} (ℕ)), #(f i.down)) :=
begin
  unfold cardinal.sum,
  apply cardinal.mk_congr,
  let F : (Σ (i : ℕ), quotient.out (# (f i))) → (Σ (i : ulift ℕ), quotient.out (# (f i.down))) :=
    λ ⟨ i , q ⟩, ⟨ ulift.up i , q ⟩,
  let G : (Σ (i : ulift ℕ), quotient.out (# (f i.down))) → (Σ (i : ℕ), quotient.out (# (f i))) :=
    λ ⟨ i , q ⟩, ⟨ i.down , q ⟩ ,
  refine ⟨ F , G , _ , _ ⟩,
  { rintros ⟨ i , q ⟩,
    refl },
  { rintros ⟨ i , q ⟩,
    cases i,
    refl },
end

variables {κ : cardinal.{u}} (hωκ : ω ≤ κ)

include hωκ

/- Can be more general than just for ℕ' -/
lemma colimit_language_le_cardinal {F : colimit.directed_diagram_language ℕ'}
  (n : ℕ) (h : ∀ i : ℕ, # ((F.obj i).functions n) ≤ κ) :
  # ((colimit.colimit_language F).functions n) ≤ κ :=
begin
  apply le_trans cardinal.mk_quotient_le,
  dsimp only [colimit.coproduct_of_directed_diagram],
  rw cardinal.mk_sigma,
  rw cardinal.sum_nat,
  apply le_trans (cardinal.sum_le_sup _),
  simp only [cardinal.mk_denumerable],
  apply le_trans (cardinal.mul_le_max _ _),
  apply max_le _ hωκ,
  apply max_le hωκ,
  rw cardinal.sup_le,
  intro i,
  cases i,
  apply h,
end


lemma bounded_formula_card_le [is_algebraic L] (hfunc : ∀ n, #(L.functions n) ≤ κ) (n : ℕ) :
  #(bounded_formula L n) ≤ κ :=
sorry

lemma henkin_language_chain_obj_card [is_algebraic L] {T : Theory L}
  (hconsis : is_consistent T)
  (hLκ : ∀ n, # (L.functions n) ≤ κ) (i : ℕ) :
  ∀ (n : ℕ), # (((@henkin_language_chain L).obj i).functions n) ≤ κ :=
begin
  unfold henkin_language_chain,
  induction i with i hi,
  { dsimp only [henkin_language_chain_objects],
    apply hLκ },
  { dsimp only [henkin_language_chain_objects] at ⊢ hi,
    intro n,
    induction n with n hn,
    {
      rw cardinal.mk_congr (@henkin_language_functions_zero (@henkin_language_chain_objects L i)),
      simp only [cardinal.mk_sum, cardinal.lift_id],
      apply le_trans (cardinal.add_le_max _ _),
      refine max_le (max_le (hi _) _) hωκ,
      apply bounded_formula_card_le hωκ hi, },
    { rw cardinal.mk_congr (@henkin_language_functions_succ (@henkin_language_chain_objects L i) n),
      apply hi } }
end

lemma henkin_language_card [is_algebraic L] {T : Theory L}
  {hconsis : is_consistent T}
  (hLκ : ∀ n, # (L.functions n) ≤ κ) (n : ℕ) :
  # ((@henkin_language _ _ hconsis).functions n) ≤ κ :=
begin
  dsimp [henkin_language, L_infty],
  apply colimit_language_le_cardinal hωκ,
  intro i,
  apply henkin_language_chain_obj_card hωκ hconsis hLκ,
end

end le_cardinal

/-- Upward Lowenheim Skolem.
  Theories with infinite models have arbitrarily large models,
  A stronger version of this should hold with
  (hκ : ∀ n, #(L.functions n) ≤ κ) replaced with (h0κ : #(L.functions 0) ≤ κ),
  but our proof uses `term_model`, which has cardinality that depends on all function symbols,
  the stronger result should use a model built with just the constant symbols of `L`.
  A generalization would replace [is_algebraic L] with some bound
-/
theorem has_sized_model_of_has_infinite_model [is_algebraic L] {T : Theory L} {κ : cardinal}
  (hκ : ∀ n, #(L.functions n) ≤ κ) (hωκ : ω ≤ κ) :
  (∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ infinite M) →
  ∃ M : Structure L, nonempty M ∧ M ⊨ T ∧ #M = κ :=
begin
  rintro ⟨ M , hM0, hMT, hMinf ⟩,
  -- we add κ many constants to the language and ensure they're all distinct in the thoery `Tκ`
  set Tκ := union_add_distinct_constants T κ.out,
  have hTκ_consis := is_consistent_union_add_distinct_constants κ.out hMinf hMT,
  -- we extend T to a complete theory with the witness property (a.k.a. it is henkin)
  set T2 := completion_of_henkinization hTκ_consis,
  -- this has a model, which we can reduce to the language L
  use (term_model T2)[[ henkin_language_over ]]
    [[(Lhom.sum_inl : L →ᴸ L.sum (of_constants κ.out))]],
  split,
  -- the reduction of a non-empty model is non-empty
  { apply fol.nonempty_term_model, exact completion_of_henkinization_is_henkin _, },
  split,
  -- this reduction models T
  { apply Lhom.reduct_Theory_induced Lhom.sum.is_injective_inl,
    have h := reduct_of_complete_henkinization_models_T hTκ_consis,
    simp only [all_realize_sentence_union] at h,
    exact h.1 },
  -- the model (and the reduction) are size κ
  { apply cardinal.partial_order.le_antisymm,
    -- ≤ because of the construction of `term_model`
    { apply term_model.card_le_cardinal T2 hωκ,
      -- Note: we use the term "bounded by" loosely
      -- `term_model` has size bounded by the terms of the language,
      -- which in turn is bounded by the function symbols in the language
      rintro ⟨ n ⟩,
      -- for an algebraic language, the henkinization is bounded by the number of function symbols
      apply henkin_language_card hωκ,
      { intro m,  -- the bound on function symbols
        simp only [Language.sum, cardinal.mk_sum, cardinal.lift_id],
        apply le_trans (cardinal.add_le_max _ _),
        apply max_le _ hωκ,
        apply max_le,
        { apply hκ },
        { cases m,
          { simp [of_constants] },
          { simp [of_constants] } } },
      { split, -- adding κ constant symbols to an `is_algebraic` language preserves `is_algebraic`
        intro m,
        dsimp [Language.sum],
        let f := _inst_1.1,
        simp only [sum.forall, forall_pempty, and_true],
        exact f m },
    },
    -- ≥ because we added κ constants and made sure they're distinct in any model of Tκ
    { have hle : #κ.out ≤ #((term_model T2)[[henkin_language_over]]
               [[(Lhom.sum_inr : _ →ᴸ L.sum (of_constants κ.out))]]),
      { apply all_realize_sentence_distinct_constants,
        apply Lhom.reduct_Theory_induced Lhom.sum.is_injective_inr,
        have h := reduct_of_complete_henkinization_models_T hTκ_consis,
        simp only [all_realize_sentence_union] at h,
        exact h.2 },
      { simp only [fol.Lhom.reduct_coe, cardinal.mk_out] at hle ⊢,
        exact hle } } },
end

/-- Vaught's test for showing a theory is complete.
  Like with Upward Lowenheim Skolem this could be strengthened
  with just asking for `#(L.constants) ≤ κ` and generalized
  by giving a bound on relations instead of using `[is_algebraic]`
-/
lemma is_complete'_of_only_infinite_of_categorical
  [is_algebraic L] {T : Theory L} (M : Structure L) (hM : M ⊨ T)
  (hinf : only_infinite T) {κ : cardinal}
  (hκ : ∀ n, #(L.functions n) ≤ κ) (hωκ : ω ≤ κ) (hcat : categorical κ T) :
is_complete' T :=
begin
  intro ϕ,
  by_contra hbot,
  simp only [not_or_distrib, not_ssatisfied] at hbot,
  obtain ⟨ ⟨ M , hM0 , hM ⟩ , ⟨ N , hN0 , hN ⟩ ⟩ := hbot,
  obtain ⟨ M' , hM'0 , hM' , hMcard ⟩ := has_sized_model_of_has_infinite_model hκ hωκ
    ⟨
      M , hM0 , hM ,
      hinf ⟨ M , all_realize_sentence_of_subset hM (set.subset_insert _ _) ⟩
    ⟩,
  obtain ⟨ N' , hN'0 , hN' , hNcard ⟩ := has_sized_model_of_has_infinite_model hκ hωκ
    ⟨
      N , hN0 , hN ,
      hinf ⟨ N , all_realize_sentence_of_subset hN (set.subset_insert _ _) ⟩
    ⟩,
  have hiso := hcat M' N'
    (all_realize_sentence_of_subset hM' (set.subset_insert _ _))
    (all_realize_sentence_of_subset hN' (set.subset_insert _ _)) hMcard hNcard,
  rw all_realize_sentence_insert at hM' hN',
  rw Language.equiv.realize_sentence _ (classical.choice hiso) at hN',
  exact hN'.1 hM'.1,
end

end fol

