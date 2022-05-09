import Rings.ToMathlib.fol
import set_theory.cardinal
import completeness
import language_extension
import data.W.cardinal
import Rings.ToMathlib.Lhom
import Rings.ToMathlib.completeness
import Rings.ToMathlib.cardinal

noncomputable theory

universes u v

open fol fol.Language fol.Lhom

namespace fol

open_locale cardinal fol
variables {L : Language.{u}}

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

lemma card_le_functions : #(term_model T) ≤
  max (cardinal.sum (λ n : ulift.{u} (ℕ), #(L.functions n.down))) ω :=
calc #(term_model T)
      ≤ #(closed_term L) : card_le_closed_term T
  ... ≤ max (cardinal.sum (λ n : ulift.{u} ℕ, #(L.functions n.down))) ω :
    cardinal.bounded_preterm_le_functions _

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
begin
  apply le_trans (cardinal.bounded_formula_le_functions L),
  apply max_le _ hωκ,
  apply le_trans (cardinal.sum_le_sup _),
  simp only [cardinal.mk_denumerable],
  apply le_trans (cardinal.mul_le_max _ _),
  apply max_le (max_le hωκ _) hωκ,
  rw cardinal.sup_le,
  intro i, cases i, apply hfunc,
end

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

