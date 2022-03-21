import fol
import to_mathlib
import Rings.Notation
import data.fin.basic
import Rings.ToMathlib.fin
import Rings.ToMathlib.dvector
import data.set_like.basic
import data.set.lattice
import order.closure

namespace fol

/-- repeated ∧ for a FOL -/
def bd_big_and {L : Language} {d : ℕ} :
  Π (n : ℕ), (fin n → (bounded_formula L d)) → bounded_formula L d
| nat.zero fs := bd_not bd_falsum
| (nat.succ n) fs := bd_and (bd_big_and n (λ i, fs i)) (fs n)

/-- forward direction for following lemma -/
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

/-- realizing ∀ x_1 ... x_k, f is the same as realizing f for each (x_1 ... x_k) -/
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
@[simp] def bd_exs' {L : Language} (k n : ℕ) :
  bounded_formula L (n + k) → bounded_formula L n :=
λ f, bd_not (bd_alls' k n (bd_not f))

/-- realizing ∀ x_1 ... x_k, f is the same as realizing f for each (x_1 ... x_k) -/
lemma realize_bounded_formula_bd_exs' {L} {n} {k} {f : bounded_formula L (n + k)}
  {S : Structure L} (v : dvector S n) :
  (realize_bounded_formula v (bd_exs' k n f) dvector.nil)
  ↔
  (∃ xs : dvector S k, realize_bounded_formula (dvector.append xs v) f dvector.nil) :=
begin
  have hrw : (∀ (x : dvector ↥S k), ¬realize_bounded_formula (x.append v) f dvector.nil)
    ↔ (∀ (x : dvector ↥S k), realize_bounded_formula (x.append v) (bd_not f) dvector.nil),
  {simp only [realize_bounded_formula_not]},
  simp only [bd_exs'],
  rw [← not_iff_not, not_exists, hrw, realize_bounded_formula_not, not_not,
    realize_bounded_formula_bd_alls'],
end


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

lemma all_realize_sentence_union {L} (S : Structure L) (T₁ T₂ : Theory L) :
  S ⊨ T₁ ∪ T₂ ↔ S ⊨ T₁ ∧ S ⊨ T₂ :=
by simp only [all_realize_sentence, set.mem_union_eq,
  or_imp_distrib, forall_and_distrib]

lemma all_realize_sentence_range {L} {α}
  (S : Structure L) (fs : α → sentence L) :
S ⊨ set.range fs ↔ ∀ a : α, S ⊨ fs a :=
by simp only [all_realize_sentence, forall_apply_eq_imp_iff',
  set.mem_range, exists_imp_distrib]

lemma all_realize_sentence_image {L} {α}
  (S : Structure L) (fs : α → sentence L) (s : set α) :
S ⊨ set.image fs s ↔ ∀ a : α, a ∈ s → S ⊨ fs a :=
by simp [all_realize_sentence]

lemma all_realize_sentence_insert {L} {s : Theory L} (ϕ : sentence L)
  (S : Structure L) :
  S ⊨ set.insert ϕ s ↔ S ⊨ ϕ ∧ S ⊨ s :=
⟨ (λ h, ⟨ h (set.mem_insert _ _) , λ f hf, h (set.mem_insert_of_mem _ hf) ⟩)
  ,
  ( λ h f hf,
  begin
    cases hf with hf hf,
    { rw hf, exact h.1 },
    { exact h.2 hf },
  end ) ⟩



namespace bounded_preterm


-- I don't know if this is already in fol but
@[simp] def lift_succ {L} {n : ℕ} : Π {l},
  fol.bounded_preterm L n l → fol.bounded_preterm L n.succ l
| l (bd_var k) := x_ k
| l (bd_func f) := fol.bounded_preterm.bd_func f
| l (bd_app t s) :=
  fol.bounded_preterm.bd_app (@lift_succ l.succ t) (@lift_succ 0 s)

  -- instance has_lift_succ {L} {n : ℕ} : Π l,
  --   has_lift (fol.bounded_preterm L n l) (fol.bounded_preterm L n.succ l) :=
  --   λ l, ⟨ lift_succ ⟩

lemma lift_succ_x_k {L} {n : ℕ} {k : fin n} :
  lift_succ (x_ k : fol.bounded_preterm L n 0) = x_ k := rfl


lemma realize_lift_succ {L} {n : ℕ} {S : Structure L} :
  Π {l} {t : bounded_preterm L n l} {as : dvector S (n+1)} {bs},
  realize_bounded_term as (lift_succ t) bs
  = realize_bounded_term (dvector.remove_mth n as) t bs
| l (bd_var k) as bs :=
begin
  simp only [lift_succ, realize_bounded_term],
  rw dvector.nth_remove_mth_big_m _ k.2 k.2,
  simp only [fin.val_eq_coe, fin.coe_eq_cast_succ, fin.coe_cast_succ],
end
| l (bd_func f) as bs := by simp only [lift_succ, realize_bounded_term]
| l (bd_app t s) as bs :=
by simp only [lift_succ, realize_bounded_term, realize_lift_succ]



end bounded_preterm



variables {L : Language}

namespace bounded_preformula

lemma bd_not.inj {n} {f0 f1 : bounded_formula L n} :
  ∼ f0 = ∼ f1 → f0 = f1 := λ h, (bd_imp.inj h).1

lemma bd_notequal.inj {n} {t0 t1 s0 s1 : bounded_term L n} :
  t0 ≄ s0 = t1 ≄ s1 → t0 = t1 ∧ s0 = s1 :=
bd_equal.inj ∘ bd_not.inj

end bounded_preformula


-- not to be confused with is_complete
/-- A theory is_complete' if it deduces any sentence or its complement -/
def is_complete' (T : Theory L) : Prop :=
∀ (ϕ : sentence L), T ⊨ ϕ ∨ T ⊨ ∼ ϕ

/-- A theory is_complete'' if deductions for the model transfer to deductions for the theory-/
def is_complete'' (T : Theory L) : Prop :=
∀ (M : Structure L) (hM : nonempty M) (ϕ : sentence L), M ⊨ T → M ⊨ ϕ → T ⊨ ϕ

/-- Note fewer assumptions than the if and only if -/
lemma is_complete''_to_is_complete' {T : Theory L} :
  is_complete' T → is_complete'' T :=
begin
  intros H M hM ϕ hMT hMϕ,
  cases H ϕ with hTϕ hTϕ,
  { exact hTϕ },
  {
    have hbot := hTϕ hM hMT,
    rw realize_sentence_not at hbot,
    exfalso,
    exact hbot hMϕ,
  },
end

/-- When T is satisfied by some model then two notions of complete coincide -/
lemma is_complete''_iff_is_complete' {T : Theory L} (M : Structure L)
  (hM : nonempty M) (hMT : M ⊨ T) :
  is_complete' T ↔ is_complete'' T :=
begin
  split,
  { exact is_complete''_to_is_complete' },
  {
    intros H ϕ,
    by_cases hMϕ : M ⊨ ϕ,
    { left, exact H M hM ϕ hMT hMϕ },
    {
      right,
      rw ← realize_sentence_not at hMϕ,
      exact H M hM _ hMT hMϕ
    },
  },
end


end fol

/- Copied from mathlib but renamed to fit original fol definitions
## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

namespace fol

namespace Language

/-- The empty language has no symbols. -/
def empty : Language := ⟨λ _, pempty, λ _, pempty⟩

instance : inhabited Language := ⟨empty⟩

variable (L : Language)

/-- A Language is relational when it has no function symbols. -/
class is_relational : Prop :=
(empty_functions : ∀ n, L.functions n → false)

/-- A Language is algebraic when it has no relation symbols. -/
class is_algebraic : Prop :=
(empty_relations : ∀ n, L.relations n → false)

variable {L}

instance is_relational_of_empty_functions {symb : ℕ → Type*} : is_relational ⟨λ _, pempty, symb⟩ :=
⟨by { intro n, apply pempty.elim }⟩

instance is_algebraic_of_empty_relations {symb : ℕ → Type*}  : is_algebraic ⟨symb, λ _, pempty⟩ :=
⟨by { intro n, apply pempty.elim }⟩

instance is_relational_empty : is_relational (empty) := Language.is_relational_of_empty_functions
instance is_algebraic_empty : is_algebraic (empty) := Language.is_algebraic_of_empty_relations

variables (L) (M : Structure L) (N : Structure L)

/- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  Language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/

open Structure

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
protected structure hom :=
(to_fun : M → N)
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (M.fun_map f x)
  = N.fun_map f (dvector.map to_fun x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, M.rel_map r x
  → N.rel_map r (dvector.map to_fun x) . obviously)

localized "notation A ` →[`:25 L `] ` B := L.hom A B" in fol

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
protected structure embedding extends M ↪ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (M.fun_map f x)
  = N.fun_map f (dvector.map to_fun x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, N.rel_map r (dvector.map to_fun x)
  ↔ M.rel_map r x . obviously)

localized "notation A ` ↪[`:25 L `] ` B := L.embedding A B" in fol

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
protected structure equiv extends _root_.equiv M N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (M.fun_map f x)
  = N.fun_map f (dvector.map to_fun x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, N.rel_map r (dvector.map to_fun x)
  ↔ M.rel_map r x . obviously)

localized "notation A ` ≃[`:25 L `] ` B := L.equiv A B" in fol

variables {L M N} {P : Structure L} {Q : Structure L}

instance : has_coe_t L.constants M :=
⟨λ c, M.fun_map c dvector.nil⟩

lemma fun_map_eq_coe_constants {c : L.constants} {x : dvector M 0} :
  M.fun_map c x = c := by cases x; refl

namespace hom

@[simps] instance has_coe_to_fun : has_coe_to_fun (M →[L] N) (λ _, M → N) :=
⟨fol.Language.hom.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : M →[L] N} : f.to_fun = (f : M → N) := rfl

lemma coe_injective : @function.injective (M →[L] N) (M → N) coe_fn
| f g h := by {cases f, cases g, cases h, refl}

@[ext]
lemma ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) (x : dvector M n) :
  φ (M.fun_map f x) = N.fun_map f (dvector.map φ x) := φ.map_fun' f x

@[simp] lemma map_constants (φ : M →[L] N) (c : L.constants) : φ c = c :=
(φ.map_fun c dvector.nil).trans rfl

@[simp] lemma map_rel (φ : M →[L] N) {n : ℕ} (r : L.relations n) (x : dvector M n) :
  M.rel_map r x → N.rel_map r (dvector.map φ x) := φ.map_rel' r x

variables (L) (M)
/-- The identity map from a structure to itself -/
@[refl] def id : M →[L] M :=
{ to_fun := id,
  map_fun' := λ n f x, by rw dvector.map_id' x; refl,
  map_rel' := λ n r x hr, by rw dvector.map_id' x; exact hr}

variables {L} {M}

instance : inhabited (M →[L] M) := ⟨id L M⟩

@[simp] lemma id_apply (x : M) :
  id L M x = x := rfl

/-- Composition of first-order homomorphisms -/
@[trans] def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P :=
{ to_fun := hnp ∘ hmn,
  map_rel' := λ n r xs h,
  begin
    simp [dvector.map_comp],
    apply hnp.map_rel',
    simp only [dvector.map_map, dvector.map_id, dvector.map_comp],
    apply hmn.map_rel',
    simp only [dvector.map_id],
    exact h,
  end  }

@[simp] lemma comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end hom

namespace embedding

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ↪[L] N) (λ _, M → N) :=
⟨λ f, f.to_fun⟩

@[simp] lemma map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.functions n) (x : dvector M n) :
  φ (M.fun_map f x) = N.fun_map f (dvector.map φ x) := φ.map_fun' f x

@[simp] lemma map_constants (φ : M ↪[L] N) (c : L.constants) : φ c = c :=
(φ.map_fun c dvector.nil).trans rfl

@[simp] lemma map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.relations n) (x : dvector M n) :
  N.rel_map r (dvector.map φ x) ↔ M.rel_map r x := φ.map_rel' r x

/-- A first-order embedding is also a first-order homomorphism. -/
def to_hom (f : M ↪[L] N) : M →[L] N :=
{ to_fun := f }

@[simp]
lemma coe_to_hom {f : M ↪[L] N} : (f.to_hom : M → N) = f := rfl

lemma coe_injective : @function.injective (M ↪[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ↪[L] N) : function.injective f :=
f.to_embedding.injective

-- /-- The identity embedding from a structure to itself -/
-- @[refl] def refl (L : Language) (M : Structure L) : L.embedding M M :=
-- { to_embedding := function.embedding.refl M }

-- #check refl

variables {L} {M}

-- instance : inhabited (M ↪[L] M) := ⟨ refl L M ⟩

-- @[simp] lemma refl_apply (x : M) :
--   refl L M x = x := rfl

-- Composition of first-order embeddings
-- @[trans] def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P :=
-- { to_fun := hnp ∘ hmn,
--   inj' := hnp.injective.comp hmn.injective }

-- @[simp] lemma comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) :
--   g.comp f x = g (f x) := rfl

-- /-- Composition of first-order embeddings is associative. -/
-- lemma comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
--   (h.comp g).comp f = h.comp (g.comp f) := rfl

end embedding

namespace equiv

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm] def symm (f : M ≃[L] N) : N ≃[L] M :=
{ map_fun' := λ n f' x, begin
    simp only [equiv.to_fun_as_coe],
    rw [equiv.symm_apply_eq],
    refine eq.trans _ (f.map_fun' f' (dvector.map f.to_equiv.symm x)).symm,
    rw [equiv.to_fun_as_coe, ← dvector.map_comp, equiv.self_comp_symm,
      dvector.map_id'],
  end,
  map_rel' := λ n r x, begin
    simp only [equiv.to_fun_as_coe],
    refine (f.map_rel' r (dvector.map f.to_equiv.symm x)).symm.trans _,
    rw [equiv.to_fun_as_coe, ← dvector.map_comp, equiv.self_comp_symm,
      dvector.map_id'],
  end,
  .. f.to_equiv.symm }

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ≃[L] N) (λ _, M → N) :=
⟨λ f, f.to_fun⟩

@[simp] lemma map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.functions n) (x : dvector M n) :
  φ (M.fun_map f x) = N.fun_map f (dvector.map φ x) := φ.map_fun' f x

@[simp] lemma map_constants (φ : M ≃[L] N) (c : L.constants) : φ c = c :=
(φ.map_fun c dvector.nil).trans rfl

@[simp] lemma map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.relations n) (x : dvector M n) :
  N.rel_map r (dvector.map φ x) ↔ M.rel_map r x := φ.map_rel' r x

/-- A first-order equivalence is also a first-order embedding. -/
def to_embedding (f : M ≃[L] N) : M ↪[L] N :=
{ to_fun := f,
  inj' := f.to_equiv.injective }

/-- A first-order equivalence is also a first-order embedding. -/
def to_hom (f : M ≃[L] N) : M →[L] N :=
{ to_fun := f }

@[simp] lemma to_embedding_to_hom (f : M ≃[L] N) : f.to_embedding.to_hom = f.to_hom := rfl

@[simp]
lemma coe_to_hom {f : M ≃[L] N} : (f.to_hom : M → N) = (f : M → N) := rfl

@[simp] lemma coe_to_embedding (f : M ≃[L] N) : (f.to_embedding : M → N) = (f : M → N) := rfl

lemma coe_injective : @function.injective (M ≃[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ≃[L] N) : function.injective f := f.to_embedding.injective

-- variables (L) (M)
-- The identity equivalence from a structure to itself
-- @[refl] def refl : M ≃[L] M :=
-- { to_equiv := equiv.refl M }

-- variables {L} {M}

-- instance : inhabited (M ≃[L] M) := ⟨refl L M⟩

-- @[simp] lemma refl_apply (x : M) :
  -- refl L M x = x := rfl

-- Composition of first-order equivalences
-- @[trans] def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
-- { to_fun := hnp ∘ hmn,
  -- .. (hmn.to_equiv.trans hnp.to_equiv) }

-- @[simp] lemma comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) :
  -- g.comp f x = g (f x) := rfl

-- Composition of first-order homomorphisms is associative.
-- lemma comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
  -- (h.comp g).comp f = h.comp (g.comp f) := rfl

end equiv

section closed_under

open set

variables {n : ℕ} (f : L.functions n) (s : set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
def closed_under : Prop :=
∀ (x : dvector M n), (∀ i : fin n, dvector.nth' x i ∈ s) → M.fun_map f x ∈ s

variables {f} {s} {t : set M}

namespace closed_under

lemma inter (hs : closed_under f s) (ht : closed_under f t) :
  closed_under f (s ∩ t) :=
λ x h, mem_inter (hs x (λ i, mem_of_mem_inter_left (h i)))
  (ht x (λ i, mem_of_mem_inter_right (h i)))

lemma inf (hs : closed_under f s) (ht : closed_under f t) :
  closed_under f (s ⊓ t) := hs.inter ht

variables {S : set (set M)}

lemma Inf (hS : ∀ s, s ∈ S → closed_under f s) : closed_under f (Inf S) :=
λ x h s hs, hS s hs x (λ i, h i s hs)

end closed_under
end closed_under

variables (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
structure substructure :=
(carrier : set M)
(fun_mem : ∀{n}, ∀ (f : L.functions n), closed_under f carrier)

variables {L} {M}

namespace substructure

instance : set_like (L.substructure M) M :=
⟨substructure.carrier, λ p q h, by cases p; cases q; congr'⟩

/-- See Note [custom simps projection] -/
def simps.coe (S : L.substructure M) : set M := S
initialize_simps_projections substructure (carrier → coe)

@[simp]
lemma mem_carrier {s : L.substructure M} {x : M} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {S T : L.substructure M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
protected def copy (S : L.substructure M) (s : set M) (hs : s = S) : L.substructure M :=
{ carrier := s,
  fun_mem := λ n f, hs.symm ▸ (S.fun_mem f) }

variable {S : L.substructure M}

@[simp] lemma coe_copy {s : set M} (hs : s = S) :
  (S.copy s hs : set M) = s := rfl

lemma copy_eq {s : set M} (hs : s = S) : S.copy s hs = S :=
set_like.coe_injective hs

lemma constants_mem {c : L.constants} : ↑c ∈ S :=
mem_carrier.2 (S.fun_mem c _ fin.elim0)

/-- The substructure `M` of the structure `M`. -/
instance : has_top (L.substructure M) :=
⟨{ carrier := set.univ,
   fun_mem := λ n f x h, set.mem_univ _ }⟩

instance : inhabited (L.substructure M) := ⟨⊤⟩

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : L.substructure M) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : L.substructure M) : set M) = set.univ := rfl

/-- The inf of two substructures is their intersection. -/
instance : has_inf (L.substructure M) :=
⟨λ S₁ S₂,
  { carrier := S₁ ∩ S₂,
    fun_mem := λ n f, (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
lemma coe_inf (p p' : L.substructure M) : ((p ⊓ p' : L.substructure M) : set M) = p ∩ p' := rfl

@[simp]
lemma mem_inf {p p' : L.substructure M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

lemma set.Inter_pos {α} {p : Prop} {μ : p → set α} (hp : p) : (⋂h:p, μ h) = μ hp := infi_pos hp

lemma set.Inter_neg {α} {p : Prop} {μ : p → set α} (hp : ¬ p) : (⋂h:p, μ h) = set.univ := infi_neg hp

instance : has_Inf (L.substructure M) :=
⟨λ s, { carrier := ⋂ t ∈ s, ↑t,
        fun_mem := λ n f, closed_under.Inf begin
          rintro _ ⟨t, rfl⟩,
          simp only,
          by_cases h : t ∈ s,
          { rw [set.Inter_pos h],
            exact t.fun_mem f },
          { rw [set.Inter_neg h],
            exact λ _ _, set.mem_univ _ }
        end }⟩


@[simp, norm_cast]
lemma coe_Inf (S : set (L.substructure M)) :
  ((Inf S : L.substructure M) : set M) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (L.substructure M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
  set.mem_Inter₂

lemma mem_infi {ι : Sort*} {S : ι → L.substructure M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → L.substructure M} : (↑(⨅ i, S i) : set M) = ⋂ i, S i :=
by simp only [infi, coe_Inf, set.bInter_range]

/-- Substructures of a structure form a complete lattice. -/
instance : complete_lattice (L.substructure M) :=
{ le           := (≤),
  lt           := (<),
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (L.substructure M) $ λ s,
    is_glb.of_image (λ S T,
      show (S : set M) ≤ T ↔ S ≤ T, from set_like.coe_subset_coe) is_glb_binfi }

variable (L)

/-- The `L.substructure` generated by a set. -/
def closure : lower_adjoint (coe : L.substructure M → set M) := ⟨λ s, Inf {S | s ⊆ S},
  λ s S, ⟨set.subset.trans (λ x hx, mem_Inf.2 $ λ S hS, hS hx), λ h, Inf_le h⟩⟩

variables {L} {s : set M}

lemma mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.substructure M, s ⊆ S → x ∈ S :=
mem_Inf

/-- The substructure generated by a set includes the set. -/
@[simp]
lemma subset_closure : s ⊆ closure L s := (closure L).le_closure s

@[simp]
lemma closed (S : L.substructure M) : (closure L).closed (S : set M) :=
_root_.congr rfl ((closure L).eq_of_le set.subset.rfl (λ x xS, mem_closure.2 (λ T hT, hT xS)))

open set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
lemma closure_le : closure L s ≤ S ↔ s ⊆ S := (closure L).closure_le_closed_iff_le s S.closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
lemma closure_mono ⦃s t : set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
(closure L).monotone h

lemma closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
(closure L).eq_of_le h₁ h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator] lemma closure_induction
  {p : M → Prop} {x} (h : x ∈ closure L s)
  (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p)) : p x :=
(@closure_le L M ⟨set_of p, λ n, Hfun⟩ _).2 Hs h

-- (@closure_le L M _ ⟨set_of p, λ n, Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_eliminator] lemma dense_induction {p : M → Prop} (x : M) {s : set M}
  (hs : closure L s = ⊤) (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p)) : p x :=
have ∀ x ∈ closure L s, p x, from λ x hx, closure_induction hx Hs (λ n, Hfun),
by simpa [hs] using this x

variables (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure L M) coe :=
{ choice := λ s _, closure L s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variables {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp] lemma closure_eq : closure L (S : set M) = S := (substructure.gi L M).l_u_eq S

@[simp] lemma closure_empty : closure L (∅ : set M) = ⊥ :=
(substructure.gi L M).gc.l_bot

@[simp] lemma closure_univ : closure L (set.univ : set M) = ⊤ :=
@coe_top L M ▸ closure_eq ⊤

lemma closure_union (s t : set M) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
(substructure.gi L M).gc.l_sup

lemma closure_Union {ι} (s : ι → set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
(substructure.gi L M).gc.l_supr

end substructure

namespace hom

open substructure

-- /-- The substructure of elements `x : M` such that `f x = g x` -/
-- def eq_locus (f g : M →[L] N) : substructure L M :=
-- { carrier := {x : M | f x = g x},
--   fun_mem := λ n fn x hx,
--   begin
--     have h0 : f (M.fun_map fn x) = g (M.fun_map fn x),
--     {
--       simp only [dvector.map_comp, fol.Language.hom.map_fun],
--       rw dvector.map_id,
--       congr1,
--       rw dvector.ext,
--       intro i,
--       simp only [dvector.nth', dvector.map_nth],
--       apply hx,
--     },
--     exact h0,
--   end}

-- /-- If two `L.hom`s are equal on a set, then they are equal on its substructure closure. -/
-- lemma eq_on_closure {f g : M →[L] N} {s : set M} (h : set.eq_on f g s) :
--   set.eq_on f g (closure L s) :=
-- show substructure.closure L s ≤ f.eq_locus g, from closure_le.2 h

-- lemma eq_of_eq_on_top {f g : M →[L] N} (h : set.eq_on f g (⊤ : substructure L M)) :
--   f = g :=
-- ext $ λ x, h trivial

-- variable {s : set M}

-- lemma eq_of_eq_on_dense (hs : substructure.closure L s = ⊤) {f g : M →[L] N} (h : s.eq_on f g) :
--   f = g :=
-- eq_of_eq_on_top $ hs ▸ eq_on_closure h

end hom

namespace equiv

lemma realize_bounded_term {M N : Structure L} (equiv : M ≃[L] N) {n l} (v : dvector M n)
  (t : bounded_preterm L n l) (xs : dvector M l) :
  realize_bounded_term (dvector.map equiv v) t (dvector.map equiv xs) =
    equiv (realize_bounded_term v t xs) :=
begin
  induction t with _ _ _ _ t s ht hs,
  { simp only [realize_bounded_term, dvector.map_nth] },
  { simp only [realize_bounded_term, dvector.map_nth, map_fun] },
  { specialize hs dvector.nil, rw dvector.map at hs,
    simp only [realize_bounded_term, hs, dvector.map],
    apply ht (xs.cons $ realize_bounded_term v s dvector.nil) }
end

/-- Isomorphic structures realize the same formulas -/
lemma realize_bounded_formula {M N : Structure L} (g : M ≃[L] N) {n l} (v : dvector M n)
  (ϕ : bounded_preformula L n l) (xs : dvector M l) :
  (realize_bounded_formula (v.map g) ϕ (xs.map g)
  ↔ realize_bounded_formula v ϕ xs) :=
begin
  induction ϕ with _ _ _ _ _ _ _ _ _ s t hs _ ϕ ψ hϕ hψ _ _ hϕ,
  { refl },
  { simp only [realize_bounded_formula, realize_bounded_term, g.injective.eq_iff] },
  { simp only [realize_bounded_formula, map_rel] },
  { specialize hs v (xs.cons $ fol.realize_bounded_term v t dvector.nil),
    simp only [dvector.map, ← equiv.realize_bounded_term g v t dvector.nil] at hs,
    rw [realize_bounded_formula, hs, realize_bounded_formula] },
  { simp [realize_bounded_formula, hϕ, hψ] },
  { split,
    { intros H _, rw ← hϕ, apply H },
    { intros H x, specialize hϕ (v.cons $ g.inv_fun x) xs,
      have fun_inv : g (g.to_equiv.inv_fun x) = x, {unfold_coes, simp},
      simp only [dvector.map, fun_inv] at hϕ, rw hϕ, apply H } }
end

/-- Isomorphic structures realize the same sentences -/
lemma realize_sentence {M N : Structure L} (ϕ : sentence L) (g : M ≃[L] N) : (N ⊨ ϕ ↔ M ⊨ ϕ) :=
by {convert realize_bounded_formula g dvector.nil ϕ dvector.nil }

/-- Isomorphic structures model the same theories -/
lemma all_realize_sentence (M N : Structure L) (T : Theory L) :
(M ≃[L] N) → (M ⊨ T ↔ N ⊨ T) :=
λ H, by simp only [all_realize_sentence, Language.equiv.realize_sentence _ H]

end equiv
end Language

section only_infinite

open_locale cardinal

variable {L : Language}

/-- Theory T only has infinitely large models -/
def only_infinite (T : Theory L) : Prop :=
∀ (M : Model T), infinite M.1

lemma only_infinite_subset {T₀ T₁ : Theory L} (hsub : T₀ ⊆ T₁) :
only_infinite T₀ → only_infinite T₁ :=
λ hinf M, hinf ⟨ M.1 , all_realize_sentence_of_subset M.2 hsub ⟩

end only_infinite

section categorical

variable {L : Language}

open_locale cardinal fol

/-- Categoricity states any two models of the same cardinality κ are isomorphic -/
def categorical (κ : cardinal) (T : Theory L) :=
∀ (M N : Structure L) (hM : M ⊨ T) (hN : N ⊨ T), #M = κ → #N = κ → nonempty (M ≃[L] N)

/-- The theory doesn't deduce ϕ ↔ there is a model satisfying its negation -/
lemma not_ssatisfied {T : Theory L} {ϕ : sentence L} :
¬ T ⊨ ϕ ↔ ∃ M : Structure L, nonempty M ∧ M ⊨ set.insert (∼ ϕ) T :=
by { simp only [ssatisfied, not_forall, not_imp, all_realize_sentence_insert,
       realize_sentence_not], tauto }

end categorical

end fol
