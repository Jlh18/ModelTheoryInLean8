import fol
import to_mathlib
import Rings.Notation
import data.fin
import Rings.ToMathlib.fin
import Rings.ToMathlib.dvector

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
