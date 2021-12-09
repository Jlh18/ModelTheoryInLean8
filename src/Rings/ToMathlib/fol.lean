import fol
import to_mathlib
import Rings.Notation
import data.fin
import Rings.ToMathlib.fin

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
@[simp] def bd_exs' {L : Language} : Π k n : ℕ, bounded_formula L (n + k) → bounded_formula L n
| 0 n         f := f
| (k+1) n     f := bd_exs' k n (∃' f)

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



end fol


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
