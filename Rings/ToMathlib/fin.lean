import data.fin

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

/-- converts an n-ary tuple to an n.succ-ary tuple -/
@[simp] def x_val {A : Type*} {n} (x : A) (val : fin n → A) :
  fin n.succ → A :=
@fin.cases n (λ _, A) x (λ i, val i)

end fin
