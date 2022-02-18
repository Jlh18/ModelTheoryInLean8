import fol
import Rings.Notation
import Rings.ToMathlib
import Rings.ToMathlib.fol
import Rings.ToMathlib.dvector
import Rings.ToMathlib.fin
import Rings.ToMathlib.list
import Rings.ToMathlib.nat
import data.polynomial.eval
import data.mv_polynomial

universe u

local infix ` ≃ `:64 := fol.bounded_preformula.bd_equal

namespace Rings

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/-- The constant symbols in RingSignature -/
inductive ring_consts : Type*
| zero : ring_consts
| one : ring_consts

/-- The unary function symbols in RingSignature-/
inductive ring_unaries : Type*
| neg : ring_unaries

/-- The binary function symbols in RingSignature-/
inductive ring_binaries : Type*
| add : ring_binaries
| mul : ring_binaries

/-- All function symbols in RingSignature-/
def ring_funcs : ℕ → Type*
| 0 := ring_consts
| 1 := ring_unaries
| 2 := ring_binaries
| (n + 3) := pempty

instance : inhabited ring_consts := ⟨ ring_consts.zero ⟩
instance : inhabited ring_unaries := ⟨ ring_unaries.neg ⟩
instance : inhabited ring_binaries := ⟨ ring_binaries.add ⟩

open fol

/-- The language of rings -/
def ring_signature : Language :=
(Language.mk) (ring_funcs) (λ n, pempty)

/-- To show two structures are equal it suffices that they are
    equal on carrier sets and heterogeneously equal on fun_map -/

lemma Structure.ext {A B : Structure ring_signature} :
  A.carrier = B.carrier → A.fun_map == B.fun_map → A = B :=
begin
  obtain ⟨ A , A_fun , A_rel ⟩ := A, obtain ⟨ B , B_fun , B_rel ⟩ := B,
  simp only,
  intros hcarrier hfun, subst hcarrier,
  refine ⟨ rfl, hfun, _ ⟩,
  rw heq_iff_eq,
  funext _ mem_empty,
  cases mem_empty,
end

/-- Shorter name for bounded_term ring_signature -/
@[reducible] def bounded_ring_term := bounded_term ring_signature

/-- Shorter name for bounded_preterm ring_signature n 0 -/
@[reducible] def bounded_ring_term' (n : ℕ) := bounded_preterm ring_signature n 0

/-- Shorter name for bounded_formula ring_signature -/
@[reducible] def bounded_ring_formula := bounded_formula ring_signature

/-- Shorter name for realize_bounded_term ring_signature -/
@[reducible] def realize_bounded_ring_term := @realize_bounded_term ring_signature

namespace ring_signature

/- The following instances allow us to use symbols 0 1 - + * ^ -/
/- to write terms in the language-/

@[reducible] instance bounded_ring_term_has_zero {n} :
  has_zero (bounded_ring_term n) := ⟨ bd_func ring_consts.zero ⟩
@[reducible] instance bounded_ring_term_has_zero' {n} :
  has_zero (bounded_ring_term' n) := ⟨ bd_func ring_consts.zero ⟩

@[reducible] instance bounded_ring_term_has_one {n} :
  has_one (bounded_ring_term n) := ⟨ bd_func ring_consts.one ⟩
@[reducible] instance bounded_ring_term_has_one' {n} :
  has_one (bounded_ring_term' n) := ⟨ bd_func ring_consts.one ⟩

@[reducible] instance bounded_ring_term_has_neg {n} : has_neg (bounded_ring_term n) :=
⟨ bd_app (bd_func ring_unaries.neg) ⟩
@[reducible] instance bounded_ring_term_has_neg' {n} : has_neg (bounded_ring_term' n) :=
⟨ bd_app (bd_func ring_unaries.neg) ⟩

@[reducible] instance bounded_ring_term_has_add {n} : has_add (bounded_ring_term n) :=
⟨ λ x, bd_app (bd_app (bd_func ring_binaries.add) x) ⟩
@[reducible] instance bounded_ring_term_has_add' {n} : has_add (bounded_ring_term'  n) :=
⟨ λ x, bd_app (bd_app (bd_func ring_binaries.add) x) ⟩

@[reducible] instance bounded_ring_term_has_mul {n} : has_mul (bounded_ring_term n) :=
⟨ λ x, bd_app (bd_app (bd_func ring_binaries.mul) x) ⟩
@[reducible] instance bounded_ring_term_has_mul' {n} : has_mul (bounded_ring_term' n) :=
⟨ λ x, bd_app (bd_app (bd_func ring_binaries.mul) x) ⟩

@[reducible] instance bounded_ring_term_has_pow {n} : has_pow (bounded_ring_term n) ℕ :=
⟨ λ t n, npow_rec n t ⟩

@[simp] lemma pow_zero {n} (t : bounded_ring_term n) : t ^ 0 = 1 := rfl
@[simp] lemma pow_succ {n m} (t : bounded_ring_term m) :
  t ^ (n + 1) = t * t ^ n := rfl

/-
-- variables x0 , x1 in the signature
-- (they are only variables in bounded terms that have up to n + 1, n + 2 variables)
example {n} : bounded_term ring_signature (n + 1) := x_ 0
-- for example {n} : bounded_term ring_signature n := x_ 0 doesn't work
-- since fin n doesn't have an instance of 0 in general (when n = 0)
example {n} : bounded_term ring_signature (n + 2) := x_ 1
-- actually example {n} : bounded_term ring_signature (n + 1) := x_ 1 also works because
-- fin (n + 1) is implemented mod (n + 1), in particular 1 = 0 ∈ fin 1
-- but let's avoid that

-- neg x
example {n} : bounded_ring_term (n + 1) := - (x_ 0)
example {n} : bounded_ring_term (n + 1) := (x_ 0) + 1
example {n} : bounded_ring_term (n + 2):= (- x_ 0) * x_ 1
example {n} : bounded_ring_term (n + 1) := x_ 0 + x_ 0
-/

/-- Part of the definition of ring_term_rec -/
@[simp] def ring_func_rec {n} {C : bounded_term ring_signature n → Sort*}
  (cvar : Π (k : fin n), C (x_ k))
  (c0 : C 0) (c1 : C 1)
  (cneg : Π {t}, C t → C (- t))
  (cadd : Π {s t}, C s → C t → C (s + t)) (cmul : Π {s t}, C s → C t → C (s * t)) :
  Π {l : ℕ} (f : ring_signature.functions l) (ts : dvector (bounded_term ring_signature n) l),
  (Π (t : bounded_ring_term n), dvector.pmem t ts → C t)
  → C (bd_apps (bd_func f) ts)
| 0 (ring_consts.zero) ([]) h := c0
| 0 (ring_consts.one) ([]) h := c1
| 1 (ring_unaries.neg) ([t]) h := cneg (h t (psum.inl rfl))
| 2 (ring_binaries.add) ([s,t]) h := cadd (h s (psum.inl rfl)) (h t (psum.inr (psum.inl rfl)))
| 2 (ring_binaries.mul) ([s,t]) h := cmul (h s (psum.inl rfl)) (h t (psum.inr (psum.inl rfl)))
| (n + 3) f ts h := pempty.elim f

/-- An interface for mapping out of bounded_ring_term n (basically bounded_term.rec) -/
def ring_term_rec {n : ℕ} {C : bounded_ring_term n → Sort*}
  (cvar : Π (k : fin n), C (x_ k))
  (c0 : C 0) (c1 : C 1)
  (cneg : Π {t}, C t → C (- t))
  (cadd : Π {s t}, C s → C t → C (s + t)) (cmul : Π {s t}, C s → C t → C (s * t))
  : Π (t : bounded_ring_term n), C t :=
@bounded_term.rec ring_signature n C
(λ k, cvar k)
(λ l, ring_func_rec cvar c0 c1 @cneg @cadd @cmul)

-- def ring_term_ind {n : ℕ} {C : bounded_ring_term n → Prop}
--   (cvar : Π (k : fin n), C (x_ k))
--   (c0 : C 0) (c1 : C 1)
--   (cneg : Π {t}, C t → C (- t))
--   (cadd : Π {s t}, C s → C t → C (s + t)) (cmul : Π {s t}, C s → C t → C (s * t))
--   : Π (t : bounded_ring_term n), C t :=
-- @bounded_term.rec ring_signature n C
-- (λ k, cvar k)
-- (λ l, ring_func_rec cvar c0 c1 @cneg @cadd @cmul)

/- Sentences for the theory of rings: commutative group under addition -/

/-- Assosiativity of addition -/
def add_assoc : sentence ring_signature :=
  ∀' ∀' ∀' ( (x_ 0 + x_ 1) + x_ 2 ≃ x_ 0 + (x_ 1 + x_ 2) )

/-- Identity for addition -/
def add_id : sentence ring_signature := ∀' ( x_ 0 + 0 ≃ x_ 0 )
-- def add_id : sentence ring_signature := ∀' (   &'0 r+ r0 ≃ &'0   ⊓   r0 r+ &'0 ≃ &'0   )

/-- Inverse for addition -/
def add_inv : sentence ring_signature := ∀' ( - x_ 0 + x_ 0 ≃ 0 )
-- def add_inv : sentence ring_signature := ∀' (  &'0 r+ r- &'0 ≃ r0  ⊓  r- &'0 r+ &'0 ≃ r0  )

/-- Commutativity of addition-/
def add_comm : sentence ring_signature := ∀' ∀' ( x_ 0 + x_ 1 ≃ x_ 1 + x_ 0 )

/- Sentences for theory of rings: commutative monoid under multiplication -/

/-- Associativity of multiplication -/
def mul_assoc : sentence ring_signature :=
∀' ∀' ∀' ( (x_ 0 * x_ 1) * x_ 2 ≃ x_ 0 * (x_ 1 * x_ 2) )

/-- Identity of multiplication -/
def mul_id : sentence ring_signature :=  ∀' ( x_ 0 * 1 ≃ x_ 0 )
-- def mul_id : sentence ring_signature :=  ∀' (   &'0 r× r1 ≃ &'0   )

/-- Commutativity of multiplication -/
def mul_comm : sentence ring_signature := ∀' ∀' ( x_ 0 * x_ 1 ≃ x_ 1 * x_ 0   )

/-- Distributibity -/
def add_mul : sentence ring_signature := ∀' ∀' ∀' ( (x_ 0 + x_ 1) * x_ 2 ≃ x_ 0 * x_ 2 + x_ 1 * x_ 2 )

/-- The theory of rings -/
def ring_theory : Theory ring_signature :=
{add_assoc, add_id, add_inv, add_comm, mul_assoc, mul_id, mul_comm, add_mul}

lemma add_assoc_in_ring_theory : add_assoc ∈ ring_theory :=
begin left, refl end

lemma add_id_in_ring_theory : add_id ∈ ring_theory :=
begin apply_rules [set.mem_insert, set.mem_insert_of_mem] end

lemma add_inv_in_ring_theory : add_inv ∈ ring_theory :=
begin apply_rules [set.mem_insert, set.mem_insert_of_mem] end

lemma add_comm_in_ring_theory : add_comm ∈ ring_theory :=
begin apply_rules [set.mem_insert, set.mem_insert_of_mem] end

lemma mul_assoc_in_ring_theory : mul_assoc ∈ ring_theory :=
begin apply_rules [set.mem_insert, set.mem_insert_of_mem] end

lemma mul_id_in_ring_theory : mul_id ∈ ring_theory :=
begin apply_rules [set.mem_insert, set.mem_insert_of_mem] end

lemma mul_comm_in_ring_theory : mul_comm ∈ ring_theory :=
begin apply_rules [set.mem_insert, set.mem_insert_of_mem] end

lemma add_mul_in_ring_theory : add_mul ∈ ring_theory :=
begin apply_rules [set.mem_insert, set.mem_insert_of_mem, set.mem_singleton] end

end ring_signature

namespace struc_to_ring_struc
-- We make any (type theoretic) structure A,0,1,-,+,* into a
-- (model theoretic) Structure in ring_signature

variable {A : Type*}

/-- Interpreting consant symbols from ring_signature -/
@[simp] def const_map [has_zero A] [has_one A] : ring_consts → (dvector A 0) → A
| ring_consts.zero _ := 0
| ring_consts.one  _ := 1

/-- Interpreting unary function symbols from ring_signature -/
@[simp] def unaries_map [has_neg A] : ring_unaries → (dvector A 1) → A
| ring_unaries.neg a := - (dvector.last a)

/-- Interpreting binary function symbols from ring_signature -/
@[simp] def binaries_map [has_add A] [has_mul A] : ring_binaries → (dvector A 2) → A
| ring_binaries.add   (a :: b) := a + dvector.last b
| ring_binaries.mul  (a :: b) := a * dvector.last b

variables [has_zero A] [has_one A] [has_neg A] [has_add A] [has_mul A]

/-- Interpreting all symbols from ring_signature-/
@[simp] def func_map : Π (n : ℕ), (ring_funcs n) → (dvector A n) → A
| 0       := const_map
| 1       := unaries_map
| 2       := binaries_map
| (n + 3) := pempty.elim

variable (A)

/-- Interpreting the symbols -/
@[reducible] def Structure : Structure ring_signature :=
Structure.mk A func_map (λ n, pempty.elim)

variable {A}

@[simp] lemma realize_zero {n} {vec : dvector A n} :
  @realize_bounded_ring_term (struc_to_ring_struc.Structure A) n vec 0
    (@bd_func ring_signature _ 0 ring_consts.zero) dvector.nil = 0 := rfl

lemma apps_zero {n} : Π {t_ : dvector (bounded_ring_term n) 0},
  bd_apps (@bd_func ring_signature _ 0 ring_consts.zero) t_ = 0
| [] := rfl

@[simp] lemma realize_one {n} {vec : dvector A n} :
  @realize_bounded_ring_term (Structure A) n vec 0
    (@bd_func ring_signature _ 0 ring_consts.one) dvector.nil = 1 := rfl

lemma realize_nat {as} : Π (n : ℕ),
@realize_bounded_term _ (Structure A) _ as _ (n : bounded_ring_term 0) dvector.nil
= n
| 0 := rfl
| (n+1) :=
by simpa only [const_map, realize_bounded_term,
      nat.cast_succ, realize_nat n]

lemma apps_one {n} : Π {t_ : dvector (bounded_ring_term n) 0},
  bd_apps (@bd_func ring_signature _ 0 ring_consts.one) t_ = 1
| [] := rfl

lemma app_neg {n} {t : bounded_ring_term n} :
  bd_app (@bd_func ring_signature _ 1 ring_unaries.neg) t = - t := rfl

lemma apps_neg {n} {t : bounded_ring_term n} :
   bd_apps (@bd_func ring_signature _ 1 ring_unaries.neg) ([t]) = - t := rfl

lemma app_add {n} {s t : bounded_ring_term n} :
  ((@bd_func ring_signature _ 2 ring_binaries.add).bd_app t).bd_app s = t + s := rfl

lemma apps_add {n} {s t : bounded_ring_term n} :
   bd_apps (@bd_func ring_signature _ 2 ring_binaries.add) ([s,t]) = s + t := rfl

lemma app_mul {n} {s t : bounded_ring_term n} :
  ((@bd_func ring_signature _ 2 ring_binaries.mul).bd_app t).bd_app s = t * s := rfl

lemma apps_mul {n} {s t : bounded_ring_term n} :
   bd_apps (@bd_func ring_signature _ 2 ring_binaries.mul) ([s,t]) = s * t := rfl

  -- lemma preterm_upper_bound {n} : bounded_preterm ring_signature n 3 → false := _

end struc_to_ring_struc

namespace comm_ring_to_model

variables (A : Type*) [comm_ring A]

lemma realize_ring_theory :
  (struc_to_ring_struc.Structure A) ⊨ ring_signature.ring_theory :=
begin
  intros ϕ h,
  repeat {cases h},
  { intros a b c, simp [add_assoc] },
  { intro a, simp }, -- add_zero
  { intro a, simp }, -- add_left_neg
  { intros a b, simp [add_comm] },
  { intros a b c, simp [mul_assoc] },
  { intro a, simp [mul_one] },
  { intros a b, simp [mul_comm] },
  { intros a b c, simp [add_mul] }
end

/-- Commutative rings model the theory of rings -/
def model : Model ring_signature.ring_theory :=
⟨ struc_to_ring_struc.Structure A ,  realize_ring_theory A ⟩

end comm_ring_to_model

namespace mv_polynomial

variable {σ : Type}

open ring_signature

/-- Terms in the ring_signature are multivariable polynomials over ℤ -/
noncomputable def term {n} :
  bounded_ring_term n → mv_polynomial (fin n) ℤ :=
@ring_term_rec n (λ _, mv_polynomial (fin n) ℤ)
  mv_polynomial.X 0 1
  (λ _ p, - p)
  (λ _ _ p q, p + q)
  (λ _ _ p q, p * q)

@[simp] lemma term_x {n} {k : fin n} : term (x_ k) = mv_polynomial.X k := rfl
@[simp] lemma term_zero {n} : @term n (bd_func ring_consts.zero) = 0 := rfl
@[simp] lemma term_one {n} : @term n (bd_func ring_consts.one) = 1 := rfl
@[simp] lemma term_neg {n} {t : bounded_ring_term n} :
  term (- t) = - term t := rfl
@[simp] lemma term_add {n} {s t : bounded_ring_term n} :
  term (s + t) = term s + term t := rfl
@[simp] lemma term_mul {n} {s t : bounded_ring_term n} :
  term (s * t) = term s * term t := rfl

variables {A : Type*} [comm_ring A]

@[reducible] private def AStruc := struc_to_ring_struc.Structure A

/-- terms realized at values in A are the corresponding polynomials -/
/- evaluated at those values -/
lemma realized_term_is_evaluated_poly {n} {as : dvector A n} :
Π (t : bounded_ring_term n),
  @realize_bounded_term _ AStruc _ as _ t dvector.nil
  = mv_polynomial.eval (dvector.fin_val as) (term t) :=
@ring_term_rec n (λ (t : bounded_ring_term n),
  @realize_bounded_term _ AStruc _ as _ t dvector.nil
    = mv_polynomial.eval (dvector.fin_val as) (term t))
  (begin intro k, simpa, end) -- variables
  (by simpa)
  (by simp)
  (by { intros t h, unfold_coes at h ⊢, simp [h] } ) -- neg
  (by { intros s t hs ht, unfold_coes at hs ht ⊢, simp [hs, ht] }) -- add
  (by { intros s t hs ht, unfold_coes at hs ht ⊢, simp [hs, ht] }) -- mul

end mv_polynomial

namespace polynomial

  variables {A : Type*} [comm_ring A]

  @[reducible] private def AStruc := struc_to_ring_struc.Structure A

  /-- Takes a term in variables x₀ ⋯ xₙ and values a₁ ⋯ aₙ : A and returns
    a polynomial in A[X] such that x₀ ↦ X and otherwise xₙ ↦ aₙ -/
  @[reducible] noncomputable def term_evaluated_at_coeffs {n} (as : dvector A n)
    (t : bounded_ring_term n.succ) : polynomial A :=
  let σ : fin n.succ → polynomial A :=
  @fin.cases n (λ _, polynomial A) polynomial.X (λ i, polynomial.C (as.nth' i)) in
  mv_polynomial.eval σ (mv_polynomial.term t)

  /-- Evaluating the polynomial term_evaluated_at_coeffs at a₀ : A produces the same
    term in A as realising the term at a₀ a₁ ⋯ aₙ -/
  lemma eval_term_evaluated_at_coeffs_eq_realize_bounded_term
    {n} {as : dvector A n} {x : A} (t : bounded_term ring_signature n.succ) :
    (polynomial.eval x (term_evaluated_at_coeffs as t)
      = @realize_bounded_term _ AStruc n.succ (x::as) _ t dvector.nil) :=
  begin
    rw [mv_polynomial.realized_term_is_evaluated_poly,
      dvector.fin_val_eq_x_val,
      mv_polynomial.eval_eq_poly_eval_mv_coeffs],
    simp only [dvector.fin_val, function.comp_app, fin.x_val,
      mv_polynomial.to_polynomial, term_evaluated_at_coeffs],
    unfold_coes,
    have hcoes : int.cast_ring_hom (polynomial A) =
      polynomial.C.comp (int.cast_ring_hom AStruc) := by simp,
    rw hcoes,
    simp,
  end

  lemma term_evaluated_at_coeffs_X {n} {as : dvector A n} :
    term_evaluated_at_coeffs as (x_ ⟨ 0 , nat.zero_lt_succ _ ⟩) = polynomial.X :=
  begin
    simp only [term_evaluated_at_coeffs],
    unfold_coes,
    simp,
  end


lemma term_evaluated_at_coeffs_coeff
  {n} {as : dvector A n} {k : fin n} :
    term_evaluated_at_coeffs as (x_ ⟨ k.1.succ , nat.succ_lt_succ k.2 ⟩)
    = polynomial.C (dvector.nth' as k) :=
  begin
    simp only [term_evaluated_at_coeffs],
    unfold_coes,
    simp,
  end

  lemma term_evaluated_at_coeffs_zero {n} {as : dvector A n} :
    term_evaluated_at_coeffs as (bd_func ring_consts.zero) = 0 :=
  begin
    simp only [term_evaluated_at_coeffs],
    unfold_coes,
    simp,
  end

  lemma term_evaluated_at_coeffs_one {n} {as : dvector A n} :
    term_evaluated_at_coeffs as (bd_func ring_consts.one) = 1 :=
  begin
    simp only [term_evaluated_at_coeffs],
    unfold_coes,
    simp,
  end

  lemma term_evaluated_at_coeffs_neg {n} {as : dvector A n} {t : bounded_ring_term n.succ} :
    term_evaluated_at_coeffs as (- t) = - term_evaluated_at_coeffs as t :=
  begin
    simp only [term_evaluated_at_coeffs],
    unfold_coes,
    simp,
  end

  lemma term_evaluated_at_coeffs_add {n} {as : dvector A n} {s t : bounded_ring_term n.succ} :
    term_evaluated_at_coeffs as (s + t) = term_evaluated_at_coeffs as s + term_evaluated_at_coeffs as t :=
  begin
    simp only [term_evaluated_at_coeffs],
    unfold_coes,
    simp,
  end

  lemma term_evaluated_at_coeffs_mul {n} {as : dvector A n} {s t : bounded_ring_term n.succ} :
    term_evaluated_at_coeffs as (s * t) = term_evaluated_at_coeffs as s * term_evaluated_at_coeffs as t :=
  begin
    simp only [term_evaluated_at_coeffs],
    unfold_coes,
    simp,
  end

  lemma term_evaluated_at_coeffs_pow {n : ℕ} : Π {m : ℕ} {as : dvector A n},
    polynomial.term_evaluated_at_coeffs as (x_ ⟨ 0 , nat.zero_lt_succ _ ⟩ ^ m)
    = polynomial.X ^ m
  | 0       _ :=
  by simp [npow_rec, ring_signature.pow_zero, term_evaluated_at_coeffs_one]
  | (m + 1) as :=
  by rw [ring_signature.pow_succ, term_evaluated_at_coeffs_mul,
      @term_evaluated_at_coeffs_pow m as, pow_succ, term_evaluated_at_coeffs_X]

  lemma term_evaluated_at_coeffs_monomial {n : ℕ} {m : ℕ} {as : dvector A n} {k : fin n} :
    polynomial.term_evaluated_at_coeffs as
      (x_ ⟨ k.1.succ , nat.succ_lt_succ k.2 ⟩ *
      npow_rec m x_ ⟨ 0 , nat.zero_lt_succ _ ⟩)
      = polynomial.monomial m (dvector.nth' as k) :=
  by rw [term_evaluated_at_coeffs_mul, term_evaluated_at_coeffs_coeff,
     term_evaluated_at_coeffs_pow, polynomial.monomial_eq_C_mul_X]

  lemma term_evaluated_at_coeffs_monomial'
    {n m k : ℕ} {as : dvector A n} (hk : k < n) :
    polynomial.term_evaluated_at_coeffs as
      (x_ ⟨ k.succ , nat.succ_lt_succ hk ⟩ *
      x_ ⟨ 0 , nat.zero_lt_succ _ ⟩ ^ m)
      = polynomial.monomial m (dvector.nth as k hk) :=
  begin
    rw term_evaluated_at_coeffs_mul,
    have h : term_evaluated_at_coeffs as x_⟨k.succ, _⟩
      = polynomial.C (dvector.nth as k hk),
    { unfold_coes,
      simp [term_evaluated_at_coeffs, dvector.nth'] },
    rw [h, term_evaluated_at_coeffs_pow, polynomial.monomial_eq_C_mul_X],
  end

  lemma lift_succ_remove_last {n : ℕ} :
  Π {t : bounded_ring_term (n + 1)} {as : dvector A (n + 1)},
    polynomial.term_evaluated_at_coeffs as (lift_succ t)
    = polynomial.term_evaluated_at_coeffs (dvector.remove_mth (n + 2) as) t :=
  @ring_signature.ring_term_rec (n + 1)
  (λ {t : bounded_ring_term (n + 1)}, Π {as : dvector A (n + 1)},
    polynomial.term_evaluated_at_coeffs as (lift_succ t)
    = polynomial.term_evaluated_at_coeffs (dvector.remove_mth (n + 2) as) t)
    (begin -- variables
      intros k as,
      rw lift_succ_x_k,
      cases k with k hk,
      cases k,
      { simp [term_evaluated_at_coeffs] },
      {
        simp only [mv_polynomial.eval_X, polynomial.C_inj,
          fin.coe_eq_cast_succ, fin.cases_succ', mv_polynomial.coe_mv_poly_X,
          fin.cast_succ_mk, mv_polynomial.term_x, term_evaluated_at_coeffs,
          dvector.nth'],
        rw dvector.nth_eq_succ_nth,
      },
    end)
    (by { intro, simp [lift_succ, term_evaluated_at_coeffs_zero] })
    (by { intro, simp [lift_succ, term_evaluated_at_coeffs_one] })
    (by { intros _ h _,
      simp [lift_succ, struc_to_ring_struc.app_neg,
        term_evaluated_at_coeffs_neg, h] })
    (by { intros s t hs ht as,
      simp only [lift_succ, struc_to_ring_struc.app_add,
        term_evaluated_at_coeffs_add, hs, ht] })
    (by { intros s t hs ht as,
      simp only [lift_succ, struc_to_ring_struc.app_mul,
        term_evaluated_at_coeffs_mul, hs, ht] })

end polynomial

namespace models_ring_theory_to_comm_ring

variable {M : Structure ring_signature}

def zero : ↥ M := @Structure.fun_map _ M 0 ring_consts.zero dvector.nil
def one : ↥ M := @Structure.fun_map _ M 0 ring_consts.one dvector.nil
def neg (a : M.carrier) : M.carrier := @Structure.fun_map _ M 1 ring_unaries.neg ([a])
def add (a b : M.carrier) : M.carrier := @Structure.fun_map _ M 2 ring_binaries.add ([a , b])
def mul (a b : M.carrier) : M.carrier := @Structure.fun_map _ M 2 ring_binaries.mul ([a , b])

instance : has_zero M := ⟨ zero ⟩
instance : has_one M := ⟨ one ⟩
instance : has_neg M := ⟨ neg ⟩
instance : has_add M := ⟨ add ⟩
instance : has_mul M := ⟨ mul ⟩

@[simp] lemma realize_zero {n} {vec : dvector M.carrier n} :
  realize_bounded_term vec (@bd_func ring_signature _ 0 ring_consts.zero) dvector.nil = 0 := rfl

@[simp] lemma realize_one {n} {vec : dvector M.carrier n} :
  realize_bounded_term vec (@bd_func ring_signature _ 0 ring_consts.one) dvector.nil = 1 := rfl

@[simp] lemma realize_neg {a : M.carrier} :
  @Structure.fun_map _ M 1 ring_unaries.neg ([a]) = - a := rfl

@[simp] lemma realize_add {a b : M.carrier} :
  @Structure.fun_map _ M 2 ring_binaries.add ([a , b]) = a + b := rfl

@[simp] lemma realize_mul {a b : M.carrier} :
  @Structure.fun_map _ M 2 ring_binaries.mul ([a , b]) = a * b := rfl

lemma realize_pow {a : M.carrier} : ∀ {m n} {vec : dvector M.carrier n},
realize_bounded_term (a :: vec) (npow_rec m (x_ 0)) dvector.nil
= npow_rec m a
| 0 n vec := rfl
| (m+1) n vec :=
by simp only [npow_rec, realize_bounded_term, realize_mul,
      fin.val_zero, dvector.nth, @realize_pow m]

lemma realize_nat {M : fol.Structure ring_signature} {as : dvector M 0} :
Π (n : ℕ),
@realize_bounded_term _ M _ as _ (n : bounded_ring_term 0) dvector.nil
= n
| 0 := rfl
| (n+1) :=
by simpa only [realize_bounded_term, nat.cast_succ, realize_nat n, realize_one]

variable (h : M ⊨ ring_signature.ring_theory)

include h

lemma add_assoc (a b c : M) : (a + b) + c = a + (b + c) :=
begin
  have hAssoc := h ring_signature.add_assoc_in_ring_theory,
  have habc := hAssoc c b a,
  simpa [habc]
end

lemma add_comm (a b : M) : a + b = b + a :=
begin
  have hId := h ring_signature.add_comm_in_ring_theory,
  have hab := hId b a,
  simpa [hab]
end

lemma add_zero (a : M) : a + 0 = a :=
begin
  have hId := h ring_signature.add_id_in_ring_theory,
  have ha := hId a,
  simpa [ha]
end

lemma zero_add (a : M) : 0 + a = a :=
begin
  rw add_comm h, apply add_zero h,
end

lemma left_neg (a : M) : - a + a = 0 :=
begin
  have hInv := h ring_signature.add_inv_in_ring_theory,
  have ha := hInv a,
  simpa [ha]
end

lemma mul_assoc (a b c : M) : (a * b) * c = a * (b * c) :=
begin
  have hAssoc := h ring_signature.mul_assoc_in_ring_theory,
  have habc := hAssoc c b a,
  simpa [habc]
end

lemma mul_comm (a b : M) : a * b = b * a :=
begin
  have hId := h ring_signature.mul_comm_in_ring_theory,
  have hab := hId b a,
  simpa [hab]
end

lemma mul_one (a : M) : a * 1 = a :=
begin
  have hId := h ring_signature.mul_id_in_ring_theory, have ha := hId a, simpa using ha
end

lemma one_mul (a : M) : 1 * a = a :=
by rw [mul_comm h, mul_one h]

lemma add_mul (a b c : M) : (a + b) * c = a * c + b * c :=
begin
  have hAM := h ring_signature.add_mul_in_ring_theory,
  have habc := hAM c b a,
  simpa [habc]
end

lemma mul_add (c a b : M) : c * (a + b) = c * a + c * b :=
begin
  rw [mul_comm h c (a + b), mul_comm h c a, mul_comm h c b],
  exact add_mul h a b c,
end

instance comm_ring : comm_ring M :=
{
  add            := add,
  add_assoc      := add_assoc h,
  zero           := zero,
  zero_add       := zero_add h,
  add_zero       := add_zero h,
  neg            := neg,
  add_left_neg   := left_neg h,
  add_comm       := add_comm h,
  mul            := mul,
  mul_assoc      := mul_assoc h,
  one            := one,
  one_mul        := one_mul h,
  mul_one        := mul_one h,
  left_distrib   := mul_add h,
  right_distrib  := add_mul h,
  mul_comm       := mul_comm h,
}

end models_ring_theory_to_comm_ring

lemma Structure_structure_eq_self (M : Structure ring_signature) :
  struc_to_ring_struc.Structure M = M :=
begin
  apply Structure.ext,
  { refl },
  { simp only [struc_to_ring_struc.Structure, heq_iff_eq],
    funext n, cases n,
    { funext c, cases c; { funext nil, cases nil, refl }},
    cases n,
    { funext neg, cases neg, funext y, cases y with _ _ y, cases y, refl },
    cases n,
    {
      funext addmul, cases addmul; { funext y, repeat {cases y with _ _ y}, refl },
    },
    { funext mem_empty, cases mem_empty }}
end

namespace instances

open ulift

def pℕ : Type* := ulift ℕ

def nat_ring_consts :
  ring_consts → dvector pℕ 0 → pℕ
| ring_consts.zero as := up 0
| ring_consts.one as := up 1

def nat_ring_structure_funcs :
  Π {n}, ring_signature.functions n → dvector pℕ n → pℕ
| 0 ring_consts.zero as := up 0
| 0 ring_consts.one as := up 1
| 1 ring_unaries.neg as := up 0
| 2 ring_binaries.add (dvector.cons a (dvector.cons b nil)) :=
  up ( down a + down b)
| 2 ring_binaries.mul (dvector.cons a (dvector.cons b nil)) :=
  up ( down a * down b)
| (n+3) f as := pempty.elim f

def nat_ring_structure : fol.Structure ring_signature :=
⟨ pℕ , λ _, nat_ring_structure_funcs , λ _, pempty.elim ⟩

lemma nat_ring_structure_realize_nat :
  Π (n : ℕ) {k : ℕ} (v : dvector nat_ring_structure k),
  realize_bounded_ring_term v
    (n : fol.bounded_preterm ring_signature k 0) dvector.nil = up n
| 0 _ _ := rfl
| (n+1) k v :=
begin
  have h := @nat_ring_structure_realize_nat n k v,
  rw [realize_bounded_ring_term] at h,
  simpa only [nat.cast_succ, realize_bounded_ring_term,
    fol.realize_bounded_term, h],
end

lemma nat_cast_bd_ring_term_inj {k n m : ℕ} :
  (n : fol.bounded_preterm ring_signature.{u} k 0) = m → n = m :=
begin
  let v : dvector nat_ring_structure k := dvector.of_fn (λ i, 0),
  intro hnm,
  rw [← down_up n, ← down_up m, ← nat_ring_structure_realize_nat n v,
    ← nat_ring_structure_realize_nat m v],
  apply congr_arg down.{u},
  exact @congr_arg (fol.bounded_preterm ring_signature k 0)
    nat_ring_structure n m
    (λ t : fol.bounded_preterm ring_signature k 0,
      realize_bounded_ring_term v t dvector.nil) hnm,
end

end instances

end Rings

namespace realize_ring_term

open Rings fol


variables
  {A : Type*} [comm_ring A]
  {c : ℕ} (xs : dvector (struc_to_ring_struc.Structure A) c)

@[simp] lemma list_sumr :
  Π {l : list (bounded_ring_term c)},
  realize_bounded_term xs (list.sumr l) dvector.nil
  =
  list.sumr (list.map (λ t, realize_bounded_term xs t dvector.nil) l)
| list.nil := by simp
| (list.cons t ts) :=
begin
  simp only [list.map, models_ring_theory_to_comm_ring.realize_add,
    list.sumr, realize_bounded_term],
  simp only [struc_to_ring_struc.func_map, dvector.last,
    struc_to_ring_struc.binaries_map, add_right_inj, dvector.nth],
  rw list_sumr,
end

def add_zero_hom :
  add_zero_hom (bounded_ring_term c) A :=
⟨ λ t, realize_bounded_term xs t dvector.nil ,
  models_ring_theory_to_comm_ring.realize_zero ,
  λ t s, models_ring_theory_to_comm_ring.realize_add ⟩

lemma sumr
  {ts : list (bounded_ring_term c)} :
  realize_bounded_term xs (ts).sumr dvector.nil
  =
  (list.map (add_zero_hom xs).to_fun ts).sumr :=
begin
  rw ← list.add_zero_hom_sumr (add_zero_hom xs) ts,
  refl,
end

lemma nat_non_comm_prod :
  Π (n : ℕ) (ts : fin n → bounded_ring_term c),
  realize_bounded_term xs (nat.non_comm_prod _ ts) dvector.nil
  =
  nat.non_comm_prod n (λ i, realize_bounded_term xs (ts i) dvector.nil)
| nat.zero ts :=
begin
  simp only [nat.non_comm_prod],
  refl,
end
| (nat.succ n) ts :=
begin
  simp only [nat.non_comm_prod, struc_to_ring_struc.func_map,
    dvector.last, struc_to_ring_struc.binaries_map, realize_bounded_term,
    dvector.nth],
  rw nat_non_comm_prod n,
end

lemma pow (t : bounded_ring_term c) : Π (n : ℕ),
  realize_bounded_term xs (npow_rec n t) dvector.nil
  =
  (realize_bounded_term xs t dvector.nil) ^ n
| nat.zero := by simpa
| (nat.succ n) := by simp [npow_rec, pow n, pow_succ]

end realize_ring_term
