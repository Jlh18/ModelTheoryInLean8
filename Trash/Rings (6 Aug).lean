import tactic
import fol
import Rings.Notation
import Rings.ToMathlib
import data.polynomial.eval
import data.mv_polynomial

universe u

namespace Rings

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/-- The constant symbols in RingSignature -/
inductive RingConsts : Type u
| zero : RingConsts
| one : RingConsts

/-- The unary function symbols in RingSignature-/
inductive RingUnaries : Type u
| neg : RingUnaries

/-- The binary function symbols in RingSignature-/
inductive RingBinaries : Type u
| add : RingBinaries
| mul : RingBinaries

/-- All function symbols in RingSignature-/
def RingFuncs : ℕ → Type u
| 0 := RingConsts
| 1 := RingUnaries
| 2 := RingBinaries
| (n + 3) := pempty

instance : inhabited RingConsts := ⟨ RingConsts.zero ⟩
instance : inhabited RingUnaries := ⟨ RingUnaries.neg ⟩
instance : inhabited RingBinaries := ⟨ RingBinaries.add ⟩

open fol

/-- The language of rings -/
def RingSignature : Language :=
(Language.mk) (RingFuncs) (λ n, pempty)

@[reducible] private def bdt (n : ℕ) := bounded_term RingSignature n
@[reducible] private def bdt' (n : ℕ) := bounded_preterm RingSignature n 0
-- I shouldn't need to make a duplicate since they are definitionally equal

/- The following instances allow us to use symbols 0 1 - + * to write down terms in the language-/
@[simp] def zero {n} : bdt n := bd_const RingConsts.zero

@[reducible] instance RingBDTHasZero {n} : has_zero (bdt n) := ⟨ zero ⟩
@[reducible] instance RingBDTHasZero' {n} : has_zero (bdt' n) := ⟨ zero ⟩

@[simp] def one {n} : bdt n := bd_const RingConsts.one
@[reducible] instance RingBDTHasOne {n} : has_one (bdt n) := ⟨ one ⟩
@[reducible] instance RingBDTHasOne' {n} : has_one (bdt' n) := ⟨ one ⟩

@[simp] def neg {n} : bdt n → bdt n := bd_app (bd_func RingUnaries.neg)
@[reducible] instance RingBDTHasNeg {n} : has_neg (bdt n) := ⟨ neg ⟩
@[reducible] instance RingBDTHasNeg' {n} : has_neg (bdt'  n) := ⟨ neg ⟩

@[simp] def add {n} (x : bdt n) : bdt n → bdt n :=
  bd_app (bd_app (bd_func RingBinaries.add) x)
@[reducible] instance RingBDTHasAdd {n} : has_add (bdt n) := ⟨ add ⟩
@[reducible] instance RingBDTHasAdd' {n} : has_add (bdt'  n) := ⟨ add ⟩

@[simp] def mul {n} (x : bdt n) : bdt n → bdt n :=
  bd_app (bd_app (bd_func RingBinaries.mul) x)
@[reducible] instance RingBDTHasMul {n} : has_mul (bdt n) := ⟨ mul ⟩
@[reducible] instance RingBDTHasMul' {n} : has_mul (bdt' n) := ⟨ mul ⟩

-- has_pow comes for free by having instances of mul and 1 (see ToMathlib) -- input x ^ n

@[simp] lemma pow_zero {n} (t : bounded_term RingSignature n) : t ^ 0 = 1 := rfl
@[simp] lemma pow_succ {n m} (t : bounded_term RingSignature m) : t ^ (n + 1) = t * t ^ n := rfl

-- with has_one and has_add you can write any natural and lean will know what term you mean
-- with has_neg you can write any integer etc.

/-
-- variables x0 , x1 in the signature
-- (they are only variables in bounded terms that have up to n + 1, n + 2 variables)
example {n} : bounded_term RingSignature (n + 1) := x_ 0
-- for example {n} : bounded_term RingSignature n := x_ 0 doesn't work
-- since fin n doesn't have an instance of 0 in general (when n = 0)
example {n} : bounded_term RingSignature (n + 2) := x_ 1
-- actually example {n} : bounded_term RingSignature (n + 1) := x_ 1 also works because
-- fin (n + 1) is implemented mod (n + 1), in particular 1 = 0 ∈ fin 1
-- but let's avoid that

-- neg x
example {n} : bounded_term RingSignature (n + 1) := - (x_ 0)
example {n} : bounded_term RingSignature (n + 1) := (x_ 0) + 1
example {n} : bounded_term RingSignature (n + 2):= (- x_ 0) * x_ 1
example {n} : bounded_term RingSignature (n + 1) := x_ 0 + x_ 0
-/

/-- Part of the definition of BdtRec -/
@[simp] def RingFuncRec {n} {C : bounded_term RingSignature n → Sort u}
  (cvar : Π (k : fin n), C (x_ k))
  (c0 : C 0) (c1 : C 1)
  (cneg : Π {t}, C t → C (- t))
  (cadd : Π {s t}, C s → C t → C (s + t)) (cmul : Π {s t}, C s → C t → C (s * t)) :
  Π {l : ℕ} (f : RingSignature.functions l) (ts : dvector (bounded_term RingSignature n) l),
  (Π (t : bounded_term RingSignature n), dvector.pmem t ts → C t)
  → C (bd_apps (bd_func f) ts)
| 0 (RingConsts.zero) ([]) h := c0
| 0 (RingConsts.one) ([]) h := c1
| 1 (RingUnaries.neg) ([t]) h := cneg (h t (psum.inl rfl))
| 2 (RingBinaries.add) ([s,t]) h := cadd (h s (psum.inl rfl)) (h t (psum.inr (psum.inl rfl)))
| 2 (RingBinaries.mul) ([s,t]) h := cmul (h s (psum.inl rfl)) (h t (psum.inr (psum.inl rfl)))
| (n + 3) f ts h := pempty.elim f

/-- An interface for mapping out of bounded_term RingSignature n (basically bounded_term.rec) -/
def RingTermRec {n : ℕ} {C : bounded_term RingSignature n → Sort u}
  (cvar : Π (k : fin n), C (x_ k))
  (c0 : C 0) (c1 : C 1)
  (cneg : Π {t}, C t → C (- t))
  (cadd : Π {s t}, C s → C t → C (s + t)) (cmul : Π {s t}, C s → C t → C (s * t))
  : Π (t : bounded_term RingSignature n), C t :=
@bounded_term.rec RingSignature n C
(λ k, cvar k)
(λ l, RingFuncRec cvar c0 c1 @cneg @cadd @cmul)

def RingTermInd {n : ℕ} {C : bounded_term RingSignature n → Prop}
  (cvar : Π (k : fin n), C (x_ k))
  (c0 : C 0) (c1 : C 1)
  (cneg : Π {t}, C t → C (- t))
  (cadd : Π {s t}, C s → C t → C (s + t)) (cmul : Π {s t}, C s → C t → C (s * t))
  : Π (t : bounded_term RingSignature n), C t :=
@bounded_term.rec RingSignature n C
(λ k, cvar k)
(λ l, RingFuncRec cvar c0 c1 @cneg @cadd @cmul)

/- Commutative group for additions axioms -/

/-- Assosiativity of addition -/
def AddAssoc : sentence RingSignature :=
  ∀' ∀' ∀' ( (x_ 0 + x_ 1) + x_ 2 ≃ x_ 0 + (x_ 1 + x_ 2) )

/-- Identity for addition -/
def AddId : sentence RingSignature := ∀' ( x_ 0 + 0 ≃ x_ 0 )
-- def AddId : sentence RingSignature := ∀' (   &'0 r+ r0 ≃ &'0   ⊓   r0 r+ &'0 ≃ &'0   )

/-- Inverse for addition -/
def AddInv : sentence RingSignature := ∀' ( - x_ 0 + x_ 0 ≃ 0 )
-- def AddInv : sentence RingSignature := ∀' (  &'0 r+ r- &'0 ≃ r0  ⊓  r- &'0 r+ &'0 ≃ r0  )

/-- Commutativity of addition-/
def AddComm : sentence RingSignature := ∀' ∀' ( x_ 0 + x_ 1 ≃ x_ 1 + x_ 0 )

/- Commutative monoid for multiplication axioms -/
/-- Associativity of multiplication -/
def MulAssoc : sentence RingSignature := ∀' ∀' ∀' ( (x_ 0 * x_ 1) * x_ 2 ≃ x_ 0 * (x_ 1 * x_ 2) )

/-- Identity of multiplication -/
def MulId : sentence RingSignature :=  ∀' ( x_ 0 * 1 ≃ x_ 0 )
-- def MulId : sentence RingSignature :=  ∀' (   &'0 r× r1 ≃ &'0   )

/-- Commutativity of multiplication -/
def MulComm : sentence RingSignature := ∀' ∀' ( x_ 0 * x_ 1 ≃ x_ 1 * x_ 0   )

/-- Distributibity -/
def AddMul : sentence RingSignature := ∀' ∀' ∀' ( (x_ 0 + x_ 1) * x_ 2 ≃ x_ 0 * x_ 2 + x_ 1 * x_ 2 )

/-- The theory of rings -/
def RingTheory : Theory RingSignature :=
{AddAssoc, AddId, AddInv, AddComm, MulAssoc, MulId, MulComm, AddMul}

lemma AddAssocInRingTheory : AddAssoc ∈ RingTheory :=
begin unfold RingTheory, left, refl end

lemma AddIdInRingTheory : AddId ∈ RingTheory :=
begin unfold RingTheory, iterate 1 {right}, left, refl end

lemma AddInvInRingTheory : AddInv ∈ RingTheory :=
begin unfold RingTheory, iterate 2 {right}, left, refl end

lemma AddCommInRingTheory : AddComm ∈ RingTheory :=
begin unfold RingTheory, iterate 3 {right}, left, refl end

lemma MulAssocInRingTheory : MulAssoc ∈ RingTheory :=
begin unfold RingTheory, iterate 4 {right}, left, refl end

lemma MulIdInRingTheory : MulId ∈ RingTheory :=
begin unfold RingTheory, iterate 5 {right}, left, refl end

lemma MulCommInRingTheory : MulComm ∈ RingTheory :=
begin unfold RingTheory, iterate 6 {right}, left, refl end

lemma AddMulInRingTheory : AddMul ∈ RingTheory :=
begin unfold RingTheory, iterate 7 {right}, exact set.mem_singleton _, end

namespace structureTo
  -- We make any (type theoretic) structure A,0,1,-,+,* into a
  -- (model theoretic) Structure in RingSignature

  variable
    {A : Type u}

  /-- Interpreting consant symbols from RingSignature -/
  @[simp] def ConstMap [has_zero A] [has_one A] : RingConsts → (dvector A 0) → A
  | RingConsts.zero _ := 0
  | RingConsts.one  _ := 1

  /-- Interpreting unary function symbols from RingSignature -/
  @[simp] def UnariesMap [has_neg A] : RingUnaries → (dvector A 1) → A
  | RingUnaries.neg a := - (dvector.last a)

  /-- Interpreting binary function symbols from RingSignature -/
  @[simp] def BinariesMap [has_add A] [has_mul A] : RingBinaries → (dvector A 2) → A
  | RingBinaries.add   (a :: b) := a + dvector.last b
  | RingBinaries.mul  (a :: b) := a * dvector.last b

  variables [has_zero A] [has_one A] [has_neg A] [has_add A] [has_mul A]

  /-- Interpreting all symbols from RingSignature-/
  @[simp] def FuncMap : Π (n : ℕ), (RingFuncs n) → (dvector A n) → A
  | 0       := ConstMap
  | 1       := UnariesMap
  | 2       := BinariesMap
  | (n + 3) := pempty.elim

  variable (A)

  /-- Interpreting the symbols -/
  @[reducible] def Structure : Structure RingSignature :=
  Structure.mk A FuncMap (λ n, pempty.elim)

  @[simp] lemma realize_zero {n} {vec : dvector A n} :
    @realize_bounded_term RingSignature (structureTo.Structure A) n vec 0
      (@bd_const RingSignature _ RingConsts.zero) dvector.nil = 0 := rfl

  @[simp] lemma realize_zero' {n} {vec : dvector A n} :
    @realize_bounded_term RingSignature (structureTo.Structure A) n vec 0
      (@bd_func RingSignature _ 0 RingConsts.zero) dvector.nil = 0 := rfl

  @[simp] lemma realize_one {n} {vec : dvector A n} :
    @realize_bounded_term RingSignature (structureTo.Structure A) n vec 0
      (@bd_const RingSignature _ RingConsts.one) dvector.nil = 1 := rfl

  @[simp] lemma realize_one' {n} {vec : dvector A n} :
    @realize_bounded_term RingSignature (structureTo.Structure A) n vec 0
      (@bd_func RingSignature _ 0 RingConsts.one) dvector.nil = 1 := rfl

  @[simp] lemma apps_zero {n} : Π {t_ : dvector (bounded_term RingSignature n) 0},
    bd_apps (@bd_func RingSignature _ 0 RingConsts.zero) t_ = 0
  | [] := rfl

  @[simp] lemma apps_one {n} : Π {t_ : dvector (bounded_term RingSignature n) 0},
    bd_apps (@bd_func RingSignature _ 0 RingConsts.one) t_ = 1
  | [] := rfl

  @[simp] lemma app_neg {n} {t : bounded_term RingSignature n} :
    bd_app (@bd_func RingSignature _ 1 RingUnaries.neg) t = - t := rfl

  lemma apps_neg {n} {t : bounded_term RingSignature n} :
     bd_apps (@bd_func RingSignature _ 1 RingUnaries.neg) ([t]) = - t := rfl

  @[simp] lemma app_add {n} {s t : bounded_term RingSignature n} :
    ((@bd_func RingSignature _ 2 RingBinaries.add).bd_app t).bd_app s = t + s := rfl

  lemma apps_add {n} {s t : bounded_term RingSignature n} :
     bd_apps (@bd_func RingSignature _ 2 RingBinaries.add) ([s,t]) = s + t := rfl

  @[simp] lemma app_mul {n} {s t : bounded_term RingSignature n} :
    ((@bd_func RingSignature _ 2 RingBinaries.mul).bd_app t).bd_app s = t * s := rfl

  lemma apps_mul {n} {s t : bounded_term RingSignature n} :
     bd_apps (@bd_func RingSignature _ 2 RingBinaries.mul) ([s,t]) = s * t := rfl

  -- lemma preterm_upper_bound {n} : bounded_preterm RingSignature n 3 → false := _

end structureTo

namespace comm_ring_to

  variables
    (A : Type u) [comm_ring A]

  lemma RealizeRingTheory :
    (structureTo.Structure A) ⊨ RingTheory := -- squeeze_simp, val_zero
  begin
    intros ϕ h,
    repeat {cases h},
    {
      intros a b c,
      simp only [structureTo.FuncMap, fin.val_zero', structureTo.BinariesMap, dvector.last,
        add, realize_bounded_formula, realize_bounded_term, fin.val_two, fin.val_one, dvector.nth],
      apply add_assoc
    },
    {
      intro a,
      simp only [add_zero, structureTo.FuncMap, fin.val_zero', structureTo.BinariesMap,
        dvector.last, eq_self_iff_true, realize_bounded_term_bd_app, add, realize_bounded_formula,
        realize_bounded_term, structureTo.realize_zero, dvector.nth, zero],
    },
    {
      intro a,
      simp only [structureTo.FuncMap, fin.val_zero', structureTo.BinariesMap,
        structureTo.UnariesMap, dvector.last, eq_self_iff_true, realize_bounded_term_bd_app, add,
        realize_bounded_formula, realize_bounded_term, structureTo.realize_zero,
        dvector.nth, zero, neg, add_left_neg],
    },
    {
      intros a b,
      simp only [structureTo.FuncMap, fin.val_zero', structureTo.BinariesMap,
        dvector.last, add, realize_bounded_formula,
        realize_bounded_term, fin.val_one, dvector.nth, add_comm]
    },
    {
      intros a b c,
      simp only [mul, structureTo.FuncMap, fin.val_zero', structureTo.BinariesMap,
      dvector.last, realize_bounded_formula,
      realize_bounded_term, fin.val_two, fin.val_one, dvector.nth, mul_assoc],
    },
    {
      intro a,
      simp only [mul, structureTo.realize_one, structureTo.FuncMap, fin.val_zero',
        mul_one, structureTo.BinariesMap, dvector.last, eq_self_iff_true, one,
        realize_bounded_term_bd_app, realize_bounded_formula, realize_bounded_term, dvector.nth],
    },
    {
      intros a b,
      simp only [mul, structureTo.FuncMap, fin.val_zero', structureTo.BinariesMap,
      dvector.last, realize_bounded_formula,
      realize_bounded_term, fin.val_one, dvector.nth, mul_comm],
    },
    {
      intros a b c,
      simp only [mul, structureTo.FuncMap, fin.val_zero', structureTo.BinariesMap, dvector.last,
      add, realize_bounded_formula, realize_bounded_term, fin.val_two,
      fin.val_one, dvector.nth, add_mul]
    }
  end

  /-- -/
  def ModelOfRingTheory : Model RingTheory.{u} :=
  ⟨ structureTo.Structure A ,  RealizeRingTheory A ⟩

end comm_ring_to


namespace mv_polynomial
  /- Terms in the RingSignature are multivariable polynomials over ℤ -/



  variable {σ : Type}

  @[simp] noncomputable def Const : RingConsts → mv_polynomial σ ℤ
  | RingConsts.zero := 0
  | RingConsts.one := 1

  @[simp] noncomputable def UniAux : RingUnaries → mv_polynomial σ ℤ → mv_polynomial σ ℤ
  | RingUnaries.neg p := - p

  @[simp] noncomputable def Uni {n} (f : RingSignature.functions 1) :
    Π (ts : dvector (bounded_term RingSignature n) 1),
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → mv_polynomial σ ℤ)
    → mv_polynomial σ ℤ
  | [t] h := UniAux f (h t (psum.inl rfl))

  noncomputable def BinAux : RingBinaries →
    mv_polynomial σ ℤ → mv_polynomial σ ℤ → mv_polynomial σ ℤ
  | RingBinaries.add p q := p + q
  | RingBinaries.mul p q := p * q

  noncomputable def Bin {n} (f : RingSignature.functions 2) :
    Π (ts : dvector (bounded_term RingSignature n) 2),
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → mv_polynomial σ ℤ)
    → mv_polynomial σ ℤ
  | [s, t] h := BinAux f (h s (psum.inl rfl)) (h t (psum.inr (psum.inl rfl)))

  @[simp] noncomputable def Func {n} :
    Π {l : ℕ} (f : RingSignature.functions l) (ts : dvector (bounded_term RingSignature n) l),
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → mv_polynomial σ ℤ) →
    (λ (_x : bounded_term RingSignature n), mv_polynomial σ ℤ) (bd_apps (bd_func f) ts)
  | 0 := λ f ts h, Const f
  | 1 := Uni
  | 2 := Bin
  | (n + 3) := λ f, pempty.elim f

  noncomputable def Term {n} :
    bounded_term RingSignature n → mv_polynomial (fin n) ℤ :=
  @RingTermRec n (λ _, mv_polynomial (fin n) ℤ)
    mv_polynomial.X 0 1
    (λ _ p, - p)
    (λ _ _ p q, p + q)
    (λ _ _ p q, p * q)

  noncomputable def Term' {n} :
    bounded_term RingSignature n → mv_polynomial (fin n) ℤ :=
  @bounded_term.rec RingSignature n (λ _, mv_polynomial (fin n) ℤ)
    mv_polynomial.X (λ _, Func)

  @[simp] lemma TermX {n} {k : fin n} : Term (x_ k) = mv_polynomial.X k := rfl

  @[simp] lemma TermZero {n} : @Term n (bd_const RingConsts.zero) = 0 := rfl
  @[simp] lemma TermOne {n} : @Term n (bd_const RingConsts.one) = 1 := rfl

  @[simp] lemma TermNeg {n} {t : bounded_term RingSignature n} :
    Term (- t) = - Term t := rfl

  @[simp] lemma TermAdd {n} {s t : bounded_term RingSignature n} :
    Term (s + t) = Term s + Term t := rfl

  @[simp] lemma TermMul {n} {s t : bounded_term RingSignature n} :
    Term (s * t) = Term s * Term t := rfl

  variables {A : Type u} [comm_ring A]

  @[reducible] private def AStruc := structureTo.Structure A

  lemma RealisedVarIsEvaluatedVar {n} {as : dvector A n} : Π (k : fin n),
  @realize_bounded_term _ AStruc _ as _ (x_ k) dvector.nil
  = mv_polynomial.eval (fin_val_of_dvector as) (Term (x_ k)) :=
  begin
    intro k,
    simpa only [mv_polynomial.eval_X, fin_val_of_dvector, fin.val_eq_coe,
      TermX, coe_mv_poly_X, realize_bounded_term],
  end

  lemma RealisedFuncIsEvaluatedFunc {n} {as : dvector A n} :
    Π {l : ℕ} (f : RingSignature.functions l)
    (ts : dvector (bounded_term RingSignature n) l),
    (Π (t : bounded_term RingSignature (n )),
       dvector.pmem t ts →
       (@realize_bounded_term _ AStruc _ as _ t dvector.nil =
         mv_polynomial.eval (fin_val_of_dvector as) (Term t)))
    → @realize_bounded_term _ AStruc _ as _ (bd_apps (bd_func f) ts) dvector.nil =
       mv_polynomial.eval (fin_val_of_dvector as) (Term (bd_apps (bd_func f) ts))
  | 0 RingConsts.zero _ h :=
  begin
    rw structureTo.apps_zero,
    simp only [fin_val_of_dvector, realize_bounded_term, structureTo.realize_zero, TermZero, zero],
    refl,
  end
  | 0 RingConsts.one _ h :=
  begin
    rw structureTo.apps_one,
    simp only [fin_val_of_dvector, realize_bounded_term, structureTo.realize_one, TermOne,
      one, coe_mv_poly_one, ring_hom.map_one],
  end
  | 1 RingUnaries.neg [t] h :=
  begin
    rw [structureTo.apps_neg, TermNeg],
    unfold_coes,
    unfold_coes at h,
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map] at h,
    simp only [structureTo.UnariesMap, structureTo.FuncMap,
      dvector.last, realize_bounded_term, neg, dvector.nth, coe_mv_poly_neg],
    simp only [ring_hom.to_fun_eq_coe, ring_hom.map_neg,
    mv_polynomial.eval_map, neg_inj],
    rw ← h t (psum.inl rfl),
  end
  | 2 RingBinaries.add ([s,t]) h :=
  begin
    rw [structureTo.apps_add, TermAdd],
    unfold_coes,
    unfold_coes at h,
    simp only [structureTo.FuncMap, structureTo.BinariesMap,
      ring_hom.map_add, dvector.last, ring_hom.to_fun_eq_coe,
      realize_bounded_term, mv_polynomial.eval_map, dvector.nth, add],
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map] at h,
    rw ← (h s (psum.inl rfl)),
    rw ← (h t (psum.inr (psum.inl rfl))),
  end
  | 2 RingBinaries.mul [s,t] h :=
  begin
    rw [structureTo.apps_mul, TermMul],
    unfold_coes,
    unfold_coes at h,
    simp only [structureTo.FuncMap, structureTo.BinariesMap,
      ring_hom.map_mul, dvector.last, ring_hom.to_fun_eq_coe,
      realize_bounded_term, mv_polynomial.eval_map, dvector.nth, mul],
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map] at h,
    rw ← (h s (psum.inl rfl)),
    rw ← (h t (psum.inr (psum.inl rfl))),
  end
  | (n + 3) f t_ h := pempty.elim f

  lemma RealizedTermIsEvaluatedPoly {n} {as : dvector A n} :
  Π (t : bounded_term RingSignature n),
    @realize_bounded_term _ AStruc _ as _ t dvector.nil
    = mv_polynomial.eval (fin_val_of_dvector as) (Term t) :=
  @bounded_term.rec RingSignature n
  (λ t, @realize_bounded_term _ AStruc _ as _ t dvector.nil
    = mv_polynomial.eval (fin_val_of_dvector as) (Term t))
  (RealisedVarIsEvaluatedVar)
  (λ l, RealisedFuncIsEvaluatedFunc)

end mv_polynomial

namespace polynomial

  variables {A : Type u} [comm_ring A]

  @[reducible] private def AStruc := structureTo.Structure A

  -- noncomputable def mv_poly_Z_to_poly_A {n} (as : dvector A n) (p : mv_polynomial (fin n.succ) ℤ) :
  --   polynomial A :=
  -- let σ : fin n.succ → polynomial A :=
  -- @fin.cases n (λ _, polynomial A) polynomial.X (λ i, polynomial.C (dvector.nth' as i)) in
  -- mv_polynomial.eval σ p

  @[simp] noncomputable def TermEvaluatedAtCoeffs {n} (as : dvector A n)
    (t : bounded_term RingSignature n.succ) : polynomial A :=
  let σ : fin n.succ → polynomial A :=
  @fin.cases n (λ _, polynomial A) polynomial.X (λ i, polynomial.C (dvector.nth' as i)) in
  mv_polynomial.eval σ (mv_polynomial.Term t)

  -- lemma this'x_k {n} {as : dvector A n} {x : A} : Π {k : fin n.succ},
  --   polynomial.eval x (TermEvaluatedAtCoeffs as (x_ k))
  --   = @realize_bounded_term _ AStruc n.succ (x::as) _ (x_ k) dvector.nil :=
  -- @fin.cases n
  -- (λ k, polynomial.eval x (TermEvaluatedAtCoeffs as (x_ k))
  --   = @realize_bounded_term _ AStruc n.succ (x::as) _ (x_ k) dvector.nil)
  -- (begin
  --   simp only [TermEvaluatedAtCoeffs, realize_bounded_term,
  --     mv_polynomial.Term, bounded_term.rec],
  --   simp,
  -- end)
  -- (begin
  --   intro k,
  --   simp only [TermEvaluatedAtCoeffs, realize_bounded_term,
  --     mv_polynomial.Term, bounded_term.rec],
  --   simpa,
  -- end)

  lemma fin_val_of_dvector_eq_x_val {n} {x : A} {as : dvector A n} :
    fin_val_of_dvector (x :: as) = x_val x (fin_val_of_dvector as) :=
    funext (
    @fin.cases n (λ k, fin_val_of_dvector (x :: as) k = x_val x (fin_val_of_dvector as) k)
    rfl
    (λ k, begin unfold fin_val_of_dvector, simp, end)
    )


  lemma eval_eq_realize_bounded_term
    {n} {as : dvector A n} {x : A} (t : bounded_term.{u} RingSignature n.succ) :
    (polynomial.eval x (TermEvaluatedAtCoeffs as t)
      = @realize_bounded_term _ AStruc n.succ (x::as) _ t dvector.nil) :=
  begin
    rw mv_polynomial.RealizedTermIsEvaluatedPoly,
    rw fin_val_of_dvector_eq_x_val,
    rw mv_polynomial.eval_eq_poly_eval_mv_coeffs,
    simp only [fin_val_of_dvector, function.comp_app, x_val,
      mv_poly_coeffs_to_poly, TermEvaluatedAtCoeffs],
    have hcoes : polynomial.C.comp (int.cast_ring_hom AStruc) = int.cast_ring_hom (polynomial A) :=
    by simp,
    unfold_coes,
    rw ← hcoes,
    simp,
  end

  lemma TermEvaluatedAtCoeffsX {n} {as : dvector A n} :
    TermEvaluatedAtCoeffs as (x_ 0) = polynomial.X :=
  begin
    simp only [TermEvaluatedAtCoeffs],
    unfold_coes,
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map, mv_polynomial.TermX],
    simp,
  end

  lemma TermEvaluatedAtCoeffsCoeff
  {n} {as : dvector A n} {k : fin n} :
    TermEvaluatedAtCoeffs as (x_ (k.succ)) = polynomial.C (dvector.nth' as k) :=
  begin
    simp only [TermEvaluatedAtCoeffs],
    unfold_coes,
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map, mv_polynomial.TermX],
    simp,
  end

  lemma TermEvaluatedAtCoeffsZero {n} {as : dvector A n} :
    TermEvaluatedAtCoeffs as (bd_const RingConsts.zero) = 0 :=
  begin
    simp only [TermEvaluatedAtCoeffs],
    unfold_coes,
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map, mv_polynomial.TermZero],
    simp,
  end

  lemma TermEvaluatedAtCoeffsOne {n} {as : dvector A n} :
    TermEvaluatedAtCoeffs as (bd_const RingConsts.one) = 1 :=
  begin
    simp only [TermEvaluatedAtCoeffs],
    unfold_coes,
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map, mv_polynomial.TermOne],
    simp,
  end

  lemma TermEvaluatedAtCoeffsNeg {n} {as : dvector A n} {t : bounded_term RingSignature n.succ} :
    TermEvaluatedAtCoeffs as (- t) = - TermEvaluatedAtCoeffs as t :=
  begin
    simp only [TermEvaluatedAtCoeffs],
    unfold_coes,
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map, mv_polynomial.TermNeg],
    simp,
  end

  lemma TermEvaluatedAtCoeffsAdd {n} {as : dvector A n} {s t : bounded_term RingSignature n.succ} :
    TermEvaluatedAtCoeffs as (s + t) = TermEvaluatedAtCoeffs as s + TermEvaluatedAtCoeffs as t :=
  begin
    simp only [TermEvaluatedAtCoeffs],
    unfold_coes,
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map, mv_polynomial.TermAdd],
    simp,
  end

  lemma TermEvaluatedAtCoeffsMul {n} {as : dvector A n} {s t : bounded_term RingSignature n.succ} :
    TermEvaluatedAtCoeffs as (s * t) = TermEvaluatedAtCoeffs as s * TermEvaluatedAtCoeffs as t :=
  begin
    simp only [TermEvaluatedAtCoeffs],
    unfold_coes,
    simp only [ring_hom.to_fun_eq_coe, mv_polynomial.eval_map, mv_polynomial.TermMul],
    simp,
  end

  lemma TermEvaluatedAtCoeffsPow {n : ℕ} : Π {m : ℕ} {as : dvector A n},
    polynomial.TermEvaluatedAtCoeffs as (x_ 0 ^ m) = polynomial.X ^ m
  | 0       _ :=
  begin
    rw pow_zero,
    simp,
  end
  | (n + 1) as :=
  begin
    rw Rings.pow_succ,
    rw TermEvaluatedAtCoeffsMul,
    rw TermEvaluatedAtCoeffsX,
    rw TermEvaluatedAtCoeffsPow,
    refl
  end

  lemma TermEvaluatedAtCoeffsMonomial {n : ℕ} {m : ℕ} {as : dvector A n} {k : fin n} :
    polynomial.TermEvaluatedAtCoeffs as (x_ (k.succ) * x_ 0 ^ m)
      = polynomial.monomial m (dvector.nth' as k) :=
  begin
    rw TermEvaluatedAtCoeffsMul,
    rw TermEvaluatedAtCoeffsCoeff,
    rw TermEvaluatedAtCoeffsPow,
    rw polynomial.monomial_eq_C_mul_X,
  end

  lemma nth_eq_succ_nth : Π {k n : ℕ} {as : dvector A (n + 1)} {h : k < n},
  as.nth k (lt_trans h (by simp)) = (dvector.remove_mth (n + 2) as).nth k h
  | k nat.zero ([a]) h := by {exfalso, simpa using h}
  | nat.zero (nat.succ n) (a::as) h := by simp
  | (nat.succ k) (nat.succ n) (a::as) h := by {simpa using nth_eq_succ_nth}

  lemma lift_succ_remove_last {n : ℕ} :
  Π {t : bounded_term RingSignature (n + 1)} {as : dvector A (n + 1)},
    polynomial.TermEvaluatedAtCoeffs as (lift_succ t)
    = polynomial.TermEvaluatedAtCoeffs (dvector.remove_mth (n + 2) as) t :=
  @RingTermRec (n + 1)
  (λ {t : bounded_term RingSignature (n + 1)}, Π {as : dvector A (n + 1)},
    polynomial.TermEvaluatedAtCoeffs as (lift_succ t)
    = polynomial.TermEvaluatedAtCoeffs (dvector.remove_mth (n + 2) as) t)
    (begin -- variables
      intros k as,
      rw lift_succ_x_k,
      cases k with k hk,
      cases k,
      {simp only [mv_polynomial.eval_X, fin.mk_zero, fin.cases_zero, fin.coe_eq_cast_succ,
        fin.cast_succ_zero, coe_mv_poly_X,
        mv_polynomial.TermX, TermEvaluatedAtCoeffs]},
      {
        simp only [mv_polynomial.eval_X, polynomial.C_inj,
          fin.coe_eq_cast_succ, fin.cases_succ', coe_mv_poly_X, fin.cast_succ_mk,
          mv_polynomial.TermX, TermEvaluatedAtCoeffs, dvector.nth'],
        apply nth_eq_succ_nth,
      },
    end)
    (begin -- 0
      intro as,
      simp only [zero, bd_const, lift_succ],
      repeat {rw ← bd_const},
      repeat {rw TermEvaluatedAtCoeffsZero},
    end)
    (begin -- 1
      intro as,
      simp only [one, bd_const, lift_succ],
      repeat {rw ← bd_const},
      repeat {rw TermEvaluatedAtCoeffsOne},
    end)
    (begin -- neg
      intros t h as,
      simp only [neg, lift_succ],
      repeat {rw structureTo.app_neg},
      repeat {rw TermEvaluatedAtCoeffsNeg},
      rw h,
    end)
    (begin
      intros s t hs ht as,
      simp only [add, lift_succ],
      repeat {rw structureTo.app_add},
      repeat {rw TermEvaluatedAtCoeffsAdd},
      rw [hs, ht],
    end)
    (begin
      intros s t hs ht as,
      simp only [mul, lift_succ],
      repeat {rw structureTo.app_mul},
      repeat {rw TermEvaluatedAtCoeffsMul},
      rw [hs, ht],
    end)

end polynomial

namespace ModelTo

  variable {M : Structure RingSignature}

  def zero : ↥ M := @Structure.fun_map _ M 0 RingConsts.zero dvector.nil
  def one : ↥ M := @Structure.fun_map _ M 0 RingConsts.one dvector.nil
  def neg (a : M.carrier) : M.carrier := @Structure.fun_map _ M 1 RingUnaries.neg ([a])
  def add (a b : M.carrier) : M.carrier := @Structure.fun_map _ M 2 RingBinaries.add ([a , b])
  def mul (a b : M.carrier) : M.carrier := @Structure.fun_map _ M 2 RingBinaries.mul ([a , b])

  instance : has_zero M := ⟨ zero ⟩
  instance : has_one M := ⟨ one ⟩
  instance : has_neg M := ⟨ neg ⟩
  instance : has_add M := ⟨ add ⟩
  instance : has_mul M := ⟨ mul ⟩

  @[simp] lemma realize_zero {n} {vec : dvector M.carrier n} :
    realize_bounded_term vec (bd_const RingConsts.zero) dvector.nil = 0 := rfl

  @[simp] lemma realize_one {n} {vec : dvector M.carrier n} :
    realize_bounded_term vec (bd_const RingConsts.one) dvector.nil = 1 := rfl

  @[simp] lemma realize_neg {a : M.carrier} :
    @Structure.fun_map _ M 1 RingUnaries.neg ([a]) = - a := rfl

  @[simp] lemma realize_add {a b : M.carrier} :
    @Structure.fun_map _ M 2 RingBinaries.add ([a , b]) = a + b := rfl

  @[simp] lemma realize_mul {a b : M.carrier} :
    @Structure.fun_map _ M 2 RingBinaries.mul ([a , b]) = a * b := rfl

  variable [h : fact (M ⊨ RingTheory)]

  include h
  lemma add_assoc (a b c : M) : (a + b) + c = a + (b + c) :=
  begin
      have hAssoc := h.elim AddAssocInRingTheory, have habc := hAssoc c b a,
      simpa using habc
  end

  lemma add_comm (a b : M) : a + b = b + a :=
  begin
    have hId := h.elim AddCommInRingTheory, have hab := hId b a, simpa using hab
  end

  lemma add_zero (a : M) : a + 0 = a :=
  begin
    have hId := h.elim AddIdInRingTheory, have ha := hId a, simpa using ha
  end

  lemma zero_add (a : M) : 0 + a = a :=
  begin
    rw add_comm, apply add_zero,
  end

  lemma left_neg (a : M) : - a + a = 0 :=
  begin
    have hInv := h.elim AddInvInRingTheory, have ha := hInv a, simpa using ha
  end

  lemma mul_assoc (a b c : M) : (a * b) * c = a * (b * c) :=
  begin
    have hAssoc := h.elim MulAssocInRingTheory, have habc := hAssoc c b a,
    simpa using habc
  end

  lemma mul_comm (a b : M) : a * b = b * a :=
  begin
    have hId := h.elim MulCommInRingTheory, have hab := hId b a, simpa using hab
  end

  lemma mul_one (a : M) : a * 1 = a :=
  begin
    have hId := h.elim MulIdInRingTheory, have ha := hId a, simpa using ha
  end

  lemma one_mul (a : M) : 1 * a = a :=
  begin
    rw mul_comm, apply mul_one
  end

  lemma add_mul (a b c : M) : (a + b) * c = a * c + b * c :=
  begin
    have hAM := h.elim AddMulInRingTheory, have habc := hAM c b a, simpa using habc
  end

  lemma mul_add (c a b : M) : c * (a + b) = c * a + c * b :=
  begin
    rw (mul_comm c (a + b)), rw (mul_comm c a), rw (mul_comm c b),
    exact add_mul a b c,
  end

  instance CommRing : comm_ring M :=
  {
    add            := add,
    add_assoc      := add_assoc,
    zero           := zero,
    zero_add       := zero_add,
    add_zero       := add_zero,
    neg            := neg,
    add_left_neg   := left_neg,
    add_comm       := add_comm,
    mul            := mul,
    mul_assoc      := mul_assoc,
    one            := one,
    one_mul        := one_mul,
    mul_one        := mul_one,
    left_distrib   := mul_add,
    right_distrib  := add_mul,
    mul_comm       := mul_comm,
  }

end ModelTo

end Rings
