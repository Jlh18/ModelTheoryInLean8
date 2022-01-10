import tactic
import fol
import Rings.Notation
import Rings.ToMathlib
import data.polynomial.eval

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
| minus : RingUnaries

/-- The binary function symbols in RingSignature-/
inductive RingBinaries : Type u
| plus : RingBinaries
| times : RingBinaries

/-- All function symbols in RingSignature-/
def RingFuncs : ℕ → Type u
| 0 := RingConsts
| 1 := RingUnaries
| 2 := RingBinaries
| (n + 3) := pempty

instance : inhabited RingConsts := ⟨ RingConsts.zero ⟩
instance : inhabited RingUnaries := ⟨ RingUnaries.minus ⟩
instance : inhabited RingBinaries := ⟨ RingBinaries.plus ⟩

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

@[simp] def minus {n} : bdt n → bdt n := bd_app (bd_func RingUnaries.minus)
@[reducible] instance RingBDTHasNeg {n} : has_neg (bdt n) := ⟨ minus ⟩
@[reducible] instance RingBDTHasNeg' {n} : has_neg (bdt'  n) := ⟨ minus ⟩

@[simp] def plus {n} (x : bdt n) : bdt n → bdt n :=
  bd_app (bd_app (bd_func RingBinaries.plus) x)
@[reducible] instance RingBDTHasAdd {n} : has_add (bdt n) := ⟨ plus ⟩
@[reducible] instance RingBDTHasAdd' {n} : has_add (bdt'  n) := ⟨ plus ⟩

@[simp] def times {n} (x : bdt n) : bdt n → bdt n :=
  bd_app (bd_app (bd_func RingBinaries.times) x)
@[reducible] instance RingBDTHasMul {n} : has_mul (bdt n) := ⟨ times ⟩
@[reducible] instance RingBDTHasMul' {n} : has_mul (bdt' n) := ⟨ times ⟩

-- has_pow comes for free by having instances of mul and 1 (see ToMathlib) -- input x ^ n

@[simp] lemma pow_zero {n} (t : bounded_term RingSignature n) : t ^ 0 = 1 := rfl
@[simp] lemma pow_succ {n m} (t : bounded_term RingSignature m) : t ^ (n + 1) = t * t ^ n := rfl


-- @[simp] lemma to_the_one {n} (t : bounded_term RingSignature n) : t ^ 1 = t * 1 := rfl

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

-- minus x
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
| 1 (RingUnaries.minus) ([t]) h := cneg (h t (psum.inl rfl))
| 2 (RingBinaries.plus) ([s,t]) h := cadd (h s (psum.inl rfl)) (h t (psum.inr (psum.inl rfl)))
| 2 (RingBinaries.times) ([s,t]) h := cmul (h s (psum.inl rfl)) (h t (psum.inr (psum.inl rfl)))
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
  | RingUnaries.minus a := - (dvector.last a)

  /-- Interpreting binary function symbols from RingSignature -/
  @[simp] def BinariesMap [has_add A] [has_mul A] : RingBinaries → (dvector A 2) → A
  | RingBinaries.plus   (a :: b) := a + dvector.last b
  | RingBinaries.times  (a :: b) := a * dvector.last b

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

  @[simp] lemma realize_one {n} {vec : dvector A n} :
    @realize_bounded_term RingSignature (structureTo.Structure A) n vec 0
      (@bd_const RingSignature _ RingConsts.one) dvector.nil = 1 := rfl
end structureTo

namespace comm_ring_to

  variables
    (A : Type u) [comm_ring A]

  lemma RealizeRingTheory :
    (structureTo.Structure A) ⊨ RingTheory := -- squeeze_simp, val_zero
  begin
    intros ϕ h,
    repeat {cases h},
    {intros a b c, simp, apply add_assoc},
    {intro a, simp},
    {intro a, simp},
    {intros a b, simp, apply add_comm},
    {intros a b c, simp, apply mul_assoc},
    {intro a, simp},
    {intros a b, simp, apply mul_comm},
    {intros a b c, simp, apply add_mul},
  end

  /-- -/
  def ModelOfRingTheory : Model RingTheory.{u} :=
  ⟨ structureTo.Structure A ,  RealizeRingTheory A ⟩


  open polynomial

  variable {A}

   @[simp] noncomputable def ConstPoly : RingConsts → polynomial A
  | RingConsts.zero := 0
  | RingConsts.one := 1

  @[simp] noncomputable def UniPoly : RingUnaries → polynomial A → polynomial A
  | RingUnaries.minus p := - p

  @[simp] noncomputable def UniToPoly {n} (f : RingSignature.functions 1) :
    Π (ts : dvector (bounded_term RingSignature n) 1),
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → polynomial A) → polynomial A
  | [t] h := UniPoly f (h t (psum.inl rfl))

  noncomputable def BinPoly : RingBinaries → polynomial A → polynomial A → polynomial A
  | RingBinaries.plus p q := p + q
  | RingBinaries.times p q := p * q

  noncomputable def BinToPoly {n} (f : RingSignature.functions 2) :
    Π (ts : dvector (bounded_term RingSignature n) 2),
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → polynomial A) → polynomial A
  | [s, t] h := BinPoly f (h s (psum.inl rfl)) (h t (psum.inr (psum.inl rfl)))

  @[simp] noncomputable def FuncToPoly {n} :
    Π {l : ℕ} (f : RingSignature.functions l) (ts : dvector (bounded_term RingSignature n) l),
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → polynomial A) →
    (λ (_x : bounded_term RingSignature n), polynomial A) (bd_apps (bd_func f) ts)
  | 0 := λ f ts h, ConstPoly f
  | 1 := UniToPoly
  | 2 := BinToPoly
  | (n + 3) := λ f, pempty.elim f

  @[simp] noncomputable def TermToPoly {n} (a_ : dvector A n) :
    bounded_term RingSignature (n + 1) → polynomial A :=
  @bounded_term.rec RingSignature (n + 1) (λ _, polynomial A)
    (
      λ k : fin (n + 1),
      @fin.cases n (λ k, polynomial A) polynomial.X (λ k, polynomial.C (dvector.nth' a_ k)) k
    )
    (λ _, FuncToPoly)

  lemma TermToPolyZero {n} {a_ : dvector A n} : Π {t_},
    TermToPoly a_ (bd_apps (@bd_func RingSignature _ 0 RingConsts.zero) t_) = 0
  | [] := begin unfold TermToPoly, unfold bounded_term.rec, simp, end

  lemma TermToPolyOne {n} {a_ : dvector A n} : Π {t_},
    TermToPoly a_ (bd_apps (@bd_func RingSignature _ 0 RingConsts.one) t_) = 1
  | [] := begin unfold TermToPoly, unfold bounded_term.rec, simp, end

  lemma TermToPolyMinus {n} {a_ : dvector A n} {t} :
    TermToPoly a_ (- t) = - TermToPoly a_ t :=
  begin
    simp only [TermToPoly, minus],
    unfold bounded_term.rec,
    unfold FuncToPoly,
    unfold UniToPoly,
    unfold UniPoly,
  end

  lemma TermToPolyPlus {n} {a_ : dvector A n} {s t : bounded_term RingSignature (n + 1)} :
    TermToPoly a_ (s + t) = TermToPoly a_ s + TermToPoly a_ t :=
  begin
    simp only [TermToPoly, plus],
    unfold bounded_term.rec,
    unfold FuncToPoly,
    unfold BinToPoly,
    unfold BinPoly,
  end

  lemma TermToPolyTimes {n} {a_ : dvector A n} {s t : bounded_term RingSignature (n + 1)} :
    TermToPoly a_ (s * t) = TermToPoly a_ s * TermToPoly a_ t :=
  begin
    simp only [TermToPoly, times],
    unfold bounded_term.rec,
    unfold FuncToPoly,
    unfold BinToPoly,
    unfold BinPoly,
  end

  @[reducible] def AStruc := structureTo.Structure A

  lemma RealisedVarIsEvaluatedVar {n} {a_ : dvector A n} {x : A} : Π (k : fin n.succ),
  @realize_bounded_term _ AStruc _ (x :: a_) _ (x_ k) dvector.nil
  = eval x (TermToPoly a_ (x_ k)) :=
  @fin.cases n
  (λ k, @realize_bounded_term _ AStruc _ (x :: a_) _ (x_ k) dvector.nil
    = eval x (TermToPoly a_ (x_ k)))
  (begin unfold TermToPoly, unfold bounded_term.rec, simp, end)
  (begin
    intro i,
    unfold TermToPoly,
    unfold bounded_term.rec,
    simpa,
  end)

  @[simp] lemma apps_zero {n} : Π {t_ : dvector (bounded_term RingSignature (n + 1)) 0},
    bd_apps (@bd_func RingSignature _ 0 RingConsts.zero) t_ = 0
  | [] := rfl

  @[simp] lemma apps_one {n} : Π {t_ : dvector (bounded_term RingSignature (n + 1)) 0},
    bd_apps (@bd_func RingSignature _ 0 RingConsts.one) t_ = 1
  | [] := rfl

  lemma apps_minus {n} {t : bounded_term RingSignature (n + 1)} :
     bd_apps (@bd_func RingSignature _ 1 RingUnaries.minus) ([t]) = - t := rfl

  lemma apps_plus {n} {s t : bounded_term RingSignature (n + 1)} :
     bd_apps (@bd_func RingSignature _ 2 RingBinaries.plus) ([s,t]) = s + t := rfl

  lemma apps_times {n} {s t : bounded_term RingSignature (n + 1)} :
     bd_apps (@bd_func RingSignature _ 2 RingBinaries.times) ([s,t]) = s * t := rfl
  -- should be in the library
  lemma dvector.pmem_of_last {α : Type u} : Π {a_ : dvector α 1}, dvector.pmem a_.last a_
  | [a] := psum.inl rfl

  lemma RealisedFuncIsEvaluatedFunc {n} {a_ : dvector A n} {x : A} :
    Π {l : ℕ} (f : RingSignature.functions l)
    (ts : dvector (bounded_term RingSignature (n + 1)) l),
    (Π (t : bounded_term RingSignature (n + 1)),
       dvector.pmem t ts →
       (λ (p : bounded_term RingSignature (n + 1)),
          @realize_bounded_term _ AStruc _ (x :: a_) _ p dvector.nil = eval x (TermToPoly a_ p))
        t)
    → (λ (p : bounded_term RingSignature (n + 1)),
       @realize_bounded_term _ AStruc _ (x :: a_) _ p dvector.nil = eval x (TermToPoly a_ p))
      (bd_apps (bd_func f) ts)
  | 0 RingConsts.zero t_ h := begin rw TermToPolyZero, simp end
  | 0 RingConsts.one t_ h := begin rw TermToPolyOne, simp end
  | 1 RingUnaries.minus [t] h :=
  begin
    rw apps_minus,
    rw TermToPolyMinus,
    rw eval_neg,
    rw ← h t (psum.inl rfl),
    refl,
  end
  | 2 RingBinaries.plus [s,t] h :=
  begin
    rw apps_plus,
    rw TermToPolyPlus,
    rw eval_add,
    rw ← (h s (psum.inl rfl)),
    rw ← (h t (psum.inr (psum.inl rfl))),
    refl,
  end
  | 2 RingBinaries.times [s,t] h :=
  begin
    rw apps_times,
    rw TermToPolyTimes,
    rw eval_mul,
    rw ← (h s (psum.inl rfl)),
    rw ← (h t (psum.inr (psum.inl rfl))),
    refl,
  end
  | (n + 3) f t_ h := pempty.elim f

  lemma RealizedTermIsEvaluatedPoly {n} {a_ : dvector A n} {x : A} :
    Π (p : bounded_term RingSignature (n + 1)),
    @realize_bounded_term _ (structureTo.Structure A) _ (dvector.cons x a_) _ p dvector.nil
    = eval x (TermToPoly a_ p) :=
  @bounded_term.rec RingSignature (n + 1)
  (λ p, @realize_bounded_term _ (structureTo.Structure A) _ (dvector.cons x a_) _ p dvector.nil
    = eval x (TermToPoly a_ p))
  (RealisedVarIsEvaluatedVar)
  (λ l, RealisedFuncIsEvaluatedFunc)

end comm_ring_to

namespace ModelTo

  variable {M : Structure RingSignature}

  def zero : ↥ M := @Structure.fun_map _ M 0 RingConsts.zero dvector.nil
  def one : ↥ M := @Structure.fun_map _ M 0 RingConsts.one dvector.nil
  def neg (a : M.carrier) : M.carrier := @Structure.fun_map _ M 1 RingUnaries.minus ([a])
  def add (a b : M.carrier) : M.carrier := @Structure.fun_map _ M 2 RingBinaries.plus ([a , b])
  def mul (a b : M.carrier) : M.carrier := @Structure.fun_map _ M 2 RingBinaries.times ([a , b])

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
    @Structure.fun_map _ M 1 RingUnaries.minus ([a]) = - a := rfl

  @[simp] lemma realize_add {a b : M.carrier} :
    @Structure.fun_map _ M 2 RingBinaries.plus ([a , b]) = a + b := rfl

  @[simp] lemma realize_mul {a b : M.carrier} :
    @Structure.fun_map _ M 2 RingBinaries.times ([a , b]) = a * b := rfl

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
