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

  -- realize_bounded_term (dvector.cons x a_) (GenPoly n) dvector.nil

  -- def yuck {n} : fin (n + 2) → fin (n + 1) := _

  -- def whateever {n} (a_ : dvector A n) : (k : ℕ) → polynomial A
  -- |
  -- |

  variable {A}

  noncomputable def yuck1 {n} (a_ : dvector A n) : fin (n + 1) → polynomial A :=
  @fin.cases n (λ k, polynomial A) polynomial.X (λ k, polynomial.C (dvector.nth' a_ k))

  noncomputable def ConstPoly : RingConsts → polynomial A
  | RingConsts.zero := 0
  | RingConsts.one := 1

  noncomputable def ConstToPoly {n} (f : RingSignature.functions 0)
    (ts : dvector (bounded_term RingSignature n) 0) :
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → polynomial A) → polynomial A :=
  λ h, ConstPoly f

  noncomputable def UniPoly : RingUnaries → polynomial A → polynomial A
  | RingUnaries.minus p := - p

  noncomputable def UniToPoly {n} (f : RingSignature.functions 1) :
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

  def MoreToPoly {m} {n} (f : RingSignature.functions (m + 3))
    (ts : dvector (bounded_term RingSignature n) 3) :
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → polynomial A) → polynomial A :=
    pempty.elim f

  -- #check @bounded_term.rec
  -- #check @bd_func RingSignature _ 2 RingBinaries.plus

  -- -- def yuck4 {n} {l} : bounded_preterm RingSignature n l
  -- --   → Σ (m : ℕ), RingSignature.functions m :=
  -- -- @bounded_term.rec RingSignature _ (λ k, ⟨ 0 , RingConsts.zero ⟩) _


  -- lemma yuck2 {n} (k) : bounded_preterm RingSignature n (k + 3) → pempty
  -- | (bd_func f) := pempty.elim f
  -- | (bd_app t s) := have false,
  -- begin
  --   unfold bounded_preterm,

  -- end,
  -- _


  -- noncomputable def term_to_polynomial2 {n} : bounded_preterm RingSignature (n + 1) 2
  --   → polynomial A → polynomial A → polynomial A
  -- | (bd_func f) := BinPoly f
  -- | (bd_app t s) := _


  -- noncomputable def term_to_polynomial1 {n} : bounded_preterm RingSignature (n + 1) 1
  --   → polynomial A → polynomial A
  -- | (bd_func f) := UniPoly f
  -- | (bd_app t s) := _


  -- -- @fin.induction_on n k (λ i, polynomial A) polynomial.X (λ i hi, polynomial.C (dvector.nth' a_ i))

  noncomputable def FuncToPoly {n} :
    Π {l : ℕ} (f : RingSignature.functions l) (ts : dvector (bounded_term RingSignature n) l),
    (Π (t : bounded_term RingSignature n), dvector.pmem t ts → polynomial A) →
    (λ (_x : bounded_term RingSignature n), polynomial A) (bd_apps (bd_func f) ts)
  | 0 := ConstToPoly
  | 1 := UniToPoly
  | 2 := BinToPoly
  | (n + 3) := λ f, pempty.elim f


  -- noncomputable def term_to_polynomial {n} (a_ : dvector A n) :
  --   bounded_preterm RingSignature (n + 1) 0 → polynomial A
  -- | (bd_var k) :=
  --   @fin.cases n (λ k, polynomial A) polynomial.X (λ k, polynomial.C (dvector.nth' a_ k)) k
  -- | (bd_func f) := ConstPoly f
  -- | (bd_app t s) := _

  #check @bounded_term.rec

  noncomputable def term_to_polynomial {n} (a_ : dvector A n) :
    bounded_term RingSignature n → polynomial A :=
  @bounded_term.rec RingSignature n (λ _, polynomial A)
    (
      λ k : fin n,
      @fin.cases n (λ k, polynomial A) polynomial.X (λ k, polynomial.C (dvector.nth' a_ k)) k
    )
    (λ _, FuncToPoly)



  -- lemma polynomial_to_term {p : polynomial A} : bounded_term RingSignature 1 :=
  -- _

  -- @[simp] lemma notsure {x : structureTo.Structure A} {n m : ℕ} {a_ : dvector A n}
  --   {p : polynomial A} :
  --   realize_bounded_term (dvector.cons x a_) (polynomial_to_term p) dvector.nil = polynomial.eval x p := _

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
