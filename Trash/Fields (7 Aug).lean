import fol
import Rings.Notation
import Rings.Rings
import field_theory.algebraic_closure
notation h :: t  := dvector.cons h t
notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

universe u


namespace Fields
open fol
open Rings


def MulInv : sentence RingSignature :=
∀' (x_ 1 ≃ 0) ⊔ (∃' x_ 1 * x_ 0 ≃ 1)

def NonTriv : sentence RingSignature := 0 ≄ 1

def FieldTheory : Theory RingSignature :=  RingTheory ∪ {MulInv , NonTriv}

lemma MulInvInFieldTheory : MulInv ∈ FieldTheory := begin right, left, refl end

lemma NonTrivInFieldTheory : NonTriv ∈ FieldTheory :=
begin right, right, exact set.mem_singleton _ end

lemma RingTheorySubFieldTheory : RingTheory ⊆ FieldTheory :=
begin intros f hf, left, exact hf end

namespace field_to
  -- open classical
  -- local attribute [instance] prop_decidable
  variables
    {K : Type u} [field K]

  lemma K_is_field : is_field K := field.to_is_field K

  lemma RealizeFieldTheory :
    (structureTo.Structure K) ⊨ FieldTheory := -- squeeze_simp, val_zero
  begin
    intros ϕ h,
    cases h,
    {apply (comm_ring_to.RealizeRingTheory K h)},
    repeat {cases h},
     {
       intro,
       unfold fol.bd_or,
       simp only [ModelTo.realize_one, mul, structureTo.FuncMap,
         fin.val_zero', realize_bounded_formula_not, structureTo.BinariesMap,
         fin.val_eq_coe, dvector.last, realize_bounded_formula_ex, realize_bounded_term_bd_app,
         realize_bounded_formula, realize_bounded_term, fin.val_one, dvector.nth,
         ModelTo.realize_zero],
       apply is_field.mul_inv_cancel,
       apply K_is_field,
     },
    {unfold fol.realize_sentence, simp},
  end

  def ModelOfFieldTheory : Model FieldTheory.{u} :=
  ⟨ structureTo.Structure K ,  RealizeFieldTheory ⟩

end field_to

namespace FieldModelTo

  variables {M : Structure RingSignature} [h : fact (M ⊨ FieldTheory)]
  -- M inherits instances of 0 1 - + * from Rings.ModelTo

  include h

  instance RingModel : fact (M ⊨ RingTheory) :=
  ⟨ begin intros f hf, apply h.elim, apply RingTheorySubFieldTheory, exact hf end ⟩

  instance CommRing : comm_ring M := ModelTo.CommRing

  instance Ring : ring M := comm_ring.to_ring M

  lemma zero_ne_one : (0 : M) ≠ 1 := by simpa using (h.elim NonTrivInFieldTheory)

  lemma mul_inv (a : M) (ha : a ≠ 0) : (∃ (b : M), a * b = 1) :=
  let hmulinv := h.elim MulInvInFieldTheory in by simpa using hmulinv a ha

  instance is_field : fact (is_field M) :=
  ⟨⟨
    ⟨ 0 , 1 , zero_ne_one ⟩,
    Rings.ModelTo.mul_comm,
    mul_inv
  ⟩⟩

  noncomputable instance field : field M := is_field.to_field M FieldModelTo.is_field.elim

end FieldModelTo

-- GenPoly n is the polynomial aₙ₊₁ xⁿ + ⋯ + a₂ x + a₁
-- where aₖ = x_ k and x = x_ 0, i.e. we are seeing the variables x_ k with 0 < k as coefficients
-- and x_ 0 as the indeterminate
@[simp] def GenPoly : Π (n : ℕ), bounded_term RingSignature (n + 2)
| 0       := x_ 1
| (n + 1) := (x_ (fin.succ n.succ)) * ((x_ 0) ^ (n + 1)) +
  bounded_preterm.lift_succ (GenPoly n)



-- Adds a monic term at the beginning of GenPoly.
-- We will require that these polynomials have solutions.
-- We cannot just use GenPoly as we need the polynomials to have 0 < deg
@[simp] def GenMonicPoly (n : ℕ) : bounded_term RingSignature (n + 2) :=
(x_ 0) ^ (n + 2) + GenPoly n

-- lemma comeone {A : Type u} [ring A] {p q : polynomial A} : (p.degree) ≤ (p + q).degree := by
-- hint

-- #check @nat.lt_add_one_iff

--   #check @polynomial.degree_add_eq_left_of_degree_lt

-- #check polynomial.degree
-- #check with_bot ℕ

-- lemma TermToPolyBaseIdk {A : Type u} [comm_ring A] (a : A) :
--   comm_ring_to.TermToPoly ([a]) x_ 1 = polynomial.C a := rfl

-- lemma TermToPolyInd {A : Type u} [comm_ring A] {n} (as : dvector A (n + 1)) (k : fin (n + 1)) :
--   comm_ring_to.TermToPoly as x_(k + 1) = polynomial.C (dvector.nth' as k) :=
-- begin
--   unfold comm_ring_to.TermToPoly,
--   unfold bounded_term.rec,
--   simp,
--   unfold fin.cases,
--   unfold fin.induction,
--   simp,
--   sorry,
-- end

-- lemma TermToPolyMonomial


-- lemma GenPolyDeg {A : Type u} [comm_ring A] [decidable_eq A]:
--   Π {n} {a_ : dvector A (n + 1)},
--   (comm_ring_to.TermToPoly.{u u} a_ (GenPoly n)).degree ≤ n
-- | nat.zero (a :: []) :=
-- begin
--   unfold GenPoly,
--   rw TermToPolyBaseIdk a,
--   by_cases ha : a = 0,
--   {rw ha, simp},
--   {rw polynomial.degree_C ha, simp},
-- end
-- | (nat.succ n) as :=
-- begin
--   unfold GenPoly,
--   rw comm_ring_to.TermToPolyAdd,
--   have hq : (comm_ring_to.TermToPoly as (x_(n + 2) * x_ 0 ^ (n + 1))).degree ≤ n.succ,
--   {
--     rw comm_ring_to.TermToPolyMul,

--     -- by_cases ha : as.last = 0,
--     -- {
--     --   rw TermToPolyInd as ⟨ n + 1 , _ ⟩,

--     --   unfold pow,
--     --   simp,
--     --   -- rw ha,

--     -- },
--     -- sorry,
--   },
--   have hle : (comm_ring_to.TermToPoly (a :: as) (lift_bounded_term1 (GenPoly n))).degree <
--   (comm_ring_to.TermToPoly (a :: as) (x_(n + 2) * x_ 0 ^ (n + 1))).degree,
--   sorry,
--   rw (polynomial.degree_add_eq_left_of_degree_lt hle),
--   exact hq,
-- end

--   sorry,
--   have hle :
--   sorry,
-- end

-- should be in the library
lemma with_bot.succ_lt_succ_succ {n : ℕ} : (n + 1 : with_bot ℕ) < ↑n.succ + 1 := by tidy

lemma DegPow {A : Type u} [comm_ring A] [nontrivial A] {n m : ℕ} {as : dvector A (n + 1)} :
(polynomial.TermEvaluatedAtCoeffs as (x_ 0 ^ m)).degree = m :=
begin
  rw polynomial.TermEvaluatedAtCoeffsPow,
  apply polynomial.degree_X_pow,
end

section PolyLemmas

variables {A : Type u} [hcomm : comm_ring A] [hnt : nontrivial A] [hde : decidable_eq A]

include hcomm hnt hde

lemma GenPolyDegree : Π {n} {as : dvector A (n + 1)},
  (polynomial.TermEvaluatedAtCoeffs as (GenPoly n)).degree < n.succ
| nat.zero as :=
begin
  simp only [GenPoly],
  have h : polynomial.TermEvaluatedAtCoeffs as x_ 1 = polynomial.C (as.nth' 0),
  {rw ← polynomial.TermEvaluatedAtCoeffsCoeff, simp,},
  rw h,
  by_cases h0 : as.nth' 0 = 0,
  {
    rw h0,
    rw polynomial.C_0,
    rw polynomial.degree_zero,
    exact dec_trivial,
  },
  {
    rw polynomial.degree_C h0,
    exact dec_trivial,
  }
end
| (nat.succ n) as :=
begin
  simp only [GenPoly, polynomial.TermEvaluatedAtCoeffsAdd],
  rw polynomial.TermEvaluatedAtCoeffsMonomial,
  rw polynomial.lift_succ_remove_last,
  -- have am : dvector A n.succ := dvector.remove_mth (n + 2) as,
  apply has_le.le.trans_lt (polynomial.degree_add_le _ _),
  apply max_lt,
  {
    apply has_le.le.trans_lt (polynomial.degree_monomial_le _ _),
    exact with_bot.succ_lt_succ_succ,
  },
  {
    apply lt_trans (@GenPolyDegree n (dvector.remove_mth (n.succ + 2) as)),
    exact with_bot.succ_lt_succ_succ,
  },
end

lemma GenMonicPolyNonConst {n} {as : dvector A (n + 1)} :
  polynomial.degree (polynomial.TermEvaluatedAtCoeffs as (GenMonicPoly n)) ≠ 0 :=
begin
  unfold GenMonicPoly,
  rw polynomial.TermEvaluatedAtCoeffsAdd,
  apply ne_of_gt,
  have hp : (polynomial.TermEvaluatedAtCoeffs as (x_ 0 ^ (n + 2))).degree = n + 2,
  {apply DegPow},
  have hq : (polynomial.TermEvaluatedAtCoeffs as (GenPoly n)).degree < n + 2,
  {
    apply lt_trans GenPolyDegree,
    exact with_bot.succ_lt_succ_succ,
    exact hnt, -- why??
    exact hde, -- why??
  },
  have hle : (polynomial.TermEvaluatedAtCoeffs as (GenPoly n)).degree
    < (polynomial.TermEvaluatedAtCoeffs as (x_ 0 ^ (n + 2))).degree,
  { rw hp, exact hq },
  rw (polynomial.degree_add_eq_left_of_degree_lt hle),
  rw hp,
  exact dec_trivial,
end

end PolyLemmas
/-
From fol - takes a formula with n free variables and sticks n many ∀'s in front
@[simp] def bd_alls : Π n : ℕ, bounded_formula L n → sentence L
| 0     f := f
| (n+1) f := bd_alls n (∀' f) -- bd_alls' (n+1) 0 (f.cast_eqr (zero_add (n+1)))
-/

-- @[simp] lemma bd_alls_0 {L} {ϕ} : @bd_alls L 0 ϕ = ϕ := rfl

@[simp] def AllGenMonicPolyHasRoot (n : ℕ) : sentence RingSignature :=
fol.bd_alls (n + 1) (∃' GenMonicPoly n ≃ 0)

-- #reduce GenMonicPolyHasSolution 1

def ACF : Theory RingSignature := FieldTheory ∪ (set.range AllGenMonicPolyHasRoot)
-- the latter stands for {GenMonicPolyHasSolution n | n : ℕ}

-- ACF with p = 0 chucked in
def ACFₚ (p : ℕ) : Theory RingSignature := set.insert (p ≃ 0) ACF

-- ACF with p ≠ 0 chucked in for every natural p
def ACF₀ : Theory RingSignature := ACF ∪ (set.range (λ p : ℕ, p ≄ 0))

namespace is_alg_closed_to

  variables {K : Type u} [field K] [is_alg_closed K] [decidable_eq K]

  -- #check is_alg_closed.of_exists_root

  -- should be in the library
  theorem is_alg_closed.exists_root (f : polynomial K) (h : f.degree ≠ 0) :
    ∃ x : K, f.eval x = 0 := polynomial.exists_root_of_splits _ (is_alg_closed.splits f) h

  -- lemma ExistsRoot {n} (a_ : dvector K (n + 1)) :
  --   ∃ x : K, polynomial.eval x (ToPoly (GenMonicPoly n)) = 0 :=
  -- sorry

  -- @[simp] lemma notsure {A : Type u} [has_one A] [has_mul A] {x : M} {n m : ℕ} {a_ : dvector M n} :
  --   realize_bounded_term (dvector.cons x a_) (x_ 0 ^ m) dvector.nil = x ^ m := _

  lemma RealizeACF : structureTo.Structure K ⊨ ACF :=
  begin
    intros ϕ h,
    cases h,
    {apply field_to.RealizeFieldTheory h},
    {
      cases h with n hϕ,
      rw ← hϕ,
      unfold AllGenMonicPolyHasRoot,
      rw realize_sentence_bd_alls,
      simp only [realize_bounded_formula_ex, realize_bounded_formula, ModelTo.realize_zero, zero],
      intro as,
      have root := is_alg_closed.exists_root
        (polynomial.TermEvaluatedAtCoeffs as (GenMonicPoly n)) GenMonicPolyNonConst,
      cases root with x hx,
      use x,
      rw polynomial.eval_eq_realize_bounded_term at hx,
      exact hx,
    },
  end

end is_alg_closed_to



end Fields

-- #lint
