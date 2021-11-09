import data.finset
import algebra.field
import order.zorn
import Rings.ToMathlib

open classical
local attribute [instance] prop_decidable

universe u

/-- A pregeometry consists of
  * a type `Carrier`
  * a closure map `Cl` from the powerset of `Carrier` to itself
  such that
  * `Cl` is a morphism of orders (with the natural ordering on the powerset)
  * `Cl` is idempotent
  * Any element in the closure is in the closure of some finite subset
  * The generalized Steinitz exchange works with `Cl` viewed as the span
-/
class Pregeometry : Type (u + 1) :=
(Carrier : Type u)
(Cl : set Carrier → set Carrier)
(Closure : Π {U : set Carrier}, U ⊆ Cl U)
(OrdMor : Π {U V : set Carrier}, U ⊆ V → Cl U ⊆ Cl V)
(Idem : Π (U : set Carrier), Cl (Cl U) = Cl U)
(FinChar : Π {U} {a : Carrier} (h : a ∈ Cl U), finset Carrier)
(FinCharProp : Π {U} {a} (h : a ∈ Cl U), ↑(FinChar h) ⊆ U ∧ a ∈ Cl (FinChar h))
(Exch : Π {U : set Carrier} {a b : Carrier}, a ∈ Cl (U ∪ {b}) → a ∈ Cl U ∨ b ∈ Cl (U ∪ {a}))

namespace Pregeometry
  variables
    {X : Pregeometry} (U V W : set Carrier)

  def Spans : Prop := U ⊆ V ∧ Cl U = Cl V

  def Indep : Prop := Π a : Carrier, (a ∈ U) → a ∉ Cl (U \ {a})

  def Basis : Prop := Spans U V ∧ Indep U

  def Dep : Prop := ∃ (a : Carrier) (haU : a ∈ U), a ∈ Cl (U \ {a})

  variables {U} {V} {W}

  lemma SubIndep : Indep V → Π (U : set Carrier), U ⊆ V → Indep U :=
  begin
    intros hV U hsub a haU hbot,
    have haV := hsub haU,
    apply hV a haV,
    apply OrdMor _ hbot,
    apply set.diff_subset_diff hsub,
    simp,
  end

  lemma SpansTrans : Spans U V → Spans V W → Spans U W :=
  begin
    intros hUV hVW,
    split,
    {apply set.subset.trans hUV.1 hVW.1},
    {rw hUV.2, exact hVW.2}
  end

  lemma SubClSpans : U ⊆ V → V ⊆ Cl U → Spans U V :=
  begin
    intros hUV hVCl,
    split,
    {exact hUV},
    {
      apply set.ext,
      intro x,
      split,
      {apply OrdMor hUV},
      {
        rw ← @Idem _ U,
        apply OrdMor hVCl,
      },
    }
  end

  lemma NotIndep : ¬ Indep U ↔ Dep U :=
  begin
    split,
    {
      intro hnIndU,
      cases not_forall.1 hnIndU with x hx,
      cases not_imp.1 hx with hxU hnn,
      rw not_not at hnn,
      use x,
      exact ⟨ hxU , hnn ⟩
    },
    {
      intros hDep hbot,
      cases hDep with x hx,
      cases hx with hxU hxCl,
      exact hbot x hxU hxCl,
    }
  end

  lemma IndepInsert : Indep U → Π (a : Carrier), (a ∉ Cl U) → Indep (U ∪ {a}) :=
  begin
    intros hU a haClU b hbUa hbot,
    cases hbUa,
    {
      have hExch : b ∈ Cl ((U \ {b}) ∪ {a}),
      {
        apply OrdMor _ hbot,
        intros x hx,
        cases hx with hxUa hxb,
        cases hxUa with hxU hxa,
        {
          left,
          split,
          exact hxU,
          exact hxb,
        },
        {
          right,
          exact hxa,
        },
      },
      cases Pregeometry.Exch hExch with hb ha,
      {apply hU b hbUa hb},
      {
        apply haClU,
        apply OrdMor _ ha,
        tidy,
      },
    },
    {
      have hba : b = a := set.mem_singleton_iff.1 hbUa,
      apply haClU,
      rw hba at hbot,
      apply OrdMor _ hbot,
      simp,
    },
  end

  lemma FinCharIndep :
    Indep U ↔ (Π (F : finset Carrier), (↑F ⊆ U) → Indep (F : set Carrier)) :=
  begin
    split,
    {
      intros hU F hsub,
      apply SubIndep hU F hsub,
    },
    {
      intros hFin a haU hbot,
      have Fp := FinCharProp hbot,
      cases Fp with hFU haF,
      have hsub : ↑(FinChar hbot) ∪ {a} ⊆ U,
      {
        intros x hx,
        cases hx,
        {
          have hsub : U \ {a} ⊆ U := by simp,
          apply hsub (hFU _),
          exact hx,
        },
        {
          rw (set.mem_singleton_iff.1 hx),
          exact haU,
        },
      },
      have ha : a ∈ (FinChar hbot : set Carrier) ∪ {a} := by simp,
      have hcoe : (FinChar hbot : set Carrier) ∪ {a} = ↑(FinChar hbot ∪ {a})
        := by simp,
      rw hcoe at hsub ha,
      apply hFin (FinChar hbot ∪ {a}) hsub a ha,
      have hsub1 : (FinChar hbot : set Carrier) ⊆ ↑(FinChar hbot ∪ {a}) \ {a},
      {
        intros x hx,
        simp,
        split,
        {exact hx},
        {
          intro hxa,
          cases hFU hx with _ hr,
          apply hr,
          simpa using hxa,
        },
      },
      apply OrdMor hsub1,
      exact haF,
    },
  end

  lemma BasisBetweenAux : U ⊆ V → V ⊆ W → Indep U → Spans V W →
    ∃ (B : set Carrier) (hB : B ∈ {Y : set Carrier | U ⊆ Y ∧ Y ⊆ V ∧ Indep Y}),
    U ⊆ B ∧
    ∀ (Y : set Carrier), Y ∈ {Y : set Carrier | U ⊆ Y ∧ Y ⊆ V ∧ Indep Y} → B ⊆ Y → Y = B :=
  λ hUV hVW hIndU hSpV,
    (@zorn.zorn_subset_nonempty Carrier { Y : set Carrier | U ⊆ Y ∧ Y ⊆ V ∧ Indep Y }
      (λ c hcsub hchain hc0,
        ⟨
          -- the upper bound by taking union
          ⋃₀ c ,
          ⟨
            let hUcup : U ⊆ ⋃₀ c :=
            begin
              cases hc0 with Y hY,
              cases hcsub hY with hUY hand,
              have hYcup : Y ⊆ ⋃₀ c := λ y hy , ⟨ Y , hY , hy ⟩,
              exact set.subset.trans hUY hYcup,
            end,
            hcupV : ⋃₀ c ⊆ V :=
            begin
              intros y hy,
              cases hy with Y hY,
              cases hY with hYc hyY,
              cases hcsub hYc with _ hYV,
              cases hYV with hYV,
              exact hYV hyY,
            end,
            hcupInd : Indep (⋃₀ c) :=
            begin
              rw FinCharIndep,
              intros F hF,
              -- F finite → F ⊆ Y for some Y ∈ c
              cases zorn.fin_sub_mem_chain_of_sub_union hchain hc0 F hF with Y hY,
              cases hY with hYc hFY,
              cases hcsub hYc with _ hY,
              cases hY with _ hIndY,
              apply SubIndep hIndY _ hFY,
            end in
            -- the upper bound is in the set
            ⟨ hUcup , hcupV , hcupInd ⟩ ,
            (λ Y hY y hy, ⟨ Y , hY , hy ⟩) -- showing the maximal element is in the set
          ⟩
        ⟩
      )
      U -- give U for the set being non-empty
      ⟨ set.subset.refl _ , hUV , hIndU ⟩)

  -- not sure if it would be better to have a lemma saying maximally independent elements
  -- are bases, the meat of the name theorem

  lemma BasisBetween : U ⊆ V → V ⊆ W → Indep U → Spans V W →
    ∃ (B : set Carrier), Basis B W ∧ U ⊆ B ∧ B ⊆ V :=
  begin
    intros hUV hVW hIndU hSpV,
    have hmax := BasisBetweenAux hUV hVW hIndU hSpV,
    cases hmax with B hB,
    cases hB with hB hmax,
    cases hmax with hUB hmax,
    use B,
    split,
    split,
    { -- B spans W
      -- it suffices that B spans V
      apply SpansTrans _ hSpV,
      -- it suffices that V ⊆ Cl B
      apply SubClSpans (set.subset.trans hB.2.1 (set.subset.refl _)),
      intros x hxV,
      by_cases hxB : x ∈ B,
      {exact Closure hxB},
      {
        -- we will show that B ∪ {x} is dependent, hence giving us an element y ∈ B to
        -- exchange with x
        have hDep : ¬ Indep (B ∪ {x}),
        {
          intro hInd,
          have hBx : B ∪ {x} ∈ {Y : set Carrier | U ⊆ Y ∧ Y ⊆ V ∧ Indep Y},
          {
            split,
            {apply (@set.subset.trans _ U B (B ∪ {x}) hUB), simp,},
            split,
            {
              simp only [set.union_singleton, set.insert_subset],
              exact ⟨ hxV , hB.2.1 ⟩,
            },
            {exact hInd},
          },
          apply hxB,
          rw ← (hmax (B ∪ {x}) hBx (by simp)),
          simp,
        },
        rw NotIndep at hDep,
        cases hDep with y hy,
        cases hy with hyU hyCl,
        by_cases hxy : x = y,
        {
          -- in the case when x = y we just added x to B then removed x again
          rw ← hxy at hyCl,
          rw set.remove_insert_not_mem hxB,
          exact hyCl,
        },
        {
          -- when x ≠ y we can exchange x for y
          have hB2 : (B ∪ {x}) \ {y} = (B \ {y}) ∪ {x} := set.union_sdiff hxy,
          rw hB2 at hyCl,
          have hyB : y ∈ B,
          {
            cases hyU,
            exact hyU,
            rw set.mem_singleton_iff at hyU,
            exfalso,
            apply hxy,
            rw hyU
          },
          cases Exch hyCl with hy hyCl1,
          {
            -- as B is independent the first case is false
            exfalso,
            apply hB.2.2 y hyB hy,
          },
          {
            -- now we have just removed and added y from B
            rw set.remove_insert hyB at hyCl1,
            exact hyCl1,
          },
        },
      },
    },
    {exact hB.2.2},
    {exact ⟨ hB.1 , hB.2.1 ⟩}
  end

  lemma IndepEmpty : @Indep X ∅ :=
  begin
    intros x hx,
    cases hx,
  end

  lemma UnivSpans : @Spans X set.univ set.univ :=
  begin
    split,
    simp,
  end

  lemma HasBasis : ∃ (B : set X.Carrier), Basis B set.univ :=
  begin
    cases BasisBetween (set.empty_subset _) (set.subset_univ _) IndepEmpty UnivSpans with B hB,
    exact ⟨ B , hB.1 ⟩,
  end

  def Degree (X) : cardinal := cardinal.mk (@classical.some _ _ (@HasBasis X))

end Pregeometry
