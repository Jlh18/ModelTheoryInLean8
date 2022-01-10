-- import data.finset
import algebra.field
import field_theory.subfield
import field_theory.intermediate_field
-- import order.zorn
-- import Rings.ToMathlib
import Rings.Pregeometry

open classical
local attribute [instance] prop_decidable

universe u


namespace intermediate_field

  variables
    (K L : Type u) [field K] [field L] [algebra K L]

  @[simp] def closure : set L → subfield L :=
  λ S, subfield.closure (S ∪ set.range (algebra_map K L))

  @[simp] def closure' : set L → intermediate_field K L :=
  λ S, subfield.to_intermediate_field (closure K L S)
    (λ x, subfield.subset_closure (by simp))

  @[simp] def closure_fun : set L → set L :=
  λ S, closure K L S

  variables {K L}

  lemma closure_fun_closure {U : set L} : closure_fun K L U = closure K L U := rfl

  lemma closure'_closure {U : set L} : (closure' K L U : set L) = closure K L U := rfl

  lemma subset_closure (U : set L) : U ⊆ closure_fun K L U :=
  begin
    intros _ ha,
    simp only [closure, closure_fun],
    apply subfield.subset_closure,
    left,
    exact ha,
  end

  lemma closure_mono (U V : set L) (hUV : U ⊆ V) :
    closure_fun K L U ⊆ closure_fun K L V :=
  begin
    simp only [closure, closure_fun],
    intros _ ha,
    have hUVK : U ∪ set.range (algebra_map K L) ⊆ V ∪ set.range (algebra_map K L),
    {
      intros x hx,
      cases hx,
      {left, exact hUV hx},
      {right, exact hx}
    },
    apply subfield.closure_mono hUVK ha,
  end

  lemma closure_idem (U : set L) :
    closure_fun K L (closure_fun K L U)
      = closure_fun K L U :=
  begin
    rw closure_fun_closure,
    simp only [closure],
    have h : (closure_fun K L U) ∪ set.range (algebra_map K L) = closure_fun K L U,
    {
      rw set.union_eq_self_of_subset_right,
      intros x hx,
      simp only [closure, set_like.mem_coe, closure_fun],
      apply subfield.subset_closure,
      right,
      exact hx,
    },
    rw h,
    repeat {rw closure_fun_closure},
    simp only [set_like.coe_set_eq],
    apply subfield.closure_eq (closure K L U),
  end

end intermediate_field
