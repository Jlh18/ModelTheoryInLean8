import language_extension

namespace fol
namespace Lhom

universe u


variables {L L' : Language.{u}} {ϕ : L →ᴸ L'}

/-- restatement of `Lhom.reduct_all_ssatisfied` -/
def reduct_Theory_induced {S : Structure L'} {T : Theory L} (hϕ : ϕ.is_injective)
  (h : S ⊨ Theory_induced ϕ T) : S[[ϕ]] ⊨ T :=
reduct_all_ssatisfied hϕ h

namespace sum

lemma is_injective_inl : (@Lhom.sum_inl L L').is_injective :=
{ on_function := λ n x y hxy, sum.inl.inj hxy,
  on_relation := λ n x y hxy, sum.inl.inj hxy, }

lemma is_injective_inr : (@Lhom.sum_inr L L').is_injective :=
{ on_function := λ n x y hxy, sum.inr.inj hxy,
  on_relation := λ n x y hxy, sum.inr.inj hxy, }

end sum
end Lhom
end fol
