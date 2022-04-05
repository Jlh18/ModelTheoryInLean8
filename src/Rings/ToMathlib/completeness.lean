import completeness

namespace fol

/-- A version of compactness theorem: a theory is consistent (a.k.a satisfiable)
  if and only if it is finitely consistent -/
theorem compactness' {L} {T : Theory L} : is_consistent T ↔
  ∀ fs : finset (sentence L), ↑fs ⊆ T → is_consistent (↑fs : Theory L) :=
begin
  split,
  { rintros hT fs hfsT ⟨hbot⟩,
    exact hT ⟨sweakening hfsT hbot⟩ },
  { intros h hbot,
    rw theory_proof_compactness_iff at hbot,
    obtain ⟨ fs , hfsbot , hfsT ⟩ := hbot,
    exact h fs hfsT hfsbot },
end

end fol
