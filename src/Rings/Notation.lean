import fol
open fol

prefix `x_`:max := fol.bounded_preterm.bd_var
notation `⊥` := fol.bounded_preformula.bd_falsum -- input: \bot
-- infix ` ≃ `:64 := fol.bounded_preformula.bd_equal
infixr ` ⟹ `:62 := fol.bounded_preformula.bd_imp -- input \==>
prefix `∼`:max := fol.bd_not -- input \~, the ASCII character ~ has too low precedence
infixr ` ⊓ ` := fol.bd_and -- input: \sqcap
infixr ` ⊔ ` := fol.bd_or -- input: \sqcup
infix ` ⇔ `:61 := fol.bd_biimp -- input \<=>
prefix `∀'`:40 := fol.bounded_preformula.bd_all
prefix `∃'`:40 := fol.bd_ex

-- | bd_equal {n} (t₁ t₂ : bounded_term L n) : bounded_preformula n 0
def fol.bounded_preformula.bd_notequal {L} {n} (t s : bounded_term L n) :
  fol.bounded_preformula L n 0 := ∼ (t ≃ s)
infix ` ≄ `:64 := fol.bounded_preformula.bd_notequal

