import data.nat.basic

universe u

notation A `^^` n := fin n → A

structure Language (A : Type u) : Type u :=
(functions : Π n : ℕ, set ((A ^^ n) → A))
(relations : Π n : ℕ, set ((A ^^ n) → Prop))

variable A : Type u

def Language.constants (L : Language A) := L.functions 0

inductive preterm : Π n : ℕ, set ((fin n) → A)
| var {} : ∀ (k : ℕ), preterm 0
| func : ∀ {l : ℕ} (f : L.functions l), preterm l
| app : ∀ {l : ℕ} (t : preterm (l + 1)) (s : preterm 0), preterm l
export preterm
