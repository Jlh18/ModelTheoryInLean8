import data.equiv.transfer_instance
import Rings.ToMathlib.algebraic_closure

namespace equiv


section instances

variables {α β : Type*} (e : α ≃ β)


-- protected def is_alg_closed [is_alg_closed β] : field α :=
-- let zero := e.has_zero, add := e.has_add, one := e.has_one, mul := e.has_mul, neg := e.has_neg,
--   sub := e.has_sub, inv := e.has_inv, div := e.has_div in
-- by resetI; apply e.injective.field _; intros; exact e.apply_symm_apply _

end instances
end equiv
