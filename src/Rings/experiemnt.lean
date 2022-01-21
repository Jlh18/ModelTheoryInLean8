import Rings.Rings

open fol

open Rings

set_option trace.class_instances true
lemma stueifje {M : Structure ring_signature} {n : ℕ} : (n : M) = n :=
rfl

-- [class_instances] cached instance for has_add ↥M
-- @models_ring_theory_to_comm_ring.has_add M
-- [class_instances] cached instance for has_one ↥M
-- @models_ring_theory_to_comm_ring.has_one M
-- [class_instances] cached instance for has_zero ↥M
-- @models_ring_theory_to_comm_ring.has_zero M
-- [class_instances] caching instance for has_coe_t ℕ ↥M
-- @nat.cast_coe ↥M (@models_ring_theory_to_comm_ring.has_zero M) (@models_ring_theory_to_comm_ring.has_one M)
--   (@models_ring_theory_to_comm_ring.has_add M)
