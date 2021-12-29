-- import fol language_extension

-- open fol

-- variable {L : Language}

-- -- lemma subst_bounded_formula_rel : Π {n n' n''}
-- --   (s : bounded_term L n') (R : L.relations n'')
-- --   (h : n+(n'+1) = n''),
-- --   subst_bounded_formula (bd_rel R) s h
-- --   =
-- --   bd_rel R
-- -- | _ _ _ _ s rfl := rfl

-- -- lemma subst_bounded_formula_apprel : Π {n n' n'' l}
-- --   (f : bounded_preformula L (n'') (l+1))
-- --   (t : bounded_term L n'') (s : bounded_term L n') (h : n+n'+1 = n''),
-- --   subst_bounded_formula (bd_apprel f t) s h
-- --   =
-- --   bd_apprel (subst_bounded_formula f s h) (subst_bounded_term (cast (by rw h) t) s)
-- -- | _ _ _ _ f t s rfl := rfl



-- -- lemma subst_bounded_formula_cast {ϕ} :
--   -- bounded_preformula.cast _ (subst_bounded_formula ϕ s h)


-- -- lemma bounded_preformula.cast_equal {n m} (h : n ≤ m) {t₁ t₂ : bounded_term L n} :
-- --   bounded_preformula.cast h (t₁ ≃ t₂) = t₁.cast h ≃ t₂.cast h := rfl

-- -- lemma bounded_preformula.cast_rel {n m} (h : n ≤ m) {R : L.relations n} :
-- --   bounded_preformula.cast h (bd_rel R) = bd_rel R := rfl

-- -- set_option pp.all true

-- -- lemma subst0_bounded_formula_rel {n : ℕ}
-- --   (s : bounded_term L n) (R : L.relations n.succ) :
-- --   subst0_bounded_formula (bd_rel R) s = bd_rel R :=
-- -- begin
-- --   simp only [subst0_bounded_formula, bounded_preformula.cast_eq],
-- --   rw subst_bounded_formula_rel,
-- --   refl,
-- --   -- rw bounded_preformula.cast_rel,

-- -- end

-- lemma on_bounded_term_subst_bounded_term {L0 L1} {F : L0 →ᴸ L1} {c : L0.constants}
--   {n n' : ℕ} : Π {l : ℕ} {t : bounded_preterm L0 (n + n' + 1) l},
--   F.on_bounded_term (subst_bounded_term t (bd_const c)) =
--     subst_bounded_term (F.on_bounded_term t) (bd_const (F.on_function c))
-- | _ (bd_var k)     :=
-- begin
--   by_cases hkn : k.val < n,
--   { simp only [Lhom.on_bounded_term, subst_bounded_term, dif_pos hkn] },
--   { by_cases hnk : n < k.val,
--     {simp only [Lhom.on_bounded_term, subst_bounded_term, dif_neg hkn,
--       dif_pos hnk]},
--     {simpa only [Lhom.on_bounded_term, subst_bounded_term, dif_neg hkn,
--       dif_neg hnk]},},
-- end
-- | _ (bd_func f)    := rfl
-- | _ (bd_app t₁ t₂) :=
-- begin
--   simp only [Lhom.on_bounded_term, subst_bounded_term],
--   split,
--   exact on_bounded_term_subst_bounded_term,
--   exact on_bounded_term_subst_bounded_term,
-- end

-- lemma on_bounded_formula_cast {L0 L1} {F : L0 →ᴸ L1} :
--   Π {n m l} {h : n ≤ m} {ψ : bounded_preformula L0 n l},
--       F.on_bounded_formula (bounded_preformula.cast h ψ) =
--     bounded_preformula.cast h (F.on_bounded_formula ψ)
-- | _ _ _ h bd_falsum       := rfl
-- | _ _ _ h (t₁ ≃ t₂)       :=
-- by simp only [bounded_preformula.cast, Lhom.on_bounded_formula,
--     Lhom.on_bounded_term_cast, eq_self_iff_true, and_self, cast_eq]
-- | _ _ _ h (bd_rel R)      := rfl
-- | _ _ _ h (bd_apprel f t) :=
-- by simp only [bounded_preformula.cast, Lhom.on_bounded_formula,
--     Lhom.on_bounded_term_cast, @on_bounded_formula_cast _ _ _ _ f,
--     eq_self_iff_true, and_self, cast_eq]
-- | _ _ _ h (f₁ ⟹ f₂)     :=
-- by simp only [bounded_preformula.cast, Lhom.on_bounded_formula,
--     Lhom.on_bounded_term_cast, @on_bounded_formula_cast _ _ _ _ f₁,
--     @on_bounded_formula_cast _ _ _ _ f₂,
--     eq_self_iff_true, and_self, cast_eq]
-- | _ _ _ h (∀' f)          :=
-- by simp only [bounded_preformula.cast, Lhom.on_bounded_formula,
--     @on_bounded_formula_cast _ _ _ _ f]

-- lemma on_bounded_formula_subst_bounded_formula
--   {L0 L1} {F : L0 →ᴸ L1} {c : L0.constants}
--   : Π {n n' n'' l} {ψ : bounded_preformula L0 n'' l} {h : n + (n' + 1) = n''},
--   F.on_bounded_formula (subst_bounded_formula ψ (bd_const c) h) =
--   subst_bounded_formula (F.on_bounded_formula ψ) (bd_const (F.on_function c)) h
-- | _ _ _ _ bd_falsum       rfl := rfl
-- | _ _ _ _ (t₁ ≃ t₂)       rfl :=
-- by simp only [Lhom.on_bounded_formula,
--   subst_bounded_formula_term, bounded_preformula.cast_eq,
--   Lhom.on_bounded_term_cast, on_bounded_term_subst_bounded_term,
--   eq_self_iff_true, and_self, cast_eq]
-- | _ _ _ _ (bd_rel R)      rfl :=
-- by simp only [subst_bounded_formula, Lhom.on_bounded_formula]
-- | _ _ _ _ (bd_apprel f t) rfl :=
-- by simp only [subst_bounded_formula, Lhom.on_bounded_formula,
--   @on_bounded_formula_subst_bounded_formula _ _ _ _ f,
--   on_bounded_term_subst_bounded_term, eq_self_iff_true, and_self]
-- | _ _ _ _ (f₁ ⟹ f₂)     rfl :=
-- by simp only [subst_bounded_formula, Lhom.on_bounded_formula,
--   @on_bounded_formula_subst_bounded_formula _ _ _ _ f₁,
--   @on_bounded_formula_subst_bounded_formula _ _ _ _ f₂,
--   eq_self_iff_true, and_self]
-- | _ _ _ _ (∀' f)          rfl :=
-- by simp only [subst_bounded_formula, Lhom.on_bounded_formula,
--     bounded_preformula.cast_eq, on_bounded_formula_cast];
--    rw ← @on_bounded_formula_subst_bounded_formula _ _ _ _ f

-- lemma on_bounded_formula_subst0_bounded_formula
--   {L0 L1} {F : L0 →ᴸ L1} {c : L0.constants}
--   {n l} {ψ : bounded_preformula L0 (n+1) l} :
--   F.on_bounded_formula (ψ[bd_const c /0]) =
--   (F.on_bounded_formula ψ)[bd_const (F.on_function c) /0] :=
-- by simp only [subst0_bounded_formula, bounded_preformula.cast_eq,
--     on_bounded_formula_cast, on_bounded_formula_subst_bounded_formula]

-- -- lemma on_bounded_formula_subst0_bounded_formula {L0 L1} {F : L0 →ᴸ L1} {c : L0.constants}
-- --   : Π {n l} {ψ : bounded_preformula L0 (n+1) l},
-- --   F.on_bounded_formula (ψ[bd_const c /0]) =
-- --   (F.on_bounded_formula ψ)[bd_const (F.on_function c) /0]
-- -- | _ _ bd_falsum       := by simpa only [Lhom.on_bounded_formula,
-- --   subst0_bounded_formula, subst_bounded_formula_falsum]
-- -- | _ _ (t₁ ≃ t₂)       :=
-- -- begin
-- --   simp only [Lhom.on_bounded_formula, subst0_bounded_formula,
-- --     subst_bounded_formula_term, bounded_preformula.cast_eq,
-- --     bounded_preformula.cast_equal],
-- --   split,
-- --   repeat {
-- --     simp only [Lhom.on_bounded_term_cast, on_bounded_term_subst_bounded_term],
-- --     congr,
-- --     apply on_bounded_term_cast,
-- --     rw [add_assoc, nat.zero_add],
-- --   },
-- -- end
-- -- | _ l (bd_rel R)      :=
-- -- begin
-- --   simp only [Lhom.on_bounded_formula],
--   -- simp only [subst0_bounded_formula_rel],
--   -- sorry,

--   -- induction l with l hl,
--   -- sorry,
--   -- simp only [Lhom.on_bounded_formula, subst0_bounded_formula,
--   --   bounded_preformula.cast_eq],

--   -- -- set f := subst0_bounded_formula._proof_2,
--   -- rw subst_bounded_formula_rel (bd_const (F.on_function c))
--   --   (F.on_relation R) (subst0_bounded_formula._proof_2),
--   -- rw subst_bounded_formula_rel (bd_const c) R
--   --   (subst0_bounded_formula._proof_2),

--   -- set h := subst_bounded_formula_rel (bd_const c) R
--     -- (subst0_bounded_formula._proof_2) with hf,


--   --, bounded_preformula.cast_eq,
--   --  bounded_preformula.cast_rel],

--   -- rw subst_bounded_formula_rel (bd_const c) R,

-- -- end
-- -- | _ _ (bd_apprel f t) :=
-- -- begin
-- --   simp only [Lhom.on_bounded_formula, subst0_bounded_formula],
-- --   simp only [subst_bounded_formula_apprel],
-- --   -- rw on_bounded_formula_subst0_bounded_formula,
-- --   sorry
-- -- end
-- -- | _ _ (f₁ ⟹ f₂)     := sorry
-- -- | _ _ (∀' f)          := sorry
