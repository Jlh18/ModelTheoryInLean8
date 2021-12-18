import Rings.current
noncomputable theory
open AxGroth

#check finset.prod_congr


-- lemma help'' {n d : ℕ} (f : fin n → ℕ) :
--   list.index_of' f (monom_deg_le_finset n d).to_list
--   < (monom_deg_le n d).length :=
-- list.index_of'_lt_length (zero_lt_monom_deg_le_length n d)

-- lemma help' {n d : ℕ} (f : fin n → ℕ) :
--   list.index_of' f (monom_deg_le_finset n d).to_list
--   < (monom_deg_le₀ n d).length :=
-- begin
--   rw monom_deg_le₀,
--   rw list.length_map,
--   apply list.index_of'_lt_length (zero_lt_monom_deg_le_length n d),
-- end

lemma help {A : Type*} [comm_ring A] {n d : ℕ}
  {ps : poly_map_data A n} (j : fin n) (f : fin n → ℕ)
  (hf : f ∈ monom_deg_le n d) :
  (ps j).to_fun (finsupp_of_fin_dom_emb.to_fun f)
  =
  (ps ⟨j.1, j.2⟩).to_fun ((monom_deg_le₀ n d).nth_le
    (list.index_of' f (monom_deg_le_finset n d).to_list)
    (index_of_monom_deg_le₀_lt_length f)) :=
begin
  have hj : (⟨ j.1, j.2 ⟩ : fin n) = j := fin.eta j j.2,
  rw [hj],
  apply congr_arg,
  rw monom_deg_le₀_nth_le (index_of_monom_deg_le_lt_length f),
  apply congr_arg,
  simp only,
  delta monom_deg_le,
  have h := @list.index_of'_nth_le _ _
    f (monom_deg_le_finset n d).to_list hf,
  funext i,
  rw ← congr_fun h i,
  congr,
end

#check list.index_of_nth_le
