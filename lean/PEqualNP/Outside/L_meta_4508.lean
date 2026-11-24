import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4508

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

-- Gates only append wires, so the input list is a prefix of the list of wires.
theorem wires_prefix (gs : List Gate) (o : ℕ) (x : List Bool) :
    ∃ t : List Bool, (Circuit.mk gs o).wires x = x ++ t := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [Circuit.wires]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ t, ?_⟩
    have h1 : (Circuit.mk (g :: gs) o).wires x =
        (Circuit.mk gs o).wires (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl
    rw [h1, ht, List.append_assoc]

-- A circuit whose output wire is an input wire returns that input bit.
theorem eval_of_output_lt (gs : List Gate) (o : ℕ) (x : List Bool) (h : o < x.length) :
    (Circuit.mk gs o).eval x = x.getD o false := by
  obtain ⟨t, ht⟩ := wires_prefix gs o x
  show ((Circuit.mk gs o).wires x).getD o false = _
  rw [ht, List.getD_append _ _ _ _ h]

theorem length_input (N : ℕ) (X Y : Finset (Fin N)) :
    (incidenceInput X Y).length = N + N := by
  simp [incidenceInput]

-- Bit o of an incidence input, for o a point wire.
theorem input_point (N : ℕ) (X Y : Finset (Fin N)) (o : ℕ) (ho : o < N) :
    (incidenceInput X Y).getD o false = decide ((⟨o, ho⟩ : Fin N) ∈ X) := by
  unfold incidenceInput
  rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact ho)]
  rw [List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_ofFn]

-- Bit o of an incidence input, for o a line wire.
theorem input_line (N : ℕ) (X Y : Finset (Fin N)) (o : ℕ) (h1 : N ≤ o) (h2 : o < N + N) :
    (incidenceInput X Y).getD o false = decide ((⟨o - N, by omega⟩ : Fin N) ∈ Y) := by
  unfold incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; exact h1)]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]

-- If the output wire is an input wire, some incident pair leaves that wire off,
-- so the circuit cannot be right on every incident pair.
theorem contra (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1) (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (hline : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, a ∈ S l ∧ b ∈ S l)
    (hout : C.output < N + N) (hright : RightOnIncidentPairs S C) : False := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hN3 : 3 ≤ N := by omega
  obtain ⟨gs, o⟩ := C
  change o < N + N at hout
  have hcardN : 1 < Fintype.card (Fin N) := by simp only [Fintype.card_fin]; omega
  by_cases ho : o < N
  · -- the output is the wire of the point p0
    obtain ⟨p, hp⟩ := Fintype.exists_ne_of_one_lt_card hcardN (⟨o, ho⟩ : Fin N)
    obtain ⟨l, ⟨hpl, _⟩, _⟩ := hline p ⟨o, ho⟩ hp
    have h := hright l p hpl
    rw [eval_of_output_lt gs o _ (by rw [length_input]; exact hout),
      input_point N _ _ o ho] at h
    simp only [Finset.mem_singleton, decide_eq_true_eq] at h
    exact hp h.symm
  · -- the output is the wire of the line l0
    have h1 : N ≤ o := by omega
    obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card hcardN (⟨o - N, by omega⟩ : Fin N)
    have hne : (S l).Nonempty := by
      rw [← Finset.card_pos, hcard l]
      omega
    obtain ⟨p, hp⟩ := hne
    have h := hright l p hp
    rw [eval_of_output_lt gs o _ (by rw [length_input]; exact hout),
      input_line N _ _ o h1 hout] at h
    simp only [Finset.mem_singleton, decide_eq_true_eq] at h
    exact hl h.symm

end PEqualNP.Outside.L_meta_4508

theorem PEqualNP.Outside.L_meta_4508 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 + x2 + x2 ≤ x4.size + (1 : ℕ) := by
  intro q N S C hq hN hcard hline _ hout hright _
  exact (PEqualNP.Outside.L_meta_4508.contra q N S C hq hN hcard hline hout hright).elim
