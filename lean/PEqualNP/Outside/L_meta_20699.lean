import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_20699 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25332736 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [4, 14]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [16, 15]⟩], 17⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
