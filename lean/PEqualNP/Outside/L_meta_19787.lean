import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19787 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15451209511025767005 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  refine ⟨⟨[⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.or, [22, 18]⟩, ⟨GateOp.and, [0, 23]⟩, ⟨GateOp.or, [13, 20]⟩, ⟨GateOp.and, [1, 25]⟩, ⟨GateOp.or, [8, 20]⟩, ⟨GateOp.and, [2, 27]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.or, [29, 19]⟩, ⟨GateOp.and, [3, 30]⟩, ⟨GateOp.or, [9, 21]⟩, ⟨GateOp.and, [4, 32]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [34, 15]⟩, ⟨GateOp.or, [35, 16]⟩, ⟨GateOp.and, [5, 36]⟩, ⟨GateOp.or, [14, 21]⟩, ⟨GateOp.and, [6, 38]⟩, ⟨GateOp.or, [10, 20]⟩, ⟨GateOp.and, [7, 40]⟩, ⟨GateOp.or, [24, 26]⟩, ⟨GateOp.or, [42, 28]⟩, ⟨GateOp.or, [43, 31]⟩, ⟨GateOp.or, [44, 33]⟩, ⟨GateOp.or, [45, 37]⟩, ⟨GateOp.or, [46, 39]⟩, ⟨GateOp.or, [47, 41]⟩], 48⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
