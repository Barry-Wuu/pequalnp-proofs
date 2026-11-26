import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19840 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14802692711996862330 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  refine ⟨⟨[⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [14, 18]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [17, 20]⟩, ⟨GateOp.and, [0, 22]⟩, ⟨GateOp.or, [9, 16]⟩, ⟨GateOp.or, [24, 18]⟩, ⟨GateOp.and, [1, 25]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.or, [27, 19]⟩, ⟨GateOp.and, [2, 28]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [30, 13]⟩, ⟨GateOp.or, [31, 19]⟩, ⟨GateOp.and, [3, 32]⟩, ⟨GateOp.or, [16, 21]⟩, ⟨GateOp.and, [4, 34]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.and, [5, 36]⟩, ⟨GateOp.or, [16, 20]⟩, ⟨GateOp.and, [6, 38]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.or, [40, 19]⟩, ⟨GateOp.and, [7, 41]⟩, ⟨GateOp.or, [23, 26]⟩, ⟨GateOp.or, [43, 29]⟩, ⟨GateOp.or, [44, 33]⟩, ⟨GateOp.or, [45, 35]⟩, ⟨GateOp.or, [46, 37]⟩, ⟨GateOp.or, [47, 39]⟩, ⟨GateOp.or, [48, 42]⟩], 49⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
