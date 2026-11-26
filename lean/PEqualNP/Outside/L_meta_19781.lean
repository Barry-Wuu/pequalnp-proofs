import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19781 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16488339210259238520 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  refine ⟨⟨[⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [13, 20]⟩, ⟨GateOp.and, [0, 22]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [24, 19]⟩, ⟨GateOp.and, [1, 25]⟩, ⟨GateOp.or, [8, 21]⟩, ⟨GateOp.and, [2, 27]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.and, [3, 29]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.and, [4, 31]⟩, ⟨GateOp.or, [8, 20]⟩, ⟨GateOp.and, [5, 33]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [35, 19]⟩, ⟨GateOp.and, [6, 36]⟩, ⟨GateOp.or, [14, 21]⟩, ⟨GateOp.and, [7, 38]⟩, ⟨GateOp.or, [23, 26]⟩, ⟨GateOp.or, [40, 28]⟩, ⟨GateOp.or, [41, 30]⟩, ⟨GateOp.or, [42, 32]⟩, ⟨GateOp.or, [43, 34]⟩, ⟨GateOp.or, [44, 37]⟩, ⟨GateOp.or, [45, 39]⟩], 46⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
