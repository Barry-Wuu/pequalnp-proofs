import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19644_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The ten gates. Wire i below 5 is the left vertex i, wire 5 + j is the right vertex j,
-- and gate k produces wire 10 + k. Gate 0 negates the right vertex 0, gate 1 the left
-- vertex 4, so that the fourth row and the fourth column can be handled without a
-- separate read of the two equal rows and the two equal columns.
def theGates : List Gate :=
  [ ⟨GateOp.not, [5]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.and, [13, 5]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.and, [9, 11]⟩,
    ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [17, 15]⟩, ⟨GateOp.or, [18, 16]⟩ ]

def theCircuit : Circuit := ⟨theGates, 19⟩

theorem main_proof :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧
      Represents (fun u v : Fin 5 => (3686974 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨theCircuit, ?_, ?_, ?_⟩
  · show ∀ g ∈ theGates, _
    intro g hg
    simp only [theGates, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by simp⟩
  · show theGates.length ≤ 10
    decide
  · decide

end PEqualNP.Outside.L_meta_19644_aux

theorem PEqualNP.Outside.L_meta_19644 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 10 ∧
      PEqualNP.Represents.Represents
        (fun u v : Fin 5 => (3686974 : ℕ).testBit (5 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_19644_aux.main_proof
