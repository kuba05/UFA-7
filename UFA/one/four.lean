import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Basic

theorem one_four (s: Real) [m: MetricSpace X] [Nonempty X]: (∃ n: MetricSpace X, (x y: X) -> n.dist x y = s + m.dist x y) <-> s = 0 := by
  constructor
  · --first direction
    intro h
    obtain ⟨n, h⟩ := h
    obtain ⟨u⟩  := (inferInstance: Nonempty X)
    have h := h u u
    rw [@dist_self X m.toPseudoMetricSpace u, @dist_self X n.toPseudoMetricSpace u] at h
    rw [h]
    simp

  · --second direction
    intro s_zero
    simp [s_zero]
    use m
    intro x y
    rfl


    
    


