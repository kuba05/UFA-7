import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Basic

theorem one_three (s: Real) [m: MetricSpace X] [Nontrivial X]: (∃ n: MetricSpace X, (x y: X) -> n.dist x y = s * m.dist x y) <-> s > 0 := by
  constructor 
  · -- Goal 1
    intro h
    obtain ⟨n, h⟩ := h
    obtain ⟨x, y, hh⟩ := exists_pair_ne X
    have l := h x y
    have h1 : @dist X m.toDist x y > 0 := by
      rw [<- @dist_pos X m x y] at hh
      rw [gt_iff_lt]
      exact hh
    have h2 : @dist X n.toDist x y > 0 := by
      rw [<- @dist_pos X n x y] at hh
      rw [gt_iff_lt]
      exact hh
    nlinarith [l, h1, h2]
  · -- Goal 2
    intro s_pos
    let new_dist := fun (x y: X) => s * dist x y
    let n: MetricSpace X := {
      dist := new_dist
      eq_of_dist_eq_zero := by 
        simp [new_dist]
        intro x y h
        cases h with
        | inl h =>
          linarith
        | inr h =>
          exact h

      dist_self := by
        simp [new_dist]

      dist_comm := by
        simp [new_dist]
        intro x y
        left
        rw [dist_comm]

      dist_triangle := by
        simp [new_dist]
        intro x y z
        nlinarith [s_pos, @dist_triangle X m.toPseudoMetricSpace x y z]
    }
    use n
    intro x y
    rfl

