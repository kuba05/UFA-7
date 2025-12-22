import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
def abs_diference_of_acrtan (a b: Real): Real := |Real.arctan a - Real.arctan b|

theorem one_one: ∃ m: MetricSpace Real, m.dist = abs_diference_of_acrtan := by
  let x : MetricSpace Real := {
    dist := abs_diference_of_acrtan

    dist_self := by
      intro h
      rw [abs_diference_of_acrtan, abs_eq_zero]
      simp
    dist_comm := by
      intro x y
      rw [abs_diference_of_acrtan, abs_diference_of_acrtan, abs_sub_comm]
    dist_triangle := by
      intro x y z
      simp [abs_diference_of_acrtan, abs_sub_le]
    eq_of_dist_eq_zero := by
      intro x y h
      rw [abs_diference_of_acrtan, abs_eq_zero, sub_eq_zero, Real.arctan_inj] at h
      exact h
  }
  use x
  rfl
