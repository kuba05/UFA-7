import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Basic

theorem one_five [m: MetricSpace X]: ∃ n: MetricSpace X, (x y: X) -> n.dist = min 1 m.dist := by 
  let n: MetricSpace X := {
    dist := min 1 m.dist

    dist_self := by
      simp 

    dist_comm := by
      simp [dist_comm]

    eq_of_dist_eq_zero := by
      simp 
      intro x y h
      rw [min_eq_iff] at h
      simp at h
      exact h.left

    dist_triangle := by
      simp [min_def]
      intro x y h
      split_ifs with h1 h2 h3 h4 h5
      all_goals
        try simp [dist_triangle]
        try linarith
      exact le_trans' (dist_triangle x y h) h1
      rw [not_le] at h1
      linarith [dist_nonneg (x:=y) (y:=h)]
      rw [not_le] at h1
      linarith [dist_nonneg (x:=x) (y:=y)]
  }
  use n
  intro x y
  rfl
