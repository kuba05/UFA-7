import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Basic

theorem one_six [m: MetricSpace X]: ∃ h: MetricSpace X, (x y: X) -> h.dist x y = m.dist x y /(1+m.dist x y) := by
  let newDist (x y: X) : ℝ := dist x y / (1 + dist x y)
  let m: MetricSpace X := {
    dist := newDist
    eq_of_dist_eq_zero := by
      intro x y
      simp [newDist]
      intro h
      cases h with
        | inl h => exact h 
        | inr h => 
          linarith [dist_nonneg (x:=x) (y:=y)]

    dist_self := by
      intro x
      dsimp [newDist]
      simp [dist_self]

    dist_comm := by
      intro x y
      dsimp [newDist]
      simp [dist_comm]

    dist_triangle := by
      intro x y z
      dsimp [newDist]
      set a := dist x z
      set b := dist x y
      set c := dist y z
      have h_tri : a ≤ b + c := dist_triangle x y z
      have ha : 0 ≤ a := dist_nonneg
      have hb : 0 ≤ b := dist_nonneg
      have hc : 0 ≤ c := dist_nonneg
      field_simp [
        add_pos_of_nonneg_of_pos ha zero_lt_one, 
        add_pos_of_nonneg_of_pos hb zero_lt_one, 
        add_pos_of_nonneg_of_pos hc zero_lt_one
      ]
      rw [<- sub_le_sub_iff_right (a*b + a*b*c+a*c)]
      ring_nf
      apply le_trans h_tri
      rw [<- sub_le_sub_iff_right (b+c)]
      ring_nf
      positivity
      



      

  }
  use m
  intro x y
  rfl
  

