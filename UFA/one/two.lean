import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
def metric (x y: Real): Real := (x-y)^2

theorem one_two: ¬∃ (m: MetricSpace Real), m.dist = metric := by
  intro h
  obtain ⟨m, hm⟩ := h
  have hh := m.dist_triangle 0 0.5 1
  rw [hm, metric, metric, metric] at hh
  norm_num at hh


