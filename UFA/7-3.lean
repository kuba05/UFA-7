import Mathlib
import Mathlib.Data.Complex.Basic

set_option diagnostics true

theorem seven_three [NormedAddCommGroup X] (space: InnerProductSpace Complex X)(x y: X)(x_ne_zero: ¬ x=0)(y_ne_zero: ¬ y=0)  : ‖ x+y‖ = ‖ x‖ + ‖ y‖ <-> ∃ c: Real, c > 0 ∧ y = c • x := by
  constructor
  intro h
  
  have ⟨k, e, h_decomp, h_ortho⟩ : ∃ k : ℂ, ∃ e : X, y = k • x + e ∧ space.inner x e = 0 := by
    by_cases hP: ‖x‖ = 0
    use 0
    use y
    simp
    have x_zero: x = 0:= by
      rw [norm_eq_zero] at hP
      exact hP
    rw [x_zero]
    simp

    use (space.inner x y)/(space.inner x x)
    use (y - ((space.inner x y)/(space.inner x x)) • x)
    constructor
    simp
    rw [inner_sub_right, inner_smul_right]
    rw [div_mul_cancel₀]
    simp 
    simp [hP]


  have h_ortho2 : space.inner e x = 0 := by
    rw [inner_eq_zero_symm]
    assumption

  have hh: e = 0:= by
    rw [h_decomp] at h
    repeat rw [@norm_eq_sqrt_re_inner Complex ] at h
    simp only [inner_add_right, inner_add_left, inner_smul_left, inner_smul_right, h_ortho, h_ortho2] at h
    ring_nf at h 
    sorry
  rw [hh] at h_decomp
  simp at h_decomp
  have hhh: k = ‖ k‖  := by
    sorry
  use k.re
  have k_real : k = k.re := by
    apply Complex.ext
    simp
    simp
    rw [hhh]
    simp
  apply And.intro
  rw [hhh]
  simp
  by_contra k_zero
  rw [k_zero] at h_decomp
  simp at h_decomp
  contradiction

  rw [k_real] at h_decomp
  assumption

-- goal 2
  intro h
  obtain ⟨ c, hc⟩  := h
  have c_positive := hc.left
  have hc := hc.right
  repeat rw [hc]
  have hu : ‖ x‖  * (1+c) = ‖ x‖ + ‖ c• x‖ := by
    rw [mul_add]
    simp [norm_smul, Real.norm_of_nonneg c_positive.le, mul_comm]
  have c_plus_positive: (1+c) > 0:= by positivity
  rw [<- hu]
  rw [<- Real.norm_of_nonneg c_plus_positive.le]
  rw [mul_comm, <- norm_smul, add_smul]
  simp







