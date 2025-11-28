import Mathlib

set_option diagnostics true

theorem seven_two [NormedAddCommGroup X] (space: InnerProductSpace Complex X)(x y: X) : ¬(x = 0) -> (‖space.inner x y‖ = ‖x‖ *‖y‖ <-> ∃ α: Complex, y = α • x) := by
  intro x_not_zero
  constructor
  intro h
  have ⟨k, e, h_decomp, h_ortho⟩ : ∃ k : ℂ, ∃ e : X, y = k • x + e ∧ space.inner x e = 0 := by
    use (space.inner x y)/(space.inner x x)
    use (y - ((space.inner x y)/(space.inner x x)) • x)
    constructor
    simp
    rw [inner_sub_right, inner_smul_right]
    rw [div_mul_cancel₀]
    simp
    simp [x_not_zero]

    
  have k_e_ortho: space.inner x ((1/k) • e) = 0 := by
    rw [inner_smul_right_eq_smul, h_ortho]
    simp
  rw [h_decomp, inner_add_right, inner_smul_right_eq_smul, h_ortho] at h
  simp at h
  have norm_x_not_zero : ¬ ‖ x‖ = 0 := by
    rw [<- norm_eq_zero] at x_not_zero
    exact x_not_zero
  by_cases h_k_zero: k=0
  rw [h_k_zero] at h
  simp at h
  cases h with
    | inl x_zero =>
        rw [<- norm_eq_zero] at x_zero
        contradiction
    | inr e_zero => 
        rw [e_zero] at h_decomp
        use k
        simp at h_decomp
        exact h_decomp
  rw [<- smul_inv_smul₀ h_k_zero e] at h 
  rw [<- smul_add] at h
  rw [norm_smul] at h
  field_simp at h
  apply_fun (· ^ 2) at h
  rw [pow_two, pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x ((1/k) • e) k_e_ortho] at h
  simp at h
  cases h with 
    | inl h_inv => 
      contradiction
    | inr h2 => 
      rw [h2] at h_decomp
      use k
      simp at h_decomp
      assumption
  -- goal 2
  rintro ⟨α, h_y_eq⟩ 
  repeat rw[h_y_eq]
  rw [norm_smul]
  rw [inner_smul_right_eq_smul]
  simp
  ring

