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

  have hh: e = 0 ∧ k.im = 0  := by
    rw [h_decomp] at h
    repeat rw [@norm_eq_sqrt_re_inner Complex ] at h
    simp only [inner_add_right, inner_add_left, inner_smul_left, inner_smul_right, h_ortho, h_ortho2] at h
    ring_nf at h
    simp at h
    set n_x := ‖ x‖
    set n_e := ‖ e‖
    have n_x_nonneg : n_x >= 0 := norm_nonneg x
    set rk := k.re
    set ik := k.im
    have k_sq: Complex.normSq k = rk^2 + ik^2 := by
      simp [Complex.normSq_eq_norm_sq, RCLike.norm_sq_eq_def (K := Complex), rk, ik, pow_two]
    apply_fun (fun x => x^2) aikkkkkkkkkkkkkkkkkkkkkkkkkkkkjjt h
    simp only [Real.sq_sqrt', add_sq] at h
    ring_nf at h
    apply_fun (fun x => (x - max (↑n_x^2: Complex ).re 0)) at h
    ring_nf at h
    simp [←Complex.ofReal_pow, Complex.ofReal_re] at h
    ring_nf at h
    set X := n_x ^ 2 + n_x ^ 2 * rk * 2 + n_x ^ 2 * rk ^ 2 + n_x ^ 2 * ik ^ 2 + n_e ^ 2 with hX
    set Y := n_x ^ 2 * rk ^ 2 + n_x ^ 2 * ik ^ 2 + n_e ^ 2 with hY
    have hY_nonneg : 0 ≤ Y := by
      rw [hY]
      nlinarith
    rw [max_eq_left hY_nonneg, max_eq_left (sq_nonneg n_x) ] at h
    apply_fun (fun x => x- Y) at h
    apply_fun (fun x => x^2) at h
    ring_nf at h
    rw [Real.sq_sqrt hY_nonneg] at h
    by_cases hx_nonneg: X >= 0
    rw [max_eq_left hx_nonneg] at h
    repeat rw [Real.sqrt_sq n_x_nonneg] at h
    rw [hX, hY] at h
    apply_fun (fun x => x -n_x^4 * rk^2 * 4) at h
    ring_nf at h
    have h_pos1 : 0 ≤ n_x ^ 2 * n_e ^ 2 * 4 := by positivity
    have h_pos2 : 0 ≤ n_x ^ 4 * ik ^ 2 * 4 := by positivity
    symm at h
    rw [add_eq_zero_iff_of_nonneg h_pos1 h_pos2] at h
    obtain ⟨ a, b⟩ := h
    have ne_or_nx_is_zero := by simpa [mul_eq_zero, n_x_nonneg] using a
    have ik_or_n_x_is_zero := by simpa [mul_eq_zero, n_x_nonneg] using b
    --clear X Y hX hY hx_nonneg hY_nonneg
   
    constructor 
    cases ne_or_nx_is_zero with 
      | inl h =>
        dsimp[n_x] at h
        rw [norm_eq_zero] at h
        contradiction
      | inr h =>
        dsimp[n_e] at h
        rw [norm_eq_zero] at h
        exact h

    cases ik_or_n_x_is_zero with
      | inl h =>
        dsimp[n_x] at h
        rw [norm_eq_zero] at h
        contradiction
      | inr h =>
        exact h
    have a:  n_x ^ 2 + n_x ^ 2 * rk * 2 + n_x ^ 2 * rk ^ 2 + n_x ^ 2 * ik ^ 2 + n_e ^ 2  >= 0 := by
      have h_factor : n_x ^ 2 + n_x ^ 2 * rk * 2 + n_x ^ 2 * rk ^ 2 + n_x ^ 2 * ik ^ 2 + n_e ^ 2 = 
                  n_x^2 * (1 + rk)^2 + n_x^2 * ik^2 + n_e^2 := by ring
      rw[h_factor]
      positivity
    rw [<-hX] at a
    contradiction

  obtain ⟨ e_zero, k_im_zero ⟩ := hh
  have k_real : k = k.re := by
    apply Complex.ext
    simp
    simp
    exact k_im_zero
  rw [e_zero] at h_decomp
  simp at h_decomp
  clear h_ortho h_ortho2 e_zero e
  have k_non_neg : k.re >= 0:= by
    rw [h_decomp] at h
    nth_rewrite 1  [<- one_smul Complex x] at h
    rw [<- add_smul] at h
    repeat rw [norm_smul] at h
    nth_rewrite 2 [← one_mul ‖x‖] at h
    rw [<- add_mul] at h
    have n_x_not_zero: ¬ ‖ x‖ = 0:= by
      rw [norm_eq_zero]
      exact x_ne_zero
    apply mul_right_cancel₀ n_x_not_zero at h

    
    rw [k_real] at h
    norm_cast at h
    repeat rw [Real.norm_eq_abs] at h 
    nth_rw 2 [<-abs_one] at h
    rw [abs_add_eq_add_abs_iff] at h
    cases h with
      | inl h =>
        rw [ge_iff_le]
        exact h.right
      | inr h =>
        linarith

  have k_pos : k.re > 0:= by
    by_cases k_zero: k.re = 0
    rw [k_real, k_zero] at h_decomp
    simp at h_decomp
    contradiction
    exact Std.lt_of_le_of_ne k_non_neg fun a => k_zero (id (Eq.symm a))
  
  use k.re
  apply And.intro
  exact k_pos 
  rw [k_real] at h_decomp
  exact h_decomp


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







