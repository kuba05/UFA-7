import Mathlib

set_option diagnostics true

theorem seven_two [NormedAddCommGroup X] (space: InnerProductSpace Complex X)(x y: X) : (space.inner x y = 0) ↔ (a: Complex) -> ‖ x+a • y‖ = ‖ x - a • y‖ := by
  constructor
  {
    sorry
    /-intro ort_1
    intro a
    have ort_2: space.inner y x = 0 := by
      rw [<- inner_conj_symm y x, ort_1]
      simp

    rw [norm_eq_sqrt_re_inner (𝕜 := Complex) (x+a•y)]
    rw [norm_eq_sqrt_re_inner (𝕜 := Complex) (x-a•y)]
    simp only [inner_add_left,inner_add_right, inner_sub_left, inner_sub_right, ort_1, ort_2, inner_smul_left, inner_smul_right]
    simp-/
  }
  {
    intro ort
    by_cases x_not_zero: x = 0
    rw [x_not_zero, inner_zero_left]
    by_cases y_not_zero: y = 0
    rw [y_not_zero, inner_zero_right]

    set u := ((space.inner y x)/(space.inner y y)) • y with hu
    set o := x - u with ho
    have ort_uo_1 : space.inner u o = 0:= by
      rw [ho, hu]
      rw [inner_sub_right, inner_smul_right, inner_smul_left, inner_smul_left, <- inner_conj_symm y x]
      set a := space.inner x y with ha
      set b := space.inner y y with hb
      have b_not_zero: ¬ b= 0:= by
        rw [hb]
        apply inner_self_ne_zero.mpr
        exact y_not_zero
      field_simp[b_not_zero]
      ring_nf
    have ort_uo_2 : space.inner o u = 0:= by
      rw [<- inner_conj_symm]
      simp [ort_uo_1]

      
    have x_dec : x = u+o := by 
      rw [ho]
      simp
    have x_norm_dec: ‖ x‖^2  = ‖u‖^2 +‖o‖^2 := by 
      rw [x_dec, norm_eq_sqrt_re_inner (𝕜:= Complex)]
      simp only [inner_add_left,inner_add_right]
      rw [ort_uo_1, ort_uo_2 ]
      simp
      rw [Complex.]


      sorry
     /- 
    simp only [norm_eq_sqrt_re_inner (𝕜 := Complex)] at ort
    simp only [inner_add_left,inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right] at ort
    simp at ort
    simp only [<- Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im] at ort
    simp at ort
    rw [x_dec] at ort

-/
    
    sorry
  }

