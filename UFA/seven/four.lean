import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic


theorem seven_four [NormedAddCommGroup X] (space: InnerProductSpace Complex X)(x y: X) : (space.inner x y = 0) ↔ (a: Complex) -> ‖ x+a • y‖ = ‖ x - a • y‖ := by
  constructor
  {
    intro ort_1
    intro a
    have ort_2: space.inner y x = 0 := by
      rw [<- inner_conj_symm y x, ort_1]
      simp

    rw [norm_eq_sqrt_re_inner (𝕜 := Complex) (x+a•y)]
    rw [norm_eq_sqrt_re_inner (𝕜 := Complex) (x-a•y)]
    simp only [inner_add_left,inner_add_right, inner_sub_left, inner_sub_right, ort_1, ort_2, inner_smul_left, inner_smul_right]
    simp
  }
  {
    intro ort
    by_cases x_not_zero: x = 0
    rw [x_not_zero, inner_zero_left]
    by_cases y_not_zero: y = 0
    rw [y_not_zero, inner_zero_right]

    set u := ((space.inner y x)/(space.inner y y)) • y with hu
    set o := x - u with ho

    have hyy : inner ℂ y y ≠ 0 := by
      by_contra h
      rw [inner_self_eq_zero] at h
      contradiction
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
    have ort_oy_1 : space.inner o y = 0:= by
      have h := ort_uo_1
      rw [ho, hu, inner_sub_left, inner_smul_left, starRingEnd_apply, star_div₀ (space.inner y x) (space.inner y y), <-starRingEnd_apply, inner_conj_symm (𝕜:=Complex) x y]
      rw [<- starRingEnd_apply, inner_self_conj (𝕜 := Complex) y]
      rw[div_mul_cancel₀ (space.inner x y) hyy]
      simp
    have ort_oy_2 : space.inner y o = 0:= by
      rw [<- inner_conj_symm]
      simp [ort_oy_1]
      
    have x_dec : x = u+o := by 
      rw [ho]
      simp
    have ort : (a: Complex) -> ‖ x+a• y‖^2 = ‖ x-a• y‖^2 := by
      intro a
      have h := ort a
      apply_fun (fun x => x^2) at h
      exact h

    rw [x_dec, inner_add_left, ort_oy_1]
    rw [x_dec] at ort
    simp only [norm_sq_eq_re_inner (𝕜 := Complex), ] at ort

    simp only [inner_add_left,inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right ] at ort
    simp only [ort_uo_1, ort_uo_2, ort_oy_1, ort_oy_2, add_zero, zero_add] at ort
    ring_nf at ort
    have h1 := ort 1
    simp [starRingEnd_apply, star_one, one_mul] at h1
    norm_cast at h1
    have x: (inner ℂ y u).re + (inner ℂ u y).re = - (inner ℂ y u).re - (inner ℂ u y).re := by
      linarith [h1]
    have x_re : (space.inner u y).re = 0:= by
      change RCLike.re (inner ℂ y u) + RCLike.re (inner ℂ u y) = - RCLike.re (inner ℂ y u) - RCLike.re (inner ℂ u y) at x
      rw [inner_re_symm (𝕜:=Complex) y u] at x
      change RCLike.re (inner ℂ u y) = _
      linarith
    clear h1
    have h1 := ort Complex.I
    simp [Complex.conj_I, Complex.I_sq, neg_mul, mul_neg, one_mul, 
           map_add, map_sub, map_neg] at h1
    norm_cast at h1
    have x: (inner ℂ y u).im - (inner ℂ u y).im = - (inner ℂ y u).im + (inner ℂ u y).im := by
      linarith [h1]

    have x_im : (space.inner u y).im = 0:= by
      rw [<- inner_conj_symm y u] at x
      simp only [Complex.conj_im] at x
      linarith 

      -- Use ring to cancel ‖u‖², ‖o‖², ‖y‖² and Re(conj ⟨u, y⟩)

    ring
    apply Complex.ext
    simp [x_re]
    simp [x_im]

  }

