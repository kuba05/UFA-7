import Lean -- Access the Lean 4 metaprogramming tools
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt


set_option diagnostics true

instance StarReal : StarRing Real  where
  star (A: Real) := A
  star_add (A B: Real) := by rfl
  star_involutive := by
    intros x
    simp
  star_mul := by
    intro x y
    exact mul_comm x y



class VecSpace (K:Type) (V: Type) [Field K] [AddCommGroup V] where
  smul: K -> V -> V

  SmulScalarMul (a b: K)(c: V): smul (a * b)  c = smul a (smul b c)
  SmulIdentityMul(a: V): smul (1:K) a = a
  SmulDistVecAdd (a: K)(u v: V): smul a  (u+v) = smul a u + smul a v
  SmulDistScalAdd(a b: K)(u: V): smul (a+b) (u) = smul a u + smul b u

class InnerProdSpace (K: Type) (V: Type) [Field K] [StarRing K] [AddCommGroup V] extends VecSpace K V where
  inner: V -> V -> K

  dot_symm (u v: V): inner u v = star (inner v u)
  dot_add (u v w : V) : inner (u + v) w = inner u w + inner v w
  dot_smul (c : K) (u v : V) : inner (smul c u) v = c * (inner u v)
  dot_def (u : V) : inner u u = 0 ↔ u = 0

class RealProdSpace (V: Type) [AddCommGroup V] extends InnerProdSpace Real V where
  norm: V -> Real

  norm_is_inner (a: V): norm a = Real.sqrt (inner a a)
  dot_is_nonegative (a: V): inner a a >= 0

class ComplexProdSpace (V: Type) [AddCommGroup V] extends InnerProdSpace Complex V where
  norm: V -> Real

  norm_is_inner (a: V): norm a = Real.sqrt (inner a a).re
  dot_is_nonegative (a: V): (inner a a).re >= 0

open Lean
namespace MyVectorStuff
variable (K V : Type)
variable [Field K] [StarRing K] [AddCommGroup V] [VecSpace K V]
noncomputable instance : HMul K V V where hMul := VecSpace.smul

end MyVectorStuff




axiom RealStar (x: Real): star x = x 

lemma InnerWithItselfIsReal {V}[AddCommGroup V] (Space: ComplexProdSpace V) (u: V): (Space.inner u u).re = Space.inner u u := by
  have h_conj_symm : star (Space.inner u u) = Space.inner u u := by
    symm
    exact Space.dot_symm u u
  rw[Complex.star_def] at h_conj_symm
  rw[Complex.conj_eq_iff_re] at h_conj_symm
  exact h_conj_symm

  


    
axiom CauchySwartzComplex {V}[AddCommGroup V] (Space: ComplexProdSpace V) (u v: V): Complex.normSq (Space.inner u v) <= (Space.inner u u * Space.inner v v).re 



theorem sevenOne{V}[AddCommGroup V] (x y: V) (Space: InnerProdSpace Real V): (Space.inner (x+y) (x+y)  = Space.inner x x + Space.inner y y) <-> Space.inner x y = 0 := by
  constructor
  rw [Space.dot_add]
  rw [Space.dot_symm]
  nth_rw 2 [Space.dot_symm]
  repeat rw [Space.dot_add]
  nth_rw 2 [Space.dot_symm]
  repeat rw [RealStar]
  simp [add_comm, add_assoc, add_left_cancel_iff, add_right_cancel_iff]
  ring_nf
  simp [add_comm, add_assoc, add_left_cancel_iff, add_right_cancel_iff]

  intro h
  rw [Space.dot_add]
  rw [Space.dot_symm]
  nth_rw 2 [Space.dot_symm]
  repeat rw [Space.dot_add]
  nth_rw 2 [Space.dot_symm]
  repeat rw [RealStar]
  rw [h]
  ring_nf



theorem sevenFive {V} [AddCommGroup V] (x: V) (Space: ComplexProdSpace V): ((y: V) -> Space.norm y = 1 -> Space.norm x * Space.norm x >= Complex.normSq (Space.inner x y) ) ∧ ∃ y: V, Space.norm y = 1 -> Space.norm x = Space.inner x y := by
  constructor
  intro y
  intro hy
  have cauchy := CauchySwartzComplex Space x y
  by_contra! target
  have inner_y_y: Space.inner y y = 1 := by
    rw [Space.norm_is_inner y] at hy
    have re_one: (Space.inner y y).re = 1 := by
      rw [Real.sqrt_eq_cases] at hy
      cases hy with
        | inl hA =>
            have x:= hA.left
            ring_nf at x
            symm
            exact x
        | inr hB =>
          have x:=hB.right
          apply one_ne_zero at x
          contradiction
    have co_zero:= InnerWithItselfIsReal Space y
    rw [<- co_zero]
    norm_cast at *
  have a := lt_of_lt_of_le target cauchy
  rw [inner_y_y] at a
  rw [Space.norm_is_inner] at a
  have sq {a: Real}: a*a = a^2 := by ring
  rw [sq] at a
  rw [Real.sq_sqrt] at a
  rw [mul_one] at a
  rw [lt_self_iff_false] at a
  exact a
  exact Space.dot_is_nonegative x
  use x
  intro h
  rw [h]
  rw [<- InnerWithItselfIsReal Space x]
  rw [Space.norm_is_inner] at h
  have hh (a: Real): Real.sqrt a = 1 -> a = 1 := by
    intro x
    have h_nonneg: a >= 0 := by
      by_cases hx: a < 0
      have h_contradiction: Real.sqrt a = 0 := by
        rw[Real.sqrt_eq_zero']
        exact le_of_lt hx
      rw [x] at h_contradiction
      have f := one_ne_zero h_contradiction
      contradiction
      rw [not_lt] at hx
      exact hx
    rw [<- Real.sq_sqrt h_nonneg]
    rw[x]
    ring
  symm
  have r : (Space.inner x x).re = 1 := by
    apply hh
    exact h
  simp
  exact r





  



  


  



          


        




