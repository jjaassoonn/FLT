import Mathlib.ALgebra.QuaternionBasis

suppress_compilation

namespace Quat 

variable (a b : ℚ)

open Quaternion Classical 

def normQuat : ℍ[ℚ, a, b] →*₀ ℚ where
  toFun a := a * star a|>.re
  map_zero' := by simp only [star_zero, mul_zero, QuaternionAlgebra.zero_re]
  map_one' := by simp only [star_one, mul_one, QuaternionAlgebra.one_re]
  map_mul' x y := by 
    simp only [star_mul]; nth_rw 1 [← mul_assoc, (mul_assoc _ _ (star y)), 
      QuaternionAlgebra.mul_star_eq_coe, mul_assoc, QuaternionAlgebra.coe_mul_eq_smul,
      mul_smul_comm, QuaternionAlgebra.smul_re, smul_eq_mul, mul_comm]

theorem invertible_iff (x : ℍ[ℚ, a, b]) : (∃ y : ℍ[ℚ, a, b], x * y = 1 ∧ y * x = 1) ↔ 
    normQuat a b x ≠ 0 := by 
  constructor 
  · intro ⟨y, h1, _⟩
    by_contra hx 
    have hxy1 : normQuat a b (x * y) = 0 := by simp only [map_mul, hx, zero_mul]
    have : normQuat a b (x * y) = 1 := by rw [h1]; simp only [map_one]
    simp_all only [map_one, one_ne_zero]
  · intro hx 
    use (normQuat a b x)⁻¹ • star x ; constructor 
    · rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe]
      rw [show (x * star x).re = normQuat a b x from rfl, QuaternionAlgebra.smul_coe,
        inv_mul_cancel hx]; rfl
    · rw [Algebra.smul_mul_assoc, star_comm_self', QuaternionAlgebra.mul_star_eq_coe]
      rw [show (x * star x).re = normQuat a b x from rfl, QuaternionAlgebra.smul_coe,
        inv_mul_cancel hx]; rfl

theorem non_zero_norm_iff_div : 
    (∀(x : ℍ[ℚ, a, b]), x ≠ 0 → (∃(y : ℍ[ℚ, a, b]), y * x = 1 ∧ x * y = 1)) ↔ 
    ∀ (x : ℍ[ℚ, a, b]), (normQuat a b) x = 0 ↔ x = 0 := by 
  constructor
  · intro hD x ;constructor
    · intro hx
      by_contra! hx'
      obtain ⟨y, ⟨hy, hyy⟩⟩ := hD x hx' 
      have := invertible_iff a b x |>.1 ⟨y, ⟨hyy, hy⟩⟩ 
      exact this hx
    · intro hx; simp only [hx]; exact map_zero _
  · intro hD' x hx 
    use (normQuat a b x)⁻¹ • star x 
    constructor
    · rw [Algebra.smul_mul_assoc, star_comm_self', QuaternionAlgebra.mul_star_eq_coe]
      rw [show (x * star x).re = normQuat a b x from rfl, QuaternionAlgebra.smul_coe,
        inv_mul_cancel (by by_contra! hxx ; exact hx ((hD' x).1 hxx))]; rfl
    · rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe]
      rw [show (x * star x).re = normQuat a b x from rfl, QuaternionAlgebra.smul_coe,
        inv_mul_cancel (by by_contra! hxx ; exact hx ((hD' x).1 hxx))]; rfl

instance IsDivisionRing (hx : ∀ (x : ℍ[ℚ, a, b]), (normQuat a b) x = 0 ↔ x = 0) : 
    DivisionRing (ℍ[ℚ, a, b]) where
      one_mul := one_mul
      mul_one := mul_one
      natCast_succ n := Nat.cast_add_one n
      sub_eq_add_neg a b := sub_eq_add_neg a b
      zsmul := fun z x ↦ z • x
      add_left_neg x := neg_add_self x
      inv x := (normQuat a b x)⁻¹ • star x
      div := fun x y => x * ((normQuat a b y)⁻¹ • star y)
      mul_inv_cancel x := by 
        intro hxx; simp only [Algebra.mul_smul_comm]
        rw [QuaternionAlgebra.mul_star_eq_coe, show (x * star x).re = normQuat a b x from rfl,
          QuaternionAlgebra.smul_coe, 
          inv_mul_cancel (by by_contra! hx' ; exact hxx $ (hx x).1 hx')]; rfl
      inv_zero := by simp only [map_zero, inv_zero, star_zero, smul_zero]
      nnqsmul := _
      qsmul := _


    
      

end Quat
