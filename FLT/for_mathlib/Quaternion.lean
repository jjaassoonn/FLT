import Mathlib.Algebra.Quaternion -- probably get away with less
import FLT.for_mathlib.IsCentralSimple

variable (D : Type) [DivisionRing D] [Algebra ℚ D] [h : IsCentralSimple ℚ D] 
    [FiniteDimensional ℚ D] (hD : FiniteDimensional.finrank ℚ D = 4)
open Quaternion TensorProduct BigOperators Classical
--instance isoisoiso (h1: Module.rank ℚ D = 4): Nonempty (D ≃ₐ[ℚ] QuaternionAlgebra ℚ a b):= by sorry

variable (α : Type*) (s : Set α)

theorem Quat_is_CSA: IsCentralSimple ℚ (ℍ[ℚ]) where
  is_central z hz := by 
    rw [@Subalgebra.mem_center_iff] at hz
    let eq2 := fun y ↦ congrArg Quaternion.imI (hz y)
    let eq3 := fun y ↦ congrArg Quaternion.imJ (hz y)
    let eq4 := fun y ↦ congrArg Quaternion.imK (hz y)
    simp only [mul_re, mul_imI, mul_imJ, mul_imK] at eq2 eq3 eq4
    simp [mul_comm] at eq2 eq3 eq4 
    specialize eq2 ⟨0,0,1,0⟩ 
    simp only [zero_mul, mul_zero, add_zero, one_mul, zero_add, sub_zero, zero_sub,
      eq_neg_self_iff] at eq2
    specialize eq3 ⟨0,0,0,1⟩ 
    simp only [zero_mul, sub_self, mul_zero, add_zero, mul_one, zero_add, zero_sub,
      eq_neg_self_iff] at eq3
    specialize eq4 ⟨0,1,0,0⟩ 
    simp only [zero_mul, one_mul, zero_add, mul_zero, sub_zero, add_zero, zero_sub,
      eq_neg_self_iff] at eq4
    refine ⟨_, id (ext z (↑z.re) rfl eq3 eq4 eq2).symm⟩ 

theorem tensor_C_is_CSA : IsCentralSimple ℂ (ℂ ⊗[ℚ] D) := IsCentralSimple.baseChange ℚ D ℂ 
 
theorem isoisoisoisoisoiso:
    Nonempty (ℂ ⊗[ℚ] D  ≃ₐ[ℂ] ℍ[ℂ]) := by
  
  sorry
