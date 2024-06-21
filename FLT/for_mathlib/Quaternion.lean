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
    let eq2 := congrArg Quaternion.imI (hz ⟨0,0,1,0⟩)
    let eq3 := congrArg Quaternion.imJ (hz ⟨0,0,0,1⟩)
    let eq4 := congrArg Quaternion.imK (hz ⟨0,1,0,0⟩)
    simp only [mul_imI, zero_mul, add_zero, one_mul, zero_add, sub_zero, mul_zero, mul_one,
      zero_sub, eq_neg_self_iff, mul_imJ, sub_self, mul_imK] at eq2 eq3 eq4
    refine ⟨_, id (ext z (↑z.re) rfl eq3 eq4 eq2).symm⟩ 

theorem tensor_C_is_CSA : IsCentralSimple ℂ (ℂ ⊗[ℚ] D) := IsCentralSimple.baseChange ℚ D ℂ 
 
theorem isoisoisoisoisoiso:
    Nonempty (ℂ ⊗[ℚ] D  ≃ₐ[ℂ] ℍ[ℂ]) := by
  
  sorry
