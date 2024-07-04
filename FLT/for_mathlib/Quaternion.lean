import Mathlib.Algebra.QuaternionBasis
import FLT.for_mathlib.IsCentralSimple

variable (D : Type) [Ring D] [Algebra ℚ D] [h : IsCentralSimple ℚ D]
    [FiniteDimensional ℚ D] (hD : FiniteDimensional.finrank ℚ D = 4)
open Quaternion TensorProduct BigOperators Classical
--instance isoisoiso (h1: Module.rank ℚ D = 4): Nonempty (D ≃ₐ[ℚ] QuaternionAlgebra ℚ a b):= by sorry

variable (a b : ℚ)

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

instance : FiniteDimensional ℂ (ℂ ⊗[ℚ] D) := Module.Finite.base_change ℚ ℂ D

lemma finrank_4 : FiniteDimensional.finrank ℂ (ℂ ⊗[ℚ] D) = 4 := by
  have := FiniteDimensional.finrank_tensorProduct (S := ℚ) (M := ℂ) (M' := D)
  sorry

theorem Gen_Quat_is_CSA(h1:a≠ 0)(h2:b≠ 0): IsCentralSimple ℚ (ℍ[ℚ, a, b]) where
  is_central z hz:= by
    rw [@Subalgebra.mem_center_iff] at hz
    let eq2 := congrArg Quaternion.imI (hz ⟨0,0,1,0⟩)
    let eq3 := congrArg Quaternion.imJ (hz ⟨0,0,0,1⟩)
    let eq4 := congrArg Quaternion.imK (hz ⟨0,1,0,0⟩)
    simp only [QuaternionAlgebra.mul_imI, zero_mul, add_zero, mul_one, zero_sub, mul_zero, sub_self,
      zero_add, neg_eq_self_iff, mul_eq_zero, QuaternionAlgebra.mul_imJ, sub_zero,
      QuaternionAlgebra.mul_imK, one_mul, eq_neg_self_iff] at eq2 eq3 eq4
    simp_all only [ne_eq, false_or]
    refine ⟨_, id (QuaternionAlgebra.ext z (↑z.re) rfl eq3 eq4 eq2).symm⟩
  is_simple := _

theorem isoisoisoisoisoiso:
    Nonempty (ℂ ⊗[ℚ] D  ≃ₐ[ℂ] ℍ[ℂ]) := by

  sorry

variable (K E : Type) [Field K] [Ring E] [Algebra K E] [h : IsCentralSimple K E]
    [FiniteDimensional K E] (hD : FiniteDimensional.finrank K E = 4)
  
theorem CSA_is_quat : ∃(a b : K), Nonempty (E ≃ₐ[K] ℍ[K, a, b]) := sorry
