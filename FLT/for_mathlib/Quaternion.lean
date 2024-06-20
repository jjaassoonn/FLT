import Mathlib.Algebra.Quaternion -- probably get away with less
import FLT.for_mathlib.Con
import FLT.for_mathlib.CrazySimple
import FLT.for_mathlib.IsCentralSimple
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

variable (D : Type*) [DivisionRing D] [Algebra ℚ D]
variable (a b : ℚ)
instance: Field ℚ := by exact Rat.instField
instance isoiso : Module ℚ D := by exact Algebra.toModule
instance isoisoiso (h1: Module.rank ℚ D = 4): Nonempty (D ≃ₐ[ℚ] QuaternionAlgebra ℚ a b):= by sorry
instance isoisoiso1: Field (QuaternionAlgebra ℚ a b) := by sorry
instance isoisoisobala: Algebra ℚ (QuaternionAlgebra ℚ a b) := by sorry
theorem isoisoisoiso: IsCentralSimple ℚ (QuaternionAlgebra ℚ a b) := by sorry

noncomputable instance isoisoisoisoiso: Ring (TensorProduct ℚ D ℂ) := by exact Algebra.TensorProduct.instRing
noncomputable instance isoisoisoisoiso1: Algebra ℚ (TensorProduct ℚ D ℂ) := by exact
  Algebra.TensorProduct.instAlgebra
theorem isoisoisoisoisoiso:
    Nonempty ((TensorProduct ℚ D ℂ)  ≃ₐ[ℚ] (QuaternionAlgebra ℂ a b)) := by
  sorry
