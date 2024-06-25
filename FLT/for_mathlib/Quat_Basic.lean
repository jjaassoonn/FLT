import Mathlib.ALgebra.QuaternionBasis
import Mathlib.Tactic

suppress_compilation

namespace Quat 

variable (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)

open Quaternion Classical Matrix

def normQuat : ℍ[ℚ, a, b] →*₀ ℚ where
  toFun a := a * star a|>.re
  map_zero' := by simp only [star_zero, mul_zero, QuaternionAlgebra.zero_re]
  map_one' := by simp only [star_one, mul_one, QuaternionAlgebra.one_re]
  map_mul' x y := by 
    simp only [StarMul.star_mul]; nth_rw 1 [← mul_assoc, (mul_assoc _ _ (star y)), 
      QuaternionAlgebra.mul_star_eq_coe, mul_assoc, QuaternionAlgebra.coe_mul_eq_smul,
      mul_smul_comm, QuaternionAlgebra.smul_re, smul_eq_mul, mul_comm]

theorem invertible_iff (x : ℍ[ℚ, a, b]) : (∃ y : ℍ[ℚ, a, b], x * y = 1 ∧ y * x = 1) ↔ 
    normQuat a b x ≠ 0 := by 
  constructor 
  · intro ⟨y, h1, _⟩
    by_contra hx 
    have hxy1 : normQuat a b (x * y) = 0 := by simp only [map_mul _, hx, zero_mul]
    have : normQuat a b (x * y) = 1 := by rw [h1]; simp only [(normQuat a b).map_one]
    simp_all only [(normQuat a b).map_one , one_ne_zero]
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

-- instance IsDivisionRing (hx : ∀ (x : ℍ[ℚ, a, b]), (normQuat a b) x = 0 ↔ x = 0) : 
--     DivisionRing (ℍ[ℚ, a, b]) where
--       one_mul := one_mul
--       mul_one := mul_one
--       natCast_succ n := Nat.cast_add_one n
--       sub_eq_add_neg a b := sub_eq_add_neg a b
--       zsmul := fun z x ↦ z • x
--       add_left_neg x := neg_add_self x
--       inv x := (normQuat a b x)⁻¹ • star x
--       div := fun x y => x * ((normQuat a b y)⁻¹ • star y)
--       mul_inv_cancel x := by 
--         intro hxx; simp only [Algebra.mul_smul_comm]
--         rw [QuaternionAlgebra.mul_star_eq_coe, show (x * star x).re = normQuat a b x from rfl,
--           QuaternionAlgebra.smul_coe, 
--           inv_mul_cancel (by by_contra! hx' ; exact hxx $ (hx x).1 hx')]; rfl
--       inv_zero := by simp only [map_zero, inv_zero, star_zero, smul_zero]
--       nnqsmul := _
--       qsmul := _

--- !!Might be wrong don't try to write this
def equiv_mul_square (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0): 
    ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, u^2 * a, v^2 * b] where
  toFun x := ⟨x.1, u * x.2, v * x.3, u * v * x.4⟩
  invFun x := ⟨x.1, u⁻¹ * x.2, v⁻¹ * x.3, u⁻¹ * v⁻¹ * x.4⟩
  left_inv x := by ext <;> field_simp
  right_inv x := by ext <;> field_simp
  map_mul' x y := by ext <;> simp <;> sorry
  map_add' x y := by 
    ext <;> simp only [QuaternionAlgebra.add_re, QuaternionAlgebra.add_imI, 
      QuaternionAlgebra.add_imJ, QuaternionAlgebra.add_imK, QuaternionAlgebra.mk_add_mk]
    <;> ring
  commutes' x := by ext <;> simp 

def one_iso_matrix : ℍ[ℚ, 1, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ where
  toFun x := x.1 • 1 + x.2 • (1 - stdBasisMatrix 2 2 2) + 
    x.3 • (stdBasisMatrix 1 2 b + stdBasisMatrix 2 1 1) + 
    x.4 • (stdBasisMatrix 1 2 b - stdBasisMatrix 2 1 1)
  invFun M := ⟨(M 1 1 + M 2 2)/2, (M 1 1 - M 2 2)/2, ((M 1 2)/b + M 2 1)/2, ((M 1 2)/b - M 2 1)/2⟩ 
  left_inv x := by 
    simp only [Fin.isValue, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one, add_apply,
      smul_apply, one_apply_eq, sub_apply, Fin.reduceEq, and_self, not_false_eq_true,
      StdBasisMatrix.apply_of_ne, sub_zero, and_false, and_true, add_zero, sub_self, mul_zero,
      StdBasisMatrix.apply_same, add_sub_add_left_eq_sub, ne_eq, one_apply_ne, zero_add, zero_sub,
      mul_neg]; ext <;> ring_nf
    · nth_rw 1 [mul_assoc x.imJ, mul_inv_cancel hb, mul_one, ← mul_add]; norm_num 
      rw [mul_comm b, mul_assoc x.imK, mul_inv_cancel hb, mul_one]; ring
    · rw [mul_assoc x.imJ, mul_inv_cancel hb, mul_one, ← mul_add]; norm_num
      rw [mul_comm b, mul_assoc x.imK, mul_inv_cancel hb, mul_one]; ring
  right_inv := sorry
  map_mul' x y := by 
    simp only [QuaternionAlgebra.mul_re, one_mul, QuaternionAlgebra.mul_imI, Fin.isValue,
      QuaternionAlgebra.mul_imJ, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one,
      QuaternionAlgebra.mul_imK]; ext i j;
    sorry

  map_add' := sorry
  commutes' q := by 
    simp only [QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.coe_re,
      QuaternionAlgebra.coe_imI, Fin.isValue, zero_smul, add_zero, QuaternionAlgebra.coe_imJ,
      smul_add, QuaternionAlgebra.coe_imK]
    exact Algebra.algebraMap_eq_smul_one q|>.symm

lemma iso_to_not_div : Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) → 
    ∃(x : ℍ[ℚ, a, b]), x ≠ 0 ∧ (∀(y : ℍ[ℚ, a, b]), (y * x ≠ 1 ∨ x * y ≠ 1)) := by 
  intro ⟨hH⟩ 
  let x := hH.invFun $ stdBasisMatrix 1 1 1
  use x ; by_contra! hx ;
  have : x ≠ 0 := by 
    suffices stdBasisMatrix 1 1 1 ≠ 0 by sorry 
    intro h; rw [← Matrix.ext_iff] at h; specialize h 1 1
    simp only [StdBasisMatrix.apply_same, zero_apply, one_ne_zero] at h
  obtain ⟨y, hy1, hy2⟩ := hx this
  have : y = hH.invFun (hH.toFun y) := by simp [x]
  simp only [x] at hy1; rw [this] at hy1
  apply_fun hH at hy1
  simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe,
    AlgEquiv.symm_toEquiv_eq_symm, AlgEquiv.symm_apply_apply, Fin.isValue, _root_.map_mul,
    AlgEquiv.apply_symm_apply, _root_.map_one] at hy1
  suffices ∀(M : Matrix (Fin 2) (Fin 2) ℚ), M * stdBasisMatrix 1 1 1 ≠ 1 by tauto
  intro M ; by_contra! hM 
  rw [← Matrix.ext_iff] at hM; specialize hM 2 2 
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true,
    StdBasisMatrix.mul_right_apply_of_ne, one_apply_eq, zero_ne_one] at hM

lemma not_div_to_norm_zero : 
    (∃(x : ℍ[ℚ, a, b]), x ≠ 0 ∧ (∀(y : ℍ[ℚ, a, b]), (y * x ≠ 1 ∨ x * y ≠ 1))) → 
    (∃(x : ℍ[ℚ, a, b]), (x ≠ 0) ∧  (normQuat a b) x = 0) := by 
  intro ⟨x, ⟨hx, hy⟩⟩ 
  by_contra! hx'
  have iff_1 : ∀ (x : ℍ[ℚ, a, b]), (normQuat a b) x = 0 ↔ x = 0 := by 
    intro x; constructor
    · by_contra!; exact (hx' x this.2) this.1
    · intro hxx; simp only [hxx, map_zero]
  obtain ⟨y, hy1, hy2⟩ := non_zero_norm_iff_div a b |>.2 iff_1 x hx 
  specialize hy y ; tauto

local notation "ℚ(√"a")" => Algebra.adjoin ℚ {√a}

-- Prop 1.1.7 3 -> 4
lemma norm_zero_to_norm_in :
    (∃(x : ℍ[ℚ, a, b]), (x ≠ 0) ∧  (normQuat a b) x = 0) → 
    (∃(y : ℚ(√a)), b = Algebra.norm ℚ y) := by sorry

-- Prop 1.1.7 4 -> 1
lemma norm_in_to_iso_matrix :
    (∃(y : ℚ(√a)), b = Algebra.norm ℚ y) → 
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) := by sorry

theorem not_div_iff_iso_matrix :
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) ↔
    ∃(x : ℍ[ℚ, a, b]), x ≠ 0 ∧ (∀(y : ℍ[ℚ, a, b]), (y * x ≠ 1 ∨ x * y ≠ 1)) := by
  constructor
  · exact iso_to_not_div a b
  · sorry

end Quat
