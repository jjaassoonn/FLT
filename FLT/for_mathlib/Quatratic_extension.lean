-- import Mathlib.NumberTheory.Cyclotomic.Basic

-- #check IsCyclotomicExtension
-- #check Zsqrtd
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Associated
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Star.Unitary
variable {K: Type*} [Field K] [CharZero K]

@[ext]
structure Ksqrtd (d : K) where
  re : K
  im : K
  deriving DecidableEq

prefix:100 "K√" => Ksqrtd

namespace Ksqrtd

section

variable {d : K}
-- variable (K: Type*) [Field K] [CharZero K]
-- theorem ext : ∀ {z w : K√d}, z = w ↔ z.re = w.re ∧ z.im = w.im
--   | ⟨x, y⟩, ⟨x', y'⟩ =>
--     ⟨fun h => by injection h; constructor <;> assumption,
--      fun ⟨h₁, h₂⟩ => by congr⟩

def ofField (n : K) : K√d :=
  ⟨n, 0⟩

theorem ofField_re (n : K) : (ofField n : K√d).re = n := by aesop


theorem ofField_im (n : K) : (ofField n : K√d).im = 0 := by aesop

instance : Zero (K√d) :=
  ⟨ofField 0⟩

@[simp]
theorem zero_re : (0 : K√d).re = 0 := by aesop

@[simp]
theorem zero_im : (0 : K√d).im = 0 := by aesop

instance : Inhabited (K√d) :=
  ⟨0⟩

instance : One (K√d) :=
  ⟨ofField 1⟩

@[simp]
theorem one_re : (1 : K√d).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : K√d).im = 0 :=
  rfl

def sqrtd : K√d :=
  ⟨0, 1⟩

@[simp]
theorem sqrtd_re : (sqrtd : K√d).re = 0 :=
  rfl

@[simp]
theorem sqrtd_im : (sqrtd : K√d).im = 1 :=
  rfl

instance : Add (K√d) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
theorem add_def (x y x' y' : K) : (⟨x, y⟩ + ⟨x', y'⟩ : K√d) = ⟨x + x', y + y'⟩ := rfl

@[simp]
theorem add_re (z w : K√d) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem add_im (z w : K√d) : (z + w).im = z.im + w.im :=
  rfl

section bit
set_option linter.deprecated false

@[simp]
theorem bit0_re (z) : (bit0 z : K√d).re = bit0 z.re :=
  rfl

@[simp]
theorem bit0_im (z) : (bit0 z : K√d).im = bit0 z.im :=
  rfl

@[simp]
theorem bit1_re (z) : (bit1 z : K√d).re = bit1 z.re :=
  rfl

@[simp]
theorem bit1_im (z) : (bit1 z : K√d).im = bit0 z.im := by simp [bit1]

end bit

/-- Negation in `K√d` -/
instance : Neg (K√d) :=
  ⟨fun z => ⟨-z.1, -z.2⟩⟩

@[simp]
theorem neg_re (z : K√d) : (-z).re = -z.re :=
  rfl

@[simp]
theorem neg_im (z : K√d) : (-z).im = -z.im :=
  rfl

/-- Multiplication in `K√d` -/
instance : Mul (K√d) :=
  ⟨fun z w => ⟨z.1 * w.1 + d * z.2 * w.2, z.1 * w.2 + z.2 * w.1⟩⟩

@[simp]
theorem mul_re (z w : K√d) : (z * w).re = z.re * w.re + d * z.im * w.im :=
  rfl

@[simp]
theorem mul_im (z w : K√d) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl
-- example (x:K): K := x

-- -- x 也是 Ksqrtd K 的元素
-- example (x:K): Ksqrtd K := (x : Ksqrtd K)

-- -- 使用 simp 自动处理转换
-- example (x : K) : (x : Ksqrtd K).re = x :=
-- by simp
@[simp]
instance : CoeTC K (Ksqrtd d) :=
⟨fun x => ⟨x, 0⟩⟩
-- theorem coe_Kd_to_K : (x : K) = ↑(x : K√d) := by rfl
instance addCommGroup : AddCommGroup (K√d) := by
  refine
  { add := (· + ·)
    zero := (0 : K√d)
    sub := fun a b => a + -b
    neg := Neg.neg
    nsmul := @nsmulRec (K√d) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (K√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec (K√d) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    add_left_neg := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp]
theorem sub_re (z w : K√d) : (z - w).re = z.re - w.re := by
  exact Eq.symm (Mathlib.Tactic.Abel.unfold_sub z.re w.re (z - w).re rfl)

@[simp]
theorem sub_im (z w : K√d) : (z - w).im = z.im - w.im := by
  exact Eq.symm (Mathlib.Tactic.Abel.unfold_sub z.im w.im (z - w).im rfl)

instance addGroupWithOne : AddGroupWithOne (K√d) :=
  { Ksqrtd.addCommGroup with
    natCast := fun n => ofField n,
    intCast := fun n => ofField n,
    one := 1 }

instance commRing : CommRing (K√d) := by
  refine
  { Ksqrtd.addGroupWithOne with
    mul := (· * ·)
    npow := @npowRec (K√d) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

instance : AddMonoid (K√d) := by infer_instance

instance : Monoid (K√d) := by infer_instance

instance : CommMonoid (K√d) := by infer_instance

instance : CommSemigroup (K√d) := by infer_instance

instance : Semigroup (K√d) := by infer_instance

instance : AddCommSemigroup (K√d) := by infer_instance

instance : AddSemigroup (K√d) := by infer_instance

instance : CommSemiring (K√d) := by infer_instance

instance : Semiring (K√d) := by infer_instance

instance : Ring (K√d) := by infer_instance

instance : Distrib (K√d) := by infer_instance

instance : Star (K√d) where
  star z := ⟨z.1, -z.2⟩

instance : Algebra K (K√d) :=
{
  toFun := fun r => ⟨r, 0⟩,
  smul := fun r z => ⟨r * z.1, r * z.2⟩
  map_one' := rfl
  map_zero' := by simp_all only; apply Eq.refl
  map_add' := by intro x y; simp
  map_mul' := by intro x y; simp_all only; ext <;> simp
  commutes' := by sorry
  smul_def' := by sorry
}

-- instance : Field (K√d) := 
-- {
--   inv := fun z => ⟨z.re / (z.re ^ 2 - d * z.im ^ 2), -z.im / (z.re ^ 2 - d * z.im ^ 2)⟩,
--   div := fun z w => z * w⁻¹,
--   mul_inv_cancel := by sorry
--   inv_zero := by sorry
--   exists_pair_ne := by sorry
--   nnqsmul := by sorry
--   qsmul := by sorry
--   div_eq_mul_inv := by sorry
-- }
  -- toFun := fun r => ⟨r, 0⟩
  -- smul := fun r z => ⟨r * z.1, r * z.2⟩
@[simp]
theorem star_mk (x y : K) : star (⟨x, y⟩ : K√d) = ⟨x, -y⟩ :=
  rfl

@[simp]
theorem star_re (z : K√d) : (star z).re = z.re :=
  rfl

@[simp]
theorem star_im (z : K√d) : (star z).im = -z.im :=
  rfl

instance : StarRing (K√d) where
  star_involutive x := Ksqrtd.ext _ _ rfl (neg_neg _)
  star_mul a b := by ext <;> simp <;> ring
  star_add a b := Ksqrtd.ext _ _ rfl (neg_add _ _)

instance nontrivial : Nontrivial (K√d) :=
  ⟨⟨0, 1, (Ksqrtd.ext_iff 0 1).not.mpr (by simp)⟩⟩

@[simp]
theorem natCast_re (n : ℕ) : (n : K√d).re = n :=
  rfl

@[simp]
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : K√d).re = n :=
  rfl

@[simp]
theorem natCast_im (n : ℕ) : (n : K√d).im = 0 :=
  rfl

@[simp]
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : K√d).im = 0 :=
  rfl

theorem natCast_val (n : ℕ) : (n : K√d) = ⟨n, 0⟩ :=
  rfl

@[simp]
theorem intCast_re (n : ℤ) : (n : K√d).re = n := rfl

@[simp]
theorem intCast_im (n : ℤ ) : (n : K√d).im = 0 := rfl

theorem intCast_val (n : ℤ) : (n : K√d) = ⟨n, 0⟩ := by ext <;> simp

instance : CharZero (K√d) where cast_injective m n := by simp [Ksqrtd.ext_iff]

@[simp]
theorem ofInt_eq_intCast (n : ℤ) : (ofField n : K√d) = n := rfl

@[simp]
theorem smul_val (n x y : K) : (n : K√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by ext <;> simp

theorem smul_re (a : K) (b : K√d) : (↑a * b).re = a * b.re := by simp
-- #align zsqrtd.smul_re Zsqrtd.smul_re

theorem smul_im (a : K) (b : K√d) : (↑a * b).im = a * b.im := by simp
-- #align zsqrtd.smul_im Zsqrtd.smul_im

@[simp]
theorem muld_val (x y : K) : sqrtd (d := d) * ⟨x, y⟩ = ⟨d * y, x⟩ := by ext <;> simp
-- #align zsqrtd.muld_val Zsqrtd.muld_val

@[simp]
theorem dmuld : sqrtd (d := d) * sqrtd (d := d) = d := by ext <;> simp
-- #align zsqrtd.dmuld Zsqrtd.dmuld

@[simp]
theorem smuld_val (n x y : K) : sqrtd * (n : K√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩ := by ext <;> simp
-- #align zsqrtd.smuld_val Zsqrtd.smuld_val

theorem decompose {x y : K} : (⟨x, y⟩ : K√d) = x + sqrtd (d := d) * y := by ext <;> simp
-- #align zsqrtd.decompose Zsqrtd.decompose

theorem mul_star {x y : K} : (⟨x, y⟩ * star ⟨x, y⟩ : K√d) = x * x - d * y * y := by
  ext <;> simp [sub_eq_add_neg, mul_comm]
-- #align zsqrtd.mul_star Zsqrtd.mul_star

-- protected theorem coe_int_add (m n : K) : (↑(m + n) : K√d) = ↑m + ↑n := by aesop
  -- Int.cast_add m n
-- #align zsqrtd.coe_int_add Zsqrtd.coe_int_add

-- protected theorem coe_int_sub (m n : K) : (↑(m - n) : K√d) = ↑m - ↑n := by aesop
  -- Int.cast_sub m n
-- #align zsqrtd.coe_int_sub Zsqrtd.coe_int_sub

-- protected theorem coe_int_mul (m n : K) : (↑(m * n) : K√d) = ↑m * ↑n := by aesop
  -- Int.cast_mul m n
-- #align zsqrtd.coe_int_mul Zsqrtd.coe_int_mul

-- protected theorem coe_int_inj {m n : K} (h : (↑m : K√d) = ↑n) : m = n := by
  -- simpa using congr_arg re h
-- #align zsqrtd.coe_int_inj Zsqrtd.coe_int_inj

theorem coe_int_dvd_iff (z : K) (a : K√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp only [add_zero, intCast_re, zero_mul, mul_im, dvd_mul_right, and_self_iff,
      mul_re, mul_zero, intCast_im]
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    rw [smul_val, Ksqrtd.ext_iff]
    exact ⟨hr, hi⟩

section Norm

def norm (n : K√d) : K :=
  n.re * n.re - d * n.im * n.im

theorem norm_def (n : K√d) : n.norm = n.re * n.re - d * n.im * n.im :=
  rfl

@[simp]
theorem norm_zero : norm (0 : K√d) = 0 := by simp [norm]

@[simp]
theorem norm_one : norm (1 : K√d) = 1 := by simp [norm]

@[simp]
theorem norm_mul (n m : K√d) : norm (n * m) = norm n * norm m := by
  simp only [norm, mul_im, mul_re]
  ring

def normMonoidHom : K√d →* K where
  toFun := norm
  map_mul' := norm_mul
  map_one' := norm_one

theorem norm_eq_mul_conj (n : K√d) : (norm n : K) = n * star n := by
  ext <;> simp [norm, star, mul_comm, sub_eq_add_neg]
def inv_of_this: K√d → K√d := fun z => ⟨z.re / (z.re ^ 2 - d * z.im ^ 2), -z.im / (z.re ^ 2 - d * z.im ^ 2)⟩
instance :DivisionRing (K√d) := 
  { inv := inv_of_this,
    div := fun z w => z * (inv_of_this w),
    mul_inv_cancel := ?_
    inv_zero := ?_
    exists_pair_ne := ?_
    nnqsmul := ?_
    qsmul := ?_
    -- has_div := ?_
    div_eq_mul_inv := ?_ } 
instance : Field (K√d) := by
  rw?
-- {
--   _ := Ksqrtd.DivisionRing,
--   _ := Ksqrtd.commRing,
-- } 

end Norm

end

end Ksqrtd
