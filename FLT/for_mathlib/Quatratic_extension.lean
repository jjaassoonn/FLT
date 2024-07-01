-- import Mathlib.NumberTheory.Cyclotomic.Basic

-- #check IsCyclotomicExtension
-- #check Zsqrtd
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Associated
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Star.Unitary
variable {K: Type*} [Field K] [CharZero K]
structure Ksqrtd (d : K) where
  re : K
  im : K
  deriving DecidableEq

prefix:100 "K√" => Ksqrtd

namespace Ksqrtd

section

variable {d : K}
-- variable (K: Type*) [Field K] [CharZero K]
theorem ext : ∀ {z w : K√d}, z = w ↔ z.re = w.re ∧ z.im = w.im
  | ⟨x, y⟩, ⟨x', y'⟩ =>
    ⟨fun h => by injection h; constructor <;> assumption,
     fun ⟨h₁, h₂⟩ => by congr⟩

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
theorem add_def (x y x' y' : K) : (⟨x, y⟩ + ⟨x', y'⟩ : K√d) = ⟨x + x', y + y'⟩ :=
  rfl

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

instance addCommGroup : AddCommGroup (K√d) := by
  refine
  { add := (· + ·)
    zero := (0 : K√d)
    sub := fun a b => a + -b
    neg := Neg.neg
    zsmul := @zsmulRec (K√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
    nsmul := @nsmulRec (K√d) ⟨0⟩ ⟨(· + ·)⟩
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    add_left_neg := ?_
    add_comm := ?_ } <;>
  intros <;>
  simp [ext, add_comm, add_left_comm]
