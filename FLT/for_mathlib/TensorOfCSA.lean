import FLT.for_mathlib.IsCentralSimple

universe u v w

variable (K : Type u) [Field K]
variable (A B : Type v)[Ring A][Ring B][Algebra K A][Algebra K B]

open scoped TensorProduct
theorem tensor_CSA_is_CSA [Small.{v, u} K ](hA: IsCentralSimple K A) (hB: IsCentralSimple K B):
    IsCentralSimple K (A ⊗[K] B) where
   is_central := IsCentralSimple.TensorProduct.isCentral K A B hA.is_central hB.is_central
   is_simple := by haveI := hA.is_simple; exact IsCentralSimple.TensorProduct.simple K A B

lemma CSA_op_is_CSA (hA: IsCentralSimple K A):
    IsCentralSimple K Aᵐᵒᵖ where
   is_central z hz:= by
      let z': A := z.unop
      have hz' : ∀ (x : A), x * z' = z' * x := by
         rw [Subalgebra.mem_center_iff] at hz
         intros x
         specialize hz (MulOpposite.op x)
         have z'_eq : MulOpposite.op z'= z := rfl
         rw [← z'_eq, ← MulOpposite.op_mul, ← MulOpposite.op_mul] at hz
         have : (MulOpposite.op (z' * x)).unop = (MulOpposite.op (x * z')).unop := by
            exact congrArg MulOpposite.unop hz
         have : (MulOpposite.op (z' * x)).unop = z' * x := by
            exact rfl
         simp_all only [MulOpposite.op_mul, MulOpposite.op_unop, MulOpposite.unop_mul,
         MulOpposite.unop_op, z']
      obtain ⟨k, hk⟩ := hA.is_central (show z' ∈ _ by
         simp only [Subalgebra.mem_center_iff] at hz ⊢
         exact fun b ↦ hz' b)
      use k
      exact MulOpposite.unop_inj.mp hk
   is_simple := by haveI := hA.is_simple; exact op_simple A

def tensor_self_op (hA: IsCentralSimple K A) [FiniteDimensional K A]
    (n : ℕ) (hn : n = FiniteDimensional.finrank K A):
    A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] (Matrix (Fin n) (Fin n) K) := sorry

/-
## TODO:
  1. Define a Brauer equivalence relation on the set of All Central Simple
     K-Algebras, namely A ~ B if A ≃ₐ[K] Mₙ(D) and B ≃ₐ[K] Mₘ(D) for some
     m,n ∈ ℕ and D a division algebra over K.
  2. Prove the set of All Central Simple K-Algebras under this equivalence relation
     forms a group with mul := ⊗[K] and inv A := Aᵒᵖ.

-/

structure CSA (K : Type u) [Field K] :=
  (carrier : Type v)
  [ring : Ring carrier]
  [algebra : Algebra K carrier]
  [is_central_simple : IsCentralSimple K carrier]
  [fin_dim : FiniteDimensional K carrier]

instance : CoeSort (CSA.{u, v} K) (Type v) where
  coe A := A.carrier

instance (A : CSA K) : Ring A := A.ring

instance (A : CSA K) : Algebra K A := A.algebra

instance (A : CSA K) : IsCentralSimple K A := A.is_central_simple

instance (A : CSA K) : IsSimpleOrder (RingCon A) := A.is_central_simple.is_simple

instance (A : CSA K) : FiniteDimensional K A := A.fin_dim

variable {K : Type u} [Field K]

structure BrauerEquivalence (A B : CSA.{u, v} K) :=
(indexLeft indexRight : ℕ)
(indexLeft_ne_zero : indexLeft ≠ 0)
(indexRight_ne_zero : indexRight ≠ 0)
(base : Type v) (div : DivisionRing base) (alg : Algebra K base)
(isoLeft : A ≃ₐ[K] Matrix (Fin indexLeft) (Fin indexLeft) base)
(isoRight : B ≃ₐ[K] Matrix (Fin indexRight) (Fin indexRight) base)

abbrev IsBrauerEquivalent (A B : CSA K) := Nonempty (BrauerEquivalence A B)

namespace IsBrauerEquivalent

def refl (A : CSA K) : IsBrauerEquivalent A A := by
   obtain ⟨n, hn, D, inst1, inst2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
   refine ⟨n, n, hn, hn, D, inst1, inst2, e, e⟩

def symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by
   obtain ⟨n, m, hn, hm, D, inst1, inst2, e1, e2⟩ := h
   exact ⟨m, n, hm, hn, D, inst1, inst2, e2, e1⟩

def trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
      IsBrauerEquivalent A C := sorry

end IsBrauerEquivalent
