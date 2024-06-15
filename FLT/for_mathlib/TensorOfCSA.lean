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

def tensorproduct1 (A B: Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] (n m : ℕ):
      (Matrix (Fin n) (Fin n) A) ⊗[K] (Matrix (Fin m) (Fin m) B) ≃ₐ[K] 
      (A ⊗[K] (Matrix (Fin n) (Fin n) K)) ⊗[K] (B ⊗[K] (Matrix (Fin m) (Fin m) K)) := 
      Algebra.TensorProduct.congr (matrixEquivTensor _ _ _) (matrixEquivTensor _ _ _)

def tensorproduct2 (A B: Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] (n m : ℕ):
      (A ⊗[K] (Matrix (Fin n) (Fin n) K)) ⊗[K] (B ⊗[K] (Matrix (Fin m) (Fin m) K)) ≃ₐ[K] 
      (A ⊗[K] B) ⊗[K] (Matrix (Fin n) (Fin n) K) ⊗[K] (Matrix (Fin m) (Fin m) K) := 
      {
         TensorProduct.tensorTensorTensorComm K A 
            (Matrix (Fin n) (Fin n) K) B (Matrix (Fin m) (Fin m) K) with
         map_mul' := by 
            intros x y
            sorry
         commutes' := by aesop
      }
   
-- def tensorproduct2' (A B: Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] (n m : ℕ):
--       (A ⊗[K] (Matrix (Fin n) (Fin n) K)) ⊗[K] (B ⊗[K] (Matrix (Fin m) (Fin m) K)) ≃ₐ[K] 
--       (A ⊗[K] B) ⊗[K] (Matrix (Fin n) (Fin n) K) ⊗[K] (Matrix (Fin m) (Fin m) K) := 
--       AlgEquiv.trans (AlgEquiv.trans (Algebra.TensorProduct.assoc K (A ⊗[K] (Matrix (Fin n) (Fin n) K)) B (Matrix (Fin m) (Fin m) K)).symm
--       (Algebra.TensorProduct.congr (Algebra.TensorProduct.rightComm K K A B (Matrix (Fin n) (Fin n) K)).symm (1 : (Matrix (Fin m) (Fin m) K) ≃ₐ[K] (Matrix (Fin m) (Fin m) K)))) 
--       Algebra.TensorProduct.assoc K _ _ (A ⊗[K] B) (Matrix (Fin n) (Fin n) K) (Matrix (Fin m) (Fin m) K)

-- def tensorproduct2'' (A B: Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] (n m : ℕ):
--       (A ⊗[K] (Matrix (Fin n) (Fin n) K)) ⊗[K] (B ⊗[K] (Matrix (Fin m) (Fin m) K)) ≃ₐ[K] 
--       (A ⊗[K] B) ⊗[K] (Matrix (Fin n) (Fin n) K) ⊗[K] (Matrix (Fin m) (Fin m) K) := 
--       {
--          AlgEquiv.trans (Algebra.TensorProduct.assoc _ _ _ _)
--          Algebra.TensorProduct.congr (AlgEquiv.trans
--          (AlgEquiv.trans (Algebra.TensorProduct.assoc _ _ _ _).symm
--          Algebra.TensorProduct.congr (1 : _ ≃ₐ _) (Algebra.TensorProduct.comm _ _ _)
--          (Algebra.TensorProduct.assoc _ _ _ _))
--          (Algebra.TensorProduct.assoc _ _ _ _).symm) (1 : _ ≃ₐ _) with
--       }

def kroneckerMatrixTensor (n m : ℕ) : (Matrix (Fin n) (Fin n) K) ⊗[K] (Matrix (Fin m) (Fin m) K) ≃ₐ[K] 
      Matrix (Fin (n*m)) (Fin (n*m)) K := 
      sorry

def tensorproduct3 (A B: Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] (n m : ℕ):
      (A ⊗[K] B) ⊗[K] (Matrix (Fin n) (Fin n) K) ⊗[K] (Matrix (Fin m) (Fin m) K) ≃ₐ[K] 
      (A ⊗[K] B) ⊗[K] (Matrix (Fin (n*m)) (Fin (n*m)) K) := 
      Algebra.TensorProduct.congr (1 : (A ⊗[K] B) ≃ₐ[K] (A ⊗[K] B)) (kroneckerMatrixTensor K n m)

def kroneckerMatrixTensor' (A B: Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (n m : ℕ) :
      (Matrix (Fin n) (Fin n) A) ⊗[K] (Matrix (Fin m) (Fin m) B) ≃ₐ[K] 
      (Matrix (Fin (n*m)) (Fin (n*m)) (A ⊗[K] B)) := 
      AlgEquiv.trans (AlgEquiv.trans (AlgEquiv.trans (tensorproduct1 K A B n m) 
      (tensorproduct2 K A B n m)) (tensorproduct3 K A B n m)) 
      (matrixEquivTensor K (A⊗[K]B) (Fin (n*m))).symm
/-
## TODO:
  1. Define a Brauer equivalence relation on the set of All Central Simple
     K-Algebras, namely A ~ B if A ≃ₐ[K] Mₙ(D) and B ≃ₐ[K] Mₘ(D) for some
     m,n ∈ ℕ and D a division algebra over K.
  2. Prove the set of All Central Simple K-Algebras under this equivalence relation
     forms a group with mul := ⊗[K] and inv A := Aᵒᵖ.

-/


