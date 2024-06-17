import FLT.for_mathlib.IsCentralSimple

universe u v w

variable (K : Type u) [Field K]
variable (A B : Type v)[Ring A][Ring B][Algebra K A][Algebra K B]

open scoped TensorProduct BigOperators
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

noncomputable section BrauerGroup
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
(D : Type v) (div : DivisionRing D) (alg : Algebra K D)
(D' : Type v) (div' : DivisionRing D') (alg' : Algebra K D')
(isoLeft : A ≃ₐ[K] Matrix (Fin indexLeft) (Fin indexLeft) D)
(isoRight : B ≃ₐ[K] Matrix (Fin indexRight) (Fin indexRight) D')
(isobase : D ≃ₐ[K] D')

abbrev IsBrauerEquivalent (A B : CSA K) := Nonempty (BrauerEquivalence A B)

namespace IsBrauerEquivalent

def refl (A : CSA K) : IsBrauerEquivalent A A := by
   obtain ⟨n, hn, D, inst1, inst2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
   refine ⟨n, n, hn, hn, D, inst1, inst2, D, inst1, inst2, e, e, AlgEquiv.refl⟩

def hummmmmm (A : CSA K)(indexLeft indexRight : ℕ)
(indexLeft_ne_zero : indexLeft ≠ 0)
(indexRight_ne_zero : indexRight ≠ 0)
(D : Type v) (div : DivisionRing D) (alg : Algebra K D)
(D' : Type v) (div' : DivisionRing D') (alg' : Algebra K D')
(isoLeft : A ≃ₐ[K] Matrix (Fin indexLeft) (Fin indexLeft) D)
(isoRight : A ≃ₐ[K] Matrix (Fin indexRight) (Fin indexRight) D'): D ≃ₐ[K] D' := by
   have h1: Matrix (Fin indexLeft) (Fin indexLeft) D ≃ₐ[K] Matrix (Fin indexRight) (Fin indexRight) D' := by
      exact (id isoLeft.symm).trans isoRight
   sorry

def symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by
   obtain ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e1, e2, e⟩ := h
   exact ⟨m, n, hm, hn, D', inst1', inst2', D, inst1, inst2, e2, e1, e.symm⟩

def trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
      IsBrauerEquivalent A C := by 
      obtain ⟨n1A, m1B, hn1A, hm1B, D1, inst1, inst2, D'1, inst1', inst2', e1A, e2B, eAB⟩ := hAB
      obtain ⟨n2B, m2C, hn2B, hm2C, D2, inst12, inst22, D'2, inst1'2, inst2'2, e1B, e2C, eBC⟩ := hBC
      have : D'1 ≃ₐ[K] D2 := by 
         exact hummmmmm B m1B n2B hm1B hn2B D'1 inst1' inst2' D2 inst12 inst22 e2B e1B
      have : D1 ≃ₐ[K] D2 := by exact AlgEquiv.trans (R:= K) (A₁ := D1) (A₂ := D'1) (A₃ := D2) eAB this
      have : D1 ≃ₐ[K] D'2 := by exact AlgEquiv.trans (R:= K) (A₁ := D1) (A₂ := D2) (A₃ := D'2) this eBC
      exact ⟨n1A, m2C, hn1A, hm2C, D1, inst1, inst2, D'2, inst1'2, inst2'2, e1A, e2C, this⟩

theorem Braur_is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

end IsBrauerEquivalent

namespace BrauerGroup

open scoped Classical

instance Is_setoid_CSA : Setoid (CSA K) where
  r := IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.Braur_is_eqv

lemma iso_to_eqv (A B : CSA K) (h : A ≃ₐ[K] B) : IsBrauerEquivalent A B := by
  obtain ⟨n, hn, D, inst1, inst2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
  obtain ⟨m, hm, D', inst1', inst2', ⟨e'⟩⟩ := Wedderburn_Artin_algebra_version K B
  have := (Wedderburn_Artin_divisionRing_unique_algebra_version K A D D' n m hn hm e
    ((e.symm.trans h).trans e'))
  obtain ⟨iso⟩ := this
  exact ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e, e', iso⟩


instance mul (A B : CSA K) : CSA K where
  carrier := A ⊗[K] B
  is_central_simple := @tensor_CSA_is_CSA K _ A B _ _ _ _ _ A.is_central_simple B.is_central_simple
  fin_dim := Module.Finite.tensorProduct K A B

instance (A : Type) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    FiniteDimensional K Aᵐᵒᵖ := by 
      have f:= MulOpposite.opLinearEquiv K (M:= A)
      exact Module.Finite.of_surjective (R:= K) (M:= A) (N:= Aᵐᵒᵖ) f (LinearEquiv.surjective _)

instance inv(A : CSA K) : CSA K where
  carrier := Aᵐᵒᵖ
  is_central_simple := CSA_op_is_CSA K A A.is_central_simple

instance one_in (n : ℕ) (hn : n ≠ 0): CSA K where
  carrier := Matrix (Fin n) (Fin n) K
  is_central_simple := by
   haveI: Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
   exact MatrixRing.isCentralSimple K (Fin n)

instance one_in' : CSA K where
  carrier := K
  is_central_simple := {
    is_central := Subsingleton.le (Subalgebra.center K K) ⊥
    is_simple := instIsSimpleOrderRingCon_fLT K
  }

instance one_mul_in (n : ℕ) (hn : n ≠ 0) (A : CSA K) : CSA K where
  carrier := A ⊗[K] (Matrix (Fin n) (Fin n) K)
  is_central_simple := by
    haveI: Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    exact tensor_CSA_is_CSA K A (Matrix (Fin n) (Fin n) K)
      A.is_central_simple (MatrixRing.isCentralSimple K (Fin n))

instance mul_one_in (n : ℕ) (hn : n ≠ 0) (A : CSA K) : CSA K where
  carrier := (Matrix (Fin n) (Fin n) K) ⊗[K] A
  is_central_simple := by
    haveI: Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    exact tensor_CSA_is_CSA K (Matrix (Fin n) (Fin n) K) A
      (MatrixRing.isCentralSimple K (Fin n)) A.is_central_simple

-- example (A B C D : Type) [Ring A] [Ring B] [Ring C] [Ring D] [Algebra K A] [Algebra K B]
--   [Algebra K C] [Algebra K D] (hAB : A ≃ₐ[K] C) (hCD : B ≃ₐ[K] D):
--     A ⊗[K] B ⊗[K] C ≃ₐ[K] C ⊗[K] D := by sorry


lemma choose_span_of_Tensor (A B : Type*) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (x : A ⊗[K] B): ∃(I : Finset (A ⊗[K] B)) (x1 : (A ⊗[K] B) → A) (x2 : (A ⊗[K] B) → B),
    x = ∑ i in I, x1 i ⊗ₜ[K] x2 i := by 
  have mem1 : x ∈ (⊤ : Submodule K (A ⊗[K] B)) := ⟨⟩
  rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem1 
  obtain ⟨r, hr, (eq1 : ∑ i in r.support, (_ • _) = _)⟩ := mem1 
  choose a a' haa' using hr 
  replace eq1 := calc _
    x = ∑ i in r.support, r i • i := eq1.symm
    _ = ∑ i in r.support.attach, (r i : K) • i.1 := Finset.sum_attach _ _ |>.symm
    _ = ∑ i in r.support.attach, (r i • a i.2 ⊗ₜ a' i.2) :=
        Finset.sum_congr rfl fun i _ ↦ congr(r i.1 • $(haa' i.2)).symm
    _ = ∑ i in r.support.attach, ((r i • a i.2) ⊗ₜ a' i.2) :=
        Finset.sum_congr rfl fun i _ ↦ TensorProduct.smul_tmul' _ _ _ 
  refine ⟨r.support, fun i ↦ if h : i ∈ r.support then r i • a h else 0,
    fun i ↦ if h : i ∈ r.support then a' h else 0, eq1 ▸ ?_⟩
  conv_rhs => rw [← Finset.sum_attach]
  exact Finset.sum_congr rfl fun _ _ ↦ (by aesop)

def tensor_to_kronecker (n m : ℕ) :
    (Matrix (Fin n) (Fin n) K ⊗[K] Matrix (Fin m) (Fin m) K) →ₐ[K] 
    Matrix (Fin n∗m)(Fin n*m) (Fin  n*m) K where
  toFun x := by 
    choose I x1 x2 hx using choose_span_of_Tensor (Matrix (Fin n) (Fin n) K) (Matrix (Fin m) (Fin m) K) x
    have : Fin n × Fin m ≃ Fin (n*m) := finProdFinEquiv
    -- idea is use ∑ i in I, Matrix.kronecker (x1 i) (x2 i) but obviously 
    -- lean does not undersstand MnmK and M (Fin n × Fin m) K are the same thing.
    sorry
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry
    
def matrix_eqv (n m : ℕ): (Matrix (Fin m) (Fin m) K) ⊗[K] (Matrix (Fin n) (Fin n) K) ≃ₐ[K]
    Matrix (Fin n∗m)(Fin n*m) (Fin  n*m) K where
  toFun := by
    intro x
    --obtain ⟨⟩ := choose_span_of_Tensor (Matrix (Fin m) (Fin m) K) (Matrix (Fin n) (Fin n) K) x
    choose I x1 x2 hx using 
      choose_span_of_Tensor (Matrix (Fin m) (Fin m) K) (Matrix (Fin n) (Fin n) K) x
    
    sorry--Matrix.kronecker
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry
  commutes' := sorry

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
      Algebra.TensorProduct.congr (1 : (A ⊗[K] B) ≃ₐ[K] (A ⊗[K] B)) (kroneckerMatrixTensor n m)

def kroneckerMatrixTensor' (A B: Type v) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (n m : ℕ) :
      (Matrix (Fin n) (Fin n) A) ⊗[K] (Matrix (Fin m) (Fin m) B) ≃ₐ[K] 
      (Matrix (Fin (n*m)) (Fin (n*m)) (A ⊗[K] B)) := 
      AlgEquiv.trans (AlgEquiv.trans (AlgEquiv.trans (tensorproduct1 A B n m) 
      (tensorproduct2 A B n m)) (tensorproduct3 A B n m)) 
      (matrixEquivTensor K (A⊗[K]B) (Fin (n*m))).symm

lemma one_mul (n : ℕ) (hn : n ≠ 0) (A : CSA K) :
    IsBrauerEquivalent A (one_mul_in n hn A) := by
  obtain ⟨m, hm, D, hD1, hD2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
  unfold IsBrauerEquivalent
  suffices BrauerEquivalence A (one_mul_in n hn A) from ⟨this⟩
  unfold one_mul_in
  have hA: A ⊗[K] (Matrix (Fin n) (Fin n) K) ≃ₐ[K] Matrix (Fin n∗m)(Fin n*m) (Fin  n*m) D := by
    have h1 := Algebra.TensorProduct.congr e (AlgEquiv.refl (R := K)
      (A₁ := Matrix (Fin n) (Fin n) K))
    refine AlgEquiv.trans h1 ?_
    have h2 := Algebra.TensorProduct.congr (matrixEquivTensor K D (Fin m))
        (AlgEquiv.refl (R := K) (A₁ := Matrix (Fin n) (Fin n) K))
    refine AlgEquiv.trans h2 ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.assoc K _ _ _) ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := D))
       $ matrix_eqv n m) ?_
    exact (matrixEquivTensor K D (Fin (n * m))).symm
  exact ⟨m, (n*m), hm, Nat.mul_ne_zero hn hm, D, hD1, hD2, D, hD1, hD2, e, hA, AlgEquiv.refl⟩

lemma mul_one (n : ℕ) (hn : n ≠ 0) (A : CSA K) :
    IsBrauerEquivalent A (mul_one_in n hn A) := by
  obtain ⟨m, hm, D, hD1, hD2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
  unfold IsBrauerEquivalent
  suffices BrauerEquivalence A (mul_one_in n hn A) from ⟨this⟩
  unfold mul_one_in
  have hA: (Matrix (Fin n) (Fin n) K) ⊗[K] A ≃ₐ[K] Matrix (Fin n∗m)(Fin n*m) (Fin  n*m) D := by
    have h1 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := K)
      (A₁ := Matrix (Fin n) (Fin n) K)) e
    refine AlgEquiv.trans h1 ?_
    have h2 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := Matrix (Fin n) (Fin n) K))
      (matrixEquivTensor K D (Fin m))
    refine AlgEquiv.trans h2 ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.comm K _ _) ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.assoc K _ _ _) ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := D))
       $ matrix_eqv n m) ?_
    exact (matrixEquivTensor K D (Fin (n * m))).symm
  exact ⟨m, (n*m), hm, Nat.mul_ne_zero hn hm, D, hD1, hD2, D, hD1, hD2, e, hA, AlgEquiv.refl⟩

lemma mul_assoc (A B C : CSA K) : 
    IsBrauerEquivalent (mul (mul A B) C) (mul A (mul B C)) := 
  iso_to_eqv (K := K) _ _ $ Algebra.TensorProduct.assoc _ _ _ _

--lemma mul_inv (A : CSA K) : IsBrauerEquivalent (mul A (inv (K := K) A)) one_in' := by sorry


-- #check IsBrauerEquivalent mul(K:=K)A(inv(K:=K)A) mul (K := K) A (inv (K := K) A)  one_in'
-- This lemma keeps making funny mistakes
--lemma mul_inv (A : CSA K) : IsBrauerEquivalent one_in' (@mul K _ A (inv A)) := by sorry


def Bruaer_Group : Group (Setoid (CSA K)) := sorry


-- mul: ⊗ inv: Aᵒᵖ one: K_bar : ∀n, Mn(K)
-- A ≃ₐ[K] Mₙ(D1), Mn(D1) ⊗ Mm(D2) ≃ₐ[K] Mₙₘ(D1 ⊗ D2)
-- one_mul, mul_one, ***mul_assoc (Tensor_assoc)
-- A ≃ₐ[K] Mₙ(D), B ≃ₐ[K] Mm(D) => A ~ B

end BrauerGroup

end BrauerGroup
