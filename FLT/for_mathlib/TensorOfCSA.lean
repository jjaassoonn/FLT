import FLT.for_mathlib.IsCentralSimple
import FLT.for_mathlib.Matrixstuff

suppress_compilation
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

def tensor_op_self (hA: IsCentralSimple K A) [FiniteDimensional K A]
    (n : ℕ) (hn : n = FiniteDimensional.finrank K A):
    Aᵐᵒᵖ ⊗[K] A ≃ₐ[K] (Matrix (Fin n) (Fin n) K) :=
  (Algebra.TensorProduct.comm _ _ _).trans $ tensor_self_op _ _ hA _ hn

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
   refine ⟨n, n, hn, hn, D, inst1, inst2, D, inst1, inst2, e, e, AlgEquiv.refl ⟩

def symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by
   obtain ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e1, e2, e⟩ := h
   exact ⟨m, n, hm, hn, D', inst1', inst2', D, inst1, inst2, e2, e1, e.symm⟩

lemma iso_to_eqv (A B : CSA K) (h : A ≃ₐ[K] B) : IsBrauerEquivalent A B := by
  obtain ⟨n, hn, D, inst1, inst2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
  obtain ⟨m, hm, D', inst1', inst2', ⟨e'⟩⟩ := Wedderburn_Artin_algebra_version K B
  have := (Wedderburn_Artin_divisionRing_unique_algebra_version K D D' n m hn hm
    ((e.symm.trans h).trans e'))
  obtain ⟨iso⟩ := this
  exact ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e, e', iso⟩

def trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  obtain ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e1, e2, iso1⟩ := hAB
  obtain ⟨p, q, hp, hq, E, inst3, inst4, E', inst3', inst4', e1', e2', iso2⟩ := hBC
  obtain ⟨isoiso⟩ :=
    Wedderburn_Artin_divisionRing_unique_algebra_version K D' E m p hm hp $ e2.symm.trans e1'
  refine ⟨_, _, hn, hq, _, _, _, _, _, _, e1, e2', iso1.trans $ isoiso.trans iso2⟩

theorem Braur_is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

end IsBrauerEquivalent

namespace BrauerGroup

open scoped Classical

def matrix_eqv' (n m : ℕ): (Matrix (Fin n × Fin m) (Fin n × Fin m) K) ≃ₐ[K]
    Matrix (Fin (n * m)) (Fin (n * m)) K := Matrix.reindexAlgEquiv K finProdFinEquiv

def matrix_comp (n m : ℕ) (A : Type*) [Ring A] [Algebra K A]:
    Matrix (Fin n) (Fin n) (Matrix (Fin m) (Fin m) A) ≃ₐ[K]
    Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A) := by
  have eq1 := Matrix.swap_algHom (Fin n) (Fin m) A K
  have eq2 := Matrix.comp_algHom (Fin n) (Fin m) A K
  have eq3 := Matrix.comp_algHom (Fin m) (Fin n) A K
  -- exact eq2.trans eq1.trans eq3.symm
  sorry


theorem eqv_iff (A B : CSA K): IsBrauerEquivalent A B ↔ ∃(n m : ℕ),
    Nonempty $ Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B := by
  constructor
  · intro hAB
    obtain ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e1, e2, iso⟩ := hAB
    refine ⟨m , n, ⟨?_⟩⟩
    refine AlgEquiv.trans (e1.mapMatrix.trans iso.mapMatrix.mapMatrix) ?_
    refine AlgEquiv.trans ?_ e2.mapMatrix.symm
    exact matrix_comp (K := K) m n D'
    --refine AlgEquiv.trans iso.mapMatrix ?_
  · intro hAB
    obtain ⟨n, m, ⟨iso⟩⟩ := hAB
    obtain ⟨p, hp, D, hD1, hD2, ⟨iso1⟩⟩:= Wedderburn_Artin_algebra_version K A
    obtain ⟨q, hq, D', hD1', hD2', ⟨iso2⟩⟩:= Wedderburn_Artin_algebra_version K B

    --refine ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩⟩
    sorry



def CSA_Setoid : Setoid (CSA K) where
  r := IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.Braur_is_eqv

def mul (A B : CSA.{u, u} K) : CSA K where
  carrier := A ⊗[K] B
  is_central_simple := @tensor_CSA_is_CSA K _ A B _ _ _ _ _ A.is_central_simple B.is_central_simple
  fin_dim := Module.Finite.tensorProduct K A B

def is_fin_dim_of_mop (A : Type*) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    FiniteDimensional K Aᵐᵒᵖ := by
  have f:= MulOpposite.opLinearEquiv K (M:= A)
  exact Module.Finite.of_surjective (M:= A) (N:= Aᵐᵒᵖ) f (LinearEquiv.surjective _)

instance inv (A : CSA K) : CSA K where
  carrier := Aᵐᵒᵖ
  is_central_simple := CSA_op_is_CSA K A A.is_central_simple
  fin_dim := is_fin_dim_of_mop A

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

def matrixEquivForward (n m : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix m m K ⊗[K] Matrix n n K →ₐ[K] Matrix (m × n) (m × n) K :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProduct.lift Matrix.kroneckerBilinear)
    (fun _ _ _ _ => Matrix.mul_kronecker_mul _ _ _ _)
    (Matrix.one_kronecker_one (α := K))

open scoped Kronecker in
theorem matrixEquivForward_tmul (n m : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m m K) (N : Matrix n n K) : matrixEquivForward m n (N ⊗ₜ M) = N ⊗ₖ M := rfl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
def matrixEquivRev (n m : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix (m × n) (m × n) K →ₐ[K] Matrix m m K ⊗[K] Matrix n n K :=
  AlgHom.ofLinearMap
    (Basis.constr (S := K) (Matrix.stdBasis K _ _) fun p =>
      Matrix.stdBasisMatrix p.1.1 p.2.1 1 ⊗ₜ Matrix.stdBasisMatrix p.1.2 p.2.2 1)
    (by
      simp only [Basis.constr_apply_fintype, Basis.equivFun_apply, Fintype.sum_prod_type]

      sorry)
  sorry

def matrix_eqv (n m : ℕ): (Matrix (Fin n) (Fin n) K) ⊗[K] (Matrix (Fin m) (Fin m) K) ≃ₐ[K]
    Matrix (Fin n × Fin m) (Fin n × Fin m) K where
  toFun := matrixEquivForward (Fin m) (Fin n)
  invFun := matrixEquivRev (Fin m) (Fin n)
  left_inv := by
    intro x
    unfold matrixEquivForward matrixEquivRev
    simp only [Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply, AlgHom.ofLinearMap_apply,
      Basis.constr_apply_fintype, Basis.equivFun_apply, Fintype.sum_prod_type]

    sorry
  right_inv := sorry
  map_mul' := (matrixEquivForward (Fin m) (Fin n)).map_mul
  map_add' := (matrixEquivForward (Fin m) (Fin n)).map_add
  commutes' := (matrixEquivForward (Fin m) (Fin n)).commutes

lemma one_mul (n : ℕ) (hn : n ≠ 0) (A : CSA K) :
    IsBrauerEquivalent A (one_mul_in n hn A) := by
  obtain ⟨m, hm, D, hD1, hD2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
  unfold IsBrauerEquivalent
  suffices BrauerEquivalence A (one_mul_in n hn A) from ⟨this⟩
  unfold one_mul_in
  have hA: A ⊗[K] (Matrix (Fin n) (Fin n) K) ≃ₐ[K] Matrix (Fin $ m*n) (Fin $ m*n) D := by
    have h1 := Algebra.TensorProduct.congr e (AlgEquiv.refl (R := K)
      (A₁ := Matrix (Fin n) (Fin n) K))
    refine AlgEquiv.trans h1 ?_
    have h2 := Algebra.TensorProduct.congr (matrixEquivTensor K D (Fin m))
        (AlgEquiv.refl (R := K) (A₁ := Matrix (Fin n) (Fin n) K))
    refine AlgEquiv.trans h2 ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.assoc K _ _ _) ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := D))
       $ matrix_eqv m n) ?_
    refine AlgEquiv.trans ?_ (matrixEquivTensor K D (Fin $ m*n)).symm
    exact Algebra.TensorProduct.congr AlgEquiv.refl $ matrix_eqv' m n
  exact ⟨_, (m * n), hm, Nat.mul_ne_zero hm hn, _, _, _, _, _, _, e, hA, AlgEquiv.refl⟩

lemma mul_one (n : ℕ) (hn : n ≠ 0) (A : CSA K) :
    IsBrauerEquivalent A (mul_one_in n hn A) := by
  obtain ⟨m, hm, D, hD1, hD2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
  unfold IsBrauerEquivalent
  suffices BrauerEquivalence A (mul_one_in n hn A) from ⟨this⟩
  unfold mul_one_in
  have hA: (Matrix (Fin n) (Fin n) K) ⊗[K] A ≃ₐ[K] Matrix (Fin $ m*n) (Fin $ m*n) D := by
    have h1 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := K)
      (A₁ := Matrix (Fin n) (Fin n) K)) e
    refine AlgEquiv.trans h1 ?_
    have h2 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := Matrix (Fin n) (Fin n) K))
      (matrixEquivTensor K D (Fin m))
    refine AlgEquiv.trans h2 ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.comm K _ _) ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.assoc K _ _ _) ?_
    refine AlgEquiv.trans (Algebra.TensorProduct.congr AlgEquiv.refl $ matrix_eqv m n) ?_
    refine AlgEquiv.trans ?_ (matrixEquivTensor K D (Fin (m * n))).symm
    exact Algebra.TensorProduct.congr AlgEquiv.refl $ matrix_eqv' m n
  exact ⟨_, (m*n), hm, Nat.mul_ne_zero hm hn, _, _, _, _, _, _, e, hA, AlgEquiv.refl⟩

lemma mul_assoc (A B C : CSA K) :
    IsBrauerEquivalent (mul (mul A B) C) (mul A (mul B C)) :=
  IsBrauerEquivalent.iso_to_eqv (K := K) _ _ $ Algebra.TensorProduct.assoc _ _ _ _

lemma mul_inv (A : CSA.{u, u} K) : IsBrauerEquivalent (mul A (inv (K := K) A)) one_in' := by

  sorry

def huarongdao (A B C D : Type*) [Ring A] [Ring B] [Ring C] [Ring D] [Algebra K A]
    [Algebra K B] [Algebra K C] [Algebra K D]:
    (A ⊗[K] B) ⊗[K] C ⊗[K] D ≃ₐ[K] (A ⊗[K] C) ⊗[K] B ⊗[K] D := by
  let eq1 := Algebra.TensorProduct.congr (R := K)
    (Algebra.TensorProduct.comm K A B) $ AlgEquiv.refl (A₁ := C ⊗[K] D)
  let eq2 := Algebra.TensorProduct.assoc K B A (C ⊗[K] D)
  let eq3 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := B))
    $ Algebra.TensorProduct.assoc K A C D|>.symm
  let eq4 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := B))
    $ Algebra.TensorProduct.comm K (A ⊗[K] C) D
  let eq5 := Algebra.TensorProduct.assoc K B D (A ⊗[K] C)|>.symm
  let eq6 := Algebra.TensorProduct.comm K (B ⊗[K] D) (A ⊗[K] C)
  exact eq1.trans $ eq2.trans $ eq3.trans $ eq4.trans $ eq5.trans eq6

def kroneckerMatrixTensor' (A B: Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (n m : ℕ) :
      (Matrix (Fin n) (Fin n) A) ⊗[K] (Matrix (Fin m) (Fin m) B) ≃ₐ[K]
      (Matrix (Fin (n*m)) (Fin (n*m)) (A ⊗[K] B)) := by
    have := matrixEquivTensor K A (Fin n)
    refine AlgEquiv.trans (Algebra.TensorProduct.congr (matrixEquivTensor K A (Fin n))
      $ matrixEquivTensor K B (Fin m)) ?_
    refine AlgEquiv.trans (huarongdao _ _ _ _) ?_
    refine AlgEquiv.trans
      (Algebra.TensorProduct.congr AlgEquiv.refl $ (matrix_eqv _ _).trans $ matrix_eqv' _ _) ?_
    exact (matrixEquivTensor K (A ⊗[K] B) (Fin (n * m))).symm

def iii (D D' E E': Type*) [DivisionRing D] [DivisionRing D'] [DivisionRing E] [DivisionRing E']
    [Algebra K D] [Algebra K D'] [Algebra K E] [Algebra K E'] (e : D ≃+* D') (e' : E ≃+* E') :
    D ⊗[K] E ≃+* D' ⊗[K] E' := by
  -- have := Algebra.TensorProduct.congr e e'
  sorry


theorem eqv_tensor_eqv (A B C D : CSA K) (hAB : IsBrauerEquivalent A B) (hCD : IsBrauerEquivalent C D) :
    IsBrauerEquivalent (mul A C) (mul B D) := by
  obtain ⟨n, m, hn, hm, D1, inst1, inst2, D2, inst1', inst2', e1, e2, iso1⟩ := hAB
  obtain ⟨p, q, hp, hq, E1, inst3, inst4, E2, inst3', inst4', e1', e2', iso2⟩ := hCD
  suffices BrauerEquivalence (mul A C) (mul B D) from ⟨this⟩
  unfold mul
  --refine ⟨n*p ,m*q , Nat.mul_ne_zero hn hp, Nat.mul_ne_zero hm hq, _,_,_,_,_,_,_,_,_⟩
  sorry

abbrev BrGroup := Quotient $ CSA_Setoid (K := K)

instance Mul: Mul $ BrGroup (K := K) :=
  ⟨Quotient.lift₂ (fun A B ↦ Quotient.mk (CSA_Setoid) $ BrauerGroup.mul A B)
  (by
    simp only [Quotient.eq]
    intro A B C D hAB hCD
    change IsBrauerEquivalent _ _ at *
    exact eqv_tensor_eqv A C B D hAB hCD)⟩

theorem mul_assoc' (A B C : BrGroup (K := K)) : A * B * C = A * (B * C) := by
  sorry

instance One: One (BrGroup (K := K)) := ⟨Quotient.mk (CSA_Setoid) one_in'⟩

instance Bruaer_Group : Group (BrGroup (K := K)) where
  mul a b := a * b
  mul_assoc := mul_assoc'
  one := 1
  one_mul := sorry
  mul_one A := by
    --refine A.induction_on
    --intro A
    --change IsBrauerEquivalent _ _
    sorry
  inv := Quotient.lift (fun A ↦ Quotient.mk (CSA_Setoid) $ inv A) (by sorry)
  mul_left_inv := sorry


-- mul: ⊗ inv: Aᵒᵖ one: K_bar : ∀n, Mn(K)
-- A ≃ₐ[K] Mₙ(D1), Mn(D1) ⊗ Mm(D2) ≃ₐ[K] Mₙₘ(D1 ⊗ D2)
-- one_mul, mul_one, ***mul_assoc (Tensor_assoc)
-- A ≃ₐ[K] Mₙ(D), B ≃ₐ[K] Mm(D) => A ~ B

end BrauerGroup

end BrauerGroup
