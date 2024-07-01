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
      intro x; specialize hz (MulOpposite.op x)
      have z'_eq : MulOpposite.op z'= z := rfl
      rw [← z'_eq, ← MulOpposite.op_mul, ← MulOpposite.op_mul] at hz
      have : (MulOpposite.op (z' * x)).unop = z' * x := rfl
      simp_all only [MulOpposite.op_mul, MulOpposite.op_unop, MulOpposite.unop_mul,
          MulOpposite.unop_op, z']
    obtain ⟨k, hk⟩ := hA.is_central $ Subalgebra.mem_center_iff.mpr hz'
    exact ⟨k, MulOpposite.unop_inj.mp hk⟩
  is_simple := @op_simple A _ hA.is_simple

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
(n m : ℕ) (hn: n ≠ 0) (hm : m ≠ 0)
(iso: Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)


abbrev IsBrauerEquivalent (A B : CSA K) := Nonempty (BrauerEquivalence A B)

namespace IsBrauerEquivalent

def refl (A : CSA K) : IsBrauerEquivalent A A := ⟨⟨1, 1, one_ne_zero, one_ne_zero, AlgEquiv.refl⟩⟩

def symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by
  obtain ⟨n, m, hn, hm, iso⟩ := h
  exact ⟨⟨m, n, hm, hn, iso.symm⟩⟩

def matrix_eqv' (n m : ℕ) (A : Type*) [Ring A] [Algebra K A] :
    (Matrix (Fin n × Fin m) (Fin n × Fin m) A) ≃ₐ[K] Matrix (Fin (n * m)) (Fin (n * m)) A :=
{ Matrix.reindexLinearEquiv K A finProdFinEquiv finProdFinEquiv with
  toFun := Matrix.reindex finProdFinEquiv finProdFinEquiv
  map_mul' := fun m n ↦ by simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  commutes' := fun k ↦ by simp only [algebraMap, Algebra.toRingHom, RingHom.coe_comp,
    Function.comp_apply, Matrix.scalar_apply, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv,
    Matrix.diagonal_eq_diagonal_iff, implies_true]
}

def trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  obtain ⟨n, m, hn, hm, iso1⟩ := hAB
  obtain ⟨p, q, hp, hq, iso2⟩ := hBC
  let e1 := matrix_eqv' _ _ _ |>.symm.trans $ Matrix.comp_algHom _ _ _ _|>.symm.trans $
    iso1.mapMatrix (m := Fin p)|>.trans $ Matrix.comp_algHom _ _ _ _|>.trans $
    Matrix.swap_algHom _ _ _ _ |>.trans $ Matrix.comp_algHom _ _ _ _|>.symm.trans $
    iso2.mapMatrix.trans $ Matrix.comp_algHom _ _ _ _|>.trans $ matrix_eqv' _ _ _
  exact ⟨⟨_, _, Nat.mul_ne_zero hp hn, Nat.mul_ne_zero hm hq, e1⟩⟩

lemma iso_to_eqv (A B : CSA K) (h : A ≃ₐ[K] B) : IsBrauerEquivalent A B := by
  exact ⟨⟨_, _, one_ne_zero, one_ne_zero, h.mapMatrix (m := (Fin 1))⟩⟩

theorem Braur_is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

-- structure BrauerEquivalence' (A B : CSA.{u, v} K) :=
-- (indexLeft indexRight : ℕ)
-- (indexLeft_ne_zero : indexLeft ≠ 0)
-- (indexRight_ne_zero : indexRight ≠ 0)
-- (D : Type v) (div : DivisionRing D) (alg : Algebra K D)
-- (D' : Type v) (div' : DivisionRing D') (alg' : Algebra K D')
-- (isoLeft : A ≃ₐ[K] Matrix (Fin indexLeft) (Fin indexLeft) D)
-- (isoRight : B ≃ₐ[K] Matrix (Fin indexRight) (Fin indexRight) D')
-- (isobase : D ≃ₐ[K] D')

-- abbrev IsBrauerEquivalent' (A B : CSA K) := Nonempty (BrauerEquivalence' A B)

-- theorem iso_to_eqv' (A B : CSA K) (h : A ≃ₐ[K] B) : IsBrauerEquivalent' A B := by
--   obtain ⟨n, hn, D, inst1, inst2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
--   obtain ⟨m, hm, D', inst1', inst2', ⟨e'⟩⟩ := Wedderburn_Artin_algebra_version K B
--   have := (Wedderburn_Artin_divisionRing_unique_algebra_version K D D' n m hn hm
--     ((e.symm.trans h).trans e'))
--   obtain ⟨iso⟩ := this
--   exact ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e, e', iso⟩

-- def refl' (A : CSA K) : IsBrauerEquivalent' A A := by
--    obtain ⟨n, hn, D, inst1, inst2, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
--    refine ⟨n, n, hn, hn, D, inst1, inst2, D, inst1, inst2, e, e, AlgEquiv.refl ⟩

-- def symm' {A B : CSA K} (h : IsBrauerEquivalent' A B) : IsBrauerEquivalent' B A := by
--    obtain ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e1, e2, e⟩ := h
--    exact ⟨m, n, hm, hn, D', inst1', inst2', D, inst1, inst2, e2, e1, e.symm⟩

-- def trans' {A B C : CSA K} (hAB : IsBrauerEquivalent' A B) (hBC : IsBrauerEquivalent' B C) :
--     IsBrauerEquivalent' A C := by
--   obtain ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e1, e2, iso1⟩ := hAB
--   obtain ⟨p, q, hp, hq, E, inst3, inst4, E', inst3', inst4', e1', e2', iso2⟩ := hBC
--   obtain ⟨isoiso⟩ :=
--     Wedderburn_Artin_divisionRing_unique_algebra_version K D' E m p hm hp $ e2.symm.trans e1'
--   refine ⟨_, _, hn, hq, _, _, _, _, _, _, e1, e2', iso1.trans $ isoiso.trans iso2⟩

-- theorem Braur_is_eqv' : Equivalence (IsBrauerEquivalent' (K := K)) where
--   refl := refl'
--   symm := symm'
--   trans := trans'

end IsBrauerEquivalent

namespace BrauerGroup

open scoped Classical

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

def eqv_in (A : CSA K) (A' : Type*) [Ring A'] [Algebra K A'] (e : A ≃ₐ[K] A'): CSA K where
  carrier := A'
  is_central_simple := AlgEquiv.isCentralSimple e
  fin_dim := LinearEquiv.finiteDimensional e.toLinearEquiv

instance matrix_A (n : ℕ) (hn : n ≠ 0) (A : CSA K) : CSA K :=
  eqv_in (one_mul_in n hn A) (Matrix (Fin n) (Fin n) A) $
    by unfold one_mul_in ; exact matrixEquivTensor K A (Fin n)|>.symm

instance dim_1 (R : Type*) [Ring R] [Algebra K R]: Algebra K (Matrix (Fin 1) (Fin 1) R) where
  toFun k := Matrix.diagonal (λ _ => (Algebra.ofId K R) k)
  map_one' := by simp only [map_one, Matrix.diagonal_one]
  map_mul' := by simp only [map_mul, Matrix.diagonal_mul_diagonal, implies_true]
  map_zero' := by simp only [map_zero, Matrix.diagonal_zero]
  map_add' := by simp only [map_add, Matrix.diagonal_add, implies_true]
  commutes' r m := by ext i j; fin_cases i; fin_cases j; simp only [RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, Fin.zero_eta, Fin.isValue, Matrix.diagonal_mul,
    Matrix.mul_diagonal]; exact Algebra.commutes r (m 0 0)
  smul_def' r m := by ext i j; fin_cases i; fin_cases j; simp only [Fin.zero_eta, Fin.isValue,
    Matrix.smul_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.diagonal_mul,
    Algebra.smul_def]; rfl

def dim_one_iso (R : Type*) [Ring R] [Algebra K R]: (Matrix (Fin 1) (Fin 1) R) ≃ₐ[K] R where
  toFun m := m 0 0
  invFun r := Matrix.diagonal (λ _ => r)
  left_inv m := by ext i j; fin_cases i; fin_cases j; simp only [Fin.isValue, Fin.zero_eta,
    Matrix.diagonal_apply_eq]
  right_inv r := by simp only [Fin.isValue, Matrix.diagonal_apply_eq]
  map_mul' m n := by
    simp only [Fin.isValue, Matrix.mul_apply]
    exact Fin.sum_univ_one fun i ↦ m 0 i * n i 0
  map_add' m n := by simp only [Fin.isValue, Matrix.add_apply]
  commutes' r := by
    simp only [Fin.isValue, Algebra.algebraMap_eq_smul_one']
    rw [Matrix.smul_apply]; rfl

open IsBrauerEquivalent
-- theorem eqv_mat' (A : CSA K) (n : ℕ) (hn : n ≠ 0) : IsBrauerEquivalent' A (matrix_A _ hn A) := by
--   obtain ⟨m, hm, S, hS1, hS2, ⟨iso⟩⟩ := Wedderburn_Artin_algebra_version K A
--   let iso2 := iso.mapMatrix (m := Fin n)|>.trans $ Matrix.comp_algHom _ _ _ _|>.trans
--     $ IsBrauerEquivalent.matrix_eqv' _ _ _
--   exact ⟨⟨_, _, hm, Nat.mul_ne_zero hn hm, _, _, _, _, _, _, iso, iso2, AlgEquiv.refl⟩⟩

def matrix_comp (n m : ℕ) (A : Type*) [Ring A] [Algebra K A]:
    Matrix (Fin n) (Fin n) (Matrix (Fin m) (Fin m) A) ≃ₐ[K]
    Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A) :=
  (Matrix.comp_algHom _ _ _ _).trans $ (Matrix.swap_algHom _ _ _ _).trans
    (Matrix.comp_algHom _ _ _ _).symm

-- theorem eqv_iff (A B : CSA K) [Small.{u, u} A]: IsBrauerEquivalent A B ↔
--     IsBrauerEquivalent' A B := by
--   constructor
--   · intro hAB
--     obtain ⟨⟨n, m, hn, hm, iso⟩⟩ := hAB
--     suffices IsBrauerEquivalent' (K := K) (matrix_A _ hn A) (matrix_A _ hm B) by
--       refine IsBrauerEquivalent.trans' (eqv_mat' A n hn) $ IsBrauerEquivalent.trans' this ?_
--       exact IsBrauerEquivalent.symm' $ eqv_mat' B m hm
--     exact IsBrauerEquivalent.iso_to_eqv' (K := K) (matrix_A n hn A) (matrix_A m hm B) iso
--   · intro hAB
--     obtain ⟨n, m, hn, hm, D, inst1, inst2, D', inst1', inst2', e1, e2, iso⟩ := hAB
--     refine ⟨m , n, hm, hn, ?_⟩
--     refine (e1.mapMatrix.trans iso.mapMatrix.mapMatrix).trans $ matrix_comp _ _ _|>.trans ?_
--     exact e2.mapMatrix.symm

theorem eqv_mat (A : CSA K) (n : ℕ) (hn : n ≠ 0): IsBrauerEquivalent A (matrix_A _ hn A) := by
  refine ⟨⟨n, 1, hn, one_ne_zero, ?_⟩⟩
  unfold matrix_A one_mul_in eqv_in
  exact dim_one_iso _ |>.symm

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


def matrixEquivRev (n m : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix (m × n) (m × n) K →ₐ[K] Matrix m m K ⊗[K] Matrix n n K :=
  AlgHom.ofLinearMap
    (Basis.constr (S := K) (Matrix.stdBasis K _ _) fun p =>
      Matrix.stdBasisMatrix p.1.1 p.2.1 1 ⊗ₜ Matrix.stdBasisMatrix p.1.2 p.2.2 1)
    (by
      rw [@Basis.constr_apply_fintype, Algebra.TensorProduct.one_def]
      simp only [Basis.equivFun_apply, Fintype.sum_prod_type]
      sorry)
  sorry

def matrix_eqv (n m : ℕ): (Matrix (Fin n) (Fin n) K) ⊗[K] (Matrix (Fin m) (Fin m) K) ≃ₐ[K]
    Matrix (Fin n × Fin m) (Fin n × Fin m) K where
  toFun := matrixEquivForward (Fin m) (Fin n)
  invFun := matrixEquivRev (Fin m) (Fin n)
  left_inv := by
    intro x
    obtain ⟨I, x1, x2, hI⟩ :=
      choose_span_of_Tensor (Matrix (Fin n) (Fin n) K) (Matrix (Fin m) (Fin m) K) x
    simp only [matrixEquivRev, hI, map_sum, matrixEquivForward_tmul, AlgHom.ofLinearMap_apply,
      Basis.constr_apply_fintype, Basis.equivFun_apply, Fintype.sum_prod_type]

    sorry
  right_inv := sorry
  map_mul' := matrixEquivForward _ _|>.map_mul
  map_add' := matrixEquivForward _ _|>.map_add
  commutes' := matrixEquivForward _ _|>.commutes

lemma one_mul (n : ℕ) (hn : n ≠ 0) (A : CSA K) :
    IsBrauerEquivalent A (one_mul_in n hn A) := by sorry

lemma mul_one (n : ℕ) (hn : n ≠ 0) (A : CSA K) :
    IsBrauerEquivalent A (mul_one_in n hn A) := by sorry


lemma mul_assoc (A B C : CSA K) :
    IsBrauerEquivalent (mul (mul A B) C) (mul A (mul B C)) :=
  IsBrauerEquivalent.iso_to_eqv (K := K) _ _ $ Algebra.TensorProduct.assoc _ _ _ _

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
      (Algebra.TensorProduct.congr AlgEquiv.refl $ (matrix_eqv _ _).trans $ matrix_eqv' _ _ _) ?_
    exact (matrixEquivTensor _ _ _).symm

theorem eqv_tensor_eqv (A B C D : CSA K) (hAB : IsBrauerEquivalent A B) (hCD : IsBrauerEquivalent C D) :
    IsBrauerEquivalent (mul A C) (mul B D) := by
  unfold mul
  obtain ⟨n, m, hn, hm, e1⟩ := hAB; obtain ⟨p, q, hp, hq, e2⟩ := hCD
  let e01 := kroneckerMatrixTensor' _ _ _ _|>.symm.trans $ Algebra.TensorProduct.congr e1 e2|>.trans
    $ kroneckerMatrixTensor' _ _ _ _
  exact ⟨⟨_, _, Nat.mul_ne_zero hn hp, Nat.mul_ne_zero hm hq, e01⟩⟩

abbrev BrGroup := Quotient $ CSA_Setoid (K := K)

instance Mul: Mul $ BrGroup (K := K) :=
  ⟨Quotient.lift₂ (fun A B ↦ Quotient.mk (CSA_Setoid) $ BrauerGroup.mul A B)
  (by
    simp only [Quotient.eq]
    intro A B C D hAB hCD
    exact eqv_tensor_eqv A C B D hAB hCD)⟩

instance One: One (BrGroup (K := K)) := ⟨Quotient.mk (CSA_Setoid) one_in'⟩

theorem mul_assoc' (A B C : BrGroup (K := K)) : A * B * C = A * (B * C) := by
  induction' A using Quotient.inductionOn' with A
  induction' B using Quotient.inductionOn' with B
  induction' C using Quotient.inductionOn' with C
  apply Quotient.sound; exact mul_assoc _ _ _

lemma mul_inv (A : CSA.{u, u} K) : IsBrauerEquivalent (mul A (inv (K := K) A)) one_in' := by
  unfold mul inv one_in'
  let n := FiniteDimensional.finrank K A
  have hn : n ≠ 0 := by
    by_contra! hn
    simp only [n] at hn
    have := FiniteDimensional.finrank_pos_iff (R := K) (M := A) |>.2 $
      RingCon.instNontrivialOfIsSimpleOrder_fLT A.carrier
    omega
  have := tensor_self_op K A A.is_central_simple n rfl
  exact ⟨⟨1, n, one_ne_zero, hn, dim_one_iso _|>.trans this⟩⟩

lemma inv_mul (A : CSA.{u, u} K) : IsBrauerEquivalent (mul (inv (K := K) A) A) one_in' := by
  unfold mul inv one_in'
  let n := FiniteDimensional.finrank K A
  have hn : n ≠ 0 := by
    by_contra! hn
    simp only [n] at hn
    have := FiniteDimensional.finrank_pos_iff (R := K) (M := A) |>.2 $
      RingCon.instNontrivialOfIsSimpleOrder_fLT A.carrier
    omega
  have := tensor_op_self K A A.is_central_simple n rfl
  exact ⟨⟨1, n, one_ne_zero, hn, dim_one_iso _|>.trans this⟩⟩


lemma inv_eqv (A B: CSA K) (hAB : IsBrauerEquivalent A B):
    IsBrauerEquivalent (inv (K := K) A) (inv (K := K) B) := by
  unfold inv
  obtain ⟨n, m, hn, hm, iso⟩ := hAB
  exact ⟨⟨n, m, hn, hm, (Matrix.matrixEquivMatrixMop_algebra _ _ _).trans 
    $ (AlgEquiv.op iso).trans (Matrix.matrixEquivMatrixMop_algebra _ _ _).symm⟩⟩

instance Inv: Inv (BrGroup (K := K)) := ⟨Quotient.lift (fun A ↦ Quotient.mk (CSA_Setoid) $ inv A)
(by
  intro A B hAB
  change IsBrauerEquivalent _ _ at hAB
  simp only [Quotient.eq]; change IsBrauerEquivalent _ _
  exact inv_eqv (K := K) A B hAB)⟩

theorem mul_left_inv' (A : BrGroup (K := K)) : A⁻¹ * A = 1 := by
  induction' A using Quotient.inductionOn' with A
  change _ = Quotient.mk'' one_in'
  apply Quotient.sound ; exact inv_mul A

theorem one_mul' (A : BrGroup (K := K)) : 1 * A = A := by
  induction' A using Quotient.inductionOn' with A
  change Quotient.mk'' one_in' * _ = _ ; apply Quotient.sound
  exact (mul_one 1 one_ne_zero A).trans (iso_to_eqv _ _ (Algebra.TensorProduct.congr
    (dim_one_iso _) AlgEquiv.refl))|>.symm

theorem mul_one' (A : BrGroup (K := K)) : A * 1 = A := by
  induction' A using Quotient.inductionOn' with A
  change _ * Quotient.mk'' one_in' = _ ; apply Quotient.sound
  exact (one_mul 1 one_ne_zero A).trans (iso_to_eqv _ _ (Algebra.TensorProduct.congr
    AlgEquiv.refl (dim_one_iso _)))|>.symm

instance Bruaer_Group : Group (BrGroup (K := K)) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  mul_left_inv := mul_left_inv'

lemma Alg_closed_equiv_one [IsAlgClosed K]: ∀(A : CSA K), IsBrauerEquivalent A one_in' := by
  intro A
  obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed K A
  exact ⟨⟨1, n, one_ne_zero, hn, dim_one_iso A|>.trans iso⟩⟩

lemma Alg_closed_eq_one [IsAlgClosed K]: ∀(A : BrGroup (K := K)), A = 1 := by
  intro A ; induction' A using Quotient.inductionOn' with A
  change _ = Quotient.mk'' one_in' ; apply Quotient.sound
  change IsBrauerEquivalent _ _; exact Alg_closed_equiv_one A

instance [IsAlgClosed K]: Unique (BrGroup (K := K)) where
  default := 1
  uniq := Alg_closed_eq_one

theorem Alg_closed_Brauer_trivial [IsAlgClosed K]: (⊤ : Subgroup BrGroup) =
    (⊥ : Subgroup $ BrGroup (K := K)) :=
  Subgroup.ext fun _ => ⟨fun _ ↦ Alg_closed_eq_one _, fun _ ↦ ⟨⟩⟩

end BrauerGroup

namespace BrauerGroupHom
open BrauerGroup
variable {E : Type u} [Field E] [Algebra K E]

variable (A' B' : Type*) [Ring A'] [Ring B'] [Algebra E A']
  [Algebra E B']

def restrict (K E : Type u) [Field K] [Field E] [Algebra K E] (A' : Type*)
    [Ring A'] [Algebra E A'] := A'

instance : Ring (restrict K E A') := inferInstanceAs (Ring A')

instance is_alg' : Algebra K (restrict K E A') where
  smul k (x : A') := (Algebra.ofId K E) k • (x : A')
  toFun k := Algebra.ofId E A' ((Algebra.ofId K E) k)
  map_one' := by simp only [map_one]
  map_mul' := by simp only [map_mul, implies_true]
  map_zero' := by simp only [map_zero]
  map_add' := by simp only [map_add, implies_true]
  commutes' _ (_ : A') := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk];
    unfold restrict; exact Algebra.commutes _ _
  smul_def' k (x : A') := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    unfold restrict; exact Algebra.smul_def _ _


def iso_to_iso (h : A' ≃ₐ[E] B') : (restrict K E A') ≃ₐ[K] (restrict K E B') where
  toFun := h.toAlgHom
  invFun := h.symm.toAlgHom
  left_inv := AlgEquiv.leftInverse_symm h
  right_inv := AlgEquiv.rightInverse_symm h
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' r := by
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe];
    unfold restrict; exact h.commutes _

def rid_to_K_equiv : E ⊗[E] E ≃ₐ[K] E where
  toFun := (Algebra.TensorProduct.rid E E E)
  invFun := (Algebra.TensorProduct.rid E E E).symm
  left_inv := AlgEquiv.leftInverse_symm (Algebra.TensorProduct.rid E E E)
  right_inv := AlgEquiv.rightInverse_symm (Algebra.TensorProduct.rid E E E)
  map_mul' := by simp only [map_mul, implies_true]
  map_add' := by simp only [map_add, implies_true]
  commutes' := by simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.rid_tmul,
    smul_eq_mul, _root_.one_mul, implies_true]


set_option maxHeartbeats 800000 in
def huarongdao2 : E ⊗[K] (restrict K E A') ⊗[K] (restrict K E B') ≃ₐ[K]
    (E ⊗[K] (restrict K E A')) ⊗[E] (E ⊗[K] restrict K E B') := by
  -- unfold restrict
  refine Algebra.TensorProduct.assoc _ _ _ _|>.symm.trans $ Algebra.TensorProduct.congr
    (Algebra.TensorProduct.comm _ _ _) AlgEquiv.refl|>.trans ?_
  have e1 := Algebra.TensorProduct.congr (R := K) (S := K)
    (AlgEquiv.refl (A₁ := (restrict K E A'))) $ (rid_to_K_equiv (K := K) (E := E)).symm
  refine Algebra.TensorProduct.congr e1 AlgEquiv.refl|>.trans ?_
  sorry


-- lemma huarongdao2 : A' ⊗[E]  ≃ₐ[K] A' ⊗[E] E ⊗[E] B' := by sorry


-- abbrev changeBase : (CSA K) → (CSA E) :=
--   fun A => {
--     carrier := E ⊗[K] A
--     is_central_simple := IsCentralSimple.baseChange _ _ _
--     fin_dim := Module.Finite.base_change _ _ _
--   }

-- abbrev changeBase' : (CSA K) → (BrGroup (K := E)) :=
--   fun A => Quotient.mk (CSA_Setoid (K := E)) (changeBase E A)

-- lemma lift_aux : ∀(A B : CSA K), (IsBrauerEquivalent A B → changeBase' E A = changeBase' E B) := by
--   rintro A B ⟨n, m, hn, hm, iso⟩
--   simp only [Quotient.eq, changeBase]
--   change IsBrauerEquivalent _ _
--   have e1 :=
--     Algebra.TensorProduct.congr (AlgEquiv.refl (R := E) (A₁ := E))
--     (matrixEquivTensor K _ (Fin n)).symm|>.trans $ Algebra.TensorProduct.congr
--     (AlgEquiv.refl (R := E) (A₁ := E)) iso
--   have e2 := Algebra.TensorProduct.assoc K E A (Matrix (Fin n) (Fin n) K)
--   have e3 : (E ⊗[K] A) ⊗[K] Matrix (Fin n) (Fin n) K ≃ₐ[E]
--       E ⊗[K] A ⊗[K] Matrix (Fin n) (Fin n) K := by sorry


--   sorry

-- abbrev Change_GroupHom : (BrGroup (K := K)) → (BrGroup (K := E)) :=
--   Quotient.lift (changeBase' E) $ lift_aux E

abbrev BaseChange : BrGroup (K := K) →* BrGroup (K := E) where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry

end BrauerGroupHom
