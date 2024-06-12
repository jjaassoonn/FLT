import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.CategoryTheory.Elementwise

open Matrix

open CategoryTheory BigOperators

universe u u' u'' v v' w

local notation "M[" ι "," R "]" => Matrix ι ι R

variable (R: Type u) (S : Type u) (T : Type u'') [Ring R] [Ring S] [Ring T]

variable (ι : Type w) [Fintype ι] [Inhabited ι] [DecidableEq ι]

instance (M : Type*) [AddCommGroup M] [Module R M] : Module M[ι, R] (ι → M) where
  smul N v i := ∑ j : ι, N i j • v j
  one_smul v := funext fun i => show ∑ _, _ = _ by simp [one_apply]
  mul_smul N₁ N₂ v := funext fun i => show ∑ _, _ = ∑ _, _ • (∑ _, _) by
    simp_rw [mul_apply, Finset.smul_sum, Finset.sum_smul, MulAction.mul_smul]
    rw [Finset.sum_comm]
  smul_zero v := funext fun i => show ∑ _, _ = _ by simp
  smul_add N v₁ v₂ := funext fun i => show ∑ _, _ = (∑ _, _) + (∑ _, _) by
    simp [Finset.sum_add_distrib]
  add_smul N₁ N₂ v := funext fun i => show ∑ _, _ = (∑ _, _) + (∑ _, _) by
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul v := funext fun i => show ∑ _, _ = _ by simp

@[simps]
def toModuleCatOverMatrix : ModuleCat R ⥤ ModuleCat M[ι, R] where
  obj M := ModuleCat.of M[ι, R] (ι → M)
  map f :=
  { toFun := fun v i => f $ v i
    map_add' := fun x y => funext fun i => show f (x i + y i) = f (x i) + f (y i) from
      map_add f _ _
    map_smul' := fun m v => funext fun i => show f (∑ _, _) = ∑ _, _ by
      simp only [RingHom.id_apply, map_sum, _root_.map_smul] }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simps]
def fromModuleCatOverMatrix.α [Inhabited ι] (M : Type*) [AddCommGroup M] [Module M[ι, R] M] :
    AddSubgroup M where
  carrier := Set.range ((stdBasisMatrix (default : ι) (default : ι) (1 : R) : M[ι, R]) • ·)
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro _ ⟨m, rfl⟩
    exact ⟨-m, by simp⟩

open fromModuleCatOverMatrix

instance fromModuleCatOverMatrix.module_α (M : Type*) [AddCommGroup M] [Module M[ι, R] M] :
    Module R <| α R ι M where
  smul a x := ⟨(stdBasisMatrix default default a : M[ι, R]) • x.1, by
    obtain ⟨y, hy⟩ := x.2
    simp only [α, AddSubgroup.mem_mk, Set.mem_range]
    refine ⟨(stdBasisMatrix default default a : M[ι, R]) • y, hy ▸ ?_⟩
    simp only
    rw [← MulAction.mul_smul, ← MulAction.mul_smul]
    congr 1
    ext i j
    simp⟩
  one_smul := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = stdBasisMatrix _ _ _ • _
    rw [← MulAction.mul_smul]
    congr 1
    ext i j
    simp
  mul_smul := by
    rintro a a' ⟨_, ⟨x, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = stdBasisMatrix _ _ _ • (stdBasisMatrix _ _ _ • _)
    dsimp only [id_eq, eq_mpr_eq_cast, cast_eq]
    rw [← MulAction.mul_smul, ← MulAction.mul_smul, ← MulAction.mul_smul]
    congr 1
    ext i j
    simp
  smul_zero a := by
    ext
    change stdBasisMatrix _ _ _ • 0 = 0
    simp
  smul_add := by
    rintro a ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = stdBasisMatrix _ _ _ • _ + stdBasisMatrix _ _ _ • _
    dsimp only [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid, α_coe]
    rw [← MulAction.mul_smul, ← MulAction.mul_smul, ← smul_add, ← smul_add,
      ← MulAction.mul_smul]
  add_smul := by
    rintro a b ⟨_, ⟨x, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = stdBasisMatrix _ _ _ • _ + stdBasisMatrix _ _ _ • _
    dsimp only
    rw [← MulAction.mul_smul, ← MulAction.mul_smul, ← MulAction.mul_smul, ← add_smul,
      ← add_mul, ← stdBasisMatrix_add]
  zero_smul := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = _
    simp only [stdBasisMatrix_zero, zero_smul, ZeroMemClass.coe_zero]

@[simp]
lemma fromModuleCatOverMatrix.smul_α_coe {M : Type*} [AddCommGroup M] [Module M[ι, R] M]
    (x : R) (y : α R ι M) : ((x • y : α R ι M) : M) =
    (stdBasisMatrix default default x : M[ι, R]) • y.1 := rfl

open fromModuleCatOverMatrix
@[simps]
def fromModuleCatOverMatrix : ModuleCat M[ι, R] ⥤ ModuleCat R where
  obj M := .of _ $ α R ι M
  map f :=
    { toFun := fun x => ⟨f x.1, by
        simp only [α, AddSubgroup.coe_set_mk, AddSubgroup.mem_mk, Set.mem_range]
        obtain ⟨y, hy⟩ := x.2
        refine ⟨f y, ?_⟩
        simp only at hy
        rw [← hy, f.map_smul]⟩
      map_add' := by
        rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
        refine Subtype.ext ?_
        show f ((stdBasisMatrix _ _ _ • x) + (stdBasisMatrix _ _ _ • y)) =
          f (stdBasisMatrix _ _ _ • x) + f (stdBasisMatrix _ _ _ • y)
        rw [map_add]
      map_smul' := by
          rintro r ⟨_, ⟨x, rfl⟩⟩
          simp only [RingHom.id_apply, LinearMapClass.map_smul]
          refine Subtype.ext ?_
          show f (_ • _) = _ • (_ • f _)
          simp only [LinearMapClass.map_smul] }
  map_id X := by ext x; exact Subtype.ext rfl
  map_comp f g := by ext x; exact Subtype.ext rfl

example : true := rfl

@[simps]
def matrix.unitIsoHom :
    toModuleCatOverMatrix R ι ⋙ fromModuleCatOverMatrix R ι ⟶
    𝟭 (ModuleCat R) where
  app X :=
    { toFun := fun x => ∑ i : ι, x.1 i
      map_add' := by
        rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
        simp only [toModuleCatOverMatrix_obj, AddSubmonoid.coe_add, ← Finset.sum_add_distrib]
        rfl
      map_smul' := by
        rintro r ⟨_, ⟨x, rfl⟩⟩
        simp only [toModuleCatOverMatrix_obj, smul_α_coe, ← MulAction.mul_smul,
          StdBasisMatrix.mul_same, mul_one, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [fromModuleCatOverMatrix.smul_α_coe, Subtype.coe_mk, ← MulAction.mul_smul]
        change ∑ _, _ = r • ∑ _, _
        simp [Finset.smul_sum, stdBasisMatrix] }
  naturality {X Y} f := by
    simp only [Functor.comp_obj, toModuleCatOverMatrix_obj, fromModuleCatOverMatrix_obj,
      Functor.id_obj, Functor.comp_map, Functor.id_map]
    ext ⟨_, ⟨x, rfl⟩⟩
    change ∑ _, _ = f _
    simp only [fromModuleCatOverMatrix_map_apply_coe, LinearMapClass.map_smul, Functor.comp_obj,
      toModuleCatOverMatrix_obj, fromModuleCatOverMatrix_obj, Functor.id_obj, ModuleCat.coe_comp,
      Function.comp_apply]
    change _ = f (∑ i : ι, ∑ _, _)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    change ∑ _, _ = _
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [LinearMapClass.map_smul]
    rw [toModuleCatOverMatrix_map_apply]

example : true := rfl

-- this never finish compile if uncommented
@[simps]
def matrix.unitIsoInv :
    𝟭 (ModuleCat R) ⟶
    toModuleCatOverMatrix R ι ⋙ fromModuleCatOverMatrix R ι  where
  app X :=
    { toFun := fun x => ⟨fun i => if i = default then x else 0, by sorry
        -- simp only [toModuleCatOverMatrix_obj, α, AddSubgroup.mem_mk, Set.mem_range]
        -- refine ⟨fun _ => x, ?_⟩
        -- refine funext fun i => ?_
        -- change ∑ _, _ = _
        -- simp only [stdBasisMatrix, ite_smul, one_smul, zero_smul]
        -- split_ifs with h
        -- · subst h
        --   simp
        -- · apply Finset.sum_eq_zero
        --   intro j hj
        --   rw [if_neg]
        --   tauto
          ⟩
      map_add' := by
        rintro (x : X) (y : X)
        simp only [Functor.comp_obj, toModuleCatOverMatrix_obj, fromModuleCatOverMatrix_obj,
          Functor.id_obj]
        refine Subtype.ext $ funext fun i => ?_
        simp only [toModuleCatOverMatrix_obj]
        change (if i = default then x + y else 0) =
          (if i = default then x else 0) + (if i = default then y else 0)
        split_ifs with h
        · rfl
        · rw [add_zero]
      map_smul' := by
        rintro r (x : X)
        simp only [Functor.comp_obj, toModuleCatOverMatrix_obj, fromModuleCatOverMatrix_obj,
          Functor.id_obj, RingHom.id_apply]
        refine Subtype.ext $ funext fun i => ?_
        simp only [toModuleCatOverMatrix_obj]
        change (if i = default then r • x else 0) =
          ∑ j : ι, stdBasisMatrix default default r i j • (if j = default then x else 0)
        simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        split_ifs with h
        · subst h
          simp only [StdBasisMatrix.apply_same]
        · rw [StdBasisMatrix.apply_of_row_ne, zero_smul]
          exact Ne.symm h
          }
  naturality {X Y} f := by
    simp only [Functor.id_obj, Functor.comp_obj, toModuleCatOverMatrix_obj,
        fromModuleCatOverMatrix_obj, Functor.id_map, Functor.comp_map]
    ext x
    simp only [Functor.id_obj, Functor.comp_obj, toModuleCatOverMatrix_obj,
      fromModuleCatOverMatrix_obj, ModuleCat.coe_comp, Function.comp_apply]

    refine Subtype.ext $ funext fun i => ?_

    change (if i = default then f x else 0) = _
    rw [fromModuleCatOverMatrix_map_apply_coe, toModuleCatOverMatrix_map_apply]
    change _ = f (if _ then _ else _)
    split_ifs with h
    · rfl
    · rw [map_zero]

example : true := rfl

@[simps]
def matrix.unitIso :
    toModuleCatOverMatrix R ι ⋙ fromModuleCatOverMatrix R ι ≅
    𝟭 (ModuleCat R) where
  hom := matrix.unitIsoHom R ι
  inv := matrix.unitIsoInv R ι
  hom_inv_id := by
    ext X ⟨_, ⟨x, rfl⟩⟩
    simp only [Functor.comp_obj, toModuleCatOverMatrix_obj, fromModuleCatOverMatrix_obj,
      NatTrans.comp_app, Functor.id_obj, ModuleCat.coe_comp, Function.comp_apply, NatTrans.id_app,
      ModuleCat.id_apply]
    refine Subtype.ext $ funext fun i => ?_
    simp only [toModuleCatOverMatrix_obj]
    erw [matrix.unitIsoInv_app_apply_coe]
    change _ = ∑ _, _
    erw [matrix.unitIsoHom_app_apply]
    simp only [Functor.id_obj]
    split_ifs with h
    · refine Finset.sum_congr rfl fun i _ => ?_
      change ∑ _, _ = _
      subst h
      simp only [stdBasisMatrix, ite_smul, one_smul, zero_smul, true_and]
      split_ifs with h
      · subst h
        simp only [true_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      · apply Finset.sum_eq_zero
        intro j _
        rw [if_neg]
        tauto
    · symm
      apply Finset.sum_eq_zero
      intro j _
      dsimp only [stdBasisMatrix]
      rw [if_neg, zero_smul]
      tauto
  inv_hom_id := by
    ext X (x : X)
    simp only [Functor.id_obj, NatTrans.comp_app, Functor.comp_obj, toModuleCatOverMatrix_obj,
      fromModuleCatOverMatrix_obj, ModuleCat.coe_comp, Function.comp_apply, NatTrans.id_app,
      ModuleCat.id_apply]
    erw [matrix.unitIsoHom_app_apply]
    change (∑ i : ι, if i = default then x else 0) = x
    simp

example : true := rfl


@[simps?!]
noncomputable def test (M : ModuleCat M[ι, R]) :
    M ≅ (fromModuleCatOverMatrix R ι ⋙ toModuleCatOverMatrix R ι).obj M :=
  LinearEquiv.toModuleIso $ LinearEquiv.ofBijective
    { toFun := fun m i => ⟨(stdBasisMatrix default i 1 : M[ι, R]) • m, by
        simp only [α, AddSubgroup.mem_mk, Set.mem_range]
        refine ⟨(stdBasisMatrix default i 1 : M[ι, R]) • m, ?_⟩
        simp only [← MulAction.mul_smul, StdBasisMatrix.mul_same, mul_one]⟩
      map_add' := fun x y => funext fun i => Subtype.ext $ sorry
        -- show (stdBasisMatrix default i 1 : M[ι, R]) • (x + y) =
        --   (stdBasisMatrix default i 1 : M[ι, R]) • x +
        --   (stdBasisMatrix default i 1 : M[ι, R]) • y from _
      map_smul' := sorry } ⟨sorry, sorry⟩

@[simps]
noncomputable def matrix.counitIsoHom :
    fromModuleCatOverMatrix R ι ⋙ toModuleCatOverMatrix R ι ⟶ 𝟭 (ModuleCat M[ι, R]) where
  app M := (test R ι M).inv
  naturality X Y f := by
    simp only [Functor.comp_obj, fromModuleCatOverMatrix_obj, toModuleCatOverMatrix_obj,
      Functor.id_obj, Functor.comp_map, Functor.id_map]
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    ext x
    simp only [ModuleCat.coe_comp, Function.comp_apply]
    refine funext fun i => ?_
    rw [toModuleCatOverMatrix_map_apply]
    refine Subtype.ext ?_
    rw [fromModuleCatOverMatrix_map_apply_coe]
    change _ = _ • _
    rw [← f.map_smul]
    erw [test_hom_apply_coe]

def matrix.counitIso :
    fromModuleCatOverMatrix R ι ⋙ toModuleCatOverMatrix R ι ≅ 𝟭 (ModuleCat M[ι, R]) where
  hom := matrix.counitIsoHom R ι
  inv := _
  hom_inv_id := _
  inv_hom_id := _


def moritaEquivlentToMatrix : ModuleCat R ≌ ModuleCat M[ι, R] where
  functor := toModuleCatOverMatrix R ι
  inverse := fromModuleCatOverMatrix R ι
  unitIso := matrix.unitIso R ι |>.symm
  counitIso := _
  functor_unitIso_comp := _

structure MoritaEquivalent :=
equiv : ModuleCat R ≌ ModuleCat S

namespace MoritaEquivalent

-- noncomputable def equiv [MoritaEquivalent R S] : ModuleCat R ≌ ModuleCat S :=
--   (inferInstance : MoritaEquivalent R S) |>.out.some

-- @[refl]
-- lemma refl : MoritaEquivalent R R :=
-- ⟨⟨CategoryTheory.Equivalence.refl (C := ModuleCat R)⟩⟩

-- instance : MoritaEquivalent R R := refl R

-- @[symm]
-- lemma symm [MoritaEquivalent.{u, v} R S] : MoritaEquivalent.{u, v} S R where
--   out := ⟨equiv R S |>.symm⟩

-- @[trans]
-- lemma trans [MoritaEquivalent.{u, v} R S] [MoritaEquivalent.{u, v} S T] :
--     MoritaEquivalent.{u, v} R T where
--   out := ⟨(equiv R S).trans $ equiv S T⟩

section matrix

end matrix

end MoritaEquivalent
