import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.SimpleModule
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import FLT.for_mathlib.MoritaEquivalence

open Matrix

open CategoryTheory BigOperators

universe u u' u'' v v' v'' w

local notation "M[" ι "," R "]" => Matrix ι ι R

variable (K : Type w) (R : Type u) [Ring R] [CommRing K] [Algebra K R]

class IsMoritaEquivalent'
  (R : Type u) (S : Type u') [Ring R] [Ring S]
  [Algebra K R] [Algebra K S] : Prop :=
out : Nonempty $ ModuleCat.{v} R ≌ ModuleCat.{v'} S

namespace IsMoritaEquivalent'

-- variable (R : Type u) (S : Type u') (T : Type u'') [Ring R] [Ring S] [Ring T]
--   [Algebra K R] [Algebra K S] [Algebra K T]

-- noncomputable def equiv [IsMoritaEquivalent' K R S] : ModuleCat R ≌ ModuleCat S :=
--   (inferInstance : IsMoritaEquivalent' K R S) |>.out.some


-- instance [IsMoritaEquivalent' K R S] : (equiv K R S).functor.Additive :=
-- Functor.additive_of_preserves_binary_products _

-- instance [IsMoritaEquivalent' K R S] : (equiv K R S).inverse.Additive :=
-- inferInstance

-- @[refl]
-- lemma refl : IsMoritaEquivalent'.{u, u, v, v, w} K R R :=
-- ⟨⟨CategoryTheory.Equivalence.refl (C := ModuleCat.{v} R)⟩⟩

-- instance : IsMoritaEquivalent' K R R := refl K R

-- @[symm]
-- lemma symm [IsMoritaEquivalent'.{u, u', v, v'} K R S] :
--     IsMoritaEquivalent'.{u', u, v', v} K S R where
--   out := ⟨equiv K R S |>.symm⟩

-- @[trans]
-- lemma trans
--     [IsMoritaEquivalent'.{u, u', v, v'} K R S] [IsMoritaEquivalent'.{u', u'', v', v''} K S T] :
--     IsMoritaEquivalent'.{u, u'', v, v''} K R T where
--   out := ⟨(equiv K R S).trans $ equiv K S T⟩


-- lemma ofIso (e : R ≃ₐ[K] S) : IsMoritaEquivalent'.{u, u', v, v} K R S where
--   out := .intro
--     { functor := ModuleCat.restrictScalars e.symm.toRingEquiv.toRingHom
--       inverse := ModuleCat.restrictScalars e.toRingEquiv.toRingHom
--       unitIso :=
--       { hom :=
--         { app := fun X =>
--           { toFun := id
--             map_add' := by intros; rfl
--             map_smul' := by
--               rintro r (x : X)
--               change X.isModule.smul _ x = X.isModule.smul _ x
--               simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
--                 RingEquiv.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
--                 MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
--                 AlgEquiv.toRingEquiv_toRingHom, RingHom.id_apply, ZeroHom.coe_mk]
--               congr
--               exact e.symm_apply_apply r |>.symm }
--           naturality := fun _ _ f => rfl }
--         inv :=
--         { app := fun X =>
--           { toFun := id
--             map_add' := by intros; rfl
--             map_smul' := by
--               rintro r (x : X)
--               change X.isModule.smul _ x = X.isModule.smul _ x
--               simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
--                 RingEquiv.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
--                 MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
--                 AlgEquiv.toRingEquiv_toRingHom, ZeroHom.coe_mk, RingHom.id_apply]
--               congr
--               exact e.symm_apply_apply r }
--           naturality := fun _ _ f => rfl }
--         hom_inv_id := by ext; rfl
--         inv_hom_id := by ext; rfl }
--       counitIso :=
--       { hom :=
--         { app := fun X =>
--           { toFun := id
--             map_add' := by intros; rfl
--             map_smul' := by
--               rintro r (x : X)
--               change X.isModule.smul _ x = X.isModule.smul _ x
--               simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
--                 AlgEquiv.toRingEquiv_toRingHom, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
--                 MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
--                 AlgEquiv.symm_toRingEquiv, ZeroHom.coe_mk, RingHom.id_apply]
--               congr
--               exact e.apply_symm_apply r }
--           naturality := fun _ _ f => rfl }
--         inv :=
--         { app := fun X =>
--           { toFun := id
--             map_add' := by intros; rfl
--             map_smul' := by
--               rintro r (x : X)
--               change X.isModule.smul _ x = X.isModule.smul _ x
--               simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
--                 AlgEquiv.toRingEquiv_toRingHom, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
--                 MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
--                 AlgEquiv.symm_toRingEquiv, RingHom.id_apply, ZeroHom.coe_mk]
--               congr
--               exact e.apply_symm_apply r |>.symm }
--           naturality := fun _ _ f => rfl }
--         hom_inv_id := by ext; rfl
--         inv_hom_id := by ext; rfl }
--       functor_unitIso_comp := by intros; ext; rfl }

namespace division_ring -- auxilaries for division rings, don't use

variable (R : Type u) (S : Type u) [DivisionRing R] [DivisionRing S] [Algebra K R] [Algebra K S]
variable (e : ModuleCat.{u} R ≌ ModuleCat.{u} S)


instance : IsSimpleModule R (ModuleCat.of R R) :=
inferInstanceAs $ IsSimpleModule R R

-- This is a lemma on purpose, **don't** attempt to look at its definition

noncomputable def aFunc : (e.functor.obj $ ModuleCat.of R R) ≃ₗ[S] S :=
  @IsMoritaEquivalent.division_ring.division_ring_exists_unique_isSimpleModule S _
    (e.functor.obj $ ModuleCat.of R R) _ _
    (IsMoritaEquivalent.division_ring.IsSimpleModule.functor R S e $ ModuleCat.of R R) |>.some

noncomputable instance : Ring (e.functor.obj $ ModuleCat.of R R) where
__ := (inferInstance : AddCommGroup $ e.functor.obj $ ModuleCat.of R R)
mul := fun x y => (aFunc R S e).symm (aFunc R S e x * aFunc R S e y)
left_distrib := fun x y z => by
  show  (aFunc R S e).symm _ =  (aFunc R S e).symm _ +  (aFunc R S e).symm _
  simp only [map_add, mul_add]
right_distrib := fun x y z => by
  show  (aFunc R S e).symm _ =  (aFunc R S e).symm _ +  (aFunc R S e).symm _
  simp only [map_add, add_mul]
zero_mul := fun x => by
  show  (aFunc R S e).symm _ = _
  simp only [map_zero, zero_mul]
mul_zero := fun x => by
  show  (aFunc R S e).symm _ = _
  simp only [map_zero, mul_zero]
mul_assoc := fun x y z => by
  show  (aFunc R S e).symm (aFunc R S e ((aFunc R S e).symm _) * _) =
    (aFunc R S e).symm (_ * aFunc R S e ((aFunc R S e).symm _))
  simp only [LinearEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [mul_assoc]
one := (aFunc R S e).symm 1
one_mul := fun x => by
  show  (aFunc R S e).symm (aFunc R S e ((aFunc R S e).symm 1) * _) = _
  simp only [LinearEquiv.apply_symm_apply, one_mul, LinearEquiv.symm_apply_apply]
mul_one := fun x => by
  show  (aFunc R S e).symm (_ * aFunc R S e ((aFunc R S e).symm 1)) = _
  simp only [LinearEquiv.apply_symm_apply, mul_one, LinearEquiv.symm_apply_apply]

example : true := rfl

noncomputable instance : Algebra K (e.functor.obj $ ModuleCat.of R R) where
  smul := fun k x =>
  ((aFunc R S e).symm $ algebraMap K S k) * x
  toFun := fun k => (aFunc R S e).symm $ algebraMap K S k
  map_one' := by
    show (aFunc R S e).symm (algebraMap K S 1) = (aFunc R S e).symm 1
    simp only [_root_.map_one]
  map_mul' := fun x y => by
    simp only [_root_.map_mul]
    change _ = (aFunc R S e).symm _
    simp only [LinearEquiv.apply_symm_apply]
  map_zero' := by simp only [map_zero]
  map_add' := fun x y => by simp only [map_add]
  commutes' := fun x y => by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change (aFunc R S e).symm _ = (aFunc R S e).symm _
    simp only [LinearEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
    exact Algebra.commutes _ _
  smul_def' := fun k x => by
    change (aFunc R S e).symm _ = _
    simp only [LinearEquiv.apply_symm_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change _ = (aFunc R S e).symm _
    simp only [LinearEquiv.apply_symm_apply]

lemma algebraMap_eR_def (k : K) : algebraMap K (e.functor.obj $ ModuleCat.of R R) k =
  (aFunc R S e).symm (algebraMap K S k) := rfl

lemma mul_eR_def (x y : e.functor.obj $ ModuleCat.of R R) :
    x * y = (aFunc R S e).symm ((aFunc R S e x) * (aFunc R S e y)) := rfl

noncomputable def eRIsoS : e.functor.obj (ModuleCat.of R R) ≃ₐ[K] S :=
  { toFun := aFunc R S e
    invFun := (aFunc R S e).symm
    left_inv := (aFunc R S e).3
    right_inv := (aFunc R S e).4
    map_mul' := fun x y => by
      simp only
      change aFunc R S e ((aFunc R S e).symm _) = _
      simp only [LinearEquiv.apply_symm_apply]
    map_add' := (aFunc R S e).map_add
    commutes' := fun x => by
      simp only
      change (aFunc R S e $ (aFunc R S e).symm _) = _
      simp only [LinearEquiv.apply_symm_apply] }

lemma eRIsoS_comp :
    algebraMap K S =
      (eRIsoS K R S e).toRingEquiv.toRingHom.comp
        (algebraMap K $ e.functor.obj $ ModuleCat.of R R) := by
  ext x
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, AlgEquiv.coe_mk,
    Function.comp_apply, eRIsoS]
  change _ = (aFunc R S e) ((aFunc R S e).symm _)
  convert LinearEquiv.apply_symm_apply (aFunc R S e) (algebraMap K S x) |>.symm

instance : e.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

lemma isSimpleModule_iff_injective_or_eq_zero (M : ModuleCat R) :
    IsSimpleModule R M ↔
    (Nontrivial M ∧ ∀ (N : ModuleCat R) (f : M ⟶ N), f = 0 ∨ Function.Injective f) := by
  constructor
  · intros inst1
    constructor
    · have := inst1.1
      rwa [Submodule.nontrivial_iff] at this
    · intro N f
      refine inst1.2 (LinearMap.ker f) |>.elim
        (fun h => Or.inr $ by rwa [LinearMap.ker_eq_bot] at h) $
        fun h => Or.inl $ LinearMap.ext fun m => show f m = 0 from ?_
      rw [← LinearMap.mem_ker, h]
      trivial
  · rintro ⟨inst1, h⟩
    refine ⟨fun p => ?_⟩
    refine h (.of R (M ⧸ p)) (Submodule.mkQ p) |>.elim (fun h => Or.inr ?_) $
      fun h => Or.inl $ eq_bot_iff.2 fun x hx => h ?_
    · rw [← Submodule.ker_mkQ p, h, LinearMap.ker_zero]
    · rw [map_zero]
      exact Submodule.Quotient.mk_eq_zero _ |>.2 hx

open ZeroObject

instance : SMul K (End $ ModuleCat.of R R) :=
  inferInstanceAs $ SMul K (R →ₗ[R] R)

@[simp]
lemma algebra_smul_end_def (k : K) (f : R →ₗ[R] R) (r : R) : (k • f) r = k • f r := rfl

@[simps]
def algebraMapEnd : K →+* End (ModuleCat.of R R) where
  toFun k :=
  { toFun := fun (r : R) => k • r
    map_add' := fun (a b : R) => by simp
    map_smul' := fun (a b : R) => by simp }
  map_one' := LinearMap.ext fun (r : R) => by
    simp only [one_smul, LinearMap.coe_mk, AddHom.coe_mk, End.one_def]; rfl
  map_mul' x y := LinearMap.ext fun (r : R) => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [LinearMap.mul_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [MulAction.mul_smul]
  map_zero' := LinearMap.ext fun (r : R) => by simp
  map_add' x y := LinearMap.ext fun (r : R) => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [LinearMap.add_apply]
    simp only [add_smul, LinearMap.coe_mk, AddHom.coe_mk]

variable {R S} in
def aux1 : End (ModuleCat.of R R) ≃+* End (e.functor.obj $ ModuleCat.of R R) where
  toFun f := e.functor.map f
  invFun g := e.unit.app _ ≫ e.inverse.map g ≫ e.unitInv.app _
  left_inv := by
    intro f
    simp only [Functor.comp_obj, Equivalence.inv_fun_map, Functor.id_obj, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
    rw [← Category.assoc]
    change (e.unit ≫ e.unitInv).app _ ≫ _ = _
    simp
  right_inv := by
    intro g
    simp only [Functor.comp_obj, Functor.map_comp, Equivalence.fun_inv_map, Functor.id_obj,
      Category.assoc, Equivalence.counitInv_functor_comp, Category.comp_id]
    exact e.functor_unit_comp_assoc (ModuleCat.of R R) g
  map_mul' x y := by simp
  map_add' x y := by simp only; rw [e.functor.map_add]

@[simps!]
noncomputable def algebraMapEnd' : K →+* End (e.functor.obj $ ModuleCat.of R R) :=
  RingHom.comp
    (aux1 R e)
    (algebraMapEnd K R)

instance : Algebra K (End $ ModuleCat.of R R) where
  toRingHom := algebraMapEnd K R
  commutes' k (f : R →ₗ[R] R) := LinearMap.ext fun (r' : R) => by
    simp only [algebraMapEnd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [LinearMap.mul_apply, LinearMap.mul_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    conv_rhs => rw [Algebra.smul_def, ← smul_eq_mul]
    erw [f.map_smul]
    rw [Algebra.smul_def]
    rfl
  smul_def' k (f : R →ₗ[R] R) := LinearMap.ext fun (r' : R) => by
    simp only [algebraMapEnd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [LinearMap.mul_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Algebra.smul_def, ← smul_eq_mul]
    erw [← f.map_smul]
    rw [smul_eq_mul, ← Algebra.smul_def]
    erw [LinearMap.smul_apply]
    rw [Algebra.smul_def, ← smul_eq_mul]
    erw [← f.map_smul]
    rw [smul_eq_mul, ← Algebra.smul_def]

noncomputable instance : Algebra K (End $ e.functor.obj $ ModuleCat.of R R) where
  toRingHom := algebraMapEnd' K R S e
  commutes' k (f : _ →ₗ[_] _) := by
    simp only [algebraMapEnd'_apply, End.mul_def]
    erw [End.mul_def]
    simp only [aux1, Functor.comp_obj, RingEquiv.coe_mk, Equiv.coe_fn_mk]
    apply_fun (e.inverse.map) using e.inverse.map_injective
    simp only [Functor.map_comp, Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
      Category.assoc]
    refine LinearMap.ext fun x => ?_
    repeat erw [comp_apply]
    simp only [algebraMapEnd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]

    repeat erw [LinearMap.coe_mk, AddHom.coe_mk]
    simp only [Functor.comp_obj, Functor.id_obj, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [Algebra.smul_def, Algebra.smul_def, ← smul_eq_mul, ← smul_eq_mul]
    have := (e.unitInv.app (ModuleCat.of R R)).map_smul (algebraMap K R k) x
    erw [← this]
    have := (e.unitInv.app (ModuleCat.of R R)).map_smul (algebraMap K R k) (e.inverse.map f $ x)
    erw [← this]
    change e.unit.app _ (e.unitInv.app _ _) =
      e.inverse.map _ ((e.unitInv ≫ e.unit).app (ModuleCat.of R R) _)
    rw [Iso.inv_hom_id, NatTrans.id_app, ModuleCat.id_apply]
    change (e.unitInv.app _ ≫ e.unit.app _) _ = _
    simp only [Functor.comp_obj, Functor.id_obj, Iso.inv_hom_id_app, LinearMapClass.map_smul,
      ModuleCat.id_apply]
  smul_def' k (f : _ →ₗ[_] _) := rfl

lemma algebraMap_end_eR_def :
  algebraMap K (End $ e.functor.obj $ ModuleCat.of R R) = (algebraMapEnd' K R S e) := rfl

@[simps]
def mopToEnd : Rᵐᵒᵖ →ₐ[K] End (ModuleCat.of R R) where
-- where
  toFun a :=
    { toFun := fun (x : R) ↦ x * a.unop
      map_add' := by simp [add_mul]
      map_smul' := by simp [mul_assoc] }
  map_zero' := by aesop
  map_one' := by aesop
  map_add' := fun x y => LinearMap.ext fun r => by
    simp only [MulOpposite.unop_add, mul_add, LinearMap.coe_mk, AddHom.coe_mk]; rfl
  map_mul' := fun (x y) => LinearMap.ext fun (r : R) => by
    simp only [MulOpposite.unop_mul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [LinearMap.mul_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  commutes' k := LinearMap.ext fun (r : R) => by
    simp only [MulOpposite.algebraMap_apply, MulOpposite.unop_op, LinearMap.coe_mk, AddHom.coe_mk]
    change _ = (algebraMapEnd K R k).toFun r
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, algebraMapEnd_apply_apply]
    rw [← Algebra.commutes, ← Algebra.smul_def]

noncomputable def mopEquivEnd : Rᵐᵒᵖ ≃ₐ[K] End (ModuleCat.of R R) :=
  AlgEquiv.ofBijective (mopToEnd K R) ⟨RingHom.injective_iff_ker_eq_bot _ |>.mpr $
    SetLike.ext fun (α : Rᵐᵒᵖ) => ⟨fun h => by simpa using LinearMap.congr_fun h (1 : R),
      by rintro rfl; simp⟩, fun φ => ⟨MulOpposite.op (φ.toFun (1 : R)), LinearMap.ext fun r => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mopToEnd_apply_apply,
        MulOpposite.unop_op]
      rw [← smul_eq_mul]
      convert (φ.map_smul r (1 : R)).symm using 1
      simp⟩⟩

-- #check IsMoritaEquivalent.division_ring.aux1
-- def algebraMapEndFunctor : K →+* End (e.functor.obj $ ModuleCat.of R R) :=
-- RingHom.comp (IsMoritaEquivalent.division_ring.aux1 R S e).toRingHom $ algebraMap _ _

-- instance : Algebra K $ End (e.functor.obj $ ModuleCat.of R R) where
--   toRingHom := algebraMapEndFunctor K R S e
--   commutes' r x := by
--     simp only [algebraMapEndFunctor, IsMoritaEquivalent.division_ring.aux1, Functor.comp_obj,
--       RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, RingEquiv.coe_mk,
--       Equiv.coe_fn_mk, Function.comp_apply, End.mul_def]
--     apply_fun e.inverse.map using e.inverse.map_injective
--     simp only [Functor.map_comp, Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
--       Category.assoc]
--     have eq0 := (instAlgebraEndModuleCatOf K R).commutes r
--       ((IsMoritaEquivalent.division_ring.aux1 R S e).symm.toRingHom x)
--     simp only [IsMoritaEquivalent.division_ring.aux1, Functor.comp_obj, RingEquiv.symm_mk,
--       RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk, End.mul_def,
--       Category.assoc] at eq0
--     apply_fun (e.unitInv.app (ModuleCat.of R R) ≫ ·) at eq0
--     erw [e.unitIso.inv_hom_id_app_assoc] at eq0
--     apply_fun (· ≫ e.unit.app (ModuleCat.of R R)) at eq0
--     rw [Category.assoc, Category.assoc, Category.assoc] at eq0
--     rw [eq0]
--     simp only [Functor.id_obj, Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
--       Category.comp_id, NatIso.cancel_natIso_inv_left]
--     rfl
--   smul_def' := fun _ _ => rfl

variable {R S} in
def aux1Algebra : End (ModuleCat.of R R) ≃ₐ[K] End (e.functor.obj $ ModuleCat.of R R) where
  toFun f := e.functor.map f
  invFun g := e.unit.app _ ≫ e.inverse.map g ≫ e.unitInv.app _
  left_inv := by
    intro f
    simp only [Functor.comp_obj, Equivalence.inv_fun_map, Functor.id_obj, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
    rw [← Category.assoc]
    change (e.unit ≫ e.unitInv).app _ ≫ _ = _
    simp
  right_inv := by
    intro g
    simp only [Functor.comp_obj, Functor.map_comp, Equivalence.fun_inv_map, Functor.id_obj,
      Category.assoc, Equivalence.counitInv_functor_comp, Category.comp_id]
    exact e.functor_unit_comp_assoc (ModuleCat.of R R) g
  map_mul' x y := by simp
  map_add' x y := by simp only; rw [e.functor.map_add]
  commutes' k := by
    rfl

-- noncomputabl : Ring (e.functor.obj $ ModuleCat.of R R) :=
--   division_ring_exists_unique_isSimpleModule K R S e (ModuleCat.of R R) |>.choose

-- noncomputable def aux20 :
--     (e.functor.obj (ModuleCat.of R R)) ≃ₐ[K] ModuleCat.of S S := by
--   have :  IsSimpleModule R (ModuleCat.of R R) := inferInstanceAs $ IsSimpleModule R R
--   have : IsSimpleModule S (e.functor.obj (ModuleCat.of R R)) :=
--     IsSimpleModule.functor R S e (ModuleCat.of R R)
--   have := division_ring_exists_unique_isSimpleModule S (e.functor.obj $ ModuleCat.of R R)
--   exact this.some.toModuleIso


noncomputable def aux2
    (he : ∀ (k : K) (r : e.functor.obj $ ModuleCat.of R R), e.functor.map ({
      toFun := fun (r : R) => k • r
      map_add' := fun x y => by
        simp only [smul_add]
      map_smul' := fun (x y : R) => by
        simp only [smul_eq_mul, RingHom.id_apply, Algebra.mul_smul_comm] } :
        ModuleCat.of R R ⟶ ModuleCat.of R R) r = k • r) :
    End (e.functor.obj $ ModuleCat.of R R) ≃ₐ[K] End (ModuleCat.of S S) where
  toFun f := (aFunc R S e).symm.toLinearMap ≫ f ≫ (aFunc R S e).toLinearMap
  invFun f := (by exact (aFunc R S e).toLinearMap) ≫ f ≫ (aFunc R S e).symm.toLinearMap
  left_inv := by
    intro f
    simp only [Category.assoc]
    refine LinearMap.ext fun x => ?_
    repeat erw [comp_apply]
    repeat erw [(aFunc R S e).symm_apply_apply]
    rfl
  right_inv := by
    intro f
    simp only [Category.assoc]
    refine LinearMap.ext fun x => ?_
    repeat erw [comp_apply]
    repeat erw [(aFunc R S e).apply_symm_apply]
    rfl
  map_mul' := fun x y => by
    simp only [End.mul_def, Category.assoc]
    congr 2
    ext a
    repeat erw [comp_apply]
    repeat erw [(aFunc R S e).symm_apply_apply]
  map_add' := fun x y => by
    simp only
    rw [Preadditive.add_comp, Preadditive.comp_add]
  commutes' k := by
    simp only
    refine LinearMap.ext fun x => ?_
    repeat erw [comp_apply]
    rw [algebraMap_end_eR_def]
    change _ = (algebraMapEnd K S k).toFun x
    simp only [algebraMapEnd'_apply, algebraMapEnd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      AddHom.toFun_eq_coe, AddHom.coe_mk]
    simp only [aux1, Functor.comp_obj, RingEquiv.coe_mk, Equiv.coe_fn_mk]
    erw [he]
    change aFunc R S e ((aFunc R S e).symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    erw [(aFunc R S e).apply_symm_apply]
    rw [Algebra.smul_def]

noncomputable def toAlgMopEquiv : Rᵐᵒᵖ ≃ₐ[K] Sᵐᵒᵖ := by
  refine mopEquivEnd K R |>.trans $ AlgEquiv.trans ?_ $ mopEquivEnd K S |>.symm

  let e1 : End (ModuleCat.of R R) ≃ₐ[K] End (e.functor.obj $ ModuleCat.of R R) := aux1Algebra K R e
  let e2 : End (e.functor.obj $ ModuleCat.of R R) ≃ₐ[K] End (ModuleCat.of S S) := aux2 K R S e sorry

  refine e1.trans e2

noncomputable def toAlgEquiv : R ≃ₐ[K] S where
  toFun r := toAlgMopEquiv K R S e (.op r) |>.unop
  invFun s := toAlgMopEquiv K R S e |>.symm (.op s) |>.unop
  left_inv r := by simp
  right_inv s := by simp
  map_mul' a b := by simp
  map_add' a b := by simp
  commutes' a := by
    simp only
    apply_fun MulOpposite.op using MulOpposite.op_injective
    exact (toAlgMopEquiv K R S e).commutes a

end division_ring

noncomputable def algEquivOfDivisionRing
    (R S : Type u) [DivisionRing R] [DivisionRing S] [Algebra K R] [Algebra K S]
    [h : IsMoritaEquivalent' K R S] :
    R ≃ₐ[K] S := division_ring.toAlgEquiv K R S (h.out.some)

end IsMoritaEquivalent'
