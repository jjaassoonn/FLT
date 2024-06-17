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

instance : Algebra K (e.functor.obj $ ModuleCat.of R R) where
  smul := fun k x => ((aFunc R S e).symm $ algebraMap K S k) * x
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
  change _ = f (f.symm _)
  convert LinearEquiv.apply_symm_apply f (algebraMap K S x) |>.symm
-- set_option maxHeartbeats 1000000 in
-- def division_ring_exists_unique_isSimpleModule
--     (N : ModuleCat R) [IsSimpleModule R N] :
--     ∃ (ring : Ring (e.functor.obj N))
--       (alg : Algebra K (e.functor.obj N)) (iso1 : e.functor.obj N ≃ₐ[K] S),
--       algebraMap K S = iso1.toRingEquiv.toRingHom.comp (algebraMap K $ e.functor.obj N) := by
--   have : IsSimpleModule S (e.functor.obj N) := IsMoritaEquivalent.division_ring.IsSimpleModule.functor R S e N
--   have inst4 := IsSimpleModule.nontrivial S $ e.functor.obj N
--   have H := Module.Free.of_divisionRing S $ e.functor.obj N
--   rw [Module.free_iff_set] at H
--   obtain ⟨s, ⟨b⟩⟩ := H
--   if hs1 : s = ∅
--   then
--     subst hs1
--     have := b.index_nonempty
--     simp only [nonempty_subtype, Set.mem_empty_iff_false, exists_const] at this
--   else
--     obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hs1
--     have eq0 := IsSimpleOrder.eq_bot_or_eq_top (Submodule.span S {b ⟨i, hi⟩}) |>.resolve_left (by
--       intro h
--       simp only [Submodule.span_singleton_eq_bot] at h
--       exact b.ne_zero ⟨i, hi⟩ h)
--     have eq : s = {i} := by
--       refine le_antisymm ?_ (by simpa)
--       simp only [Set.le_eq_subset, Set.subset_singleton_iff]
--       intro j hj
--       have mem : b ⟨j, hj⟩ ∈ Submodule.span S {b ⟨i, hi⟩} := eq0 ▸ ⟨⟩
--       rw [Submodule.mem_span_singleton] at mem
--       obtain ⟨r, hr⟩ := mem
--       have hr' := congr(b.repr $hr)
--       simp only [LinearMapClass.map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
--         mul_one] at hr'
--       by_contra rid
--       have hr' := congr($hr' ⟨i, hi⟩)
--       rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (h := by simpa)] at hr'
--       subst hr'
--       simp only [zero_smul] at hr
--       exact b.ne_zero _ hr.symm |>.elim

--     subst eq
--     let f : e.functor.obj N ≃ₗ[S] S := b.repr ≪≫ₗ
--     { toFun := fun v => v ⟨i, by simp⟩
--       map_add' := fun x y => by simp
--       map_smul' := fun x y => by simp
--       invFun := fun x => Finsupp.single ⟨i, by simp⟩ x
--       left_inv := fun x => by ext; simp
--       right_inv := fun x => by simp }

--     have : FiniteDimensional.finrank S (e.functor.obj N) = 1 := by
--       rw [FiniteDimensional.finrank_eq_card_basis b]
--       simp

--     letI : Ring (e.functor.obj N) :=
--       { __ := (inferInstance : AddCommGroup (e.functor.obj N))
--         mul := fun x y => f.symm (f x * f y)
--         left_distrib := fun x y z => by
--           show f.symm _ = f.symm _ + f.symm _
--           simp only [map_add, mul_add]
--         right_distrib := fun x y z => by
--           show f.symm _ = f.symm _ + f.symm _
--           simp only [map_add, add_mul]
--         zero_mul := fun x => by
--           show f.symm _ = _
--           simp only [map_zero, zero_mul]
--         mul_zero := fun x => by
--           show f.symm _ = _
--           simp only [map_zero, mul_zero]
--         mul_assoc := fun x y z => by
--           show f.symm (f (f.symm _) * _) = f.symm (_ * f (f.symm _))
--           simp only [LinearEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
--           rw [mul_assoc]
--         one := f.symm 1
--         one_mul := fun x => by
--           show f.symm (f (f.symm 1) * _) = _
--           simp only [LinearEquiv.apply_symm_apply, one_mul, LinearEquiv.symm_apply_apply]
--         mul_one := fun x => by
--           show f.symm (_ * f (f.symm 1)) = _
--           simp only [LinearEquiv.apply_symm_apply, mul_one, LinearEquiv.symm_apply_apply] }
--     letI : Algebra K (e.functor.obj N) :=
--       { smul := fun k x => (f.symm $ algebraMap K S k) * x
--         toFun := fun k => f.symm $ algebraMap K S k
--         map_one' := by
--           show f.symm (algebraMap K S 1) = f.symm 1
--           simp only [_root_.map_one]
--         map_mul' := fun x y => by
--           simp only [_root_.map_mul]
--           change _ = f.symm _
--           simp only [LinearEquiv.apply_symm_apply]
--         map_zero' := by simp only [map_zero]
--         map_add' := fun x y => by simp only [map_add]
--         commutes' := fun x y => by
--           simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
--           change f.symm _ = f.symm _
--           simp only [LinearEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
--           exact Algebra.commutes _ _
--         smul_def' := fun k x => by
--           change f.symm _ = _
--           simp only [LinearEquiv.apply_symm_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
--           change _ = f.symm _
--           simp only [LinearEquiv.apply_symm_apply] }
--     letI : Module S (e.functor.obj N) := (e.functor.obj N).isModule
--     let ff : e.functor.obj N ≃ₐ[K] S :=
--       { toFun := f
--         invFun := f.symm
--         left_inv := f.3
--         right_inv := f.4
--         map_mul' := fun x y => by
--           simp only
--           change f (f.symm _) = _
--           simp only [LinearEquiv.apply_symm_apply]
--         map_add' := f.map_add
--         commutes' := fun x => by
--           simp only
--           change (f $ f.symm _) = _
--           simp only [LinearEquiv.apply_symm_apply] }
--     refine ⟨inferInstance, inferInstance, ff, ?_⟩
--     ext x
--     simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
--       AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, AlgEquiv.coe_mk,
--       Function.comp_apply, ff]
--     change _ = f (f.symm _)
--     convert LinearEquiv.apply_symm_apply f (algebraMap K S x) |>.symm

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

-- variable {R S} in
-- instance _root_.CategoryTheory.Equivalence.nontrivial
--     (M : ModuleCat R) [h : Nontrivial M] : Nontrivial (e.functor.obj M) := by
--   obtain ⟨m, n, h⟩ := h
--   by_contra inst1
--   rw [not_nontrivial_iff_subsingleton] at inst1
--   let iso1 : e.functor.obj M ≅ 0 :=
--   { hom := ⟨⟨fun _ => 0, by intros; simp⟩, by intros; simp⟩
--     inv := ⟨⟨fun _ => 0, by intros; simp⟩, by intros; simp⟩
--     hom_inv_id := by intros; ext; exact Subsingleton.elim _ _
--     inv_hom_id := by intros; ext; simp only [ModuleCat.coe_comp, Function.comp_apply,
--       Limits.id_zero]; rfl }
--   let iso2 : M ≅ 0 := calc M
--       _ ≅ e.inverse.obj (e.functor.obj M) := e.unitIso.app M
--       _ ≅ e.inverse.obj 0 := e.inverse.mapIso iso1
--       _ ≅ 0 := e.inverse.mapZeroObject
--   let iso3 : (0 : ModuleCat R) ≅ ModuleCat.of R PUnit :=
--   { hom := ⟨⟨fun _ => 0, by intros; simp⟩, by intros; simp⟩
--     inv := ⟨⟨fun _ => 0, by intros; simp⟩, by intros; simp⟩
--     hom_inv_id := by intros; ext; simp only [ModuleCat.coe_comp, Function.comp_apply,
--       Limits.id_zero]; rfl
--     inv_hom_id := by intros; ext; exact Subsingleton.elim _ _ }
--   refine h $ LinearEquiv.injective iso2.toLinearEquiv $
--     LinearEquiv.injective iso3.toLinearEquiv $ Subsingleton.elim _ _


-- lemma IsSimpleModule.functor
--     (M : ModuleCat R) [simple_module : IsSimpleModule R M] : IsSimpleModule S (e.functor.obj M) := by
--   rw [isSimpleModule_iff_injective_or_eq_zero] at simple_module ⊢
--   rcases simple_module with ⟨nontriv, H⟩
--   refine ⟨e.nontrivial M, fun N f => ?_⟩
--   let F := e.unit.app M ≫ e.inverse.map f
--   rcases H _ F with H|H
--   · simp only [Functor.id_obj, Functor.comp_obj, Preadditive.IsIso.comp_left_eq_zero, F] at H
--     replace H : e.inverse.map f = e.inverse.map 0 := by simpa using H
--     exact Or.inl $ e.inverse.map_injective H
--   · simp only [Functor.id_obj, Functor.comp_obj, F] at H
--     refine Or.inr ?_
--     rw [← ModuleCat.mono_iff_injective] at H ⊢
--     have m1 : Mono (e.functor.map $ e.unit.app M ≫ e.inverse.map f) := e.functor.map_mono _
--     simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp, Equivalence.fun_inv_map,
--       Equivalence.functor_unit_comp_assoc] at m1
--     exact mono_of_mono f (e.counitInv.app N)

instance : SMul K (End $ ModuleCat.of R R) where
  smul k (f : R →ₗ[R] R) := k • f

@[simp]
lemma algebra_smul_end_def (k : K) (f : R →ₗ[R] R) (r : R) : (k • f) r = k • f r := rfl

#synth Algebra K $ R →ₗ[R] R

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

-- variable {R S} in
-- def aux1 : End (ModuleCat.of R R) ≃ₐ[K] End (e.functor.obj $ ModuleCat.of R R) where
--   toFun f := e.functor.map f
--   invFun g := e.unit.app _ ≫ e.inverse.map g ≫ e.unitInv.app _
--   left_inv := by
--     intro f
--     simp only [Functor.comp_obj, Equivalence.inv_fun_map, Functor.id_obj, Category.assoc,
--       Iso.hom_inv_id_app, Category.comp_id]
--     rw [← Category.assoc]
--     change (e.unit ≫ e.unitInv).app _ ≫ _ = _
--     simp
--   right_inv := by
--     intro g
--     simp only [Functor.comp_obj, Functor.map_comp, Equivalence.fun_inv_map, Functor.id_obj,
--       Category.assoc, Equivalence.counitInv_functor_comp, Category.comp_id]
--     exact e.functor_unit_comp_assoc (ModuleCat.of R R) g
--   map_mul' x y := by simp
--   map_add' x y := by simp only; rw [e.functor.map_add]
--   commutes' k := rfl


-- noncomputabl : Ring (e.functor.obj $ ModuleCat.of R R) :=
--   division_ring_exists_unique_isSimpleModule K R S e (ModuleCat.of R R) |>.choose

-- noncomputable def aux20 :
--     (e.functor.obj (ModuleCat.of R R)) ≃ₐ[K] ModuleCat.of S S := by
--   have :  IsSimpleModule R (ModuleCat.of R R) := inferInstanceAs $ IsSimpleModule R R
--   have : IsSimpleModule S (e.functor.obj (ModuleCat.of R R)) :=
--     IsSimpleModule.functor R S e (ModuleCat.of R R)
--   have := division_ring_exists_unique_isSimpleModule S (e.functor.obj $ ModuleCat.of R R)
--   exact this.some.toModuleIso


noncomputable def toRingMopEquiv : Nonempty $ Rᵐᵒᵖ ≃ₐ[K] Sᵐᵒᵖ := by
  obtain ⟨ring_inst, alg_inst, iso1, h⟩ :=
    division_ring_exists_unique_isSimpleModule K R S e (ModuleCat.of R R)
  refine Nonempty.intro $ mopEquivEnd K R |>.trans $ AlgEquiv.trans ?_ $ mopEquivEnd K S |>.symm
  let alg' : Algebra K (End $ e.functor.obj $ ModuleCat.of R R) :=
  { smul := fun k f =>
      _
    toFun := _
    map_one' := _
    map_mul' := _
    map_zero' := _
    map_add' := _
    commutes' := _
    smul_def' := _ }

  let e1 : End (ModuleCat.of R R) ≃ₐ[K] End (e.functor.obj $ ModuleCat.of R R) := sorry


noncomputable def toRingEquiv : R ≃+* S where
  toFun r := toRingMopEquiv R S e (.op r) |>.unop
  invFun s := toRingMopEquiv R S e |>.symm (.op s) |>.unop
  left_inv r := by simp
  right_inv s := by simp
  map_mul' a b := by simp
  map_add' a b := by simp

end division_ring

noncomputable def ringEquivOfDivisionRing
    (R S : Type u) [DivisionRing R] [DivisionRing S] [IsMoritaEquivalent' R S] :
    R ≃+* S := division_ring.toRingEquiv R S (equiv R S)

end IsMoritaEquivalent'
