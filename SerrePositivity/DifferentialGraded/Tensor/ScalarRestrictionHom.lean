module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionModuleMaps
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # 係数制限による全次数 Hom の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

instance restrictionLaxMonoidal : (restriction φ).LaxMonoidal :=
  (adjunction φ).rightAdjointLaxMonoidal

instance adjunctionMonoidal : (adjunction φ).IsMonoidal := inferInstance

/-- 斉次射の各成分を係数制限する。 -/
abbrev restrictCochain {K L : Complex A'} {p : ℤ} (f : Homogeneous K L p) :
    Homogeneous ((restriction φ).obj K) ((restriction φ).obj L) p :=
  f.map (ModuleCat.restrictScalars φ)

/-- 全次数 Hom を、係数制限した複体の間の Hom に送る。 -/
def restrictionHom (K L : Complex A') :
    (restriction φ).obj (homComplex A' K L) ⟶
      homComplex A ((restriction φ).obj K) ((restriction φ).obj L) where
  f p := ModuleCat.ofHom
    (X := ((restriction φ).obj (homComplex A' K L)).X p)
    (Y := (homComplex A ((restriction φ).obj K) ((restriction φ).obj L)).X p) {
    toFun := restrictCochain φ
    map_add' f g := Cochain.map_add f g (ModuleCat.restrictScalars φ)
    map_smul' a f := by
      apply Cochain.ext
      intro i j h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (φ a) • f.v i j h x = (φ a) • f.v i j h x
      rfl }
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact δ_map p q f (ModuleCat.restrictScalars φ) |>.symm

lemma restrictionHom_v (K L : Complex A') (p i j : ℤ) (h : i + p = j)
    (f : Homogeneous K L p) :
    ((restrictionHom φ K L).f p f).v i j h = (ModuleCat.restrictScalars φ).map (f.v i j h) := rfl

set_option backward.isDefEq.respectTransparency true in
lemma restriction_μ_apply (K L : Complex A') (p q n : ℤ) (h : p + q = n)
    (x : K.X p) (y : L.X q) :
    (Functor.LaxMonoidal.μ (restriction φ) K L).f n
      (ιTensorObj ((restriction φ).obj K) ((restriction φ).obj L) p q n h (x ⊗ₜ[A] y)) =
        ιTensorObj K L p q n h (x ⊗ₜ[A'] y) := by
  let := φ.toAlgebra
  change ((adjunction φ).counit.app K ⊗ₘ (adjunction φ).counit.app L).f n
    ((tensorIso φ ((restriction φ).obj K) ((restriction φ).obj L)).hom.f n
      ((1 : A') ⊗ₜ[A]
        ιTensorObj ((restriction φ).obj K) ((restriction φ).obj L) p q n h (x ⊗ₜ[A] y))) = _
  erw [cochainTensorBaseChangeIso_apply_ι φ ((restriction φ).obj K) ((restriction φ).obj L),
    tensorMap_apply]
  congr 1
  change ((ModuleCat.extendRestrictScalarsAdj φ).counit.app (K.X p) ((1 : A') ⊗ₜ[A] x)) ⊗ₜ[A']
    ((ModuleCat.extendRestrictScalarsAdj φ).counit.app (L.X q) ((1 : A') ⊗ₜ[A] y)) = _
  erw [ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ,
    ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ]

set_option backward.isDefEq.respectTransparency true in
lemma restriction_ε_one :
    (Functor.LaxMonoidal.ε (restriction φ)).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A') := by
  let := φ.toAlgebra
  change (unitIso φ).hom.f 0
    ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = _
  exact sphereIso_one φ 0

lemma restrictCochain_units_smul {K L : Complex A'} {p : ℤ}
    (a : ℤˣ) (f : Homogeneous K L p) :
    restrictCochain φ (a • f) = a • restrictCochain φ f := by
  apply Cochain.ext
  intro i j h
  simp only [restrictCochain, Cochain.map_v, Cochain.units_smul_v,
    CategoryTheory.Functor.map_units_smul]

lemma restrictionHom_identity (K : Complex A') :
    Functor.LaxMonoidal.ε (restriction φ) ≫ (restriction φ).map (identity K) ≫
      restrictionHom φ K K = identity ((restriction φ).obj K) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change restrictCochain φ ((identity K).f 0
    ((Functor.LaxMonoidal.ε (restriction φ)).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))) = _
  rw [restriction_ε_one]
  have hid : (identity K).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A')) = Cochain.ofHom (𝟙 K) := by
    exact congrArg Subtype.val (cycleFromUnit_unitFromCycle _ _)
  rw [hid]
  change (Cochain.ofHom (𝟙 K)).map (ModuleCat.restrictScalars φ) =
    (cycleFromUnit _ (identity ((restriction φ).obj K))).val
  rw [Cochain.map_ofHom, CategoryTheory.Functor.map_id, identity, cycleFromUnit_unitFromCycle]

lemma restrictionHom_composition (K L M : Complex A') :
    Functor.LaxMonoidal.μ (restriction φ) (homComplex A' K L) (homComplex A' L M) ≫
        (restriction φ).map (enrichedComposition K L M) ≫ restrictionHom φ K M =
      (restrictionHom φ K L ⊗ₘ restrictionHom φ L M) ≫
        enrichedComposition ((restriction φ).obj K) ((restriction φ).obj L)
          ((restriction φ).obj M) := by
  apply tensorHom_ext
  intro p q n h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change restrictCochain φ ((enrichedComposition K L M).f n
    ((Functor.LaxMonoidal.μ (restriction φ) (homComplex A' K L) (homComplex A' L M)).f n
      (ιTensorObj ((restriction φ).obj (homComplex A' K L))
        ((restriction φ).obj (homComplex A' L M))
        p q n h (f ⊗ₜ[A] g)))) =
    (enrichedComposition _ _ _).f n
      ((restrictionHom φ K L ⊗ₘ restrictionHom φ L M).f n
        (ιTensorObj ((restriction φ).obj (homComplex A' K L))
        ((restriction φ).obj (homComplex A' L M))
          p q n h (f ⊗ₜ[A] g)))
  rw [restriction_μ_apply, enrichedComposition_apply, tensorMap_apply, enrichedComposition_apply]
  rw [restrictCochain_units_smul]
  change (p * q).negOnePow • ((Cochain.comp f g h).map (ModuleCat.restrictScalars φ)) =
    (p * q).negOnePow • (f.map (ModuleCat.restrictScalars φ)).comp
      (g.map (ModuleCat.restrictScalars φ)) h
  rw [Cochain.map_comp]

/-- 係数制限は、移送した自己豊穣構造からの dg 関手を与える。 -/
def restrictionComplexDGFunctor :
    DGFunctor A (TransportEnrichment (restriction φ) (Complex A')) (Complex A) where
  obj := (restriction φ).obj
  map K L := restrictionHom φ K L
  map_id K := restrictionHom_identity φ K
  map_comp K L M := restrictionHom_composition φ K L M

end SerrePositivity.DifferentialGraded.ScalarExtension
