module

public import SerrePositivity.HomologicalAlgebra.AlgebraBaseChangeTensorAugmentation
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionSingleH0
public import SerrePositivity.HomologicalAlgebra.RealizedSingleH0Normalization

/-! # 実底変換と導来 tensor の H⁰ 正規化

標準 augmentation と係数制限の既存 H⁰ 正規化を使い、元の通常 tensor の元を保つ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S]

/-- 実底変換の元の H⁰ を係数制限し、元の導来 tensor の H⁰ へ比較する。 -/
def algebraBaseChangeTensorH0Iso :
    (ModuleCat.restrictScalars (algebraMap R B)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj :=
  ((derivedRestrictScalarsHomologyIso (algebraMap R B) 0).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso
      (algebraBaseChangeTensorIso R B S)

/-- 元の augmentation の H⁰ 比較は、通常 tensor への標準正規化を保つ。 -/
theorem algebraBaseChangeTensorH0Iso_augmentation :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) B S)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) B S)
    (algebraBaseChangeTensorH0Iso R B S).hom ≫
      (derivedTensorH0AlgEquiv (R := R) B S).toLinearEquiv.toModuleIso.hom =
    (ModuleCat.restrictScalars (algebraMap R B)).map
      ((boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app (ModuleCat.of R S)) ≫
      (algebraBaseChangeModuleNormalizationIso R B S).hom := by
  let := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) B S)
  let := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) B S)
  let φ := algebraMap R B
  let U := ModuleCat.restrictScalars φ
  let H := DerivedCategory.homologyFunctor (ModuleCat R) 0
  let H' := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0
  let M := ModuleCat.of R S
  let L := (ModuleCat.extendScalars φ).obj M
  let X := ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
  let a := (boundedAboveDerivedBaseChangeModuleAugmentation φ).app M
  let eN := algebraBaseChangeModuleNormalizationIso R B S
  let eT := algebraBaseChangeTensorIso R B S
  let ρ := (derivedRestrictScalarsHomologyIso φ 0).app X
  let hT := (derivedTensorH0AlgEquiv (R := R) B S).toLinearEquiv.toModuleIso.hom
  have ht : hT = H.map (boundedAboveDerivedTensorAlgebraAugmentation (R := R) B S).hom.hom.hom ≫
      ε.hom.app (ModuleCat.of R (B ⊗[R] S)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change derivedTensorH0AlgEquiv B S z = _
    rw [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_apply]
    rw [boundedAboveDerivedTensorAlgebraAugmentation_hom]
    rfl
  have hn := ε.hom.naturality eN.hom
  change H.map ((DerivedCategory.singleFunctor (ModuleCat R) 0).map eN.hom) ≫
      ε.hom.app (ModuleCat.of R (B ⊗[R] S)) = ε.hom.app (U.obj L) ≫ eN.hom at hn
  have hρ := (derivedRestrictScalarsHomologyIso φ 0).hom.naturality a
  change H.map ((derivedRestrictScalars φ).map a) ≫
      (derivedRestrictScalarsHomologyIso φ 0).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj L) =
    ρ.hom ≫ U.map (H'.map a) at hρ
  have hb := boundedAboveDerivedBaseChangeModuleAugmentation_homology φ M
  rw [realizedSingleH0Iso_hom_eq_standard] at hb
  have hraw : H.map eT.hom ≫ hT =
      ρ.hom ≫ U.map ((boundedAboveDerivedBaseChangeModuleH0Iso φ).hom.app M) ≫ eN.hom := by
    rw [ht]
    have he := congrArg (fun k => H.map k ≫ ε.hom.app (ModuleCat.of R (B ⊗[R] S)))
      (algebraBaseChangeTensorIso_augmentation R B S)
    simp only [Functor.map_comp, Category.assoc] at he
    rw [show H.map eT.hom ≫
        H.map (boundedAboveDerivedTensorAlgebraAugmentation (R := R) B S).hom.hom.hom ≫
        ε.hom.app (ModuleCat.of R (B ⊗[R] S)) = _ from he.symm]
    rw [hn]
    erw [reassoc_of% (derivedRestrictionSingleH0_normalization φ L)]
    erw [reassoc_of% hρ]
    rw [← Functor.map_comp_assoc, hb]
  change (ρ.inv ≫ H.map eT.hom) ≫ hT = _
  rw [Category.assoc, hraw, Iso.inv_hom_id_assoc]

/-- 元の B 線形 H⁰ 比較と tensor の環比較は、全ての元で一致する。 -/
theorem algebraBaseChangeTensorH0Iso_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) B S)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) B S)
    derivedTensorH0AlgEquiv B S ((algebraBaseChangeTensorH0Iso R B S).hom x) =
      (algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom
        ((boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app
          (ModuleCat.of R S) x) := by
  let := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) B S)
  let := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) B S)
  have h := congrArg (fun k => k.hom x) (algebraBaseChangeTensorH0Iso_augmentation R B S)
  change derivedTensorH0AlgEquiv B S ((algebraBaseChangeTensorH0Iso R B S).hom x) =
    (algebraBaseChangeModuleNormalizationIso R B S).hom
      ((boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app
          (ModuleCat.of R S) x) at h
  exact h.trans (algebraBaseChangeModuleNormalizationIso_apply R B S _)

end SerrePositivity
