module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleGlobalAugmentation

/-! # K-flat部分圏の準同型局所化と全導来bimodule圏の同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

instance derivedRightKFlatReplacement_lifting (hC : localHomKFlat A C) :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (rightKFlatReplacementFunctor A B C hC) (derivedRightKFlatReplacement A B C hC) :=
  ⟨eqToIso (derivedRightKFlatReplacement_fac A B C hC)⟩

def rightKFlatCompositeFacIso (hC : localHomKFlat A C) :
    rightKFlatToDerived A B C ⋙
        (rightKFlatDerivedInclusion A B C ⋙ derivedRightKFlatReplacement A B C hC) ≅
      rightKFlatInclusion A B C ⋙ rightKFlatReplacementFunctor A B C hC :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (rightKFlatDerivedInclusion_fac A B C))
      (derivedRightKFlatReplacement A B C hC) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightKFlatInclusion A B C)
      (eqToIso (derivedRightKFlatReplacement_fac A B C hC))

instance rightKFlatComposite_lifting (hC : localHomKFlat A C) :
    Localization.Lifting (rightKFlatToDerived A B C) (rightKFlatQuasiIso A B C)
      (rightKFlatInclusion A B C ⋙ rightKFlatReplacementFunctor A B C hC)
      (rightKFlatDerivedInclusion A B C ⋙ derivedRightKFlatReplacement A B C hC) :=
  ⟨rightKFlatCompositeFacIso A B C hC⟩

def rightKFlatReplacementUnitIso (hC : localHomKFlat A C) :
    rightKFlatDerivedInclusion A B C ⋙ derivedRightKFlatReplacement A B C hC ≅
      𝟭 (DerivedRightKFlatBimoduleCategory A B C) :=
  Localization.liftNatIso (rightKFlatToDerived A B C) (rightKFlatQuasiIso A B C)
    (rightKFlatInclusion A B C ⋙ rightKFlatReplacementFunctor A B C hC)
    (rightKFlatToDerived A B C)
    (rightKFlatDerivedInclusion A B C ⋙ derivedRightKFlatReplacement A B C hC) (𝟭 _)
    (rightKFlatAugmentationIso A B C hC)

def rightKFlatReplacementCounitIso (hC : localHomKFlat A C) :
    derivedRightKFlatReplacement A B C hC ⋙ rightKFlatDerivedInclusion A B C ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (rightKFlatReplacementFunctor A B C hC ⋙ rightKFlatDerivedInclusion A B C)
    (bimoduleToDerived A B C)
    (derivedRightKFlatReplacement A B C hC ⋙ rightKFlatDerivedInclusion A B C) (𝟭 _)
    (rightKFlatGlobalAugmentationIso A B C hC)

/-- Mathlibのadjointificationで三角恒等式も備えた圏同値を構成する。 -/
def rightKFlatDerivedEquivalence (hC : localHomKFlat A C) :
    DerivedRightKFlatBimoduleCategory A B C ≌ DerivedBimoduleCategory A B C :=
  CategoryTheory.Equivalence.mk (rightKFlatDerivedInclusion A B C)
    (derivedRightKFlatReplacement A B C hC)
    (rightKFlatReplacementUnitIso A B C hC).symm (rightKFlatReplacementCounitIso A B C hC)

lemma rightKFlatDerivedInclusion_isEquivalence (hC : localHomKFlat A C) :
    (rightKFlatDerivedInclusion A B C).IsEquivalence :=
  (rightKFlatDerivedEquivalence A B C hC).isEquivalence_functor

def rightKFlatDerivedInclusion_fullyFaithful (hC : localHomKFlat A C) :
    (rightKFlatDerivedInclusion A B C).FullyFaithful :=
  (rightKFlatDerivedEquivalence A B C hC).fullyFaithfulFunctor

end SerrePositivity.DifferentialGraded.BimoduleTensor
