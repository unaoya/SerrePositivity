module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarSourceVerdier
public import SerrePositivity.DifferentialGraded.Verdier.ScalarGraphDerivedComparison
public import SerrePositivity.DifferentialGraded.Verdier.GraphCompositionShift

/-! # 元の tria からの係数変更と明示的 dg 商の比較

通常の交換、射影的 perfect モデル、固定 path の包含等式から構成する。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

/-- 係数変更の前後で明示的 dg 商への実際の導来延長を行う正方形。 -/
def sourceScalarQuotientDerivedSquare :
    triaInclusion A D ⋙ dgDerivedExtension A D (QuotientObject D S) (inclusion A D S) ⋙
        ScalarExtension.derivedExtension φ (QuotientObject D S) ⋙
          dgDerivedExtension A' (ScalarExtension.DGBaseChange φ (QuotientObject D S))
            (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
            (quotientBaseChangeDGFunctor φ D S) ≅
      triaInclusion A D ⋙ ScalarExtension.derivedExtension φ D ⋙
        dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
          (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
          (inclusion A' (ScalarExtension.DGBaseChange φ D) S) := by
  let e : triaInclusion A D ⋙
      dgDerivedExtension A D (QuotientObject D S) (inclusion A D S) ⋙
        ScalarExtension.derivedExtension φ (QuotientObject D S) ≅
      triaInclusion A D ⋙ ScalarExtension.derivedExtension φ D ⋙
        dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
          (ScalarExtension.DGBaseChange φ (QuotientObject D S))
          (ScalarExtension.dgFunctor φ (inclusion A D S)) :=
    isoWhiskerLeft (triaToPerfect A D)
      (scalarGraphPerfectDerivedSquare φ D (QuotientObject D S) (inclusion A D S))
  exact isoWhiskerRight e
      (dgDerivedExtension A' (ScalarExtension.DGBaseChange φ (QuotientObject D S))
        (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
        (quotientBaseChangeDGFunctor φ D S)) ≪≫
    isoWhiskerLeft (triaInclusion A D ⋙ ScalarExtension.derivedExtension φ D)
      (derivedGraphExtensionCompositionIso A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.DGBaseChange φ (QuotientObject D S))
        (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
        (ScalarExtension.dgFunctor φ (inclusion A D S)) (quotientBaseChangeDGFunctor φ D S) ≪≫
        eqToIso (congrArg
          (dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
            (QuotientObject (ScalarExtension.DGBaseChange φ D) S))
          (quotientBaseChangeDGFunctor_inclusion φ D S)))

/-- 上の同型を商側の tria に制限した実際の正方形。 -/
def sourceScalarQuotientTriaSquare :
    derivedComparisonTria A D S ⋙ quotientScalarTriaFunctor φ S ≅
      sourceScalarTriaFunctor φ D ⋙
        derivedComparisonTria A' (ScalarExtension.DGBaseChange φ D) S :=
  ((whiskeringRight _ _ _).obj
    (triaInclusion A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S))).preimageIso
    (sourceScalarQuotientDerivedSquare φ D S)

/-- 元の係数変更を先に局所化した関手と、局所商比較との正方形。 -/
def sourceScalarLocalQuotientSquare :
    sourceScalarVerdierFunctor φ D S ⋙
        localQuotientTriaFunctor A' (ScalarExtension.DGBaseChange φ D) S ≅
      localQuotientTriaFunctor A D S ⋙ quotientScalarTriaFunctor φ S :=
  (Localization.fullyFaithfulWhiskeringLeft
    (triaQuotient A D S) (triaImage A D S).trW _).preimageIso
    ((associator _ _ _).symm ≪≫
      isoWhiskerRight (sourceScalarVerdierFactors φ D S) _ ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft (sourceScalarTriaFunctor φ D)
        (localQuotientTriaFactors A' (ScalarExtension.DGBaseChange φ D) S) ≪≫
      (sourceScalarQuotientTriaSquare φ D S).symm ≪≫
      isoWhiskerRight (localQuotientTriaFactors A D S).symm _ ≪≫ associator _ _ _)

variable (h : localKFlat A D S) (h' : localKFlat A' (ScalarExtension.DGBaseChange φ D) S)

/-- 直接局所化した元の係数変更と、以前の局所同値による輸送は自然同型になる。 -/
def sourceScalarLocalTransportIso :
    sourceScalarVerdierFunctor φ D S ≅ localScalarTriaExtension φ S h h' :=
  ((whiskeringRight _ _ _).obj
    (localQuotientTriaEquivalence A' (ScalarExtension.DGBaseChange φ D) S h').functor).preimageIso
    (sourceScalarLocalQuotientSquare φ D S ≪≫ (localScalarTriaSquare φ S h h').symm)

/-- 直接局所化した係数変更に対する、既存の指定 Verdier 比較そのものの正方形。 -/
def sourceScalarCanonicalQuotientSquare :
    sourceScalarVerdierFunctor φ D S ⋙
        quotientVerdierComparison A' (ScalarExtension.DGBaseChange φ D) S ≅
      quotientVerdierComparison A D S ⋙ quotientScalarTriaFunctor φ S :=
  isoWhiskerLeft _ (quotientComparisonModelsIso A' (ScalarExtension.DGBaseChange φ D) S).symm ≪≫
    sourceScalarLocalQuotientSquare φ D S ≪≫
      isoWhiskerRight (quotientComparisonModelsIso A D S) _
end SerrePositivity.DifferentialGraded.DGQuotient
