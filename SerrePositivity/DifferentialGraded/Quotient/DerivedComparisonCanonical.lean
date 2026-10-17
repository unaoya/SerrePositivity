module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonExtensionCoherence
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonEquivalence
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonTriangulated

/-! # 既存の有限 cell 比較と導来延長による比較の自然同型

指定 Verdier 商上の既存の比較関手そのものへ、局所 K-flat の同値を移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- tria 上の二つの導来加群圏への比較は自然同型。 -/
def quotientTriaDerivedModelsIso (S : Set D) :
    derivedComparisonFromTria A D S ≅ quotientTriaToDerived A D S := by
  let e := homotopyFiniteCellTriaEquivalence A D Set.univ
  let G := derivedComparisonFromTria A D S
  let hc : e.functor ⋙ G ≅ quotientCellToDerived A D S :=
    finiteCellHomotopyDerivedExtensionIso A D (QuotientObject D S) (inclusion A D S) Set.univ
  exact (isoWhiskerRight e.counitIso G).symm ≪≫ isoWhiskerLeft e.inverse hc

/-- 商側の tria に制限した同じ自然同型。 -/
def quotientTriaModelsIso (S : Set D) :
    derivedComparisonTria A D S ≅ quotientTriaFunctor A D S :=
  ((whiskeringRight _ _ _).obj (triaInclusion A (QuotientObject D S))).preimageIso
    (X := derivedComparisonTria A D S) (Y := quotientTriaFunctor A D S)
    (quotientTriaDerivedModelsIso A D S)

/-- 導来延長から作った tria 比較の、指定 Verdier 局所化による因子化。 -/
def localQuotientTriaFactors (S : Set D) :
    triaQuotient A D S ⋙ localQuotientTriaFunctor A D S ≅ derivedComparisonTria A D S :=
  ((whiskeringRight _ _ _).obj (triaInclusion A (QuotientObject D S))).preimageIso
    (X := triaQuotient A D S ⋙ localQuotientTriaFunctor A D S)
    (Y := derivedComparisonTria A D S) (derivedQuotientLiftFactors A D S)

/-- 指定 Verdier 商上の、二つの実際の比較関手の自然同型。 -/
def quotientComparisonModelsIso (S : Set D) :
    localQuotientTriaFunctor A D S ≅ quotientVerdierComparison A D S :=
  (Localization.fullyFaithfulWhiskeringLeft
    (triaQuotient A D S) (triaImage A D S).trW _).preimageIso
    (localQuotientTriaFactors A D S ≪≫ quotientTriaModelsIso A D S ≪≫
      (quotientVerdierComparisonFactors A D S).symm)

/-- 既存の指定比較関手そのものの、局所 K-flat 仮定下の充満忠実性。 -/
def quotientVerdierComparisonFullyFaithful (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierComparison A D S).FullyFaithful :=
  (localQuotientTriaFullyFaithful A D S h).ofIso (quotientComparisonModelsIso A D S)

/-- 有限 cell のホモトピー圏モデルを使う既存の比較関手を関手部分とする同値。 -/
def quotientVerdierLocalEquivalence (S : Set D) (h : localKFlat A D S) :
    TriaQuotient A D S ≌ TriaCategory A (QuotientObject D S) :=
  (localQuotientTriaEquivalence A D S h).changeFunctor (quotientComparisonModelsIso A D S)

instance quotientVerdierLocalEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).functor.CommShift ℤ := by
  change (quotientVerdierComparison A D S).CommShift ℤ
  infer_instance
instance quotientVerdierLocalEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).inverse.CommShift ℤ :=
  (quotientVerdierLocalEquivalence A D S h).commShiftInverse ℤ
instance quotientVerdierLocalEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).CommShift ℤ :=
  (quotientVerdierLocalEquivalence A D S h).commShift_of_functor ℤ
instance quotientVerdierLocalEquivalenceFunctorIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).functor.IsTriangulated := by
  change (quotientVerdierComparison A D S).IsTriangulated
  infer_instance
instance quotientVerdierLocalEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (quotientVerdierLocalEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (quotientVerdierLocalEquivalence A D S h) inferInstance

end SerrePositivity.DifferentialGraded.DGQuotient
