module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientCompositeRealization
public import SerrePositivity.InfinityCategories.Derived.DGPresentedFamilyEvaluationIso
/-!
概要：同じ実同時細分の三評価族を、商の実 AW 合成と全降下選択空間上で比較する。
方針：商内の実合成比較を保持したまま、任意反転標的の三評価族と一つの実三角形を取る。
規約：各評価比較は全選択空間上の関手同型。使われ方：商 Hom 作用の二入力合成整合性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x y z : D) {K Y : SSet.{max u v}} [Quasicategory Y]
variable (F : dgNerve A D ⟶ Y)
variable (r : K ⟶ dgRoofCorrespondence A D P x y) (s : K ⟶ dgRoofCorrespondence A D P y z)
variable (C : DGInvertingFiniteRoofComposition A D P x y z (dgQuotientNerveProjection A D P) r s)
variable (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))
variable (c : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj y) ((DGQuotient.inclusion A D P).obj z))
/-- 同じ細分の三実評価族・実三角形と、全選択空間上の三作用族の比較。 -/
structure DGInvertingBinaryEvaluation where
  quotient : DGQuotientCompositeRealization A D P x y z r s C b c
  first : DGInvertingPinchedFamilyEvaluation A D F
    C.source.first.denominator.obj.hom C.source.first.coefficient
  second : DGInvertingPinchedFamilyEvaluation A D F
    C.source.second.denominator.obj.hom C.source.second.coefficient
  composite : DGInvertingPinchedFamilyEvaluation A D F
    C.source.compositeDenominator.obj.hom C.source.compositeNumerator
  triangle : Truncated.Edge.CompStruct
    (intervalFamilyEdge (first.value ≫ pinchedHomToIntervalMappingSpace _ _))
    (intervalFamilyEdge (second.value ≫ pinchedHomToIntervalMappingSpace _ _))
    (intervalFamilyEdge (composite.value ≫ pinchedHomToIntervalMappingSpace _ _))
  firstIso : FunctorIso (dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
    (SSet.const (functorVertex first.value))
  secondIso : FunctorIso (dgInvertingHomActionFamily A D P y z F ≫ (pre c).app _)
    (SSet.const (functorVertex second.value))
  compositeIso : FunctorIso (dgInvertingHomActionFamily A D P x z F ≫
    (pre (pinchedHomCompositionFamily b c)).app _) (SSet.const (functorVertex composite.value))
/-- 指定二商 Hom 族と商側の同時細分に、任意反転標的での三作用族の同時実評価が存在する。 -/
lemma dgInvertingBinaryEvaluation_nonempty (hP : DGQuotient.localKFlat A D P)
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (Hr : SSet.Homotopy (r ≫ dgRoofCorrespondenceMap A D P x y)
      (b ≫ dgQuotientFixedHomRoofMap A D P x y))
    (Hs : SSet.Homotopy (s ≫ dgRoofCorrespondenceMap A D P y z)
      (c ≫ dgQuotientFixedHomRoofMap A D P y z)) :
    Nonempty (DGInvertingBinaryEvaluation A D P x y z F r s C b c) := by
  obtain ⟨Q⟩ := dgQuotientCompositeRealization_nonempty A D P x y z r s C b c hP Hr Hs
  obtain ⟨er⟩ := dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    C.source.first.denominator.obj.hom C.source.first.denominator.property
      C.source.first.coefficient
  obtain ⟨es⟩ := dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    C.source.second.denominator.obj.hom C.source.second.denominator.property
      C.source.second.coefficient
  obtain ⟨ec⟩ := dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    C.source.compositeDenominator.obj.hom C.source.compositeDenominator.property
      C.source.compositeNumerator
  obtain ⟨T⟩ := dgInvertingPinchedFamilyEvaluation_compositionTriangle_nonempty A D F P x y z
    C.source C.prisms hF er es ec
  obtain ⟨Ir⟩ := dgPresentedFamilyEvaluationIso_nonempty A D P x y F r C.source.first er b Hr
  obtain ⟨Is⟩ := dgPresentedFamilyEvaluationIso_nonempty A D P y z F s C.source.second es c Hs
  let R : DGFiniteRoofPresentation A D P x z C.source.compositeDiagram :=
    ⟨C.source.compositeDenominator, C.source.compositeNumerator,
      functorHomotopyRefl C.source.compositeDiagram⟩
  obtain ⟨Ic⟩ := dgPresentedFamilyEvaluationIso_nonempty A D P x z F C.source.compositeDiagram R ec
    (pinchedHomCompositionFamily b c) Q.comparison
  exact ⟨⟨Q, er, es, ec, T, Ir, Is, Ic⟩⟩
end SerrePositivity.InfinityCategories
