module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientCompositeRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPresentedFamilyEvaluationIso
/-!
概要：同じ実同時細分の三評価族を、商の実 AW 合成と全降下選択空間上で比較する。
方針：商内の実合成比較を保持したまま、任意反転標的の三評価族と一つの実三角形を取る。
規約：各評価比較は全選択空間上の関手同型。使われ方：商 Hom 作用の二入力合成整合性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y z : D) {K Y : SSet.{max u v}} [Quasicategory Y]
variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
variable (r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) (s : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z)
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingFiniteRoofComposition A D P x y z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) r s)
variable (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
variable (c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj z))
/-- 同じ細分の三実評価族・実三角形と、全選択空間上の三作用族の比較。 -/
structure DGInvertingBinaryEvaluation where
  quotient : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientCompositeRealization A D P x y z r s C b c
  first : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingPinchedFamilyEvaluation A D F
    C.source.first.denominator.obj.hom C.source.first.coefficient
  second : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingPinchedFamilyEvaluation A D F
    C.source.second.denominator.obj.hom C.source.second.coefficient
  composite : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingPinchedFamilyEvaluation A D F
    C.source.compositeDenominator.obj.hom C.source.compositeNumerator
  triangle : Truncated.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (first.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (second.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (composite.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
  firstIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex first.value))
  secondIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P y z F ≫ (pre c).app _)
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex second.value))
  compositeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x z F ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily b c)).app _) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex composite.value))
/-- 指定二商 Hom 族と商側の同時細分に、任意反転標的での三作用族の同時実評価が存在する。 -/
lemma dgInvertingBinaryEvaluation_nonempty (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (Hr : SSet.Homotopy (r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y))
    (Hs : SSet.Homotopy (s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P y z)
      (c ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P y z)) :
    Nonempty (DGInvertingBinaryEvaluation A D P x y z F r s C b c) := by
  obtain ⟨Q⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientCompositeRealization_nonempty A D P x y z r s C b c hP Hr Hs
  obtain ⟨er⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    C.source.first.denominator.obj.hom C.source.first.denominator.property
      C.source.first.coefficient
  obtain ⟨es⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    C.source.second.denominator.obj.hom C.source.second.denominator.property
      C.source.second.coefficient
  obtain ⟨ec⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingPinchedFamilyEvaluation_nonempty A D F P hF
    C.source.compositeDenominator.obj.hom C.source.compositeDenominator.property
      C.source.compositeNumerator
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingPinchedFamilyEvaluation_compositionTriangle_nonempty A D F P x y z
    C.source C.prisms hF er es ec
  obtain ⟨Ir⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPresentedFamilyEvaluationIso_nonempty A D P x y F r C.source.first er b Hr
  obtain ⟨Is⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPresentedFamilyEvaluationIso_nonempty A D P y z F s C.source.second es c Hs
  let R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofPresentation A D P x z C.source.compositeDiagram :=
    ⟨C.source.compositeDenominator, C.source.compositeNumerator,
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl C.source.compositeDiagram⟩
  obtain ⟨Ic⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPresentedFamilyEvaluationIso_nonempty A D P x z F C.source.compositeDiagram R ec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily b c) Q.comparison
  exact ⟨⟨Q, er, es, ec, T, Ir, Is, Ic⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
