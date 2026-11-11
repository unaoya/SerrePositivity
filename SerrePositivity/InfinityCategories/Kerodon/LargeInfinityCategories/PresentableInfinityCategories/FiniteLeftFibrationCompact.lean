module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteRelativeHomAccessible
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationHomIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeHomModel
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteLeftFibrationFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.F2CompactUniverseColimits

/-!
概要：有限底上模型の連続置換は、元の left fibration ∞ 圏で compact である。
方針：相対 Hom の全 filtered 保存を、元の大きい共変 Hom との全自然比較で輸送する。
規約：compact 性は既存の定義を使い、置換後の全空間の有限性は要求しない。
使われ方：一般の小さい底上の前層の小さい compact 生成族。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：相対 Hom の全 filtered 保存から、同じ left fibration 対象の compact 性を得る。
方針：元の共変 Hom への宇宙変更と全自然同型で同じ指定余錐像の保存を移す。
規約：元の小さい添字と元の指定余錐を保持する。
使われ方：有限底上模型の連続置換の compact 性の判定。 -/
lemma leftFibrationObject_isKappaCompact_of_homPreservation {B : SSet.{u}}
    {κ : Cardinal.{u}} (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation X.val)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) := by
  intro I hI hFiltered D c hc
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation X.val) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.mapJoinCocone_universe_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram_map_isColimit (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation X.val)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation X.val) c) (h I D c hc)
  exact hm.of_functorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeHom_covariantModelIso X).precomp (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c).val).symm

/-- 概要：任意の有限底上模型の元の連続置換は compact である。
方針：有限始域の相対 Hom 保存を元の単位の全関手同型で置換後へ移す。
規約：底は任意の小さい quasicategory、全空間の有限性は置換前だけに要求する。
使われ方：前層の小さい compact 生成圏の対象族。 -/
lemma finiteLeftFibrationReplacement_isCompact {B : SSet.{u}} [Quasicategory B]
    (A : Over B) [A.left.Finite] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} Cardinal.aleph0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject A)) :=
  leftFibrationObject_isKappaCompact_of_homPreservation _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteRelativeHom_isKappaAccessibleFunctor A).of_functorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationHomIso A).symm)

/-- 概要：共通の小さい有限底上符号族の全頂点は compact である。
方針：各符号の実現の有限性を、同じ連続置換の compact 性へ渡す。
規約：対象族は元の宇宙 u、compact 性は元の ∞ 圏の定義で述べる。
使われ方：小さい compact 全部分生成圏の構成。 -/
lemma finiteLeftFibrationGeneratorVertex_isCompact {B : SSet.{u}} [Quasicategory B]
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverCode B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} Cardinal.aleph0 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteLeftFibrationGeneratorVertex q) :=
  finiteLeftFibrationReplacement_isCompact q.realization

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
