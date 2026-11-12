module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftFibrationStrictColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationUnitIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratorEquivalence

/-!
概要：有限底上模型の連続置換で、元の指定 left fibration の小さい filtered 全表示を作る。
方針：元の有限部分複体の置換余錐を left fibration 対象へ持ち上げ、単位の逆で頂点を戻す。
規約：添字は元の宇宙 u、指定された同じ対象を厳密な頂点にする。
使われ方：一般の小さい底上の前層の小さい compact 生成族。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：底上の連続置換を left fibration 対象値の全関手に持ち上げる。
方針：元の置換の射と関手則をそのまま使う。
規約：忘却すると元の置換と厳密に一致する。
使われ方：元の有限部分複体の図式と余錐を同時に持ち上げる。 -/
def continuousLeftFibrationObjectFunctor (B : SSet.{u}) : Over B ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B where
  obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject X
  map f := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacement B).map f
  map_id X := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacement B).map_id X
  map_comp f g := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacement B).map_comp f g

/-- 概要：元の有限底上模型の置換を同じ添字の left fibration 図式にする。
方針：元の有限部分複体図式に置換関手を後合成する。
規約：対象の独立な選択で図式を代用しない。
使われ方：小さい生成族による元の対象の全表示。 -/
def finiteLeftFibrationDiagram {B : SSet.{u}} (X : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.FiniteOverPieces X ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.finiteOverPiecesDiagram X ⋙ continuousLeftFibrationObjectFunctor B

/-- 概要：元の全包含余錐を置換後の left fibration 対象へ持ち上げる。
方針：同じ全余錐に置換関手を適用する。
規約：各脚は元の包含の連続置換。
使われ方：通常の余極限性から native な余極限性への移送。 -/
def finiteLeftFibrationCocone {B : SSet.{u}} (X : Over B) :
    Cocone (finiteLeftFibrationDiagram X) :=
  (continuousLeftFibrationObjectFunctor B).mapCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.finiteOverPiecesCocone X)

/-- 概要：同じ有限模型の全余錐は left fibration ∞ 圏の余極限となる。
方針：忘却後の元の通常の filtered 余極限を strict 余錐の判定へ渡す。
規約：元の底は quasicategory、図式と全脚は変更しない。
使われ方：置換前の指定頂点へ戻す前の全表示。 -/
lemma finiteLeftFibrationCocone_isColimit {B : SSet.{u}} [Quasicategory B] (X : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (finiteLeftFibrationCocone X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationStrictCocone_isColimit _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.finiteOverReplacementCocone_isColimit X)

/-- 概要：元の指定 left fibration 自身を厳密な頂点に持つ、小さい filtered 全表示を得る。
方針：置換余錐の頂点を元の単位の逆同型で輸送する。
規約：同じ有限部分複体上の全図式を保持し、頂点の同値だけで結論しない。
使われ方：一般の前層の小さい生成圏の生成性。 -/
lemma exists_finiteLeftFibrationPresentation {B : SSet.{u}} [Quasicategory B]
    (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (finiteLeftFibrationDiagram X.val)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X := by
  let c := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (finiteLeftFibrationCocone X.val)
  have hc := finiteLeftFibrationCocone_isColimit X.val
  have hv : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject X.val) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_vertex _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso c hc
    (eqToIso (congrArg HomotopyCategory.mk hv) ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationUnitVertexIso X).symm)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
