module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationComparisonRestriction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StraighteningCounitRestriction

/-!
概要：選択した余単位の底変換に関する自然性の可換式。
方針：cartesian な比較を通常の前合成と同定し表現空間の三角形を使う。
規約：全図式と全空間を保つ同じ比較を用いる。
使われ方：普遍余単位と任意の族への制限の整合性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：余単位の cartesian 制限は通常の前合成による余単位と一致する。
方針：標準表現の制限を回収し図式同型の前合成の公式を使う。
規約：終点の図式の等式の移送を明示する。
使われ方：底変換に関する余単位の可換式の右辺。 -/
lemma coherentStraighteningRestrictedCounit_diagram {B D : SSet.{u + 1}}
    (F : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (g : D ⟶ B) (h : g ≫ G = F) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningRestrictedRepresentation F G g h).diagramIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.unstraighteningTransportRepresentation F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningRestrictedCounitWitnessIso F G g h) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentStraighteningCounit G).precomp g ≪≫
        eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)) h) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningRestrictedCounitWitnessIso]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation.diagramIso_trans,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation.diagramIso_eqToIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.unstraighteningTransportRepresentation G).cartesianRestrict
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap F G g h) g (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_isPullback F G g h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.unstraighteningTransportRepresentation F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.unstraighteningTransportRepresentation_cartesianRestrict F G g h)]
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberLeftStraighteningRepresentation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.leftUnstraighteningProjection_hasSmallSimplexFibers G)
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.unstraighteningTransportRepresentation G
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberTransportRepresentationVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.leftUnstraighteningProjection_hasSmallSimplexFibers G) R S
  have he := R.cartesianRestrict_diagramIso S a (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap F G g h) g
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_isPullback F G g h)
  exact congrArg (fun e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ R.diagram) (g ≫ G) ↦
    e ≪≫ eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)) h)) he

/-- 概要：選択した余単位は分類の制限比較と通常の前合成に関して可換。
方針：表現空間で証明した三角形の二番目の辺を前合成で表示する。
規約：任意の底と底の射に適用し小ささを追加しない。
使われ方：単位・余単位の自然性の底変換側の界面。 -/
lemma coherentStraighteningCounit_baseChange_naturality {B D : SSet.{u + 1}}
    (F : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (g : D ⟶ B) (h : g ≫ G = F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningRestrictionDiagramIso F G g h ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentStraighteningCounit G).precomp g ≪≫
        eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)) h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentStraighteningCounit F := by
  rw [← coherentStraighteningRestrictedCounit_diagram F G g h]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningCounitRestriction_diagram_triangle F G g h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
