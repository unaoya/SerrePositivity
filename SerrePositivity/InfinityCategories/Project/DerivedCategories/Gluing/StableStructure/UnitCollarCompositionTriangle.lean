module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ModelUnitCollarTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.UnitSpanTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.FunctorTriangleTwoFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.LaxPullbacks.LaxHomDiagonalDeformations
/-! # 同じ四面体から取り出す左右実補正対角の合成三角形

概要：左右実補正道の対角を、同じ主経路上の実合成三角形へ接続する。
方針：正本の共通対角で端点表示を合わせ、同じ二単体の第三辺を橋として取り出す。
規約：実補正道・全入力・全時間・四面体由来の二単体を保持する。
使われ方：係数面を含む残りの高次貼り合わせを、選択済み二変形へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

def dgGluingFirstCollarDiagonalSpanHomotopy :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCollarSpanHomotopy R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomCommonDiagonal_first R C D M X Y).symm

def dgGluingLastCollarDiagonalSpanHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCollarSpanHomotopy R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)

def dgGluingUnitCollarBridgeHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorTriangleThirdHomotopy
    (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarTriangleDiagram R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarTriangleDiagram_two R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarTriangleDiagram_zero R C D M X Y)

def dgGluingUnitCollarCompositionTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingUnitCollarBridgeHomotopy R C D M X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorTriangleOfTwoFaces
    (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)
    (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarTriangleDiagram R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarTriangleDiagram_two R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarTriangleDiagram_zero R C D M X Y)

lemma dgGluingUnitCollarCompositionTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingUnitCollarBridgeHomotopy R C D M X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangle_homEq (dgGluingUnitCollarCompositionTriangle R C D M X Y)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
