module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.UnitCollarCompositionTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.UnitCapCoefficientChoiceComparison
/-! # 指定対角辺に端点を合わせた実単位補正三角形

概要：実単位補正三角形を、正本共通対角と正本係数対角を端点とする同じ三角形へ移す。
方針：元入力 lift の対角等式で端点表示だけを合わせ、実三辺と二単体を保持する。
規約：実補正道や指定済み変形の全時間を変更しない。
使われ方：六片の高次合成等式を、正本の三対角辺の合成等式へ消去する。
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

def dgGluingFirstCapDiagonalSpanHomotopy :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCapSpanHomotopy R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift_diagonal R C D M X Y)

def dgGluingLastCapDiagonalSpanHomotopy :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCapSpanHomotopy R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift_diagonal R C D M X Y) rfl

def dgGluingFirstUnitSpanAlignedDiagonalTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)
    (dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y) where
  diagram := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitSpanDiagonalTriangle R C D M X Y).diagram
  face_zero := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitSpanDiagonalTriangle R C D M X Y).face_zero
  face_one := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitSpanDiagonalTriangle R C D M X Y).face_one
  face_two := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitSpanDiagonalTriangle R C D M X Y).face_two

def dgGluingLastUnitSpanAlignedDiagonalTriangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)
    (dgGluingLastCapDiagonalSpanHomotopy R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y) where
  diagram := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitSpanDiagonalTriangle R C D M X Y).diagram
  face_zero := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitSpanDiagonalTriangle R C D M X Y).face_zero
  face_one := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitSpanDiagonalTriangle R C D M X Y).face_one
  face_two := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitSpanDiagonalTriangle R C D M X Y).face_two

lemma dgGluingFirstUnitSpanAlignedDiagonalTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstCollarDiagonalSpanHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingFirstCapDiagonalSpanHomotopy R C D M X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangle_homEq
    (dgGluingFirstUnitSpanAlignedDiagonalTriangle R C D M X Y)

lemma dgGluingLastUnitSpanAlignedDiagonalTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingLastCapDiagonalSpanHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastCollarDiagonalSpanHomotopy R C D M X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorCompositionTriangle_homEq
    (dgGluingLastUnitSpanAlignedDiagonalTriangle R C D M X Y)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
