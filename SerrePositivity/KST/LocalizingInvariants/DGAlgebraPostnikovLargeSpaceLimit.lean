module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingLargeKan
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovInfinityCone
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellSpaceLimit
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationEquivalenceLifting

/-!
概要：元の大きい代数表示の Postnikov 図式に沿う、持ち上げた cell 写像の空間値極限。
方針：元の三頂点錐で ULift の極限保存を使い、元の大きい添字へ再添字付けする。
規約：元の頂点と二脚を保持し、比較後の極限性を仮定しない。
使われ方：元の擬同型 ∞ 局所化の写像空間と同じ宇宙での普遍性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SSet.modelCategoryQuillen
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovCellLargeKanDiagram : PostnikovInfinityShape.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} :=
  (postnikovInfinityShapeDown ⋙
    cospan (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))) ⋙
        multiplicativeCellMappingLargeKanFunctor R A

set_option maxHeartbeats 800000 in -- 実 cell・Postnikov 表示と大きい宇宙の錐を照合する。
def postnikovCellLargeKanCone : Cone (postnikovCellLargeKanDiagram R A B n hn) :=
  ((multiplicativeCellMappingLargeKanFunctor R A).mapCone
    (postnikovAlgebraPullbackCone R B n hn)).whisker postnikovInfinityShapeDown

set_option maxHeartbeats 800000 in -- 実 cell・Postnikov 表示と大きい宇宙の錐を照合する。
def postnikovCellLargeKanCone_underlying_isLimit :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (postnikovCellLargeKanCone R A B n hn)) := by
  exact (multiplicativeCellMappingLargeKanCone_underlying_isLimit R A _ _
    (postnikovAlgebraPullback_isLimit R B n hn)).whiskerEquivalence
      (AsSmall.equiv : WalkingCospan ≌ PostnikovInfinityShape.{u}).symm

set_option maxHeartbeats 800000 in -- 実 cell・Postnikov 表示と大きい宇宙の錐を照合する。
def postnikovCellLargeSpaceCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (postnikovCellLargeKanDiagram R A B n hn)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (postnikovCellLargeKanCone R A B n hn)).cast
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram (postnikovCellLargeKanDiagram R A B n hn))

set_option maxHeartbeats 800000 in -- 実 cell・Postnikov 表示と大きい宇宙の錐を照合する。
lemma postnikovCellLargeSpaceCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (postnikovCellLargeSpaceCone R A B n hn) := by
  have := postnikovCellMappingClass_fibration R A B n hn
  have : Fibration
      (show ((multiplicativeCellMappingLargeKanFunctor R A).obj
          (postnikovPerturbedExtension R B n hn)).obj ⟶
        ((multiplicativeCellMappingLargeKanFunctor R A).obj
          (postnikovDerivationTarget R B n hn)).obj from
        (multiplicativeCellMappingLargeKanFunctor R A).map (postnikovPerturbedClass R B n hn)) := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_uliftFunctor_map
      (multiplicativeMappingPostcompose R (cellResolution R A) (postnikovPerturbedClass R B n hn))
  have : ∀ Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (postnikovCellLargeKanDiagram R A B n hn) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z => by
    change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1}).obj (op Z)).map
      ((multiplicativeCellMappingLargeKanFunctor R A).map (postnikovPerturbedClass R B n hn)))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHom_map_fibration Z _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (postnikovCellLargeKanCone R A B n hn)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ (postnikovCellLargeKanCone_underlying_isLimit R A B n hn))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
