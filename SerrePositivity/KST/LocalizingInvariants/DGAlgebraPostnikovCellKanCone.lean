module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingKanFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovAlgebraPullback

/-!
概要：元の Postnikov 錐の cell 写像模型を、実 Kan 錐と空間値の錐に束ねる。
方針：元の代数 pullback 錐を同じ cell 写像関手で写し、小さい cospan に制限する。
規約：頂点と二脚は元の射の像。空間での極限性と局所化後の比較は別に検証する。
使われ方：指定 Postnikov 拡大の全写像空間による普遍性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovCellKanDiagram : AsSmall.{u} WalkingCospan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (AsSmall.down ⋙
    cospan (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))) ⋙
        multiplicativeCellMappingKanFunctor R A

def postnikovCellKanCone : Cone (postnikovCellKanDiagram R A B n hn) :=
  (multiplicativeCellMappingKanFunctor R A).mapCone
    ((postnikovAlgebraPullbackCone R B n hn).whisker
      (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan))

def postnikovCellKanCone_isLimit : IsLimit (postnikovCellKanCone R A B n hn) :=
  multiplicativeCellMappingKanCone_isLimit R A _ _
    ((postnikovAlgebraPullback_isLimit R B n hn).whiskerEquivalence
      (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm)

set_option maxHeartbeats 800000 in -- 元の cell 分解と Postnikov 錐の頂点の定義を照合する。
lemma postnikovCellKanCone_vertex :
    (postnikovCellKanCone R A B n hn).pt.obj =
      multiplicativeMappingSimplices R (cellResolution R A) (postnikov R B (n + 1)) := rfl

def postnikovCellSpaceCone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (postnikovCellKanDiagram R A B n hn)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (postnikovCellKanCone R A B n hn)).cast
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram (postnikovCellKanDiagram R A B n hn))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
