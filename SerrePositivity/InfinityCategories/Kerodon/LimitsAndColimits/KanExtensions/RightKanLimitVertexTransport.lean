module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanLimitIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningLimitVertex

/-!
概要：同型な右 Kan の添字写像の局所図式で、指定極限錐の頂点を比較する。
方針：coslice 射影の引き戻しを全分類図式の同型で比較し、極限の一意性へ渡す。
規約：同じ係数と同じ局所頂点を使い、元の指定極限錐を引数に保つ。
使われ方：Kerodon Definition 7.3.1.2（Tag 02Y9）、HTT 5.1.5.6、S8。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
variable {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
  {δ δ' : K ⟶ C}

local instance rightKanLimitVertexTransport_leftFibration (a : K ⟶ C) (v : C _⦋0⦌) :
    LeftFibration (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm v)) a) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
    sliceUnderProjection (SSet.yonedaEquiv.symm v)))⟩

/-- 同型な右 Kan の添字写像に対する、同じ局所値の指定極限の頂点比較。
Kerodon Definition 7.3.1.2（Tag 02Y9）、既存の分類・復元と極限の一意性の移送則。 -/
def rightKanLimitVertexIsoOfFunctorIso (e : FunctorIso δ δ') (O : K ⟶ D) (v : C _⦋0⦌)
    (c : JoinCone (rightKanDiagram δ O v)) (d : JoinCone (rightKanDiagram δ' O v))
    (hc : IsLimitCone c) (hd : IsLimitCone d) : VertexIso c.vertex d.vertex :=
  limitVertexIsoOfLeftStraighteningIso
    (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm v)) δ)
    (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm v)) δ')
    (leftPullbackClassificationIso (sliceUnderProjection (SSet.yonedaEquiv.symm v)) e) O c d hc hd

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
