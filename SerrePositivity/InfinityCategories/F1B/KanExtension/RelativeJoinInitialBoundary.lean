module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialFiberTransfer
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinCartesianRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeHomRestrictionInnerFibration

/-!
概要：fiber の普遍余錐から相対 join の関手の族の制限の全空間の相対境界充填を得る。
方針：両射影の cartesian 性と制限の輸送の保存により、fiber の充填性を移す。
規約：元の射は cocartesian fibration、底と標的は quasicategory。
使われ方：Kerodon Lemma 7.3.4.5–6 の相対骨格による Kan 拡張の組み立て。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対 join の制限の fiber の始点境界充填は全空間でも成り立つ。
方針：両側の底への cartesian 射影と制限の cartesian 辺の保存を適用する。
規約：V 自体が cartesian fibration であるという追加仮定は不要。
使われ方：fiber の普遍余錐を大域的な充填条件へ移す。 -/
lemma kanRelativeJoinRestriction_initialBoundary_of_fiber {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (c : C _⦋0⦌)
    (x : (vertexFiber
      (SerrePositivity.InfinityCategories.fiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D) c) _⦋0⦌)
    (hx : InitialBoundaryLifting (SerrePositivity.InfinityCategories.fiberwiseHomPreFiber (D := D)
      (kanRelativeJoinInlOver p) c) x) :
    InitialBoundaryLifting (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)) x.val := by
  have : InnerFibration (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)) :=
    kanRelativeJoinRestriction_innerFibration p
  exact kanInitialBoundaryLifting_of_fiber_map
    (SerrePositivity.InfinityCategories.fiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D)
    (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D)
    (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
    (SerrePositivity.InfinityCategories.fiberwiseHomPre_projection (D := D) (kanRelativeJoinInlOver p))
    (kanRelativeJoinRestriction_preservesCartesianEdges p) c x hx

/-- 概要：fiber の余極限余錐は相対 join 制限の全空間で相対始点境界を充填する。
方針：通常の余錐制限の fiber の表示と輸送による全空間への移送を合成する。
規約：これは大域的な相対充填であり、全 Kan 拡張の存在の結論は別途組み立てる。
使われ方：相対骨格上の普遍余錐の族の延長。 -/
lemma kanRelativeJoinCocone_initialBoundary {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (c : C _⦋0⦌) {d : vertexFiber p c ⟶ D} {z : JoinCocone d}
    (hz : IsColimitCone z) :
    InitialBoundaryLifting (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))
      (((kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
        (functorVertex z.val)).val) := by
  apply kanRelativeJoinRestriction_initialBoundary_of_fiber p c
  exact kanRelativeJoinCoconeFiber_initialBoundary p c hz

end SerrePositivity.InfinityCategories.F1B
