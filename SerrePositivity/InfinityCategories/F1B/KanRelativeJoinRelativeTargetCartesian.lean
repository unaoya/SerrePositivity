module

public import SerrePositivity.InfinityCategories.F1B.KanPullbackCartesianFibration
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomFiberInvertibleLift
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinRelativeCartesian

/-!
概要：境界を固定する関手圏上の相対 join 比較の標的は cartesian fibration。
方針：後合成の各 fiber の可逆辺の持ち上げを、引き戻しの cartesian な輸送の構成へ渡す。
規約：固定するパラメータの包含は任意の単射。
使われ方：全空間の相対始点境界充填への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：関手の制限上の相対 join 比較の標的の射影は cartesian fibration。
方針：制限と後合成の cartesian 辺の保存、後合成の inner 性、各 fiber の可逆辺の持ち上げを使う。
規約：底 C と値域 X は quasicategory、元の p は cocartesian fibration。
使われ方：局所の相対余錐条件を全空間の充填性へ移す標的の構造。 -/
instance kanRelativeJoinRelativeProjection_pre_cartesianFibration {K C P Q X : SSet.{u}}
    [Quasicategory C] [Quasicategory X] (p : K ⟶ C) [CocartesianFibration p]
    (v : P ⟶ Q) [Mono v] :
    CartesianFibration
      (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) ((pre v).app X)) := by
  exact kanCartesianFibration_pullback_over
    (kanFiberwiseHomProjection p ((ihom Q).obj X))
    (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) ((ihom P).obj X))
    (kanFiberwiseHomProjection p ((ihom P).obj X))
    (kanFiberwiseHomPostcomp p ((pre v).app X))
    (kanFiberwiseHomPre (D := (ihom P).obj X) (kanRelativeJoinInlOver p))
    (kanFiberwiseHomPostcomp_projection p ((pre v).app X))
    (kanFiberwiseHomPre_projection (kanRelativeJoinInlOver p))
    (kanFiberwiseHomPostcomp_preservesCartesianEdges p ((pre v).app X))
    (kanRelativeJoinRestriction_preservesCartesianEdges p)
    (kanInvertibleTargetLifting_kanFiberwiseHomPostcompFiber p · v)

end SerrePositivity.InfinityCategories.F1B
