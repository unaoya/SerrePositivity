module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRelativeTargetCartesian
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRelativeFiber
public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseRelativeInnerFibration
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialFiberTransfer
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeHomRestrictionInnerFibration

/-!
概要：境界固定の関手圏に対する局所の相対余錐条件を全空間の始点境界充填へ移す。
方針：相対比較の fiber の同定と cartesian 輸送の保存から一般の移送定理を使う。
規約：結論は指定した全余錐の像を固定する全空間の相対充填。
使われ方：変動する Kan 添字に対する相対的な組み立て。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：関手の制限に対する局所相対余錐の普遍性は全空間で始点境界を充填する。
方針：局所条件を相対比較の fiber へ移し、cartesian な両射影と保存される輸送で全空間へ移す。
規約：単射 v による関手の制限を標的の射とし、元の p は cocartesian fibration。
使われ方：境界・部分図式・標的の全余錐を同時に固定する coherent な延長。 -/
lemma kanRelativeJoinRelative_initialBoundary_of_local {K C P Q X : SSet.{u}}
    [Quasicategory C] [Quasicategory X] (p : K ⟶ C) [CocartesianFibration p]
    (v : P ⟶ Q) [Mono v] (c : C _⦋0⦌)
    {d : vertexFiber p c ⟶ (ihom Q).obj X} {z : JoinCocone d}
    (hz : KanRelativeCoconeLifting ((pre v).app X) z) :
    InitialBoundaryLifting
      (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction (kanRelativeJoinInlOver p) ((pre v).app X))
      (((kanRelativeJoinCoconeFiberIso p c ((ihom Q).obj X)).hom.app (Opposite.op ⦋0⦌)
        (functorVertex z.val)).val) := by
  have : Mono (kanRelativeJoinInlOver p).left :=
    inferInstanceAs (Mono (relativeJoinInl p (𝟙 C)))
  have : CocartesianFibration (Over.mk p).hom := inferInstanceAs (CocartesianFibration p)
  have : CocartesianFibration (Over.mk (relativeJoinBaseProjection p (𝟙 C))).hom :=
    inferInstanceAs (CocartesianFibration (relativeJoinBaseProjection p (𝟙 C)))
  exact kanInitialBoundaryLifting_of_fiber_map
    (SerrePositivity.InfinityCategories.fiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) ((ihom Q).obj X))
    (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeProjection (kanRelativeJoinInlOver p) ((pre v).app X))
    (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction (kanRelativeJoinInlOver p) ((pre v).app X))
    (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_projection (kanRelativeJoinInlOver p) ((pre v).app X))
    (kanRelativeJoinRelativeRestriction_preservesCartesianEdges p ((pre v).app X)) c _
    (kanRelativeJoinRelativeFiber_initialBoundary p c ((pre v).app X) hz)

end SerrePositivity.InfinityCategories.F1B
