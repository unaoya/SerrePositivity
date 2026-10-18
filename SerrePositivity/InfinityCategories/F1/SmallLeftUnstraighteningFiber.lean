module

public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.F1.VertexFiberTotalIso
public import SerrePositivity.InfinityCategories.F1.UniverseEquivalenceDescent
public import SerrePositivity.InfinityCategories.F1.UniverseFiber

/-!
概要：小さい unstraightening の fiber と元の図式の値の同値。
方針：縮小の同型を fiber に制限し、元の fiber の比較を同じ宇宙へ降ろす。
規約：底は任意の小さい単体集合でよく、図式の strict 性は不要。
使われ方：Kerodon Example 5.6.2.9、Corollary 5.6.0.6、小さい代表の各値の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：小さい unstraightening の fiber の持ち上げは元の全空間の fiber と同型。
方針：fiber と ULift の交換同型に、全空間の底上の同型が誘導する同型を合成する。
規約：元の底の頂点 c とその ULift を比較する。
使われ方：Kerodon Corollary 5.6.0.6、小さい fiber と普遍的な fiber の比較。 -/
noncomputable def smallLeftUnstraighteningFiberIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (vertexFiber (smallLeftUnstraighteningProjection F) c) ≅
      vertexFiber (leftUnstraighteningProjection F) (ULift.up c) :=
  uliftVertexFiberIso (smallLeftUnstraighteningProjection F) c ≪≫
    vertexFiberTotalIso ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F))
      (leftUnstraighteningProjection F) (smallLeftUnstraighteningIso F)
      (smallLeftUnstraighteningIso_projection F) (ULift.up c)

/-- 概要：小さい unstraightening の fiber と図式の値の宇宙持ち上げは同値。
方針：fiber の縮小の同型と元の unstraightening の値の比較を合成する。
規約：順方向には構成した fiber の同型を使う。
使われ方：Kerodon Example 5.6.2.9、小さい fiber の値を元の宇宙へ降ろす準備。 -/
noncomputable def smallLeftUnstraighteningLiftedFiberValueEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : B _⦋0⦌) :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj
      (vertexFiber (smallLeftUnstraighteningProjection F) c))
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up c))).obj) :=
  (qCatEquivalenceOfIso (smallLeftUnstraighteningFiberIso F c)).trans
    (leftUnstraighteningFiberValueEquivalence F (ULift.up c))

/-- 概要：小さい unstraightening の fiber は元の図式の Kan 値と同じ宇宙で同値。
方針：持ち上げた二つの fiber の同値を Kan 複体の同値として降ろす。
規約：底の quasicategory 性は仮定せず、元の宇宙 u で比較する。
使われ方：Kerodon Example 5.6.2.9、Corollary 5.6.0.6、一般の coherent 図式の値の回収。 -/
noncomputable def smallLeftUnstraighteningFiberValueEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : B _⦋0⦌) :
    QCatEquivalence (vertexFiber (smallLeftUnstraighteningProjection F) c)
      (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up c))).obj :=
  (smallLeftUnstraighteningLiftedFiberValueEquivalence F c).downOfKan

end SerrePositivity.InfinityCategories
