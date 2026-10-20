module

public import SerrePositivity.InfinityCategories.F2.KanIntervalConeProjectionIsos

/-!
概要：区間引き戻しの native 錐そのものが指定する二次の可換性。
方針：元の左右の二単体から同じ中心脚を消去する。
規約：元の二単体の値を保持。使われ方：元の区間 path の可換同型との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {X Y Z : KanObject.{u}}

/-- 概要：元の cospan 射上の native な三角形の指定同型。
方針：元の二単体を読む。規約：代表を選び直さない。使われ方：二脚の可換性。 -/
def intervalPullbackConeTriangleIso (f : X ⟶ Y) (g : Z ⟶ Y)
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    FunctorIso (intervalPullbackConeKanLeg f g j)
      (intervalPullbackConeKanLeg f g i ≫ (kanPullbackDiagram f g).map a) :=
  kanNativeConeTriangleIso (intervalPullbackCone f g) _
    ((intervalPullbackCone_vertex f g).trans (spaceInfinityVertex_eq_coherent _)) a

/-- 概要：元の二つの native な脚の像の間の指定可換同型。
方針：中心脚への左右の三角形を合成する。
規約：元の錐の二単体を保持。使われ方：具体的な path の指定値との最終整合。 -/
def intervalPullbackConeNativeCommutativity (f : X ⟶ Y) (g : Z ⟶ Y) :
    FunctorIso (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left) ≫ f)
      (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right) ≫ g) :=
  (intervalPullbackConeTriangleIso f g (AsSmall.up.map WalkingCospan.Hom.inl)).symm ≪≫
    intervalPullbackConeTriangleIso f g (AsSmall.up.map WalkingCospan.Hom.inr)

end SerrePositivity.InfinityCategories.F2
