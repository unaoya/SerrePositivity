module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeNativeCommutativity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportSquare

/-!
概要：引き戻しの二脚の像から置換後の中心への指定比較同型。
方針：切断の等式と引き戻しの可換性で両端だけを揃える。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {X Y Z : KanObject.{u}}

/-- 概要：中心への元の指定脚比較を左射影と終点の合成へ表示する。
方針：通常の錐の左枝の等式。規約：指定値。使われ方：左右の三角形の共通終域。 -/
def intervalPullbackConeCenterImageIso (f : X ⟶ Y) (g : Z ⟶ Y) :
    FunctorIso (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.one))
      (pullback.fst (intervalReplacementEndpoint f) g ≫ intervalReplacementEndpoint f) :=
  functorIsoOfEq (intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.one))
    (Category.comp_id (show (intervalPullbackKanObject f g).obj ⟶ Y.obj from
      intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.one)))
    ((HomotopyLimits.kanPullbackCone (intervalReplacementKanEndpoint f) g).w
      (AsSmall.up.map WalkingCospan.Hom.inl)).symm
/-- 概要：引き戻しの二脚の像から置換後の中心への指定比較同型。
方針：切断の等式と引き戻しの可換性で両端だけを揃える。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
def intervalPullbackConeLeftImageIso (f : X ⟶ Y) (g : Z ⟶ Y) :
    FunctorIso (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left) ≫ f)
      (pullback.fst (intervalReplacementEndpoint f) g ≫ intervalReplacementEndpoint f) :=
  functorIsoOfEq
    ((intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.left)).postcomp
      (intervalReplacementEndpoint f))
    (by
      change ((show (intervalPullbackKanObject f g).obj ⟶ X.obj from
        intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left)) ≫
          intervalReplacementSection f) ≫ intervalReplacementEndpoint f = _
      rw [Category.assoc, intervalReplacementSection_endpoint]) rfl
/-- 概要：引き戻しの二脚の像から置換後の中心への指定比較同型。
方針：切断の等式と引き戻しの可換性で両端だけを揃える。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
def intervalPullbackConeRightImageIso (f : X ⟶ Y) (g : Z ⟶ Y) :
    FunctorIso (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right) ≫ g)
      (pullback.fst (intervalReplacementEndpoint f) g ≫ intervalReplacementEndpoint f) :=
  functorIsoOfEq
    ((intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.right)).postcomp g)
    (by
      exact congrArg (fun k : (intervalPullbackKanObject f g).obj ⟶ Z.obj =>
        k ≫ (show Z.obj ⟶ Y.obj from g))
        (Category.comp_id (show (intervalPullbackKanObject f g).obj ⟶ Z.obj from
          intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right))))
    pullback.condition.symm

end SerrePositivity.InfinityCategories.F2
