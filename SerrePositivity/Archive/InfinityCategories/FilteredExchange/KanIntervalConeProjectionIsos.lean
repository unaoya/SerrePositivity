module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeSpecifiedComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalPullbackPathHomotopy

/-!
概要：区間引き戻し錐の二脚と元の二射影の指定同型。
方針：同じ全錐円柱からの脚比較に元の始域射影を後合成する。
規約：存在命題から同型を選び直さない。使われ方：指定 path と native な可換性の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : KanObject.{u}}

/-- 概要：元の左脚と具体的な第一射影の指定同型。
方針：同じ脚比較を元の始域射影で後合成。
規約：元の全円柱の比較を保持。使われ方：指定 path との整合。 -/
def intervalPullbackConeFstIso (f : X ⟶ Y) (g : Z ⟶ Y) :
    FunctorIso (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left))
      (intervalPullbackLeft f g) := by
  let e := intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.left)
  change FunctorIso
    (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left) ≫
      intervalReplacementSection f)
    (pullback.fst (intervalReplacementEndpoint f) g) at e
  have h := e.postcomp (pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f)
  change FunctorIso
    ((intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left) ≫
      intervalReplacementSection f) ≫
        pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f)
    (intervalPullbackLeft f g) at h
  rw [Category.assoc, intervalReplacementSection_projection, Category.comp_id] at h
  exact h

/-- 概要：元の右脚と具体的な第二射影の指定同型。
方針：同じ脚比較の切断成分は恒等射。
規約：元の全円柱の比較を保持。使われ方：指定 path との整合。 -/
def intervalPullbackConeSndIso (f : X ⟶ Y) (g : Z ⟶ Y) :
    FunctorIso (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right))
      (intervalPullbackRight f g) := by
  let e := intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.right)
  change FunctorIso
    (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right) ≫ 𝟙 Z.obj)
    (intervalPullbackRight f g) at e
  exact functorIsoOfEq e
    (Category.comp_id (show (intervalPullbackKanObject f g).obj ⟶ Z.obj from
      intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right))) rfl

end SerrePositivity.InfinityCategories.F2
