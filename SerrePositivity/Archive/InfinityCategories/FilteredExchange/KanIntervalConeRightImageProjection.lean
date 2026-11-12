module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeImageIsos
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeProjectionIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：右脚の像の指定比較と元の第二射影の比較の整合。
方針：引き戻しの可換等式による端点の輸送を戻す。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {X Y Z : KanObject.{u}}
/-- 概要：右脚の像の指定比較と元の第二射影の比較の整合。
方針：引き戻しの可換等式による端点の輸送を戻す。
規約：元の指定同型の値と合成の向きを保持する。
使われ方：𝒮 の引き戻しと元の全 path の比較。 -/
lemma intervalPullbackConeRightImageIso_projection (f : X ⟶ Y) (g : Z ⟶ Y) :
    intervalPullbackConeRightImageIso f g ≪≫
      functorEqIso (pullback.condition (f := intervalReplacementEndpoint f) (g := g)) =
    (intervalPullbackConeSndIso f g).postcomp g := by
  let r : (intervalPullbackKanObject f g).obj ⟶ Z.obj :=
    intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right)
  let e := intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.right)
  have hs : r ≫ 𝟙 Z.obj = r := Category.comp_id _
  have hh := functorIso_postcomp_heq_of_heq e (intervalPullbackConeSndIso f g) hs rfl
    (intervalPullbackConeSndIso_heq f g) g
  have h := functorIsoOfEq_trans_eqIso (e.postcomp g)
    (congrArg (fun k ↦ k ≫ g) hs)
    (pullback.condition (f := intervalReplacementEndpoint f) (g := g)).symm
  exact h.trans (eq_of_heq ((functorIsoOfEq_heq _ _ _).trans hh.symm))

end SerrePositivity.InfinityCategories.F2
