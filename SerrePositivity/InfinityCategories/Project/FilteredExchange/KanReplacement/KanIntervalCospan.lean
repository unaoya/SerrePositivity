module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementKan
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementSection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks

/-!
概要：Kan 対象の cospan の左脚を path で置き換え、元の cospan から自然に比較する。
方針：定値 path の切断と終点での厳密な復元を使う。
規約：元の二射に fibration 性を仮定しない。
使われ方：path 引き戻しの native な極限性を元の図式へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}

/-- 概要：第一入力の区間の path 置換を Kan 対象として束ねる。
方針：構成済みの置換の Kan 性を使う。
規約：元の f に fibration 性は不要。使われ方：置換 cospan の第一対象。 -/
def intervalReplacementKanObject (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement (show X.obj ⟶ Y.obj from f), inferInstance⟩

/-- 概要：置換した Kan 対象から元の終域への終点射。
方針：区間の path 置換の終点評価を束ねる。
規約：元の終域 Y は保持する。使われ方：置換 cospan の左脚。 -/
def intervalReplacementKanEndpoint (f : X ⟶ Y) : intervalReplacementKanObject f ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint (show X.obj ⟶ Y.obj from f)

/-- 概要：束ねた置換の終点射の台は Kan fibration。
方針：単体集合での相対充填性を使う。
規約：右脚の条件は不要。使われ方：既存の native な引き戻し錐。 -/
instance intervalReplacementKanEndpoint_fibration (f : X ⟶ Y) :
    Fibration (show (intervalReplacementKanObject f).obj ⟶ Y.obj from
      intervalReplacementKanEndpoint f) :=
  inferInstanceAs (Fibration (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint (show X.obj ⟶ Y.obj from f)))

/-- 概要：元の cospan から path 置換した cospan への通常の自然変換。
方針：左対象で定値切断を使い、残る二対象は恒等射にする。
規約：自然性は元の f との厳密な等式。使われ方：coherent 図式の同型。 -/
def intervalCospanSection (f : X ⟶ Y) (g : Z ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram f g ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram (intervalReplacementKanEndpoint f) g := by
  let η : cospan f g ⟶ cospan (intervalReplacementKanEndpoint f) g :=
    cospanHomMk (𝟙 Y)
      (show X ⟶ intervalReplacementKanObject f from _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f) (𝟙 Z)
      (by
        exact (Category.comp_id (show X.obj ⟶ Y.obj from f)).trans
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection_endpoint (show X.obj ⟶ Y.obj from f)).symm) (by simp)
  exact Functor.whiskerLeft (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) η

end SerrePositivity.InfinityCategories.Project.FilteredExchange
