module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentVertices

/-!
概要：与えられた Kan 複体の引き戻し正方形の通常の錐。
方針：指定された頂点と脚を保ち台の極限性を Kan 対象へ持ち上げる。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC


variable {K E D B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (p : E ⟶ B) (q : D ⟶ B)
variable (a : K.obj ⟶ E.obj) (b : K.obj ⟶ D.obj)
variable (h : IsPullback a b (show E.obj ⟶ B.obj from p) (show D.obj ⟶ B.obj from q))
/-- 概要：与えられた Kan 複体の引き戻し正方形の通常の錐。
方針：指定された頂点と脚を保ち台の極限性を Kan 対象へ持ち上げる。
規約：正方形の元の頂点を引き戻し対象に選び直さない。
使われ方：Tamme Remark 6 のホモトピー引き戻しの証明。 -/
def spaceSquareUnderlyingCone : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram p q ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  (Cone.postcompose (Functor.isoWhiskerLeft
    (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)
    (cospanCompIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget p q)).inv).obj
      ((PullbackCone.mk a b h.w).whisker
        (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan))
/-- 概要：与えられた Kan 複体の引き戻し正方形の通常の錐。
方針：指定された頂点と脚を保ち台の極限性を Kan 対象へ持ち上げる。
規約：正方形の元の頂点を引き戻し対象に選び直さない。
使われ方：Tamme Remark 6 のホモトピー引き戻しの証明。 -/
def spaceSquareOrdinaryCone : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying _ (spaceSquareUnderlyingCone p q a b h) K.isKanComplex
/-- 概要：与えられた Kan 複体の引き戻し正方形の通常の錐。
方針：指定された頂点と脚を保ち台の極限性を Kan 対象へ持ち上げる。
規約：正方形の元の頂点を引き戻し対象に選び直さない。
使われ方：Tamme Remark 6 のホモトピー引き戻しの証明。 -/
def spaceSquareOrdinaryCone_forget_isLimit :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (spaceSquareOrdinaryCone p q a b h)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying_forget_isLimit
  apply (IsLimit.postcomposeInvEquiv
    (Functor.isoWhiskerLeft
      (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)
      (cospanCompIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget p q)) _).symm.toFun
  exact h.isLimit.whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
