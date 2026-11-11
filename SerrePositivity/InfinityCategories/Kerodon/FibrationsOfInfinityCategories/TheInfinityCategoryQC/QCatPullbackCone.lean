module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatHomPostcomposition

/-!
概要：QCat の inner fibration に沿う引き戻し錐の構成。
方針：元の単体集合の引き戻しと全ての試験対象の豊穣 Hom を比較する。
規約：小さい対象の宇宙は u、coherent nerve の宇宙は u+1。
使われ方：Cat_∞ の引き戻しの構成と普遍性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {E F B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (p : E ⟶ B) (q : F ⟶ B)
variable [InnerFibration (show E.obj ⟶ B.obj from p)]

/-- 概要：inner fibration に沿う引き戻しを QCat の対象にする。
方針：台の単体集合の引き戻しの quasicategory 性で束縛する。
規約：元の二対象と底は同じ宇宙 u の小さい quasicategory。
使われ方：Cat_∞ の厳密な引き戻し錐の頂点。 -/
def qCatPullbackObject : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  (⟨pullback (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q), inferInstance⟩ :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})
/-- 概要：QCat の二射の厳密な引き戻し錐。
方針：元の単体集合の二射影と引き戻しの可換性を使う。
規約：通常の圏としての錐であり、∞ 極限性は後で検証する。
使われ方：coherent nerve に写す厳密な錐の入力。 -/
def qCatPullbackOrdinaryCone : PullbackCone p q :=
  PullbackCone.mk (f := p) (g := q) (W := qCatPullbackObject p q)
    (pullback.fst (show E.obj ⟶ B.obj from p) q)
    (pullback.snd (show E.obj ⟶ B.obj from p) q) (by
      exact pullback.condition (f := (show E.obj ⟶ B.obj from p))
        (g := (show F.obj ⟶ B.obj from q)))
/-- 概要：QCat の二射の小さい cospan 図式。
方針：通常の cospan を AsSmall の同値に沿って持ち上げる。
規約：図式の射は元の指定された p、q のまま。
使われ方：Cat_∞ の coherent な cospan 図式。 -/
def qCatPullbackDiagram : AsSmall.{u} WalkingCospan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} := AsSmall.down ⋙ cospan p q
/-- 概要：小さい cospan に沿う QCat の厳密な引き戻し錐。
方針：通常の引き戻し錐を AsSmall の忘却で制限する。
規約：頂点と二射影を変えない。
使われ方：全豊穣 Hom で検査する錐。 -/
def qCatPullbackCone : Cone (qCatPullbackDiagram p q) :=
  (qCatPullbackOrdinaryCone p q).whisker (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
