module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeLegComparison
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeSpecifiedComparison

/-!
概要：Cat_∞ の引き戻し錐の二脚と候補の二射影の関手同型。
方針：同じ指定円柱の三角形からの比較を元の二始域へ戻す。
規約：指定 path と native な二次の可換性との照合は別工程。
使われ方：Cat_∞ の極限錐と全試験関手による引き戻し表示の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：Cat_∞ の極限錐の左脚を実際の関手として読み戻す。
方針：小さい cospan の左の添字で native な脚を読み戻す。
規約：始域は既存の引き戻し候補の台の単体集合。
使われ方：元の第一射影との関手同型。 -/
def catPullbackConeFst (p : A ⟶ C) (q : B ⟶ C) : catPullback p q ⟶ A :=
  catPullbackConeFunctorLeg p q (AsSmall.up.obj WalkingCospan.left)
/-- 概要：Cat_∞ の極限錐の右脚を実際の関手として読み戻す。
方針：小さい cospan の右の添字で native な脚を読み戻す。
規約：元の第二始域を終域とする。
使われ方：元の第二射影との関手同型。 -/
def catPullbackConeSnd (p : A ⟶ C) (q : B ⟶ C) : catPullback p q ⟶ B :=
  catPullbackConeFunctorLeg p q (AsSmall.up.obj WalkingCospan.right)
/-- 概要：読み戻した左脚は候補の元の第一射影と関手同型。
方針：切断との合成の比較を始域射影で後合成し、切断の等式で簡約する。
規約：頂点の自己同値を挟まず同じ引き戻し候補からの関手を比較する。
使われ方：native な Cat_∞ の極限錐と全試験関手の第一射影の接続。 -/
def catPullbackConeFstIso (p : A ⟶ C) (q : B ⟶ C) :
    FunctorIso (catPullbackConeFst p q) (catPullbackFst p q) := by
  let e := catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)
  change FunctorIso (catPullbackConeFst p q ≫ equivalencePathReplacementSection p)
    (pullback.fst (equivalencePathReplacementMap p) q) at e
  have h := e.postcomp (equivalencePathReplacementProjection p)
  change FunctorIso ((catPullbackConeFst p q ≫ equivalencePathReplacementSection p) ≫
    equivalencePathReplacementProjection p) (catPullbackFst p q) at h
  rw [Category.assoc, equivalencePathReplacementSection_projection, Category.comp_id] at h
  exact h
/-- 概要：読み戻した右脚は候補の元の第二射影と関手同型。
方針：切断の自然変換の右成分が恒等射であることを使う。
規約：同じ引き戻し候補からの指定関手の同型。
使われ方：native な Cat_∞ の極限錐と全試験関手の第二射影の接続。 -/
def catPullbackConeSndIso (p : A ⟶ C) (q : B ⟶ C) :
    FunctorIso (catPullbackConeSnd p q) (catPullbackSnd p q) := by
  let e := catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)
  change FunctorIso (catPullbackConeSnd p q ≫ 𝟙 B) (catPullbackSnd p q) at e
  rw [Category.comp_id] at e
  exact e

end SerrePositivity.InfinityCategories.F2
