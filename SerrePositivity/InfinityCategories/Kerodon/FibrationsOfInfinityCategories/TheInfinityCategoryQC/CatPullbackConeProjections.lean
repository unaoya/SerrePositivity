module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeLegComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeSpecifiedComparison

/-!
概要：Cat_∞ の引き戻し錐の二脚と候補の二射影の関手同型。
方針：同じ指定円柱の三角形からの比較を元の二始域へ戻す。
規約：指定 path と native な二次の可換性との照合は別工程。
使われ方：Cat_∞ の極限錐と全試験関手による引き戻し表示の接続。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：Cat_∞ の極限錐の左脚を実際の関手として読み戻す。
方針：小さい cospan の左の添字で native な脚を読み戻す。
規約：始域は既存の引き戻し候補の台の単体集合。
使われ方：元の第一射影との関手同型。 -/
def catPullbackConeFst (p : A ⟶ C) (q : B ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q ⟶ A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeFunctorLeg p q (AsSmall.up.obj WalkingCospan.left)
/-- 概要：Cat_∞ の極限錐の右脚を実際の関手として読み戻す。
方針：小さい cospan の右の添字で native な脚を読み戻す。
規約：元の第二始域を終域とする。
使われ方：元の第二射影との関手同型。 -/
def catPullbackConeSnd (p : A ⟶ C) (q : B ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q ⟶ B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeFunctorLeg p q (AsSmall.up.obj WalkingCospan.right)
/-- 概要：読み戻した左脚は候補の元の第一射影と関手同型。
方針：切断との合成の比較を始域射影で後合成し、切断の等式で簡約する。
規約：頂点の自己同値を挟まず同じ引き戻し候補からの関手を比較する。
使われ方：native な Cat_∞ の極限錐と全試験関手の第一射影の接続。 -/
def catPullbackConeFstIso (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (catPullbackConeFst p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (catPullbackConeFst p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection p)
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) q) at e
  have h := e.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((catPullbackConeFst p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection p) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q) at h
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection, Category.comp_id] at h
  exact h
/-- 概要：読み戻した右脚は候補の元の第二射影と関手同型。
方針：切断の自然変換の右成分が恒等射であることを使う。
規約：同じ引き戻し候補からの指定関手の同型。
使われ方：native な Cat_∞ の極限錐と全試験関手の第二射影の接続。 -/
def catPullbackConeSndIso (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (catPullbackConeSnd p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (catPullbackConeSnd p q ≫ 𝟙 B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q) at e
  rw [Category.comp_id] at e
  exact e

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
