module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorRestrictionFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct

/-!
概要：left anodyne な始域の制限による相対関手空間の全境界持ち上げ。
方針：相対内部 Hom の持ち上げを、固定した底の図式の fiber に制限する。
規約：p は left fibration、底の単体集合に quasicategory 性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の始対象における評価の同値性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：left anodyne な射による相対前合成は trivial Kan fibration。
方針：底を固定した持ち上げ問題を相対内部 Hom に入れて解き、再び fiber へ戻す。
規約：元の射 p の left fibration 性だけを要求する。
使われ方：Kerodon §5.3.1（Tag 035D）、始対象の nerve の頂点包含に沿う制限。 -/
lemma relativeFunctorPre_trivialKanFibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) := by
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne i hi p sq'
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPre_trivialKanFibration_of_relativeHom p a i sq'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
