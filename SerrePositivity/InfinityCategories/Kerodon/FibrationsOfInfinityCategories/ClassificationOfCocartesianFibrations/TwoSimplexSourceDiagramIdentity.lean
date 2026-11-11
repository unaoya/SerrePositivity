module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexLocalComparison

/-!
概要：二脚を明示した元の source cospan は、元の制限の合成図式そのもの。
方針：同じ三対象・二脚・恒等射を照合する。
規約：元の全局所 Hom と元の制限作用を保持する。
使われ方：巨大な合成図式を展開せず、同じ source Segal 比較を扱う。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 二脚の表示を明示しても、元の全局所 Hom の同じ反変制限図式を保つ。 -/
lemma cocartesianTwoSimplexLocalSource_original_diagram
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexLocalSource k p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexCellCospan k ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom ⋙
          SSet.uliftFunctor.{u + 1, u} := by
  refine CategoryTheory.Functor.ext (fun j ↦ by cases j with
    | none => rfl
    | some j => cases j <;> rfl) ?_
  intro i j f
  change WidePullbackShape.Hom i j at f
  cases f with
  | id j => simp
  | term j => cases j <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
