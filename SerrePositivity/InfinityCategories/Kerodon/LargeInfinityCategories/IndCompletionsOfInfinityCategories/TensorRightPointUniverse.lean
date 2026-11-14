module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TensorRightPoint
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：元の右点固定の全射は、直積の宇宙比較で同じ元の点の持ち上げを回収する。
方針：各次数の対と、元の点の同じ Yoneda 表示を照合する。
規約：元の点と全試験族を保持する。
使われ方：補間領域の終点面を、同じ元の大きい余錐積の面へ移す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の点固定は直積の宇宙比較で同じ点固定になる。
方針：同じ全次数の成分を計算。規約：全射の等号。使われ方：元の終点面の宇宙移送。 -/
lemma uliftTensorIso_hom_tensorRightPoint {A B : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ B) :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorRightPoint A p) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} A B).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorRightPoint ((SSet.uliftFunctor.{u + 1, u}).obj A)
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map p) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
