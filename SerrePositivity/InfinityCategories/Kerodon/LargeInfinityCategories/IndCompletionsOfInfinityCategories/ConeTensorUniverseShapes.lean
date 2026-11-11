module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinSimplexShapes

/-!
概要：小さい二つの形状の余錐積と、各因子を持ち上げた余錐積を実同型で比較する。
方針：直積と余錐の既存の宇宙同型を、元の両因子の順序で合成する。
規約：両境界と全積の表示変更だけを行う。
使われ方：実終点 comma の全族を小さい試験形状の拡張定理へ渡す。

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
/-- 概要：旧族側の積の厳密な宇宙比較。
方針：直積と右余錐の同型。規約：全形状。使われ方：旧族の表示変更。 -/
def coneTensorOldUniverseShape (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u})) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj A ⊗
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L Δ[0])).hom ≫
    ((SSet.uliftFunctor.{u + 1, u}).obj A ◁ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, u + 1} L 0).hom)
/-- 概要：下方族側の積の厳密な宇宙比較。
方針：直積と左余錐の同型。規約：全形状。使われ方：下方族の表示変更。 -/
def coneTensorLowerUniverseShape (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⊗ L) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj L :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) L).hom ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, u + 1} A 0).hom ▷ (SSet.uliftFunctor.{u + 1, u}).obj L)
/-- 概要：余錐の全積の厳密な宇宙比較。
方針：直積と両余錐の同型。規約：全形状。使われ方：全拡張の表示変更。 -/
def coneTensorUniverseShape (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L Δ[0]) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L Δ[0])).hom ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, u + 1} A 0).hom ▷
      (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L Δ[0])) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, u + 1} L 0).hom)
/-- 概要：旧族の比較自身が同型。
方針：同型の合成。規約：元の比較。使われ方：旧族の厳密な回収。 -/
instance coneTensorOldUniverseShape_isIso (A L : SSet.{u}) :
    IsIso (coneTensorOldUniverseShape A L) := by
  dsimp only [coneTensorOldUniverseShape]
  infer_instance
/-- 概要：下方族の比較自身が同型。
方針：同型の合成。規約：元の比較。使われ方：下方族の厳密な回収。 -/
instance coneTensorLowerUniverseShape_isIso (A L : SSet.{u}) :
    IsIso (coneTensorLowerUniverseShape A L) := by
  dsimp only [coneTensorLowerUniverseShape]
  infer_instance
/-- 概要：全積の比較自身が同型。
方針：同型の合成。規約：元の比較。使われ方：全拡張の厳密な回収。 -/
instance coneTensorUniverseShape_isIso (A L : SSet.{u}) :
    IsIso (coneTensorUniverseShape A L) := by
  dsimp only [coneTensorUniverseShape]
  infer_instance
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
