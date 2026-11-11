module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteCospanNerveIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseHorns

/-!
概要：小さい有限 span/cospan の nerve の ULift を、大きい宇宙の標準ホーンへ移す。
方針：有限半順序の実同型を持ち上げ、同じ標準ホーンの宇宙同型と合成する。
規約：元の図式を前合成できる厳密な形状同型を与える。
使われ方：Ind の小さい有限半順序図式の存在から、元の大きい標準図式へ戻す。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 小さい有限 span の持ち上げは、大きい宇宙の元の標準 span と同型。 -/
def uliftFiniteSpanNerveIso :
    (SSet.uliftFunctor.{v, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}) ≅
      (horn 2 0 : SSet.{max u v}) :=
  (SSet.uliftFunctor.{v, u}).mapIso _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso 2 0

/-- 小さい有限 cospan の持ち上げは、大きい宇宙の元の標準 cospan と同型。 -/
def uliftFiniteCospanNerveIso :
    (SSet.uliftFunctor.{v, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteCospanIndex.{u}) ≅
      (horn 2 2 : SSet.{max u v}) :=
  (SSet.uliftFunctor.{v, u}).mapIso _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.finiteCospanNerveIso ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso 2 2

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
