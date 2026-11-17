module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.ProductSimplexProjection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.ProductSimplexUniverseOver
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameIndexAugmentation
public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization

/-!
概要：元の積単体の次数 Over 表示と第一射影を任意の共通上限宇宙で扱う。
方針：元の全単体・作用素と up・down の往復を同じ max 宇宙で評価する。
規約：元の小さい単体集合と指定次数を保持する。
使われ方：一般モデル圏の実 roof 比較の積単体の次数表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite _root_.SerrePositivity.SimplicialModel
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (M : SSet.{u}) (n : AsSmall.{max u w} SimplexCategory)

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
def firstNerveMap : nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.productElements.{u, w} M n) ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.elements.{u, w} M) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.firstComponent.{u, w} M n)

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma firstComponent_eq_mapElements : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.firstComponent.{u, w} M n =
    ULiftHom.down.{0, u, max u w} ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection.projection M (ULift.down n).len).mapElements.op ⋙
        ULiftHom.up := rfl

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma firstNerveMap_augmentation : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver.firstNerveMap.{u, w} M n ≫
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{u, max u w} M =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{u, max u w}
        (M ⊗ SSet.stdSimplex.obj (ULift.down n)) ≫
          SSet.uliftFunctor.{max u w, u}.map
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection.projection M (ULift.down n).len) :=
  by
    have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_naturality.{u, max u w}
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection.projection M (ULift.down n).len)
    rw [← _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver.firstComponent_eq_mapElements.{u, w}] at h
    exact h

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma firstNerveMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver.firstNerveMap.{u, w} M n)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hP := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection.projection_weak M (ULift.down n).len)
  have := UniverseLift.anodyneQ_map_isIso_of_small _ hP
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso.{u, max u w} M
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso.{u, max u w}
    (M ⊗ SSet.stdSimplex.obj (ULift.down n))
  have he := congrArg Q.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver.firstNerveMap_augmentation.{u, w} M n)
  rw [Q.map_comp, Q.map_comp] at he
  have h : IsIso (Q.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver.firstNerveMap.{u, w} M n) ≫
      Q.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{u, max u w} M)) := he.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).1 h

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma firstNerveMap_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver.firstNerveMap.{u, w} M n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver.firstNerveMap_localized_isIso.{u, w} M n)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseOver
