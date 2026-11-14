module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.ProductSimplexProjection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.ProductSimplexLiftedOver
public import SerrePositivity.EInfinity.FrameHom.FrameIndexAugmentation
public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization

/-!
# 元の積単体の反対要素圏から第一成分への弱射影

概要：元の全単体・全作用素を持つ nerve の射影自身が弱同値となる。
方針：同じ終端 augmentation の自然性と、元の積の収縮を宇宙持ち上げ後に使う。
規約：元の M・指定 n・Hom ULift と第一成分を保持する。
使われ方：屋根の ProductHomMap と保存済みの高次比較との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.ProductSimplexLiftedOver
open CategoryTheory MonoidalCategory Opposite SerrePositivity.SimplicialModel
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (M : SSet.{u}) (n : AsSmall.{u + 1} SimplexCategory)

def firstNerveMap : nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver.productElements M n) ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver.elements M) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver.firstComponent M n)

lemma firstComponent_eq_mapElements : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver.firstComponent M n =
    ULiftHom.down.{0, u, u + 1} ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection.projection M (ULift.down n).len).mapElements.op ⋙
        ULiftHom.up := rfl

lemma firstNerveMap_augmentation : firstNerveMap M n ≫
    SimplexTerminalNerve.liftedAugmentation.{u, u + 1} M =
      SimplexTerminalNerve.liftedAugmentation.{u, u + 1}
        (M ⊗ SSet.stdSimplex.obj (ULift.down n)) ≫
          SSet.uliftFunctor.{u + 1, u}.map
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection.projection M (ULift.down n).len) :=
  by
    have h := SimplexTerminalNerve.liftedAugmentation_naturality.{u, u + 1}
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection.projection M (ULift.down n).len)
    rw [← firstComponent_eq_mapElements] at h
    exact h

lemma firstNerveMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (firstNerveMap M n)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hP := Hammock.anodyneQ_map_isIso_of_weak _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexProjection.projection_weak M (ULift.down n).len)
  have := UniverseLift.anodyneQ_map_isIso_of_small _ hP
  have := SimplexTerminalNerve.liftedAugmentation_localized_isIso.{u, u + 1} M
  have := SimplexTerminalNerve.liftedAugmentation_localized_isIso.{u, u + 1}
    (M ⊗ SSet.stdSimplex.obj (ULift.down n))
  have he := congrArg Q.map (firstNerveMap_augmentation M n)
  rw [Q.map_comp, Q.map_comp] at he
  have h : IsIso (Q.map (firstNerveMap M n) ≫
      Q.map (SimplexTerminalNerve.liftedAugmentation.{u, u + 1} M)) := he.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).1 h

lemma firstNerveMap_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (firstNerveMap M n) :=
  AnodyneWeakDetection.isWeakHomotopyEquivalence _ (firstNerveMap_localized_isIso M n)

end SerrePositivity.EInfinity.FrameHom.ProductSimplexLiftedOver
