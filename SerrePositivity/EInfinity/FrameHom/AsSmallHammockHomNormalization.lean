module

public import SerrePositivity.EInfinity.FrameHom.AsSmallHammockHomFamily
public import SerrePositivity.EInfinity.Hammock.AsSmallKanArrow

/-!
概要：同じ全図式の宇宙比較の順射・全評価成分・元の射の零単体を照合する。
方針：元の自然変換の実現した辺を保持し、原本の評価と同じ Ex∞ 単位公式を使う。
規約：全同型とは別の点ごとの同値を選ばない。
使われ方：同じ終端図式と Yoneda 比較を合成するときの零単体回収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet Opposite MonoidalClosed Hammock
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X : C)

attribute [local instance] kanHomFamily_kanComplex

/-- 概要：同じ全自然変換の成分は元の余極限同型の Ex∞ 像。
方針：元の関手による右 whisker の成分を評価する。
規約：射の厳密な等式。使われ方：全比較辺の評価を元の零単体へ戻す。 -/
lemma asSmallKanHammockHomFamilyMap_app (Y : AsSmall.{max u v} C) :
    (asSmallKanHammockHomFamilyMap W X).app Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (AsSmallComparison.colimitIso W X (AsSmall.down.obj Y)).hom := rfl

/-- 概要：同じ全図式同型の順射は元の全自然変換の実現した辺の類。
方針：原本の束ねの順射を回収する。
規約：選択した同じ全比較を保持。
使われ方：終端の全比較と元の零単体の追跡を切り離さないための照合。 -/
lemma asSmallHammockHomCoherentIso_hom :
    (asSmallHammockHomCoherentIso W X).hom =
      HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge
          (F := ⟨AsSmall.down ⋙ kanHomFamily (hammockHomFamily W X), trivial⟩)
          (G := ⟨kanHomFamily (hammockHomFamily (AsSmallComparison.weak W)
            (AsSmall.up.obj X)), trivial⟩)
          (asSmallKanHammockHomFamilyMap W X)).toTruncated := rfl

/-- 概要：同じ全比較辺の全標的成分は元の宇宙同型の Ex∞ 像そのもの。
方針：元の実自然変換の評価に原本の全図式評価公式を使う。
規約：辺の厳密な等式。使われ方：同じ全比較の零単体の照合。 -/
lemma asSmallHammockHomCoherentEdge_at (Y : AsSmall.{max u v} C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge
      (F := ⟨AsSmall.down ⋙ kanHomFamily (hammockHomFamily W X), trivial⟩)
      (G := ⟨kanHomFamily (hammockHomFamily (AsSmallComparison.weak W)
        (AsSmall.up.obj X)), trivial⟩)
      (asSmallKanHammockHomFamilyMap W X)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show
        (AsSmall.down ⋙ kanHomFamily (hammockHomFamily W X)).obj Y ⟶
          (kanHomFamily (hammockHomFamily (AsSmallComparison.weak W)
            (AsSmall.up.obj X))).obj Y from
              (asSmallKanHammockHomFamilyMap W X).app Y)).edge := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge_at
    (F := ⟨AsSmall.down ⋙ kanHomFamily (hammockHomFamily W X), trivial⟩)
    (G := ⟨kanHomFamily (hammockHomFamily (AsSmallComparison.weak W)
      (AsSmall.up.obj X)), trivial⟩)
    (asSmallKanHammockHomFamilyMap W X) Y

/-- 概要：同じ全比較の実成分は元の射の零単体を元の持ち上げた射に送る。
方針：同じ宇宙同型の全 Ex∞ 単位三角形をそのまま使う。
規約：全同型と同じ実射。使われ方：Yoneda 比較の元の局所化辺の入力。 -/
lemma asSmallKanHammockHomFamilyMap_arrow {Y : C} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) ≫
      (asSmallKanHammockHomFamilyMap W X).app (AsSmall.up.obj Y) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (AsSmallComparison.weak W) (AsSmall.up.map f) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (AsSmallComparison.weak W)
            (AsSmall.up.obj X) (AsSmall.up.obj Y)) :=
  AsSmallComparison.arrowMap_exInfinity_colimitIso W f

end SerrePositivity.EInfinity.FrameHom
