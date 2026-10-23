module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleCurry
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramArrowReindex
public import SerrePositivity.InfinityCategories.F1.Categories.QCatDiagramSimplexCurryReindex

/-!
概要：同じ三角形の最初の面を、既存の元の底変換比較の同じ底制限へ戻す。
方針：同じ区間図式と curry の底の制限に対する自然性を合成する。
規約：既存の比較 span が使う元の区間族を変更しない。
使われ方：Hom 比較 span の合成を同じ実際の三角形で結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ三角形の最初の面は、既存の最初の比較の同じ底制限である。 -/
lemma cocartesianBaseChangeTriangleCurryFamily_first_restriction
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    cocartesianBaseChangeTriangleCurryFamily l k ≫
      (pre (stdSimplex.δ (2 : Fin 3))).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) =
    cocartesianBaseChangeJointIntervalFamily k ≫ (ihom (Δ[1] : SSet.{u + 1})).map
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u}) := by
  rw [cocartesianBaseChangeTriangleCurryFamily_first,
    QuasicategoryEnrichedDiagramComparison.arrowDiagram_reindex,
    ← QuasicategoryEnrichedDiagram.realization_reindex]
  have h := qCatDiagramSimplexCurry_reindex 1 l
  rw [qCatDiagramSimplexCurry_one, qCatDiagramSimplexCurry_one] at h
  simpa only [Category.assoc, cocartesianBaseChangeJointIntervalFamily,
    cocartesianBaseChangeJointComparisonFamily] using
    congrArg (fun z ↦ cocartesianBaseChangeJointComparisonFamily k ≫ z) h

end SerrePositivity.InfinityCategories
