module

public import SerrePositivity.InfinityCategories.F1.Categories.QCatDiagramSimplexCurry

/-!
概要：元の単体と底の積の curry は、同じ全ての面の制限と厳密に可換。
方針：各次数の元の二変数の族を評価し、同じ積の射列を回収する。
規約：一次元の面では既存の同じ区間 curry を使う。
使われ方：元の比較三角形の三面を関手空間内の同じ比較辺へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ単体の面と底の恒等関手の積。 -/
def qCatDiagramSimplexFaceIndex {n : ℕ} (i : Fin (n + 2)) (C : Type u) [Category.{u} C] :
    Fin (n + 1) × C ⥤ Fin (n + 2) × C :=
  (SimplexCategory.toCat.map (SimplexCategory.δ i)).toFunctor.prod (Functor.id C)

/-- 同じ二変数の curry と、元の単体の全ての面の制限は厳密に可換。 -/
lemma qCatDiagramSimplexCurry_face (n : ℕ) (C : Type u) [Category.{u} C] (i : Fin (n + 2)) :
    qCatDiagramSimplexCurry (n + 1) C ≫
      (pre (stdSimplex.δ i)).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))) =
    (pre ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (qCatDiagramSimplexFaceIndex i C)))).app CatInfinity.{u} ≫
        qCatDiagramSimplexCurry n C := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro r α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 一次元では同じ単体 curry は、既存の元の区間 curry そのもの。 -/
lemma qCatDiagramSimplexCurry_one (C : Type u) [Category.{u} C] :
    qCatDiagramSimplexCurry 1 C = qCatDiagramArrowCurry C := rfl

end SerrePositivity.InfinityCategories
