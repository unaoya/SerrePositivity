module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportBaseChangeEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StraighteningVertices
public import SerrePositivity.InfinityCategories.F1.Categories.QCatDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomCartesianEdges

/-!
概要：strict transport の底変換比較を、同じ Cat∞ 値図式の coherent な同型へ実現する。
方針：元の自然変換の各成分の同値性を、既存の coherent な実現へ渡す。
規約：元の分類主写像の同じ底変換の頂点を標的にする。
使われ方：元の分類写像のセル制限の比較と Hom 作用の自然性の端点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
  (p : E ⟶ nerve C) [CocartesianFibration p] (k : D ⥤ C)

/-- 同じ底変換の自然変換を、元の QCat 値図式の自然変換として表す。 -/
def cocartesianStrictTransportBaseChangeQCat :
    k ⋙ cocartesianStrictTransportQCatFunctor p ⟶
      cocartesianStrictTransportQCatFunctor (pullback.fst (nerveMap k) p) where
  app d := cocartesianStrictTransportBaseChangeComponent p k d
  naturality d e f := cocartesianStrictTransportBaseChangeComponent_naturality p k f

/-- 同じ元の比較は、通常の底を制限した Cat∞ 値図式と実際の底変換の図式の同型。 -/
def cocartesianStrictTransportBaseChangeCoherentIso :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
      cocartesianStrictTransportCoherentDiagram p)
      (cocartesianStrictTransportCoherentDiagram (pullback.fst (nerveMap k) p)) := by
  change FunctorIso (qCatDiagramCoherentNerve (k ⋙ cocartesianStrictTransportQCatFunctor p))
    (qCatDiagramCoherentNerve
      (cocartesianStrictTransportQCatFunctor (pullback.fst (nerveMap k) p)))
  apply qCatDiagramFunctorIsoOfPointwise (cocartesianStrictTransportBaseChangeQCat p k)
  intro d
  exact cocartesianStrictTransportBaseChangeComponent_isQCatEquivalence p k d

/-- 同じ coherent 比較は、構成済みの分類主写像による底変換の像を標的に持つ。 -/
def cocartesianStraighteningBaseChangeVertexIso :
    VertexIso (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
      cocartesianStrictTransportCoherentDiagram p))
      ((cocartesianStraighteningCoherentMap D).app (Opposite.op ⦋0⦌)
        (cocartesianFibrationInfinityVertex (pullback.fst (nerveMap k) p))) := by
  rw [cocartesianStraighteningCoherentMap_vertex]
  exact cocartesianStrictTransportBaseChangeCoherentIso p k

end SerrePositivity.InfinityCategories
