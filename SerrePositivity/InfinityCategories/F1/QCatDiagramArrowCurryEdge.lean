module

public import SerrePositivity.InfinityCategories.F1.QCatDiagramArrowCurry
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramRestriction

/-!
概要：元の自然変換の積上の図式を curry して得る辺は、同じ prism の元の辺。
方針：定値な図式パラメーターを全次数の区間と底で評価する。
規約：同じ一単体を保持し、成分ごとの一致で代用しない。
使われ方：既存の結合区間族と結合同型の分類像の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ積上の図式の curry は、元の射を因子交換して curry した頂点になる。 -/
lemma qCatDiagramArrowCurry_vertex
    {C : Type u} [Category.{u} C]
    (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × C)) ⟶ CatInfinity.{u}) :
    (qCatDiagramArrowCurry C).app (Opposite.op ⦋0⦌) (functorVertex H) =
      functorVertex (curry
        ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (Δ[1] : SSet.{u + 1})).hom ≫
          qCatDiagramPrismBase C ≫ H)) := by
  change (functorSpaceCurryMap
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) Δ[1] CatInfinity.{u}).app
      (Opposite.op ⦋0⦌)
      (((pre ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
        (Δ[1] : SSet.{u + 1})).hom ≫ qCatDiagramPrismBase C)).app CatInfinity.{u}).app
          (Opposite.op ⦋0⦌) (functorVertex H)) = _
  rw [functorVertex_precomposition, functorSpaceCurryMap_vertex, Category.assoc]

/-- 同じ自然変換の積上の図式の curry は、元の prism から回収した同じ辺になる。 -/
lemma qCatDiagramArrowCurry_naturalTransformation_edge
    {C : Type u} [Category.{u} C] {F G : C ⥤ QCat.{u}} (η : F ⟶ G) :
    ((((qCatDiagramArrowCurry C).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (functorVertex
        (qCatDiagramCoherentNerve (qCatDiagramArrow η))) 1)).app (Opposite.op ⦋1⦌)
          (𝟙 (Opposite.op ⦋1⦌))) homotopyIntervalEdge.edge) =
    (qCatDiagramNaturalTransformationEdge η).edge := by
  rw [pinchedConstant_map, qCatDiagramArrowCurry_vertex]
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
    (homotopyIntervalEdge.edge, homotopyIntervalEdge.edge))
    (uncurry_const_functorVertex (L := (Δ[1] : SSet.{u + 1}))
      (curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
        (Δ[1] : SSet.{u + 1})).hom ≫ qCatDiagramPrismBase C ≫
          qCatDiagramCoherentNerve (qCatDiagramArrow η))))
  have hi : homotopyIntervalEdge.{u + 1}.edge =
      (ULift.up (𝟙 ⦋1⦌) : (Δ[1] : SSet.{u + 1}) _⦋1⦌) := by
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  rw [hi] at h ⊢
  exact h

end SerrePositivity.InfinityCategories
