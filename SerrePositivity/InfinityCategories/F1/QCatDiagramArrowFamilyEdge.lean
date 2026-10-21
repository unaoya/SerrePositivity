module

public import SerrePositivity.InfinityCategories.F1.QCatDiagramArrowCurryEdge

/-!
概要：積上の図式の族の一対象での値が分かれば、転置した区間族の同じ辺を回収できる。
方針：定値パラメーターの自然性と、同じ prism の辺の公式を使う。
規約：分類写像の大きな定義を展開せず、元の族をそのまま保持する。
使われ方：元の結合区間族と結合同型の分類像を同一の辺として照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ積上の図式の族を固定した区間族の辺は、指定した元の自然変換の prism の辺。 -/
lemma qCatDiagramArrowFamily_edgeAt
    {C : Type u} [Category.{u} C] {U : SSet.{u + 1}}
    (H : U ⟶ CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 2 × C))))
    (p : U _⦋0⦌) {F G : C ⥤ QCat.{u}} (η : F ⟶ G)
    (hp : H.app (Opposite.op ⦋0⦌) p =
      functorVertex (qCatDiagramCoherentNerve (qCatDiagramArrow η))) :
    (((SSet.Edge.ofTruncated homotopyIntervalEdge).map
      (transposeFunctorFamily (H ≫ qCatDiagramArrowCurry C))).map
        (evaluateFunctorAt p)).edge = (qCatDiagramNaturalTransformationEdge η).edge := by
  rw [transposeFunctorFamily_edgeAt]
  have hv := (pinchedConstant_map H p 1).trans
    (congrArg (fun v ↦ PinchedHom.constant v 1) hp)
  have ht := congrArg (fun F ↦ (((qCatDiagramArrowCurry C).app (Opposite.op ⦋1⦌) F).app
    (Opposite.op ⦋1⦌) (𝟙 (Opposite.op ⦋1⦌))) homotopyIntervalEdge.edge) hv
  exact ht.trans (qCatDiagramArrowCurry_naturalTransformation_edge η)

end SerrePositivity.InfinityCategories
