module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramNaturalPrismSimplex
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEdgeFromPrism

/-!
概要：元の自然変換の coherent な辺の実現と、同じ元の prism は厳密に一致する。
方針：全パラメーターの単体公式を Yoneda と curry の同値で戻す。
規約：成分ごとの一致に限定せず、底全体の同じ辺の一単体を保持する。
使われ方：結合同型の分類像を既存の結合区間族と同一の辺として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の自然変換の辺を実現した族の prism は、同じ自然変換から作った元の prism。 -/
lemma quasicategoryDiagramHom_realization_prism
    {C : Type u} [Category.{u} C] {F G : QuasicategoryDiagramCategory C}
    (η : F.val ⋙ quasicategoryObjectForget ⟶ G.val ⋙ quasicategoryObjectForget) :
    functorFamilyPrism (SSet.yonedaEquiv.symm
      ((quasicategoryDiagramRealization C).app (Opposite.op ⦋1⦌)
        (coherentNerveEdge (quasicategoryDiagramHom η)).edge)) =
    qCatDiagramNaturalTransformationPrism (quasicategoryDiagramQCatTransformation η) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨σ⟩⟩
  change quasicategoryDiagramDiagonalSimplex σ
    ((QuasicategoryDiagramNerve C).map t.down.op
      (coherentNerveEdge (quasicategoryDiagramHom η)).edge) = _
  have h := ConcreteCategory.congr_hom
    ((nerveToCoherent (QuasicategoryDiagramCategory C)).naturality t.down.op)
    (ComposableArrows.mk₁ (quasicategoryDiagramHom η))
  exact (congrArg (quasicategoryDiagramDiagonalSimplex σ) h.symm).trans
    (quasicategoryDiagramDiagonalSimplex_naturalPrism η σ
      (SimplexCategory.toCat.map t.down).toFunctor)

/-- 元の自然変換の辺の実現は、同じ prism から回収した既存の辺そのもの。 -/
lemma quasicategoryDiagramHom_realization_edge
    {C : Type u} [Category.{u} C] {F G : QuasicategoryDiagramCategory C}
    (η : F.val ⋙ quasicategoryObjectForget ⟶ G.val ⋙ quasicategoryObjectForget) :
    (quasicategoryDiagramRealization C).app (Opposite.op ⦋1⦌)
      (coherentNerveEdge (quasicategoryDiagramHom η)).edge =
    (qCatDiagramNaturalTransformationEdge (quasicategoryDiagramQCatTransformation η)).edge := by
  apply SSet.yonedaEquiv.symm.injective
  apply uncurry_injective
  apply (cancel_epi (β_ (Δ[1] : SSet.{u + 1})
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))).hom).mp
  change functorFamilyPrism _ = functorEdgePrism
    (qCatDiagramNaturalTransformationEdge (quasicategoryDiagramQCatTransformation η))
  exact (quasicategoryDiagramHom_realization_prism η).trans
    (functorEdgeFromPrism_prism _ _ _).symm

end SerrePositivity.InfinityCategories
