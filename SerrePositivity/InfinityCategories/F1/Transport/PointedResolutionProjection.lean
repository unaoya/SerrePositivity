module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.KanModels.StrictKanPointedComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedReverseFiberCoordinates

/-! # 左解像の既存比較と、同じ apex 移送による pointed 射影の整合性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- 両端の頂点表示を移した fiber 同型は、元の coslice の同じ apex 移送を保つ。 -/
theorem pointedSpaceCoherentFiberIso_hom_ι (K : KanObject.{u}) :
    (pointedSpaceCoherentFiberIso K).hom ≫
      vertexFiberι pointedSpaceProjection (spaceInfinityVertex (kanObjectOpFunctor.obj K)) =
    vertexFiberι (sliceUnderProjection
      (yonedaEquiv.symm (coherentNerveVertex pointKanObject)))
        (coherentNerveVertex (kanObjectOpFunctor.obj K)) ≫ _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanPointedApexIso.hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro v
  apply Subtype.ext
  change ((cosliceFiberVerticesIso
    (spaceInfinityVertex_eq_coherent pointKanObject).symm
    (spaceInfinityVertex_eq_coherent (kanObjectOpFunctor.obj K)).symm).hom.app
      (Opposite.op ⦋n⦌) v).val.val = (_root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanPointedApexIso.hom.app _ v.val).val
  rw [cosliceFiberVerticesIso_app_val]
  exact (sliceUnder_eqToHom_app_val
    (congrArg SSet.yonedaEquiv.symm (spaceInfinityVertex_eq_coherent pointKanObject).symm)
    n v.val).symm

/-- 左解像の実比較を全 pointed space に含めると、同じ標準 coherent 比較を回収する。 -/
theorem pointedSpaceLeftResolutionComparison_ι (K : KanObject.{u}) :
    pointedSpaceLeftResolutionComparison K ≫
      vertexFiberι pointedSpaceProjection (spaceInfinityVertex (kanObjectOpFunctor.obj K)) =
    coherentPointedFiberComparison K ≫
      vertexFiberι (sliceUnderProjection
        (yonedaEquiv.symm (coherentNerveVertex pointKanObject)))
          (coherentNerveVertex (kanObjectOpFunctor.obj K)) ≫ _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanPointedApexIso.hom := by
  rw [← pointedSpaceLeftCoherentComparison_eq_resolution,
    ← coherentPointedFiberComparison_coordinates, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedSpaceCoherentFiberIso_hom_ι]

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedSpaceCoherentFiberIso_hom_ι := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedSpaceCoherentFiberIso_hom_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedSpaceLeftResolutionComparison_ι := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedSpaceLeftResolutionComparison_ι
