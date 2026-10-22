module
public import SerrePositivity.KST.Fibration.WeakIdentityScaffoldClassification
public import SerrePositivity.KST.Fibration.WeakQuotientCosliceHomTriangle
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-! # 元の K-6 coslice 合成と、同じ scaffold 復元との無条件の相対三角形 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の商上の coslice 合成の恒等点と、同じ scaffold 復元恒等点を実 fiber 内で比較する。 -/
def weakCosliceComposite_scaffold_pointIso :
    VertexIso (weakQuotientCosliceCompositePoint h x)
      (scaffoldCosliceReconstructionPoint (q.hom.app (Opposite.op ⦋0⦌) x)) :=
  smallUnstraighteningFiberIsoOfPointHomEq _ _
    ((weakQuotientCosliceCompositePoint_section_image_hom h x).symm.trans
      (weakIdentityNativeComparisonImage_scaffold_pointHom h x))

/-- 同じ恒等点の照合は、元の全相対関手空間内の同じ二つの写像の同型へ戻る。 -/
def weakCosliceComposite_scaffold_relativeIso :
    VertexIso
      (relativeFunctorVertex _ _ (weakQuotientCosliceComposite h x)
        (weakQuotientCosliceComposite_projection h x))
      (relativeFunctorVertex _ _ (scaffoldPointedReconstruction
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (scaffoldPointedReconstruction_projection _)) :=
  coslicePointEvaluation_relativeIso _ _ _ _ (weakCosliceComposite_scaffold_pointIso h x)

/-- 元の coslice 合成は、同じ底上の scaffold 復元と自然同型。 -/
def weakCosliceComposite_scaffold_functorIso :
    FunctorIso (weakQuotientCosliceComposite h x)
      (scaffoldPointedReconstruction
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  VertexIso.map (weakCosliceComposite_scaffold_relativeIso h x)
    (vertexFiberι ((ihom (sliceUnder (yonedaEquiv.symm
      (q.hom.app (Opposite.op ⦋0⦌) x)))).map
      (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))))
      (functorVertex (sliceUnderProjection
        (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))))

/-- 元の単位と分数比較の coslice 側の合成は、無条件に全関手空間で前合成同値。 -/
theorem weakCosliceComposite_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (weakQuotientCosliceComposite h x) := by
  apply (isPrecompositionEquivalence_iff_isQCatEquivalence _).mpr
  have he := (scaffoldPointedReconstruction_isPrecompositionEquivalence
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))).isQCatEquivalence
  exact he.ofFunctorIso (weakCosliceComposite_scaffold_functorIso h x).symm

end SerrePositivity.KST.Fibration
