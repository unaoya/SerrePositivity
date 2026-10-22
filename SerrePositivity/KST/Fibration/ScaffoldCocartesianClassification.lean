module
public import SerrePositivity.KST.Fibration.LeftCocartesianKanPointHom
public import SerrePositivity.KST.Fibration.ScaffoldCandidateReconstruction

/-! # 元の cocartesian section から実分類まで、同じ係数点を保つ指定比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  (p : E ⟶ nerve I) [LeftFibration p]

/-- 元の section 比較と scaffold 対応を保持した、同じ実分類への合成。 -/
def scaffoldCocartesianKanClassificationIso :
    FunctorIso (cocartesianKanCoherentDiagram p) (leftStraighteningInfinityDiagram p) :=
  leftCocartesianKanComparisonIso p ≪≫ scaffoldLeftStraighteningCandidate_classificationIso p

/-- 置換単位上の同じ係数点を、同じ恒等射評価点の pointed 復元像へ送る。 -/
theorem scaffoldCocartesianKanClassificationIso_pointHom (i : I)
    (v : ((kanCocartesianStrictTransportDiagram p).obj i) _⦋0⦌) :
    cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((cocartesianKanDiagram p).obj i)).symm
        ((F2.continuousKanReplacementUnit.app
          ((kanCocartesianStrictTransportDiagram p).obj i)).app (Opposite.op ⦋0⦌) v)) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (kanDiagramCoherentNerve_vertex (cocartesianKanDiagram p) i))).inv ≫
      functorHomEvaluate (scaffoldCocartesianKanClassificationIso p).hom
        (ULift.up (nerveVertex i)) =
    cosliceFiberPointHom (smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram p) (nerveVertex i)
      ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
        (scaffoldPointedReconstruction p)
        (scaffoldPointedReconstruction_projection p) (nerveVertex i)).app
          (Opposite.op ⦋0⦌) ((leftStrictTransportEvaluate p i).app (Opposite.op ⦋0⦌)
            (((cocartesianStrictTransportInclusion p).app i).app (Opposite.op ⦋0⦌) v)))) := by
  let z := ULift.up.{u + 1} (nerveVertex i)
  let w := ((cocartesianStrictTransportInclusion p).app i).app (Opposite.op ⦋0⦌) v
  let C := eqToIso (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p i))
  let A := eqToIso (congrArg HomotopyCategory.mk
    (kanDiagramCoherentNerve_vertex (cocartesianKanDiagram p) i))
  let x := cosliceFiberPointHom
    ((pointedSpaceFiberVertexEquiv ((cocartesianKanDiagram p).obj i)).symm
      ((F2.continuousKanReplacementUnit.app
        ((kanCocartesianStrictTransportDiagram p).obj i)).app (Opposite.op ⦋0⦌) v))
  let a := x ≫ A.inv ≫ functorHomEvaluate (leftCocartesianKanComparisonIso p).hom z
  have hl := leftCocartesianKanComparisonValueIso_pointHom p i v
  simp only [leftCocartesianKanComparisonValueIso, kanDiagramValueIso, Iso.trans_hom,
    Iso.symm_hom, functorIso_app_hom_evaluate] at hl
  have he : a ≫ C.hom =
      cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
        ((leftStrictTransportFunctor p).obj i)).symm w) := by
    simpa only [a, x, A, C, w, z, Category.assoc] using hl
  have hc := (Iso.comp_inv_eq C).2 he.symm
  have hr := scaffoldLeftStraighteningCandidate_classificationIso_pointHom p i w
  change _ ≫ C.inv ≫
    functorHomEvaluate (scaffoldLeftStraighteningCandidate_classificationIso p).hom z = _ at hr
  rw [← Category.assoc, hc] at hr
  simpa only [scaffoldCocartesianKanClassificationIso, Iso.trans_hom, functorHomEvaluate_comp,
    a, x, A, z, w, Category.assoc] using hr

end SerrePositivity.KST.Fibration
