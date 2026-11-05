module
public import SerrePositivity.KST.Fibration.LeftCocartesianKanPointHom
public import SerrePositivity.KST.Fibration.ScaffoldCandidateClassification

/-! # 元の cocartesian section から実分類まで、同じ係数点を保つ指定比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  (p : E ⟶ nerve I) [LeftFibration p]

omit [LeftFibration p] in
/-- 元の section 包含の後の恒等射評価は、元の cocartesian section の評価そのもの。 -/
theorem leftCocartesianStrictTransportEvaluation_eq (i : I) :
    (cocartesianStrictTransportInclusion p).app i ≫ leftStrictTransportEvaluate p i =
      SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate p i := by
  apply vertexFiber_hom_ext p (nerveVertex i)
  have hl := congrArg (fun m => (cocartesianStrictTransportInclusion p).app i ≫ m)
    (leftStrictTransportEvaluate_ι p i)
  have hr := congrArg
    (fun m => SerrePositivity.InfinityCategories.cocartesianSectionsι p (nerveMap (Under.forget i)) ≫ m)
    (SerrePositivity.InfinityCategories.relativeFunctorEvaluate_ι p (nerveMap (Under.forget i))
      ((nerveEquiv (C := Under i)).symm (Under.mk (𝟙 i))))
  rw [Category.assoc]
  exact hl.trans hr.symm

/-- 元の section 比較と scaffold 対応を保持した、同じ実分類への合成。 -/
def leftCocartesianKanClassificationIso :
    FunctorIso (cocartesianKanCoherentDiagram p) (leftStraighteningInfinityDiagram p) :=
  leftCocartesianKanComparisonIso p ≪≫ leftStraighteningCandidate_classificationIso p

/-- 置換単位上の同じ係数点を、同じ恒等射評価点の pointed 復元像へ送る。 -/
theorem leftCocartesianKanClassificationIso_pointHom (i : I)
    (v : ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p).obj i) _⦋0⦌) :
    cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((cocartesianKanDiagram p).obj i)).symm
        ((F2.continuousKanReplacementUnit.app
          ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p).obj i)).app (Opposite.op ⦋0⦌) v)) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (kanDiagramCoherentNerve_vertex (cocartesianKanDiagram p) i))).inv ≫
      functorHomEvaluate (leftCocartesianKanClassificationIso p).hom
        (ULift.up (nerveVertex i)) =
    cosliceFiberPointHom (smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram p) (nerveVertex i)
      ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
        (pointedLeftStraighteningReconstruction p)
        (pointedLeftStraighteningReconstruction_projection p) (nerveVertex i)).app
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
        ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p).obj i)).app (Opposite.op ⦋0⦌) v))
  let a := x ≫ A.inv ≫ functorHomEvaluate (leftCocartesianKanComparisonIso p).hom z
  have hl := leftCocartesianKanComparisonValueIso_pointHom p i v
  simp only [leftCocartesianKanComparisonValueIso, _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso, Iso.trans_hom,
    Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate] at hl
  have he : a ≫ C.hom =
      cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
        ((leftStrictTransportFunctor p).obj i)).symm w) := by
    simpa only [a, x, A, C, w, z, Category.assoc] using hl
  have hc := (Iso.comp_inv_eq C).2 he.symm
  have hr := leftStraighteningCandidate_classificationIso_pointHom p i w
  change _ ≫ C.inv ≫
    functorHomEvaluate (leftStraighteningCandidate_classificationIso p).hom z = _ at hr
  rw [← Category.assoc, hc] at hr
  simpa only [leftCocartesianKanClassificationIso, Iso.trans_hom, functorHomEvaluate_comp,
    a, x, A, z, w, Category.assoc] using hr

end SerrePositivity.KST.Fibration
