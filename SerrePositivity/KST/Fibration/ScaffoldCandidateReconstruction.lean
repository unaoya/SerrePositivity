module
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionFiberPoint

/-! # 元の scaffold 対応の指定点を保持する、候補から実分類への比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan p)

/-- 元の scaffold 比較と native 表現の指定分類成分を用いる実分類比較。 -/
def scaffoldCandidateClassificationIso :
    FunctorIso (leftStraighteningCandidate p) (leftStraighteningInfinityDiagram p) :=
  (_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.candidateNativeIso s) ≪≫
    (scaffoldStraighteningRepresentationIso p
      (nativeLeftTransportRepresentation p)).symm

/-- 指定分類比較は、元の係数点を同じ実評価点の scaffold 復元像へ送る。 -/
theorem scaffoldCandidateClassificationIso_pointHom (c : I)
    (v : (leftStrictTransport p c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((leftStrictTransportFunctor p).obj c)).symm v) ≫
      (eqToIso (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p c))).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.scaffoldCandidateClassificationIso s).hom (ULift.up (nerveVertex c)) =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram p) (nerveVertex c)
      ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
        (scaffoldPointedReconstruction p)
        (scaffoldPointedReconstruction_projection p) (nerveVertex c)).app
          (Opposite.op ⦋0⦌) ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v))) := by
  let a := (scaffoldStraighteningRepresentationIso p
    (nativeLeftTransportRepresentation p)).inv
  let z := ULift.up.{u + 1} (nerveVertex c)
  have hs := congrArg (fun m => m ≫ functorHomEvaluate a z)
    ((_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.candidateNativeIso_pointHom s) c v)
  have hr := scaffoldPointedReconstruction_pointHom p (nerveVertex c)
    ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v)
  rw [nativeLeftTransportComparison_pointedImage] at hr
  have h := hs.trans hr
  simpa only [scaffoldCandidateClassificationIso, Iso.trans_hom, Iso.symm_hom,
    functorHomEvaluate_comp, Category.assoc, a, z] using h

end ScaffoldTransportComparisonSpan

/-- nerve 上の分類候補と実分類図式を、元の scaffold 対応を保持して比較する。 -/
def scaffoldLeftStraighteningCandidate_classificationIso
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] :
    FunctorIso (leftStraighteningCandidate p) (leftStraighteningInfinityDiagram p) :=
  (_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.scaffoldCandidateClassificationIso (_root_.SerrePositivity.InfinityCategories.F1.Transport.scaffoldTransportComparisonSpan p))

/-- 指定分類比較は、元の係数点を同じ実評価点の scaffold 復元像へ送る。 -/
theorem scaffoldLeftStraighteningCandidate_classificationIso_pointHom
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] (c : I)
    (v : (leftStrictTransport p c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((leftStrictTransportFunctor p).obj c)).symm v) ≫
      (eqToIso (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p c))).inv ≫
      functorHomEvaluate (scaffoldLeftStraighteningCandidate_classificationIso p).hom
        (ULift.up (nerveVertex c)) =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram p) (nerveVertex c)
      ((vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
        (scaffoldPointedReconstruction p)
        (scaffoldPointedReconstruction_projection p) (nerveVertex c)).app
          (Opposite.op ⦋0⦌) ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v))) :=
  (_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.scaffoldCandidateClassificationIso_pointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.scaffoldTransportComparisonSpan p)) c v

end SerrePositivity.KST.Fibration
