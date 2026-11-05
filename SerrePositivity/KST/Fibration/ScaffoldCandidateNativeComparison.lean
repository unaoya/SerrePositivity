module
public import SerrePositivity.KST.Fibration.StrictTransportOppositePointHom
public import SerrePositivity.KST.Fibration.PointedLeftResolutionVertices
public import SerrePositivity.KST.Fibration.NativeCoefficientResolutionPointHom

/-! # 元の scaffold 対応を保持する分類候補・native 表現の同じ比較と点の作用 -/

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

/-- 元の反転比較と、同じ scaffold 表現との指定比較の逆を用いる分類候補・native 比較。 -/
def candidateNativeIso :
    FunctorIso (leftStraighteningCandidate p) (nativeLeftTransportRepresentation p).diagram :=
  leftStraighteningCoherentMap_oppositeVertexIso p ≪≫
    (nativeRepresentationComparisonIso p (nativeLeftTransportRepresentation p)
      (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representation s.toStrictTransportComparisonSpan)).symm

/-- 元の係数点は、同じ指定比較で元の恒等射評価の native 実像へ送られる。 -/
theorem candidateNativeIso_pointHom (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((leftStrictTransportFunctor p).obj c)).symm v) ≫
      (eqToIso (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p c))).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.candidateNativeIso s).hom (ULift.up (nerveVertex c)) =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((nativeTransportPointedFiberMap p (nerveVertex c)).app
      (Opposite.op ⦋0⦌)
        (ULift.up ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v))) := by
  let z := ULift.up.{u + 1} (nerveVertex c)
  let μ := leftStraighteningCoherentMap_oppositeVertexIso p
  let φ := nativeRepresentationComparisonIso p (nativeLeftTransportRepresentation p)
    (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representation s.toStrictTransportComparisonSpan)
  let C := eqToIso (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p c))
  let O := eqToIso (congrArg HomotopyCategory.mk
    (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c))
  let x := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
    ((pointedSpaceFiberVertexEquiv ((leftStrictTransportFunctor p).obj c)).symm v)
  let n := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((nativeTransportPointedFiberMap p (nerveVertex c)).app
    (Opposite.op ⦋0⦌) (ULift.up ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v)))
  have hs := strictTransportOppositeComponentIso_pointHom p c v
  change x ≫ C.inv ≫ functorHomEvaluate μ.hom z ≫ O.hom = _ at hs
  have hn := (_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.nativeCoefficientPointHom_resolution s) c v
  rw [pointedSpaceLeftResolutionComparison_vertex_eq] at hn
  change n ≫ functorHomEvaluate φ.hom z ≫ O.hom = _ at hn
  have hc : x ≫ C.inv ≫ functorHomEvaluate μ.hom z = n ≫ functorHomEvaluate φ.hom z := by
    apply (cancel_mono O.hom).mp
    simpa only [Category.assoc] using hs.trans hn.symm
  have h := congrArg (fun m => m ≫ functorHomEvaluate φ.inv z) hc
  have hi : functorHomEvaluate φ.hom z ≫ functorHomEvaluate φ.inv z = 𝟙 _ := by
    rw [← functorHomEvaluate_comp, φ.hom_inv_id, functorHomEvaluate_id]
  change x ≫ C.inv ≫ functorHomEvaluate (μ.hom ≫ φ.inv) z = n
  rw [functorHomEvaluate_comp]
  simp only [Category.assoc, hi] at h
  exact h.trans (Category.comp_id n)

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration
