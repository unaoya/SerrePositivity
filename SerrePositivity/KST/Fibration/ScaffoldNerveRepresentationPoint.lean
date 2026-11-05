module
public import SerrePositivity.KST.Fibration.ScaffoldCandidateNativeComparison

/-! # 指定 scaffold 三角形を保持する nerve 上の表現比較と、同じ係数点の作用 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E : SSet.{u}} (p : E ⟶ nerve I) [LeftFibration p]
  (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))

/-- 元の scaffold の係数点を保持する比較を、同じ相対表現への指定比較と合成する。 -/
def scaffoldNerveRepresentationIso : FunctorIso (leftStraighteningCandidate p) R.diagram :=
  (_root_.SerrePositivity.InfinityCategories.F1.Transport.scaffoldTransportComparisonSpan p).candidateNativeIso ≪≫
    nativeRepresentationComparisonIso p (nativeLeftTransportRepresentation p) R

/-- 元の係数点は、同じ恒等射評価の実 fiber 点を表現の pointedMap へ送った点に移る。 -/
theorem scaffoldNerveRepresentationIso_pointHom (c : I)
    (v : (leftStrictTransport p c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((leftStrictTransportFunctor p).obj c)).symm v) ≫
      (eqToIso (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p c))).inv ≫
      functorHomEvaluate (scaffoldNerveRepresentationIso p R).hom
        (ULift.up (nerveVertex c)) =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((transportRepresentationPointedFiberMap R (ULift.up (nerveVertex c))).app
      (Opposite.op ⦋0⦌) ((uliftVertexFiberIso p (nerveVertex c)).hom.app
        (Opposite.op ⦋0⦌)
        (ULift.up ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v)))) := by
  let a := ULift.up.{u + 1} (nerveVertex c)
  let φ := nativeRepresentationComparisonIso p (nativeLeftTransportRepresentation p) R
  have hs := (_root_.SerrePositivity.InfinityCategories.F1.Transport.scaffoldTransportComparisonSpan p).candidateNativeIso_pointHom c v
  have he := congrArg (fun m => m ≫ functorHomEvaluate φ.hom a) hs
  have hr := nativeRepresentationComparisonIso_pointHom p R (nerveVertex c)
    ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v)
  have h := he.trans hr
  simp only [Category.assoc] at h
  change _ ≫ _ ≫ functorHomEvaluate
    ((_root_.SerrePositivity.InfinityCategories.F1.Transport.scaffoldTransportComparisonSpan p).candidateNativeIso.hom ≫ φ.hom) a = _
  rw [functorHomEvaluate_comp]
  exact h

end SerrePositivity.KST.Fibration
