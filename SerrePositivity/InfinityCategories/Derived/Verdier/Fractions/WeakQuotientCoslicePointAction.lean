module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientCosliceComparison
public import SerrePositivity.InfinityCategories.F1.Straightening.SmallUnstraighteningPointAction
public import SerrePositivity.InfinityCategories.F1.Transport.CoslicePointComparison

/-! # 元の商上の比較と coslice 単位の合成を、同じ実恒等点での作用へ還元する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 同じ合成を恒等錐で評価し、元の商像上の実 fiber 点として保持する。 -/
def weakQuotientCosliceCompositePoint :
    (vertexFiber (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))))
      (q.hom.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ :=
  (leftFibrationCoslicePointEvaluate _ _).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite h x)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite_projection h x))

/-- 同じ合成の正規化済み恒等点は、元の実 fiber 点の同じ比較像そのもの。 -/
theorem weakQuotientCosliceCompositePoint_fiberMap :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint h x =
      (vertexFiberMap (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
        (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))))
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison h x) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison_projection h x)
        (q.hom.app (Opposite.op ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientFiberPoint h x) := by
  apply Subtype.ext
  have he := _root_.SerrePositivity.InfinityCategories.F1.Transport.coslicePointEvaluation_vertex_val _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite_projection h x)
  exact he.trans (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite_identity h x)

/-- 同じ合成の実恒等点の像は、元の coherent な比較二胞体の同じ点での作用そのもの。 -/
theorem weakQuotientCosliceCompositePoint_action :
    (leftUnstraighteningMappingFiberHom (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
      (leftStraighteningInfinityDiagram
        (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
        evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointedFiber h x)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomParameter (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom h x)) =
      _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage (leftStraighteningInfinityDiagram
        (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint h x) := by
  let F := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x
  let G := leftStraighteningInfinityDiagram
    (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
  let b := q.hom.app (Opposite.op ⦋0⦌) x
  let a := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom h x
  let v := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientFiberPoint h x
  have hp : _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage F b v = _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointedFiber h x :=
    _root_.SerrePositivity.InfinityCategories.F1.Transport.smallUnstraighteningFiberPoint_recover F b (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointedFiber h x)
  have ha := congrArg (fun s =>
    (leftUnstraighteningMappingFiberHom F G (ULift.up b) ≫ evaluateFunctorAt s).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomParameter a)) hp.symm
  have he := _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_pointAction F G b a v
  have ht := congrArg (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage G b)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_fiberMap h x)
  exact ha.trans (he.trans ht.symm)

/-- 同じ coslice 射影の元の実復元写像の、正規化済み恒等錐評価点。 -/
def weakQuotientCosliceReconstructionPoint :
    (vertexFiber (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))))
      (q.hom.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ :=
  (leftFibrationCoslicePointEvaluate _ _).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _
      (leftStraighteningInfinityReconstruction
        (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
      (leftStraighteningInfinityReconstruction_projection _))

/-- 実恒等点の比較があれば、同じ全 coslice の合成比較は底上の相対写像空間内で同型。 -/
def weakQuotientCosliceTriangle_relativeIso
    (e : VertexIso (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint h x)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceReconstructionPoint (q := q) x)) :
    VertexIso
      (relativeFunctorVertex _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite h x)
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite_projection h x))
      (relativeFunctorVertex _ _
        (leftStraighteningInfinityReconstruction
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (leftStraighteningInfinityReconstruction_projection _)) :=
  _root_.SerrePositivity.InfinityCategories.F1.Transport.coslicePointEvaluation_relativeIso _ _ _ _ e

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint_action := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_action

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint_fiberMap := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_fiberMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceReconstructionPoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceReconstructionPoint := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceReconstructionPoint

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceTriangle_relativeIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceTriangle_relativeIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceTriangle_relativeIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceReconstructionPoint._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceReconstructionPoint._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceTriangle_relativeIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceTriangle_relativeIso._proof_1
