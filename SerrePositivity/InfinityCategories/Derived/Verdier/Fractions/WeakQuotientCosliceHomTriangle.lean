module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientCosliceIdentityHom
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceFiberHomClass
public import SerrePositivity.InfinityCategories.F1.UniverseVertexIso

/-! # 指定恒等点の元の射の類の比較から、同じ小さい底上の実三角比較を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 同じ小さい fiber 点を pointed-space で表示した射の類の等式は、元の実 fiber 点の同型へ戻る。 -/
def smallUnstraighteningFiberIsoOfPointHomEq {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    {v w : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌}
    (h : _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage F b v) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage F b w)) : VertexIso v w := by
  let I := smallLeftUnstraighteningFiberIso F b ≪≫ leftUnstraighteningFiberIso F (ULift.up b)
  have e := VertexIso.map (_root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberVertexIsoOfHomEq h) I.inv
  have hv : I.inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage F b v) =
      ULift.up v := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up v)) I.hom_inv_id
  have hw : I.inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage F b w) =
      ULift.up w := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up w)) I.hom_inv_id
  have ev := eqToIso (congrArg HomotopyCategory.mk hv)
  have ew := eqToIso (congrArg HomotopyCategory.mk hw)
  exact downVertexIso (ev.symm ≪≫ e ≪≫ ew)

variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 同じ native 恒等点・実制限同型・元の比較成分を保つ一点の式から、相対三角比較を回収。 -/
def weakQuotientCosliceTriangle_of_identity_hom
    (he : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativePointHom h x ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientValueIso h x).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceReconstructionPoint (q := q) x))) :
    VertexIso
      (relativeFunctorVertex _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite h x)
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite_projection h x))
      (relativeFunctorVertex _ _
        (leftStraighteningInfinityReconstruction
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (leftStraighteningInfinityReconstruction_projection _)) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceTriangle_relativeIso h x
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.smallUnstraighteningFiberIsoOfPointHomEq _ _
      ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_normalized_hom h x).symm.trans he))

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.smallUnstraighteningFiberIsoOfPointHomEq (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFiberIsoOfPointHomEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.smallUnstraighteningFiberIsoOfPointHomEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceTriangle_of_identity_hom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceTriangle_of_identity_hom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceTriangle_of_identity_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFiberIsoOfPointHomEq._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.smallUnstraighteningFiberIsoOfPointHomEq._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFiberIsoOfPointHomEq._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.smallUnstraighteningFiberIsoOfPointHomEq._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFiberIsoOfPointHomEq._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.smallUnstraighteningFiberIsoOfPointHomEq._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceTriangle_of_identity_hom._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceTriangle_of_identity_hom._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceTriangle_of_identity_hom._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceTriangle_of_identity_hom._proof_2
