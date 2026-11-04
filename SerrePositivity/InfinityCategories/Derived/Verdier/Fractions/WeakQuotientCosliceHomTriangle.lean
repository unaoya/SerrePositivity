module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientCosliceIdentityHom
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceFiberHomClass
public import SerrePositivity.InfinityCategories.F1.UniverseVertexIso

/-! # 指定恒等点の元の射の類の比較から、同じ小さい底上の実三角比較を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 同じ小さい fiber 点を pointed-space で表示した射の類の等式は、元の実 fiber 点の同型へ戻る。 -/
def smallUnstraighteningFiberIsoOfPointHomEq {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    {v w : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌}
    (h : cosliceFiberPointHom (smallUnstraighteningPointedImage F b v) =
      cosliceFiberPointHom (smallUnstraighteningPointedImage F b w)) : VertexIso v w := by
  let I := smallLeftUnstraighteningFiberIso F b ≪≫ leftUnstraighteningFiberIso F (ULift.up b)
  have e := VertexIso.map (cosliceFiberVertexIsoOfHomEq h) I.inv
  have hv : I.inv.app (Opposite.op ⦋0⦌) (smallUnstraighteningPointedImage F b v) =
      ULift.up v := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up v)) I.hom_inv_id
  have hw : I.inv.app (Opposite.op ⦋0⦌) (smallUnstraighteningPointedImage F b w) =
      ULift.up w := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up w)) I.hom_inv_id
  have ev := eqToIso (congrArg HomotopyCategory.mk hv)
  have ew := eqToIso (congrArg HomotopyCategory.mk hw)
  exact downVertexIso (ev.symm ≪≫ e ≪≫ ew)

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 同じ native 恒等点・実制限同型・元の比較成分を保つ一点の式から、相対三角比較を回収。 -/
def weakQuotientCosliceTriangle_of_identity_hom
    (he : weakIdentityNativePointHom h x ≫ (weakIdentityQuotientValueIso h x).inv ≫
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      functorHomEvaluate (fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) =
      cosliceFiberPointHom (smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (weakQuotientCosliceReconstructionPoint (q := q) x))) :
    VertexIso
      (relativeFunctorVertex _ _ (weakQuotientCosliceComposite h x)
        (weakQuotientCosliceComposite_projection h x))
      (relativeFunctorVertex _ _
        (leftStraighteningInfinityReconstruction
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (leftStraighteningInfinityReconstruction_projection _)) :=
  weakQuotientCosliceTriangle_relativeIso h x
    (smallUnstraighteningFiberIsoOfPointHomEq _ _
      ((weakQuotientCosliceCompositePoint_normalized_hom h x).symm.trans he))

end SerrePositivity.KST.Fibration
