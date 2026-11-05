module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientCoslicePointAction
public import SerrePositivity.InfinityCategories.F1.Transport.PointedTransformationPointHom

/-! # 同じ商上の coslice 合成の恒等点を、元の二胞体の成分との合成で厳密に表示する -/

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
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 合成の同じ実恒等点の矢印の類は、商へ移した元の恒等点と同じ比較成分との合成。 -/
theorem weakQuotientCosliceCompositePoint_component_hom :
    weakIdentityQuotientPointHom h x ≫
      functorHomEvaluate (weakQuotientCosliceComparisonHom h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) =
      cosliceFiberPointHom (smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (weakQuotientCosliceCompositePoint h x)) := by
  have he := pointedFunctorHomPointHom (weakQuotientCosliceComparisonHom h x)
    (q.hom.app (Opposite.op ⦋0⦌) x) (weakIdentityQuotientPointedFiber h x)
  have hs : cosliceFiberPointHom (weakIdentityQuotientPointedFiber h x) =
      weakIdentityQuotientPointHom h x := weakIdentityQuotientPointedFiber_hom h x
  rw [hs] at he
  exact he.trans (congrArg cosliceFiberPointHom (weakQuotientCosliceCompositePoint_action h x))

/-- 元の同じ strict Kan 恒等点・商への実制限同型・元の分数比較・分類同型を全て保持した式。 -/
theorem weakQuotientCosliceCompositePoint_normalized_hom :
    weakIdentityNativePointHom h x ≫ (weakIdentityQuotientValueIso h x).inv ≫
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      functorHomEvaluate (fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) =
      cosliceFiberPointHom (smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (weakQuotientCosliceCompositePoint h x)) := by
  simpa only [weakIdentityQuotientPointHom, weakQuotientCosliceComparisonHom,
    functorHomEvaluate_comp, Category.assoc] using
      weakQuotientCosliceCompositePoint_component_hom h x

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint_component_hom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_component_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint_normalized_hom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_normalized_hom
