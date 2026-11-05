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
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 合成の同じ実恒等点の矢印の類は、商へ移した元の恒等点と同じ比較成分との合成。 -/
theorem weakQuotientCosliceCompositePoint_component_hom :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom h x ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint h x)) := by
  have he := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFunctorHomPointHom (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom h x)
    (q.hom.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointedFiber h x)
  have hs : _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointedFiber h x) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom h x := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointedFiber_hom h x
  rw [hs] at he
  exact he.trans (congrArg _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_action h x))

/-- 元の同じ strict Kan 恒等点・商への実制限同型・元の分数比較・分類同型を全て保持した式。 -/
theorem weakQuotientCosliceCompositePoint_normalized_hom :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativePointHom h x ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientValueIso h x).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint h x)) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom,
    functorHomEvaluate_comp, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_component_hom h x

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint_component_hom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_component_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint_normalized_hom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_normalized_hom
