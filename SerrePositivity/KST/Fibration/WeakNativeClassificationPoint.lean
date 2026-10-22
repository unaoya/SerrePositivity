module
public import SerrePositivity.KST.Fibration.WeakIdentityNativeImage
public import SerrePositivity.KST.Fibration.WeakQuotientCosliceIdentityHom
public import SerrePositivity.KST.Fibration.FractionClassificationRestriction

/-! # 同じ coslice 合成の恒等点を、元の native 比較像と指定分類成分だけで表す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の target Kan 値から、同じ指定済み分類同型の商像成分へ至る実射。 -/
def fractionIdentityNativeClassificationHom :
    HomotopyCategory.mk (spaceInfinityVertex
      ((fractionSimplexKanMappingDiagram q.hom x).obj
        (transportSimplexIndex (n := ⦋0⦌) x))) ⟶
      HomotopyCategory.mk ((leftStraighteningInfinityDiagram
        (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))).app
          (Opposite.op ⦋0⦌) (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))) :=
  (fractionIdentityQuotientValueIso h x).inv ≫
    functorHomEvaluate (fractionKanQuotientDiagram_classificationIso h x).hom
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))

/-- 元の商比較・分類の合成の恒等点は、同じ native 実像と指定分類成分との合成。 -/
theorem weakQuotientCosliceCompositePoint_native_image_hom :
    weakIdentityNativeComparisonImageHom h x ≫ fractionIdentityNativeClassificationHom h x =
      cosliceFiberPointHom (smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (weakQuotientCosliceCompositePoint h x)) := by
  have he := congrArg (fun m => m ≫ (fractionIdentityQuotientValueIso h x).inv ≫
    functorHomEvaluate (fractionKanQuotientDiagram_classificationIso h x).hom
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))
    (weakIdentityQuotientPointHom_native_image h x)
  have hn : weakIdentityQuotientPointHom h x ≫
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      functorHomEvaluate (fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) =
      weakIdentityNativeComparisonImageHom h x ≫ fractionIdentityNativeClassificationHom h x := by
    simpa only [fractionIdentityNativeClassificationHom, Category.assoc,
      Iso.hom_inv_id_assoc] using he
  exact hn.symm.trans (by
    simpa only [weakIdentityQuotientPointHom, Category.assoc] using
      weakQuotientCosliceCompositePoint_normalized_hom h x)

end SerrePositivity.KST.Fibration
