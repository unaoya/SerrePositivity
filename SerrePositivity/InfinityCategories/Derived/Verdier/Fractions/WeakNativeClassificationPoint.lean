module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityNativeImage
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientCosliceIdentityHom
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionClassificationRestriction

/-! # 同じ coslice 合成の恒等点を、元の native 比較像と指定分類成分だけで表す -/

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

/-- 元の target Kan 値から、同じ指定済み分類同型の商像成分へ至る実射。 -/
def fractionIdentityNativeClassificationHom :
    HomotopyCategory.mk (spaceInfinityVertex
      ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj
        (transportSimplexIndex (n := ⦋0⦌) x))) ⟶
      HomotopyCategory.mk ((leftStraighteningInfinityDiagram
        (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))).app
          (Opposite.op ⦋0⦌) (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))) :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityQuotientValueIso h x).inv ≫
    functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))

/-- 元の商比較・分類の合成の恒等点は、同じ native 実像と指定分類成分との合成。 -/
theorem weakQuotientCosliceCompositePoint_native_image_hom :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom h x ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom h x =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint h x)) := by
  have he := congrArg (fun m => m ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityQuotientValueIso h x).inv ≫
    functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom_native_image h x)
  have hn : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom h x ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom h x ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom h x := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom, Category.assoc,
      Iso.hom_inv_id_assoc] using he
  exact hn.symm.trans (by
    simpa only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientPointHom, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_normalized_hom h x)

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionIdentityNativeClassificationHom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint_native_image_hom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_native_image_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionIdentityNativeClassificationHom._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionIdentityNativeClassificationHom.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom.eq_1
