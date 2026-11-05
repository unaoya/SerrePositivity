module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Straightening.SmallUnstraighteningFunctorHom
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionKanCosliceClassification
public import SerrePositivity.KST.Fibration.WeakQuotientCosliceUnit
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientMappingComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityReconstruction

/-! # 元の商上の比較二胞体を、同じ coslice 分類図式の小さい全空間への射として保持する -/

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

/-- 元の商上の比較の後に、同じ coslice 射影の実分類図式との照合を合成する。 -/
def weakQuotientCosliceComparisonHom :
    FunctorHom (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
      (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom

/-- 同じ元の比較二胞体から得られる、商上の小さい unstraightening 間の実写像。 -/
def weakQuotientCosliceComparison :
    smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x) ⟶
      smallLeftUnstraightening (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom h x)

/-- 同じ比較は、元の小さい Verdier 商上の底を厳密に固定する。 -/
theorem weakQuotientCosliceComparison_projection : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison h x ≫
    smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) =
      smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x) :=
  _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_projection _

/-- 元の恒等点からの coslice 比較の後で、同じ商上の分数評価を行う合成。 -/
def weakQuotientCosliceComposite :
    sliceUnder (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)) ⟶
      smallLeftUnstraightening (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  weakQuotientCosliceUnit h x ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison h x

/-- 合成も元の同じ coslice 射影を厳密に被覆する。 -/
theorem weakQuotientCosliceComposite_projection : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite h x ≫
    smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) =
      sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison_projection, weakQuotientCosliceUnit_projection]

/-- 同じ合成の恒等錐での値は、元の実 fiber 点の比較像そのもの。 -/
theorem weakQuotientCosliceComposite_identity :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite h x).app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone (q.hom.app (Opposite.op ⦋0⦌) x)) =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison h x).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityQuotientFiberPoint h x).val := by
  change (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison h x).app (Opposite.op ⦋0⦌)
    ((weakQuotientCosliceUnit h x).app (Opposite.op ⦋0⦌) _) = _
  rw [weakQuotientCosliceUnit_identity]

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceComparisonHom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceComparison_projection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparison_projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceComposite := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceComposite_identity := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite_identity

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceComposite_projection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceComparisonHom._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComparisonHom._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceComposite.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceComposite.eq_1
