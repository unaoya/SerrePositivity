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
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の商上の比較の後に、同じ coslice 射影の実分類図式との照合を合成する。 -/
def weakQuotientCosliceComparisonHom :
    FunctorHom (weakSpanKanQuotientDiagram h x)
      (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  weakQuotientMappingComparison h x ≫ (fractionKanQuotientDiagram_classificationIso h x).hom

/-- 同じ元の比較二胞体から得られる、商上の小さい unstraightening 間の実写像。 -/
def weakQuotientCosliceComparison :
    smallLeftUnstraightening (weakSpanKanQuotientDiagram h x) ⟶
      smallLeftUnstraightening (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  smallUnstraighteningFunctorHom (weakQuotientCosliceComparisonHom h x)

/-- 同じ比較は、元の小さい Verdier 商上の底を厳密に固定する。 -/
theorem weakQuotientCosliceComparison_projection : weakQuotientCosliceComparison h x ≫
    smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) =
      smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) :=
  smallUnstraighteningFunctorHom_projection _

/-- 元の恒等点からの coslice 比較の後で、同じ商上の分数評価を行う合成。 -/
def weakQuotientCosliceComposite :
    sliceUnder (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)) ⟶
      smallLeftUnstraightening (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) :=
  weakQuotientCosliceUnit h x ≫ weakQuotientCosliceComparison h x

/-- 合成も元の同じ coslice 射影を厳密に被覆する。 -/
theorem weakQuotientCosliceComposite_projection : weakQuotientCosliceComposite h x ≫
    smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))) =
      sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)) := by
  rw [weakQuotientCosliceComposite, Category.assoc,
    weakQuotientCosliceComparison_projection, weakQuotientCosliceUnit_projection]

/-- 同じ合成の恒等錐での値は、元の実 fiber 点の比較像そのもの。 -/
theorem weakQuotientCosliceComposite_identity :
    (weakQuotientCosliceComposite h x).app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone (q.hom.app (Opposite.op ⦋0⦌) x)) =
      (weakQuotientCosliceComparison h x).app (Opposite.op ⦋0⦌)
        (weakIdentityQuotientFiberPoint h x).val := by
  change (weakQuotientCosliceComparison h x).app (Opposite.op ⦋0⦌)
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
