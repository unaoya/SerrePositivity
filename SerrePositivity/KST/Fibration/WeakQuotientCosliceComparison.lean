module
public import SerrePositivity.KST.Fibration.SmallUnstraighteningFunctorHom
public import SerrePositivity.KST.Fibration.FractionKanCosliceClassification
public import SerrePositivity.KST.Fibration.WeakQuotientCosliceUnit
public import SerrePositivity.KST.Fibration.WeakQuotientMappingComparison
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction

/-! # 元の商上の比較二胞体を、同じ coslice 分類図式の小さい全空間への射として保持する -/

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

end SerrePositivity.KST.Fibration
