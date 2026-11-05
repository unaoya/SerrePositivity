module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.KST.LocalizingInvariants.TwoArrowConeSquares
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCosliceSpanAttachment

public import SerrePositivity.KST.LocalizingInvariants.RoofPastingConeFaces

/-!
概要：実右分数を添付した有限台を、指定合成三角柱の同じ五頂点図式へ接続する。
方針：元の二辺と分数 span を、同じ二頂点に沿う pushout で厳密に貼る。
規約：全図式と両 cospan は同じ写像の制限であり、共有辺を選び直さない。
使われ方：回収済み全錐の商比較を、元の指定合成三角柱の二面へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 元の二辺を、三角柱の同じ五頂点へ入れる。 -/
def roofPastingOriginalPair : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) ⟶
    (pastingCorner : SSet.{u}).op :=
  coprod.desc (squareLeftEdge ≫ roofPastingSquareInclusion)
    (squareRightEdge ≫ roofPastingSquareInclusion)

lemma roofPastingSpan_source : stdSimplex.δ (1 : Fin 2) ≫
    stdSimplex.δ (2 : Fin 3) ≫ roofPastingTriangleInclusion.{u} =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) ≫
        roofPastingTriangleInclusion := by
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  apply Prod.ext <;> decide

/-- 同じ実分数の span を、三角柱の同じ三頂点へ入れる。 -/
def roofPastingFractionSpan : (horn 2 0 : SSet.{u}) ⟶
    (pastingCorner : SSet.{u}).op :=
  horn₂₀.isPushout.desc
    (stdSimplex.δ (2 : Fin 3) ≫ roofPastingTriangleInclusion)
    (stdSimplex.δ (1 : Fin 3) ≫ roofPastingTriangleInclusion) roofPastingSpan_source

lemma roofPastingAttachment_pair :
    fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget ≫
      roofPastingOriginalPair = fractionSpanTargets ≫ roofPastingFractionSpan := by
  apply coprod.hom_ext
  · simp only [← Category.assoc, fractionDiagramTargets, coprod.inl_desc,
      fractionSpanTargets]
    rw [twoArrowFirstTarget_point, Category.assoc, roofPastingOriginalPair,
      coprod.inl_desc, Category.assoc, roofPastingFractionSpan,
      horn₂₀.isPushout.inl_desc]
    exact roofPastingDenominator_target
  · simp only [← Category.assoc, fractionDiagramTargets, coprod.inr_desc,
      fractionSpanTargets]
    rw [twoArrowSecondTarget_point, Category.assoc, roofPastingOriginalPair,
      coprod.inr_desc, Category.assoc, roofPastingFractionSpan,
      horn₂₀.isPushout.inr_desc]
    exact roofPastingNumerator_target.symm

/-- 同じ有限実添付台から、指定三角柱の五頂点への全写像。 -/
def roofPastingAttachmentMap :
    fractionSpanAttachmentShape twoArrowFirstTarget.{u} twoArrowSecondTarget ⟶
      (pastingCorner : SSet.{u}).op :=
  pushout.desc roofPastingOriginalPair roofPastingFractionSpan roofPastingAttachment_pair

lemma roofPastingAttachmentMap_original :
    pushout.inl (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget)
      fractionSpanTargets ≫ roofPastingAttachmentMap = roofPastingOriginalPair :=
  pushout.inl_desc _ _ _

lemma roofPastingAttachmentMap_fraction :
    pushout.inr (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget)
      fractionSpanTargets ≫ roofPastingAttachmentMap = roofPastingFractionSpan :=
  pushout.inr_desc _ _ _

lemma roofPastingAttachmentMap_denominator : conePairCospan twoArrowOriginalFirst
    twoArrowFractionDenominator twoArrow_first_target ≫ roofPastingAttachmentMap.{u} =
      roofPastingDenominatorCospan := by
  apply horn₂₂.isPushout.hom_ext
  · rw [← Category.assoc, conePairCospan_first, twoArrowOriginalFirst,
      Category.assoc, roofPastingAttachmentMap_original, roofPastingOriginalPair,
      coprod.inl_desc, roofPastingDenominatorCospan, conePairCospan_first]
  · rw [← Category.assoc, conePairCospan_second, twoArrowFractionDenominator,
      Category.assoc, roofPastingAttachmentMap_fraction, roofPastingFractionSpan,
      horn₂₀.isPushout.inl_desc, roofPastingDenominatorCospan, conePairCospan_second]

lemma roofPastingAttachmentMap_numerator : conePairCospan twoArrowFractionNumerator
    twoArrowOriginalSecond twoArrow_second_target ≫ roofPastingAttachmentMap.{u} =
      roofPastingNumeratorCospan := by
  apply horn₂₂.isPushout.hom_ext
  · rw [← Category.assoc, conePairCospan_first, twoArrowFractionNumerator,
      Category.assoc, roofPastingAttachmentMap_fraction, roofPastingFractionSpan,
      horn₂₀.isPushout.inr_desc, roofPastingNumeratorCospan, conePairCospan_first]
  · rw [← Category.assoc, conePairCospan_second, twoArrowOriginalSecond,
      Category.assoc, roofPastingAttachmentMap_original, roofPastingOriginalPair,
      coprod.inr_desc, roofPastingNumeratorCospan, conePairCospan_second]

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachmentMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingAttachmentMap := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachmentMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingAttachmentMap_denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachmentMap_denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingAttachmentMap_fraction := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachmentMap_fraction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingAttachmentMap_numerator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachmentMap_numerator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingAttachmentMap_original := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachmentMap_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingAttachment_pair := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachment_pair

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingFractionSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingFractionSpan := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingFractionSpan

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingOriginalPair (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingOriginalPair := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingOriginalPair

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingSpan_source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingSpan_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingAttachmentMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachmentMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingAttachmentMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingAttachmentMap._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingFractionSpan._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingFractionSpan._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingFractionSpan._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingFractionSpan._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingFractionSpan.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingFractionSpan.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingOriginalPair._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingOriginalPair._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.roofPastingOriginalPair.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.roofPastingOriginalPair.eq_1
