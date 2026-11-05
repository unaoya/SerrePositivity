module

public import SerrePositivity.KST.LocalizingInvariants.TwoArrowCosliceNormalization

/-!
概要：右分数添付後の同じ有限全錐から、共有辺を持つ二つの実四角形を読み出す。
方針：pushout の同じ頂点一致を使い、二つの実 cospan へ同じ全錐を制限する。
規約：四角形の全四辺は元の実辺であり、共有辺は実単体写像として厳密に一致する。
使われ方：正次数の元の前段と次辺族を、同じ実右分数へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の第一の矢印の、同じ添付後の有限台への包含。 -/
def twoArrowOriginalFirst : (Δ[1] : SSet.{u}) ⟶
    fractionSpanAttachmentShape twoArrowFirstTarget.{u} twoArrowSecondTarget :=
  (coprod.inl : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1]) ≫
    pushout.inl (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget)
      fractionSpanTargets

/-- 元の第二の矢印の、同じ添付後の有限台への包含。 -/
def twoArrowOriginalSecond : (Δ[1] : SSet.{u}) ⟶
    fractionSpanAttachmentShape twoArrowFirstTarget.{u} twoArrowSecondTarget :=
  (coprod.inr : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1]) ≫
    pushout.inl (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget)
      fractionSpanTargets

/-- 実右分数の同じ分母辺の包含。 -/
def twoArrowFractionDenominator : (Δ[1] : SSet.{u}) ⟶
    fractionSpanAttachmentShape twoArrowFirstTarget.{u} twoArrowSecondTarget :=
  horn₂₀.ι₀₁ ≫ pushout.inr
    (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget) fractionSpanTargets

/-- 実右分数の同じ分子辺の包含。 -/
def twoArrowFractionNumerator : (Δ[1] : SSet.{u}) ⟶
    fractionSpanAttachmentShape twoArrowFirstTarget.{u} twoArrowSecondTarget :=
  horn₂₀.ι₀₂ ≫ pushout.inr
    (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget) fractionSpanTargets

lemma twoArrowFirstTarget_point : SSet.yonedaEquiv.symm twoArrowFirstTarget.{u} =
    stdSimplex.δ (0 : Fin 2) ≫
      (coprod.inl : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1]) := by
  rw [twoArrowFirstTarget, ← SSet.yonedaEquiv_symm_comp]
  congr 1
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  decide

lemma twoArrowSecondTarget_point : SSet.yonedaEquiv.symm twoArrowSecondTarget.{u} =
    stdSimplex.δ (0 : Fin 2) ≫
      (coprod.inr : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1]) := by
  rw [twoArrowSecondTarget, ← SSet.yonedaEquiv_symm_comp]
  congr 1
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  decide

lemma twoArrow_first_target : stdSimplex.δ (0 : Fin 2) ≫ twoArrowOriginalFirst.{u} =
    stdSimplex.δ (0 : Fin 2) ≫ twoArrowFractionDenominator := by
  have hc : fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget ≫
      pushout.inl _ fractionSpanTargets = fractionSpanTargets ≫ pushout.inr
        (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget) _ :=
    pushout.condition
  have he := congrArg (fun f =>
    (coprod.inl : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0]) ≫ f) hc
  have hκ : (coprod.inl : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0]) ≫
      fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget =
      SSet.yonedaEquiv.symm twoArrowFirstTarget := coprod.inl_desc _ _
  have hspan : (coprod.inl : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0]) ≫
      fractionSpanTargets = stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₁ := coprod.inl_desc _ _
  simp only [← Category.assoc] at he
  rw [hκ, hspan] at he
  simpa only [twoArrowFirstTarget_point, twoArrowOriginalFirst,
    twoArrowFractionDenominator, Category.assoc] using he

lemma twoArrow_second_target : stdSimplex.δ (0 : Fin 2) ≫ twoArrowFractionNumerator.{u} =
    stdSimplex.δ (0 : Fin 2) ≫ twoArrowOriginalSecond := by
  have hc : fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget ≫
      pushout.inl _ fractionSpanTargets = fractionSpanTargets ≫ pushout.inr
        (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget) _ :=
    pushout.condition
  have he := congrArg (fun f =>
    (coprod.inr : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0]) ≫ f) hc
  have hκ : (coprod.inr : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0]) ≫
      fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget =
      SSet.yonedaEquiv.symm twoArrowSecondTarget := coprod.inr_desc _ _
  have hspan : (coprod.inr : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0]) ≫
      fractionSpanTargets = stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂ := coprod.inr_desc _ _
  simp only [← Category.assoc] at he
  rw [hκ, hspan] at he
  simpa only [twoArrowSecondTarget_point, twoArrowOriginalSecond,
    twoArrowFractionNumerator, Category.assoc] using he.symm

lemma twoArrow_fraction_source : stdSimplex.δ (1 : Fin 2) ≫
    twoArrowFractionDenominator.{u} = stdSimplex.δ (1 : Fin 2) ≫ twoArrowFractionNumerator := by
  exact congrArg (fun f => f ≫ pushout.inr
    (fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget) fractionSpanTargets)
      horn₂₀.isPushout.w

lemma twoArrow_original_source : SSet.yonedaEquiv
    (stdSimplex.δ (1 : Fin 2) ≫ twoArrowOriginalFirst.{u}) = twoArrowAttachedSource := by
  simp only [twoArrowOriginalFirst, SSet.yonedaEquiv_comp]
  have h₀ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
  rw [h₀]
  rfl

variable {X : SSet.{u}}
  {p : fractionSpanAttachmentShape twoArrowFirstTarget.{u} twoArrowSecondTarget ⟶ X}
  (c : JoinCone p)

/-- 同じ有限全錐から取る、元の前段への実四角形。 -/
def twoArrowDenominatorSquare : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X :=
  conePairSquare c twoArrowOriginalFirst twoArrowFractionDenominator twoArrow_first_target

/-- 同じ有限全錐から取る、元の次辺への実四角形。 -/
def twoArrowNumeratorSquare : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X :=
  conePairSquare c twoArrowFractionNumerator twoArrowOriginalSecond twoArrow_second_target

/-- 二つの実四角形は、同じ実辺を厳密に共有する。 -/
lemma twoArrowConeSquares_shared : squareLeftEdge ≫ twoArrowDenominatorSquare c =
    squareBottomEdge ≫ twoArrowNumeratorSquare c := by
  rw [twoArrowDenominatorSquare, twoArrowNumeratorSquare,
    conePairSquare_left, conePairSquare_bottom, twoArrow_fraction_source]

/-- 前段への実四角形の底辺は、同じ元の始点への実錐脚そのもの。 -/
lemma twoArrowDenominatorSquare_bottom_edge : (squareBottomArrow
    (twoArrowDenominatorSquare c)).edge = (F2.nativeConeLeg c twoArrowAttachedSource).edge := by
  rw [squareBottomArrow_edge, twoArrowDenominatorSquare, conePairSquare_bottom,
    SSet.yonedaEquiv_comp, twoArrow_original_source]
  rfl

namespace TwoArrowNativeSquares

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {a : (Δ[0] : SSet.{u}) ⟶ C.obj}
  (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
  (U : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) ⟶ sliceUnder a)
  {e : Truncated.Edge (X := (truncation 2).obj (sliceUnder a))
    (U.app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
    (U.app (Opposite.op ⦋0⦌) twoArrowSecondTarget)}
  (r : VerdierCosliceFractionNormalization h a e
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowSecondTarget))

lemma originalFirst : twoArrowOriginalFirst ≫
    cosliceSpanNativeDiagram (coprod.desc D L) U twoArrowFirstTarget twoArrowSecondTarget r =
      D := by
  simp only [twoArrowOriginalFirst, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.cosliceSpanNativeDiagram_original, coprod.inl_desc]

lemma originalSecond : twoArrowOriginalSecond ≫
    cosliceSpanNativeDiagram (coprod.desc D L) U twoArrowFirstTarget twoArrowSecondTarget r =
      L := by
  simp only [twoArrowOriginalSecond, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.cosliceSpanNativeDiagram_original, coprod.inr_desc]

lemma fractionDenominator : twoArrowFractionDenominator ≫
    cosliceSpanNativeDiagram (coprod.desc D L) U twoArrowFirstTarget twoArrowSecondTarget r =
      SSet.yonedaEquiv.symm r.denominator.edge := by
  simp only [twoArrowFractionDenominator, Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.cosliceSpanNativeDiagram,
    pushout.inr_desc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCosliceFractionNormalization.nativeSpan,
    horn₂₀.isPushout.inl_desc]
  rfl

lemma fractionNumerator : twoArrowFractionNumerator ≫
    cosliceSpanNativeDiagram (coprod.desc D L) U twoArrowFirstTarget twoArrowSecondTarget r =
      SSet.yonedaEquiv.symm r.numerator.edge := by
  simp only [twoArrowFractionNumerator, Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.cosliceSpanNativeDiagram,
    pushout.inr_desc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCosliceFractionNormalization.nativeSpan,
    horn₂₀.isPushout.inr_desc]
  rfl

variable (d : JoinCone
  (cosliceSpanNativeDiagram (coprod.desc D L) U twoArrowFirstTarget twoArrowSecondTarget r))

lemma denominator_right : squareRightEdge ≫ twoArrowDenominatorSquare d = D := by
  rw [twoArrowDenominatorSquare, conePairSquare_right, originalFirst]

lemma denominator_top : squareTopEdge ≫ twoArrowDenominatorSquare d =
    SSet.yonedaEquiv.symm r.denominator.edge := by
  rw [twoArrowDenominatorSquare, conePairSquare_top, fractionDenominator]

lemma numerator_right : squareRightEdge ≫ twoArrowNumeratorSquare d =
    SSet.yonedaEquiv.symm r.numerator.edge := by
  rw [twoArrowNumeratorSquare, conePairSquare_right, fractionNumerator]

lemma numerator_top : squareTopEdge ≫ twoArrowNumeratorSquare d = L := by
  rw [twoArrowNumeratorSquare, conePairSquare_top, originalSecond]

end TwoArrowNativeSquares

/-- 元の二本の矢印と指定商四角形から、共有次辺を持つ実屋根を構成する。
両端の実分母を新しい仮定として要求しない。商四角形との全比較は別途接続する。 -/
lemma exists_verdierTwoArrowNativeRoof {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj)
    (hb : squareBottomEdge ≫ F = D ≫ q.hom) (ht : squareTopEdge ≫ F = L ≫ q.hom) :
    ∃ S T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ B.obj,
      squareRightEdge ≫ S = D ∧ squareTopEdge ≫ T = L ∧
      squareLeftEdge ≫ S = squareBottomEdge ≫ T ∧
      (squareBottomArrow S).edge ∈ weakEquivalences i ∧
      (squareTopArrow S).edge ∈ weakEquivalences i := by
  obtain ⟨s, r, d, _, s₀, hs₀, hw⟩ :=
    exists_verdierTwoArrowCosliceNormalization h D L F hb ht
  refine ⟨twoArrowDenominatorSquare d, twoArrowNumeratorSquare d,
    TwoArrowNativeSquares.denominator_right D L (twoArrowCosliceDiagram s) r d,
    TwoArrowNativeSquares.numerator_top D L (twoArrowCosliceDiagram s) r d,
    twoArrowConeSquares_shared d, ?_, ?_⟩
  · rw [twoArrowDenominatorSquare_bottom_edge, ← hs₀]
    exact hw
  · have he := TwoArrowNativeSquares.denominator_top D L (twoArrowCosliceDiagram s) r d
    have he' := congrArg SSet.yonedaEquiv he
    rw [← squareTopArrow_edge] at he'
    have he'' := he'.trans (SSet.yonedaEquiv.apply_symm_apply r.denominator.edge)
    rw [he'']
    exact r.denominator_mem

end SerrePositivity.KST.LocalizingInvariants
