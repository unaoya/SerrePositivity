module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRoofPastingAttachment

/-!
概要：実二辺の屋根と元の指定商四角形を、一つの全 slice 同型で比較する。
方針：同じ有限全錐の回収を実行し、その同型を同じ合成三角柱の両屋根面へ制限する。
規約：二つの全四角形比較は同じ全錐同型から得られ、実分母を未供給入力にしない。
使われ方：有限線型図式の右分数正規化を、指定した商側の合成二胞体へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison
end SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 同じ実屋根と、その指定商合成三角柱へ向かう一つの全錐同型。 -/
structure VerdierTwoArrowRoofComparison {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj)
    (hb : squareBottomEdge ≫ F = D ≫ q.hom) (ht : squareTopEdge ≫ F = L ≫ q.hom) where
  seed : SquareCosliceSeed F
  fraction : VerdierCosliceFractionNormalization h (fractionSquarePoint F)
    (twoArrowCosliceEdge seed)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowSecondTarget)
  cone : JoinCone (cosliceSpanNativeDiagram (coprod.desc D L) (twoArrowCosliceDiagram seed)
    twoArrowFirstTarget twoArrowSecondTarget fraction)
  comparison : VertexIso
    (X := sliceOver (cosliceSpanNativeDiagram (coprod.desc D L) (twoArrowCosliceDiagram seed)
      twoArrowFirstTarget twoArrowSecondTarget fraction ≫ q.hom))
    (mapJoinCone q.hom cone)
    (cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram seed)
      twoArrowFirstTarget twoArrowSecondTarget fraction
      (twoArrowCoslice_projection q.hom D L F seed hb ht))
  sourceDenominator_mem : (squareBottomArrow (twoArrowDenominatorSquare cone)).edge ∈
    weakEquivalences i

namespace VerdierTwoArrowRoofComparison
open _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {D L : (Δ[1] : SSet.{u}) ⟶ B.obj}
  {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj}
  {hb : squareBottomEdge ≫ F = D ≫ q.hom} {ht : squareTopEdge ≫ F = L ≫ q.hom}
  (d : VerdierTwoArrowRoofComparison h D L F hb ht)

/-- 同じ元の商四角形・同じ実分数を含む指定合成三角柱。 -/
def prism : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj :=
  verdierTwoArrowQuotientPasting D L d.seed d.fraction

/-- 両屋根四角形の比較に共通な、同じ全錐の関手同型。 -/
def globalIso : FunctorIso ((mapJoinCone q.hom d.cone).val)
    (cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram d.seed)
      twoArrowFirstTarget twoArrowSecondTarget d.fraction
      (twoArrowCoslice_projection q.hom D L F d.seed hb ht)).val :=
  coneFunctorIsoOfVertexIso _ _ d.comparison

/-- 元の全商四角形を厳密に保持する。 -/
lemma original : pastingSquare d.prism 0 = (β_ Δ[1] Δ[1]).hom ≫ F :=
  verdierTwoArrowQuotientPasting_original D L d.seed d.fraction

/-- 実分母四角形の商像を、同じ指定合成三角柱の分母面へ比較する。 -/
def denominatorIso : FunctorIso (twoArrowDenominatorSquare d.cone ≫ q.hom)
    (pastingSquare d.prism 2) := by
  have e := d.globalIso.precomp (cospanConeSquareIso.inv ≫ joinMap (𝟙 Δ[0])
    (conePairCospan twoArrowOriginalFirst twoArrowFractionDenominator twoArrow_first_target))
  have e' : FunctorIso (twoArrowDenominatorSquare d.cone ≫ q.hom)
      (twoArrowDenominatorSquare (cosliceSpanQuotientCone (coprod.desc D L)
        (twoArrowCosliceDiagram d.seed) twoArrowFirstTarget twoArrowSecondTarget d.fraction
        (twoArrowCoslice_projection q.hom D L F d.seed hb ht))) := by
    simpa only [twoArrowDenominatorSquare, conePairSquare, mapJoinCone, Category.assoc] using e
  rw [verdierRoofPasting_denominator D L d.seed d.fraction hb ht] at e'
  exact e'

/-- 実分子四角形の商像を、同じ指定合成三角柱の分子面へ比較する。 -/
def numeratorIso : FunctorIso ((β_ Δ[1] Δ[1]).hom ≫ twoArrowNumeratorSquare d.cone ≫ q.hom)
    (pastingSquare d.prism 1) := by
  have e := d.globalIso.precomp ((β_ Δ[1] Δ[1]).hom ≫ cospanConeSquareIso.inv ≫
    joinMap (𝟙 Δ[0]) (conePairCospan twoArrowFractionNumerator twoArrowOriginalSecond
      twoArrow_second_target))
  have e' : FunctorIso ((β_ Δ[1] Δ[1]).hom ≫ twoArrowNumeratorSquare d.cone ≫ q.hom)
      ((β_ Δ[1] Δ[1]).hom ≫ twoArrowNumeratorSquare
        (cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram d.seed)
          twoArrowFirstTarget twoArrowSecondTarget d.fraction
          (twoArrowCoslice_projection q.hom D L F d.seed hb ht))) := by
    simpa only [twoArrowNumeratorSquare, conePairSquare, mapJoinCone, Category.assoc] using e
  rw [verdierRoofPasting_numerator D L d.seed d.fraction hb ht] at e'
  exact e'

lemma shared : squareLeftEdge ≫ twoArrowDenominatorSquare d.cone =
    squareBottomEdge ≫ twoArrowNumeratorSquare d.cone := twoArrowConeSquares_shared d.cone

lemma terminalDenominator_mem : (squareTopArrow (twoArrowDenominatorSquare d.cone)).edge ∈
    weakEquivalences i := by
  have he := TwoArrowNativeSquares.denominator_top D L (twoArrowCosliceDiagram d.seed)
    d.fraction d.cone
  have he' := congrArg SSet.yonedaEquiv he
  rw [← squareTopArrow_edge] at he'
  have he'' := he'.trans (SSet.yonedaEquiv.apply_symm_apply d.fraction.denominator.edge)
  rw [he'']
  exact d.fraction.denominator_mem

end VerdierTwoArrowRoofComparison

/-- 元の二辺と指定商四角形から、全比較付きの実屋根を新仮定なしに構成する。 -/
lemma exists_verdierTwoArrowRoofComparison {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj)
    (hb : squareBottomEdge ≫ F = D ≫ q.hom) (ht : squareTopEdge ≫ F = L ≫ q.hom) :
    Nonempty (VerdierTwoArrowRoofComparison h D L F hb ht) := by
  obtain ⟨s, r, c, ⟨e⟩, s₀, hs₀, hw⟩ :=
    exists_verdierTwoArrowCosliceNormalization h D L F hb ht
  refine ⟨⟨s, r, c, e, ?_⟩⟩
  rw [twoArrowDenominatorSquare_bottom_edge, ← hs₀]
  exact hw

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierTwoArrowRoofComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierTwoArrowRoofComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.comparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.comparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.cone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.cone := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.cone

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.denominatorIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.denominatorIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.denominatorIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.fraction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.fraction := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.fraction

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.globalIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.globalIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.globalIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.mk := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.numeratorIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.numeratorIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.numeratorIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.original := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.original

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.prism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.prism := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.prism

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.rec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.seed (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.seed := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.seed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.shared := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.shared

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.sourceDenominator_mem := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.sourceDenominator_mem

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.terminalDenominator_mem := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.terminalDenominator_mem

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.denominatorIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.denominatorIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.denominatorIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.denominatorIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.denominatorIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.denominatorIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.denominatorIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.denominatorIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.globalIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.globalIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.globalIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.globalIso._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.numeratorIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.numeratorIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.numeratorIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.numeratorIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierTwoArrowRoofComparison.numeratorIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowRoofComparison.numeratorIso._proof_3
