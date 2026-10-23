module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeKanEnriched
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeInternalHomEvaluation

/-!
概要：共通 Hom 解像から反転した二つの Kan 対象の Hom への実際の射は同値。
方針：元の射を左端射影と内部 Hom の標準反転同型の合成に厳密に同定する。
規約：元の Hom と反転 Hom を同一視しない。
使われ方：反転係数の weighted cone の全空間比較の同値判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 元の反転 Hom の作用は、同じ左端射影に標準内部 Hom 反転同型を続けた射。 -/
lemma edgewiseOppositeKanEnrichedMap_eq_left (X Y : SSet.{u}) :
    edgewiseOppositeKanEnrichedMap X Y =
      edgewiseLeft ((ihom X).obj Y) ≫ (HomotopyLimits.oppositeInternalHomIso X Y).hom := by
  apply uncurry_injective
  rw [edgewiseOppositeKanEnrichedMap, uncurry_curry,
    uncurry_natural_left, oppositeInternalHomIso_uncurry]
  rfl

/-- 反転した対象間の実際の Hom の作用は、標的が Kan なら同値。 -/
lemma edgewiseOppositeKanEnrichedMap_isQCatEquivalence (X Y : SSet.{u}) [KanComplex Y] :
    IsQCatEquivalence (edgewiseOppositeKanEnrichedMap X Y) := by
  rw [edgewiseOppositeKanEnrichedMap_eq_left]
  exact (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((ihom X).obj Y))).comp
    (qCatEquivalenceOfIso (HomotopyLimits.oppositeInternalHomIso X Y)).isQCatEquivalence

end SerrePositivity.InfinityCategories
