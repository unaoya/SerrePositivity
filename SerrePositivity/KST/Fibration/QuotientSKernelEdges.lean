module
public import SerrePositivity.KST.Fibration.QuotientSKernelInfinitySquare
public import SerrePositivity.KST.Fibration.ExInfinityCommSqEdges

/-! # 元の商核 ∞ 四角形の包含・商射・零合成の全四辺を厳密に回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} (i : ExactMap A B) (q : ExactMap B C)

/-- 同じ商核四角形の右辺は、元の商の core S 実現射の Ex∞ 像そのもの。 -/
theorem quotientSKernelInfinitySquare_right :
    squareRightEdge ≫ quotientSKernelInfinitySquare i q = SSet.yonedaEquiv.symm
      (coherentNerveEdge (exInfinityKanMap
        (simplicialDiagonalFunctor.map (coreSExactMap q)))).edge :=
  exInfinityCommSqInfinitySquare_right (quotientSKernelRealizationSquare i q)

/-- 同じ商核四角形の下辺は、元の包含の core S 実現射の Ex∞ 像そのもの。 -/
theorem quotientSKernelInfinitySquare_bottom :
    squareBottomEdge ≫ quotientSKernelInfinitySquare i q = SSet.yonedaEquiv.symm
      (coherentNerveEdge (exInfinityKanMap
        (simplicialDiagonalFunctor.map (coreSExactMap i)))).edge :=
  exInfinityCommSqInfinitySquare_bottom (quotientSKernelRealizationSquare i q)

/-- 同じ商核四角形の左辺は、元の相対 S 包含の実現射の Ex∞ 像そのもの。 -/
theorem quotientSKernelInfinitySquare_left :
    squareLeftEdge ≫ quotientSKernelInfinitySquare i q = SSet.yonedaEquiv.symm
      (coherentNerveEdge (exInfinityKanMap (simplicialDiagonalFunctor.map
        (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom))))).edge :=
  exInfinityCommSqInfinitySquare_left (quotientSKernelRealizationSquare i q)

/-- 同じ商核四角形の上辺は、元の全相対零合成と商への射の Ex∞ 像そのもの。 -/
theorem quotientSKernelInfinitySquare_top :
    squareTopEdge ≫ quotientSKernelInfinitySquare i q = SSet.yonedaEquiv.symm
      (coherentNerveEdge (exInfinityKanMap (simplicialDiagonalFunctor.map
        (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q)))).edge :=
  exInfinityCommSqInfinitySquare_top (quotientSKernelRealizationSquare i q)

/-- 元の商核四角形の零角は、元の相対 S 核の実現の Ex∞ 値そのものである。 -/
theorem quotientSKernelInfinitySquare_corner :
    squareVertex (quotientSKernelInfinitySquare i q) 0 1 = coherentNerveVertex
      (exInfinityClosedKanEnrichedFunctor.obj ⟨simplicialDiagonalFunctor.obj
        (relativeSimplicialSConstruction (i.hom ≫ q.hom))⟩) :=
  exInfinityCommSqInfinitySquare_corner (quotientSKernelRealizationSquare i q)

end SerrePositivity.KST.Fibration
