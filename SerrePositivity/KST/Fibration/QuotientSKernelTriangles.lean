module
public import SerrePositivity.KST.Fibration.KanCommSqTriangles
public import SerrePositivity.KST.Fibration.QuotientSKernelEdges

/-!
概要：元の商核 Ex∞ 四角形の上下全二胞体を、元の四射の実合成二胞体として回収する。
方針：同じ実現四角形を Kan 四角形へ送り、その strict coherent 錐の全二単体を計算する。
規約：元の二胞体そのものと共有対角を保持する。指定 Verdier 側との全比較は別途必要。
使われ方：K-6 c4 の商核側の全二胞体と、元の核零化円柱の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)

/-- 元の商核の下側全二胞体は、同じ包含と商の Ex∞ 射の標準合成二胞体。 -/
theorem quotientSKernelInfinitySquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ quotientSKernelInfinitySquare i q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct
        (exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap i)))
        (exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap q)))).simplex :=
  kanCommSqInfinitySquare_lower_compStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq (quotientSKernelRealizationSquare i q))

/-- 元の商核の上側全二胞体は、同じ相対核包含と元の零合成像の標準合成二胞体。 -/
theorem quotientSKernelInfinitySquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ quotientSKernelInfinitySquare i q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct
        (exInfinityKanMap (simplicialDiagonalFunctor.map
          (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom))))
        (exInfinityKanMap (simplicialDiagonalFunctor.map
          (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q)))).simplex :=
  kanCommSqInfinitySquare_upper_compStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq (quotientSKernelRealizationSquare i q))

/-- 元の商核の共有対角は、同じ元の包含・商の Ex∞ 射の実合成の全一単体。 -/
theorem quotientSKernelInfinitySquare_diagonal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ quotientSKernelInfinitySquare i q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap i)) ≫
          exInfinityKanMap (simplicialDiagonalFunctor.map (coreSExactMap q)))).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal (1 : Fin 2), Category.assoc, quotientSKernelInfinitySquare_lower]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct _ _).δ_one_yonedaEquiv_symm

end SerrePositivity.KST.Fibration
