module
public import SerrePositivity.KST.Fibration.ScaffoldTransportPointedCoefficient
public import SerrePositivity.KST.Fibration.OppositeKanPointedEvaluation

/-! # 元の scaffold 係数点の weighted 像を、標準 coherent Hom 比較で回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : ScaffoldTransportComparisonSpan p)

/-- 元の係数点の同じ weighted 像は、逆係数成分と標準 coherent Hom 比較の実像。 -/
theorem coefficientWeightedPointedFiberPoint_val_coherent
    (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (s.coefficientWeightedPointedFiberPoint c v).val =
      (((SSet.uliftFunctor.{u + 1, u}).map
        ((oppositePointHomDiagramIso (leftStrictTransportFunctor p)).inv.app c) ≫
          HomotopyLimits.coherentCosliceFiberComparison pointKanObject
            ((leftStrictTransportFunctor p ⋙ kanObjectOpFunctor).obj c) ≫
          vertexFiberι (sliceUnderProjection
            (yonedaEquiv.symm (coherentNerveVertex pointKanObject)))
              (coherentNerveVertex ((leftStrictTransportFunctor p ⋙ kanObjectOpFunctor).obj c)) ≫
          strictKanPointedApexIso.hom).app (Opposite.op ⦋0⦌) (ULift.up v)) := by
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up v))
    (oppositeKanUnstraighteningComparison_constant_pointed (leftStrictTransportFunctor p) c)
  exact (s.coefficientWeightedPointedFiberPoint_val c v).trans h

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration
