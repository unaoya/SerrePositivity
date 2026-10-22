module
public import SerrePositivity.KST.Fibration.ScaffoldWeightedResolutionPoint

/-! # 元の native 係数点の射を、同じ分類成分と値の表示変更で左解像点へ送る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ fiber 点の端点表示を等号で変えても、点の射の合成式を保つ。 -/
theorem pointedFiberPointHom_endpointTransport
    {a b : SpaceInfinity.{u} _⦋0⦌} (h : a = b)
    (v : (vertexFiber pointedSpaceProjection a) _⦋0⦌) :
    cosliceFiberPointHom v ≫ (eqToIso (congrArg HomotopyCategory.mk h)).hom =
      cosliceFiberPointHom (vertexFiberPointReindex pointedSpaceProjection h v) := by
  subst b
  change cosliceFiberPointHom v ≫ 𝟙 _ = cosliceFiberPointHom v
  exact Category.comp_id _

/-- 元の native 係数点の射は、同じ指定成分で元の左解像点の射へ移る。 -/
theorem ScaffoldTransportComparisonSpan.nativeCoefficientPointHom_resolution
    {I : Type u} [Category.{u} I] {E : SSet.{u}} {p : E ⟶ nerve I} [LeftFibration p]
    (s : ScaffoldTransportComparisonSpan p) (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    cosliceFiberPointHom ((nativeTransportPointedFiberMap p (nerveVertex c)).app
      (Opposite.op ⦋0⦌)
        (ULift.up ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v))) ≫
      functorHomEvaluate (nativeRepresentationComparisonIso p
        (nativeLeftTransportRepresentation p)
        s.toStrictTransportComparisonSpan.representation).hom (ULift.up (nerveVertex c)) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c))).hom =
    cosliceFiberPointHom
      ((pointedSpaceLeftResolutionComparison ((leftStrictTransportFunctor p).obj c)).app
        (Opposite.op ⦋0⦌) (ULift.up v)) := by
  have h := congrArg
    (fun m => m ≫ (eqToIso (congrArg HomotopyCategory.mk
      (ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c))).hom)
    (s.nativeCoefficientPointHom c v)
  have he := pointedFiberPointHom_endpointTransport
    (ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c)
    (s.coefficientWeightedPointedFiberPoint c v)
  have hn := (s.coefficientWeightedResolutionPoint_eq c v)
  have hr := he.trans (congrArg cosliceFiberPointHom hn)
  simpa only [Category.assoc] using h.trans hr

end SerrePositivity.KST.Fibration
