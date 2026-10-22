module
public import SerrePositivity.KST.Fibration.ScaffoldTransportCoefficientPoints
public import SerrePositivity.KST.Fibration.NativeRepresentationComparisonPoint

/-! # 元の係数点の native 像を、同じ scaffold 表現の weighted 点へ比較する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : ScaffoldTransportComparisonSpan p)

/-- 同じ相対三角の source 点を、対応する pointed-space fiber で読む。 -/
def coefficientSourcePointedFiberPoint (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (vertexFiber pointedSpaceProjection
      ((leftCoherentTransport p).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)))) _⦋0⦌ :=
  (leftUnstraighteningFiberIso (leftCoherentTransport p) (ULift.up (nerveVertex c))).hom.app
    (Opposite.op ⦋0⦌) (s.coefficientSourceFiberPoint c v)

/-- 同じ相対三角の weighted 点を、同じ pointed-space fiber で読む。 -/
def coefficientWeightedPointedFiberPoint (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (vertexFiber pointedSpaceProjection
      ((leftCoherentTransport p).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)))) _⦋0⦌ :=
  (leftUnstraighteningFiberIso (leftCoherentTransport p) (ULift.up (nerveVertex c))).hom.app
    (Opposite.op ⦋0⦌) (s.coefficientWeightedFiberPoint c v)

/-- weighted 点の値は、元の定値包含と同じ coherent 比較の実像。 -/
theorem coefficientWeightedPointedFiberPoint_val
    (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (s.coefficientWeightedPointedFiberPoint c v).val =
      (((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
          leftCoherentTransportComparison p ≫
            pullback.fst pointedSpaceProjection (leftCoherentTransport p)).app
              (Opposite.op ⦋0⦌) (ULift.up v)) := by
  have he := congrArg
    (fun m => m.app (Opposite.op ⦋0⦌) (s.coefficientWeightedFiberPoint c v))
    (leftUnstraighteningFiberIso_hom_ι (leftCoherentTransport p)
      (ULift.up (nerveVertex c)))
  exact he.trans (congrArg
    (fun w => (pullback.fst pointedSpaceProjection (leftCoherentTransport p)).app
      (Opposite.op ⦋0⦌) w) (s.coefficientWeightedFiberPoint_val c v))

/-- 底を固定した同じ相対三角により、元の点の射は厳密に一致する。 -/
theorem coefficientPointHom_eq (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    cosliceFiberPointHom (s.coefficientSourcePointedFiberPoint c v) =
      cosliceFiberPointHom (s.coefficientWeightedPointedFiberPoint c v) :=
  cosliceFiberPointHom_eq_of_vertexIso (VertexIso.map (s.coefficientFiberPointIso c v)
    (leftUnstraighteningFiberIso (leftCoherentTransport p) (ULift.up (nerveVertex c))).hom)

/-- source 点は、元の恒等射評価の同じ実点を表現の pointed map に送ったもの。 -/
theorem coefficientSourcePointedFiberPoint_eq (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    s.coefficientSourcePointedFiberPoint c v =
      (transportRepresentationPointedFiberMap s.toStrictTransportComparisonSpan.representation
        (ULift.up (nerveVertex c))).app (Opposite.op ⦋0⦌)
          ((uliftVertexFiberIso p (nerveVertex c)).hom.app (Opposite.op ⦋0⦌)
            (ULift.up ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v))) := by
  apply Subtype.ext
  have he := congrArg
    (fun m => m.app (Opposite.op ⦋0⦌) (s.coefficientSourceFiberPoint c v))
    (leftUnstraighteningFiberIso_hom_ι (leftCoherentTransport p)
      (ULift.up (nerveVertex c)))
  exact he.trans (congrArg
    (fun w => (pullback.fst pointedSpaceProjection (leftCoherentTransport p)).app
      (Opposite.op ⦋0⦌) w) (s.coefficientSourceFiberPoint_val c v))

/-- native 像の同じ指定分類成分は、元の係数点の weighted 像を回収する。 -/
theorem nativeCoefficientPointHom (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    cosliceFiberPointHom ((nativeTransportPointedFiberMap p (nerveVertex c)).app
      (Opposite.op ⦋0⦌)
        (ULift.up ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v))) ≫
      functorHomEvaluate (nativeRepresentationComparisonIso p
        (nativeLeftTransportRepresentation p)
        s.toStrictTransportComparisonSpan.representation).hom (ULift.up (nerveVertex c)) =
    cosliceFiberPointHom (s.coefficientWeightedPointedFiberPoint c v) := by
  have h := nativeRepresentationComparisonIso_pointHom p
    s.toStrictTransportComparisonSpan.representation (nerveVertex c)
    ((leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v)
  exact h.trans ((congrArg cosliceFiberPointHom
    (s.coefficientSourcePointedFiberPoint_eq c v)).symm.trans (s.coefficientPointHom_eq c v))

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration
