module
public import SerrePositivity.KST.Fibration.TransportRepresentationFiberPointHom
public import SerrePositivity.KST.Fibration.PointedCosliceNativePoint

/-! # native 表現の指定点を、同じ可縮な表現空間の選択済み分類比較で送る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の小さい射影の二表現を比較する、同じ可縮空間の指定分類同型。 -/
def nativeRepresentationComparisonIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (R S : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
    FunctorIso R.diagram S.diagram := by
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((SSet.uliftFunctor.{u + 1, u}).obj E |>.obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (E.obj n)))
  exact smallFiberTransportRepresentationDiagramIso _ (hasSmallSimplexFibers_of_small_total _) R S

/-- native 表現の元の指定 fiber 点を同じ選択済み分類比較で送ると、比較先の同じ点を回収。 -/
theorem nativeRepresentationComparisonIso_pointHom {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p]
    (S : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    (b : B _⦋0⦌) (v : (vertexFiber p b) _⦋0⦌) :
    cosliceFiberPointHom ((nativeTransportPointedFiberMap p b).app
      (Opposite.op ⦋0⦌) (ULift.up v)) ≫
      functorHomEvaluate
        (nativeRepresentationComparisonIso p (nativeLeftTransportRepresentation p) S).hom
        (ULift.up b) =
      cosliceFiberPointHom ((transportRepresentationPointedFiberMap S (ULift.up b)).app
        (Opposite.op ⦋0⦌) ((uliftVertexFiberIso p b).hom.app (Opposite.op ⦋0⦌) (ULift.up v))) := by
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((SSet.uliftFunctor.{u + 1, u}).obj E |>.obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (E.obj n)))
  exact transportRepresentationFiberPointHom_diagramIso
    ((SSet.uliftFunctor.{u + 1, u}).map p) (ULift.up b)
    ((uliftVertexFiberIso p b).hom.app (Opposite.op ⦋0⦌) (ULift.up v))
    (nativeLeftTransportRepresentation p) S
    (smallFiberTransportRepresentationVertexIso _ (hasSmallSimplexFibers_of_small_total _) _ _)

/-- 元の coslice 恒等点にも、同じ指定分類比較の同じ成分の自然性が適用される。 -/
theorem nativeCosliceIdentityPoint_comparison {B : SSet.{u}} [Quasicategory B]
    (b : B _⦋0⦌)
    (S : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map
      (sliceUnderProjection (yonedaEquiv.symm b)))) :
    cosliceFiberPointHom (nativeCosliceIdentityPoint b) ≫
      functorHomEvaluate
        (nativeRepresentationComparisonIso (sliceUnderProjection (yonedaEquiv.symm b))
          (nativeLeftTransportRepresentation (sliceUnderProjection (yonedaEquiv.symm b))) S).hom
        (ULift.up b) =
      cosliceFiberPointHom ((transportRepresentationPointedFiberMap S (ULift.up b)).app
        (Opposite.op ⦋0⦌) ((uliftVertexFiberIso
          (sliceUnderProjection (yonedaEquiv.symm b)) b).hom.app (Opposite.op ⦋0⦌)
            (ULift.up (edgeToCosliceFiberVertex (SSet.Edge.id b))))) :=
  nativeRepresentationComparisonIso_pointHom _ S b (edgeToCosliceFiberVertex (SSet.Edge.id b))

end SerrePositivity.KST.Fibration
