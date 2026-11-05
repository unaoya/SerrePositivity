module
public import SerrePositivity.InfinityCategories.F1.Transport.TransportRepresentationPointHom
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallFiberStraighteningCounit
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.NerveStraighteningRepresentation

/-! # 可縮な表現空間で選んだ同じ分類比較が、元の pointedMap の指定点を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 可縮な表現空間で選択した同じ図式同型は、同じ二表現の元の実点を結ぶ。 -/
theorem smallFiberRepresentationPointHom {E B : SSet.{u + 1}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (hp : HasSmallSimplexFibers p)
    (R S : LeftTransportRepresentation p) (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt p e R) ≫
      functorHomEvaluate (smallFiberTransportRepresentationDiagramIso p hp R S).hom
        (p.app (Opposite.op ⦋0⦌) e) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt p e S) :=
  _root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointHom_diagramIso p e R S
    (smallFiberTransportRepresentationVertexIso p hp R S)

/-- 通常の nerve 上の反転 transport と同じ相対表現の比較は、元の指定点の射も保つ。 -/
theorem nerveCoherentTransportRepresentationIso_pointHom {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt
      ((SSet.uliftFunctor.{u + 1, u}).map p) (ULift.up e)
      (nerveLeftTransportRepresentation p)) ≫
      functorHomEvaluate (nerveCoherentTransportRepresentationIso p R).hom
        (ULift.up (p.app (Opposite.op ⦋0⦌) e)) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt
        ((SSet.uliftFunctor.{u + 1, u}).map p) (ULift.up e) R) := by
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((SSet.uliftFunctor.{u + 1, u}).obj E |>.obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (E.obj n)))
  exact smallFiberRepresentationPointHom ((SSet.uliftFunctor.{u + 1, u}).map p)
    (hasSmallSimplexFibers_of_small_total _) (nerveLeftTransportRepresentation p) R (ULift.up e)

end SerrePositivity.KST.Fibration
