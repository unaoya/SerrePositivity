module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportRestriction
public import SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan
public import SerrePositivity.KST.Fibration.SpanTransportPointedTriangle

/-! # 元の scaffold に制限した、同じ coherent transport の相対三角 -/

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
  {p : E ⟶ nerve I} [LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan p)

/-- 同じ実比較を元の universal・taut scaffold に制限した三角。 -/
def scaffoldTriangle : FunctorIso
    ((SSet.uliftFunctor.{u + 1, u}).map (universalScaffold p) ≫
      (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.coherentComparison s.toStrictTransportComparisonSpan).hom)
    ((SSet.uliftFunctor.{u + 1, u}).map (tautScaffold (leftStrictTransportDiagram p)) ≫
      leftCoherentTransportComparison p) := by
  have h := (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representationTriangle s.toStrictTransportComparisonSpan).precomp (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coherentEmbedding s)
  rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coherentEmbedding_source s), (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coherentEmbedding_target s)] at h
  exact h

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration
