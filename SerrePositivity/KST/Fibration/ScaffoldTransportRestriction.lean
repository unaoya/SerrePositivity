module
public import SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan
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
  {p : E ⟶ nerve I} [LeftFibration p] (s : ScaffoldTransportComparisonSpan p)

/-- 元の scaffold の同じ埋め込みを宇宙持ち上げする。 -/
def coherentEmbedding :
    (SSet.uliftFunctor.{u + 1, u}).obj (simplicialReplacement (leftStrictTransportDiagram p)) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj s.total :=
  (SSet.uliftFunctor.{u + 1, u}).map s.embedding

/-- 元の scaffold 上への source 脚の厳密な制限。 -/
theorem coherentEmbedding_source :
    s.coherentEmbedding ≫ s.toStrictTransportComparisonSpan.coherentSource =
      (SSet.uliftFunctor.{u + 1, u}).map (universalScaffold p) := by
  rw [coherentEmbedding, StrictTransportComparisonSpan.coherentSource,
    ← Functor.map_comp, s.source_restriction]

/-- weighted 比較への因子分解も、元の taut scaffold 上で厳密に回収する。 -/
theorem coherentEmbedding_target :
    s.coherentEmbedding ≫ s.toStrictTransportComparisonSpan.coherentTarget =
      (SSet.uliftFunctor.{u + 1, u}).map (tautScaffold (leftStrictTransportDiagram p)) ≫
        leftCoherentTransportComparison p := by
  rw [coherentEmbedding, StrictTransportComparisonSpan.coherentTarget,
    ← Category.assoc, ← Functor.map_comp, s.weighted_restriction]

/-- 同じ実比較を元の universal・taut scaffold に制限した三角。 -/
def scaffoldTriangle : FunctorIso
    ((SSet.uliftFunctor.{u + 1, u}).map (universalScaffold p) ≫
      s.toStrictTransportComparisonSpan.coherentComparison.hom)
    ((SSet.uliftFunctor.{u + 1, u}).map (tautScaffold (leftStrictTransportDiagram p)) ≫
      leftCoherentTransportComparison p) := by
  have h := s.toStrictTransportComparisonSpan.representationTriangle.precomp s.coherentEmbedding
  rw [← Category.assoc, s.coherentEmbedding_source, s.coherentEmbedding_target] at h
  exact h

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration
