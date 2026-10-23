module
public import SerrePositivity.KST.Fibration.StrictTransportComparisonSpan
public import SerrePositivity.KST.Fibration.SpanCompatibleComparison
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection

/-! # 指定した復元 span の相対三角を保持する coherent transport 表現 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace StrictTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : StrictTransportComparisonSpan p)

/-- 同じ指定 span の二脚を結ぶ相対三角も含めて選んだ、coherent な実比較。 -/
def coherentComparison : SpanCompatibleComparison
    ((SSet.uliftFunctor.{u + 1, u}).map p)
    (leftUnstraighteningProjection (leftCoherentTransport p))
    s.coherentBase s.coherentSource s.coherentTarget
    s.coherentSource_over s.coherentTarget_over :=
  spanCompatibleComparison _ _ _ _ _ _ _
    s.coherentSource_equivalence s.coherentTarget_equivalence

/-- 同じ実比較を用いた表現。元の span の三角を別の存在選択で失わない。 -/
def representation :
    LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p) where
  diagram := leftCoherentTransport p
  comparison := s.coherentComparison.hom
  over_base := s.coherentComparison.over
  fiber_equivalence b :=
    vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence _ _ _
      s.coherentComparison.over s.coherentComparison.equivalence b

/-- 元の共通全空間の指定点において、同じ相対三角を実 fiber 内で評価する。 -/
def representationPointIso (z : s.total _⦋0⦌) : VertexIso
    ((relativeFunctorEvaluate
      (leftUnstraighteningProjection (leftCoherentTransport p)) s.coherentBase
      (ULift.up z)).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex _ _ (s.coherentSource ≫ s.coherentComparison.hom)
          (by rw [Category.assoc, s.coherentComparison.over, s.coherentSource_over])))
    ((relativeFunctorEvaluate
      (leftUnstraighteningProjection (leftCoherentTransport p)) s.coherentBase
      (ULift.up z)).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex _ _ s.coherentTarget s.coherentTarget_over)) :=
  s.coherentComparison.pointIso (ULift.up z)

end StrictTransportComparisonSpan
end SerrePositivity.KST.Fibration
