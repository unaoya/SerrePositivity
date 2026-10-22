module

public import SerrePositivity.InfinityCategories.F2.Compact.RepresentationValueTransport
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegPointReindex
public import SerrePositivity.InfinityCategories.F2.Compact.PointRepresentativesReflection

/-!
概要：分類図式が元の指定余錐を余極限へ写すなら、元の fiber の点を元の脚の輸送で回収。
方針：同じ全余錐像の点回収を、両端の指定した表現値同値と全自然比較で反映する。
規約：元の射影・余錐・脚・fiber の点を保つ。
使われ方：compact 対象の恒等点を、元の coslice の一つの項へ因子化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の指定余錐像の余極限性は、元の同じ脚の実輸送による全 fiber 成分の回収を与える。 -/
lemma representationCocone_point_factorization {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (R : LeftTransportRepresentation p)
    {I : SSet.{u}} (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (c : JoinCocone D) (hc : IsColimitCone (mapJoinCocone R.diagram c))
    (t : vertexFiber p c.vertex _⦋0⦌) :
    ∃ i : ((SSet.uliftFunctor.{u + 1, u}).obj I) _⦋0⦌,
      ∃ w : vertexFiber p (D.app (Opposite.op ⦋0⦌) i) _⦋0⦌,
        SSet.π₀.mk ((edgeTransport p (coconeTransportLeg c i)).app (Opposite.op ⦋0⦌) w) =
          SSet.π₀.mk t :=
  componentRepresentative_reflect (representationFiberValueEquivalence p R c.vertex)
    (fun i => vertexFiber p (D.app (Opposite.op ⦋0⦌) i))
    (fun i => (SSet.uliftFunctor.{u + 1, u}).obj
      (spaceInfinityObject (R.diagram.app (Opposite.op ⦋0⦌)
        (D.app (Opposite.op ⦋0⦌) i))).obj)
    (fun i => representationFiberValueEquivalence p R (D.app (Opposite.op ⦋0⦌) i))
    (fun i => edgeTransport p (coconeTransportLeg c i))
    (fun i => (SSet.uliftFunctor.{u + 1, u}).map
      (spaceInfinityEdgeValue ((coconeTransportLeg c i).map R.diagram)))
    (fun i => representationValueTransportIso p R (coconeTransportLeg c i))
    (mappedColimitCoconeLeg_point_representative D R.diagram c hc) t

end SerrePositivity.InfinityCategories.F2.Compact
