module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegValueComparison
public import SerrePositivity.InfinityCategories.F1.Compact.CanonicalCoconeWeakEquivalence
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeFiberPointRepresentatives
public import SerrePositivity.InfinityCategories.F2.Compact.FunctorComponentComparison

/-!
概要：弱同値な実 fiber 写像を持つ余錐の点を、元の余錐脚の作用で成分まで回収する。
方針：全空間の点を同じ fiber 同型で一つの値へ戻し、実 prism の全比較を適用。
規約：元の同じ脚を保持し、底の filtered 性や Kan 性は要求しない。
使われ方：compact Ind 対象の恒等射を元の表現可能図式の一項へ因子化する。
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

/-- 弱同値な元の実 fiber 写像の全ての点は、元の同じ脚の作用から成分まで回収できる。 -/
lemma coconeLeg_point_representative_of_weak {B : SSet.{u + 1}}
    {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F)
    (hc : IsWeakHomotopyEquivalence (coconeFiberMap c))
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject c.vertex).obj) _⦋0⦌) :
    ∃ b : B _⦋0⦌,
      ∃ v : ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj) _⦋0⦌,
        SSet.π₀.mk (((SSet.uliftFunctor.{u + 1, u}).map
          (spaceInfinityEdgeValue (coconeTransportLeg c b))).app (Opposite.op ⦋0⦌) v) =
            SSet.π₀.mk x := by
  exact componentRepresentative_of_valueIso (pointedSpaceFiberValueEquivalence c.vertex)
    (fun b => vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b))
    (fun b => (SSet.uliftFunctor.{u + 1, u}).obj
      (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj)
    (fun b => (pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) b)).hom)
    (coconeLegFiberMap c)
    (fun b => (SSet.uliftFunctor.{u + 1, u}).map
      (spaceInfinityEdgeValue (coconeTransportLeg c b)))
    (coconeLegFiberMap_valueIso c) (coconeFiber_point_representative_of_weak c hc) x

/-- 標準全空間余錐の任意の点を、元の一つの値から同じ元の脚で回収する。 -/
lemma coherentTotalCoconeLeg_point_representative {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj
      (spaceInfinityObject (coherentDiagramTotalCocone F).vertex).obj) _⦋0⦌) :
    ∃ b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌,
      ∃ v : ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj) _⦋0⦌,
        SSet.π₀.mk (((SSet.uliftFunctor.{u + 1, u}).map
          (spaceInfinityEdgeValue
            (coconeTransportLeg (coherentDiagramTotalCocone F) b))).app (Opposite.op ⦋0⦌) v) =
              SSet.π₀.mk x :=
  coconeLeg_point_representative_of_weak (coherentDiagramTotalCocone F)
    (coherentTotalCoconeFiber_isWeakHomotopyEquivalence F) x

end SerrePositivity.InfinityCategories.F2.Compact
