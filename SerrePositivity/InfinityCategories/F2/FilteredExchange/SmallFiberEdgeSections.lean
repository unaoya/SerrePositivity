module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallFiberPointedPrismEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedSectionSourceFiber
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleDiagramSource
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedSectionTargetFiber

/-!
概要：元の実際の fiber 作用を、同じ coherent 辺上の切断族として表示する。
方針：元の普遍 prism を相対 curry し、始点評価を恒等・終点評価を元の fiber 射へ同定する。
規約：元の作用と全パラメータを保持。使われ方：fiber cospan から切断 cospan への比較同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "e" => coherentTransformationPointEdge F G x b
local notation "h₀" => coherentTransformationPointEdge_source F G x b
local notation "h₁" => coherentTransformationPointEdge_target F G x b

/-- 元の実際の fiber 作用を表す、同じ辺の切断の全パラメータ族。 -/
def coherentSmallFiberEdgeSections : a ⟶ relativeFunctorSpace pointedSpaceProjection e :=
  relativeFunctorCurry (coherentSmallFiberPointedPrism F G x b)
    (coherentSmallFiberPointedPrism_projection F G x b)

/-- この切断族の始点は、元の同じ fiber の恒等写像である。 -/
lemma coherentSmallFiberEdgeSections_source :
    coherentSmallFiberEdgeSections F G x b ≫ pointedSectionSourceFiber F b e h₀ = 𝟙 a := by
  apply pointedSectionSourceFiber_eq_of_evaluate_ι
  unfold coherentSmallFiberEdgeSections
  rw [relativeCurry_evaluate_ι]
  simpa only [prismEndpoint, Category.id_comp] using coherentSmallFiberPointedPrism_source F G x b

/-- この切断族の終点は、元の実際の小さい fiber 射の持ち上げである。 -/
lemma coherentSmallFiberEdgeSections_target :
    coherentSmallFiberEdgeSections F G x b ≫ pointedSectionTargetFiber G b e h₁ =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
          (coherentTransformationTotalMap_projection F G x) b) := by
  apply pointedSectionTargetFiber_eq_of_evaluate_ι
  unfold coherentSmallFiberEdgeSections
  rw [relativeCurry_evaluate_ι]
  exact coherentSmallFiberPointedPrism_target_fiber F G x b

/-- 元の実際の fiber 作用を表す切断族は、始点評価の逆向きの同値である。 -/
lemma coherentSmallFiberEdgeSections_isQCatEquivalence :
    IsQCatEquivalence (coherentSmallFiberEdgeSections F G x b) := by
  have hp := pointedSectionSourceFiber_isQCatEquivalence F b e h₀
  apply hp.cancel_right
  rw [coherentSmallFiberEdgeSections_source]
  exact (qCatEquivalenceOfIso (Iso.refl a)).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2
