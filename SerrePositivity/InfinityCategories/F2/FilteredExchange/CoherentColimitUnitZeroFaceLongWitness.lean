module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitZeroFaceEndpointIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleFamilyLongWitness
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedLongWitness

/-!
概要：元の第零面と元の指定三角形の長辺を、同じ全始点・底・実終点の証拠へ移す。
方針：元の全証拠を結合子で移し、元の指定長辺証拠を厳密に回収する。
規約：同じ二証拠の実延長を保持。使われ方：普遍長辺を加えた三証拠の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "D" => coherentColimitUnitPointedZeroFaceFamily B T k
local notation "w" => unstraighteningMappingTriangleLongWitness Q₀ Q₁ Q₂
  (SSet.const (coherentVertexOfHomotopy a)) (SSet.const (coherentVertexOfHomotopy b))
  (SSet.const (coherentVertexOfHomotopy c))
  (CoherentTransformationVertexTriangle.diagram (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.first (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.second (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.long (coherentTriangleOfFunctorTriangle S))

/-- 元の二つの全証拠を、そのまま同じ全係数の長辺の始点固定の証拠へ移す。 -/
def coherentColimitUnitZeroFaceLongWitness (original : Bool) :=
  let wFull := coherentColimitUnitZeroFaceEndpointWitness B T k H he S hS original
  pointedTriangleFamilyLongEndpointWitness D wFull.extension wFull.initial wFull.over Q₂
    (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    wFull.endpoint wFull.endpoint_over wFull.evaluate

/-- 移した長辺の同じ全初期値は、元の実第一辺の終点の pointed 成分そのもの。 -/
lemma coherentColimitUnitZeroFaceLong_initial :
    simplexPrismVertex 0 0 (leftUnstraightening F ⊗ K) ≫
      (α_ (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) K).inv ≫ (D).boundary =
    coherentColimitUnitPointedFirstEdgeEndpoint B T k H he ≫
      pullback.fst pointedSpaceProjection Q₀ := by
  rw [coherentColimitUnitPointedZeroFace_boundary_endpoint B T k H he]
  have ht : simplexPrismVertex 0 0 (leftUnstraightening F ⊗ K) ≫
      (α_ (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) K).inv ≫
      (snd (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) ▷ K) = 𝟙 _ := by
    apply SSet.hom_ext
    intro n
    rfl
  simpa only [Category.assoc, Category.id_comp] using congrArg (fun z => z ≫
    coherentColimitUnitPointedFirstEdgeEndpoint B T k H he ≫
      pullback.fst pointedSpaceProjection Q₀) ht

/-- 移した元の指定三角形の長辺は、指定比較に使った同じ長辺証拠の同じ実始域制限。 -/
lemma coherentColimitUnitZeroFaceLong_original_extension :
    (coherentColimitUnitZeroFaceLongWitness B T k H he S hS true).extension =
      prismParameterRestriction (lift (coherentColimitUnitPointedFirstEdgeEndpoint B T k H he)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ (w).prism := by
  calc
    _ = (Δ[1] ◁ coherentColimitUnitPointedFirstEdgeEndpoint B T k H he) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ leftUnstraightening Q₀) ≫ functorTrianglePointedLift S := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = _ := functorTrianglePointedLift_long S
      (coherentColimitUnitPointedFirstEdgeEndpoint B T k H he)

end SerrePositivity.InfinityCategories.F2
