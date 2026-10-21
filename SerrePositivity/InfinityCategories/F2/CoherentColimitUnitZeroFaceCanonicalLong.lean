module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceLongWitness
public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyPointedPrism

/-!
概要：元の指定長辺の普遍 prism を、同じ第零面の長辺の共通証拠型へ入れる。
方針：同じ指定長辺証拠との射影の一致を用い、実始域と選択済み長辺作用を保持する。
規約：普遍 prism の選び直しなし。使われ方：長辺の三証拠の指定比較を合成。
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
local notation "f" => coherentColimitUnitPointedFirstEdgeEndpoint B T k H he
local notation "w" => unstraighteningMappingTriangleLongWitness Q₀ Q₁ Q₂
  (SSet.const (coherentVertexOfHomotopy a)) (SSet.const (coherentVertexOfHomotopy b))
  (SSet.const (coherentVertexOfHomotopy c))
  (CoherentTransformationVertexTriangle.diagram (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.first (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.second (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.long (coherentTriangleOfFunctorTriangle S))

/-- 実第一辺の終点の後で、元の指定長辺の選択済み作用を適用する同じ実射。 -/
def coherentColimitUnitZeroFaceCanonicalLongMap (_S : FunctorCompositionTriangle a b c) :=
  f ≫ (leftUnstraighteningMappingVertexMap Q₀ Q₂ (coherentVertexOfHomotopy c)).val

/-- 元の指定長辺の作用は、元の同じ全パラメータの底を保つ。 -/
lemma coherentColimitUnitZeroFaceCanonicalLongMap_projection :
    coherentColimitUnitZeroFaceCanonicalLongMap B T k H he S ≫
      leftUnstraighteningProjection Q₂ =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F := by
  rw [coherentColimitUnitZeroFaceCanonicalLongMap, Category.assoc,
    (leftUnstraighteningMappingVertexMap Q₀ Q₂ (coherentVertexOfHomotopy c)).property,
    coherentColimitUnitPointedFirstEdgeEndpoint_projection]

/-- 元の普遍長辺 prism を、実長辺と指定三角形の長辺の同じ全証拠型へ入れる。 -/
def coherentColimitUnitZeroFaceCanonicalLongWitness :
    RelativeExtensionEndpointWitness pointedSpaceProjection
      ((stdSimplex.δ (1 : Fin 3) ▷ (leftUnstraightening F ⊗ K)) ≫
        (α_ Δ[2] (leftUnstraightening F) K).inv ≫
        ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫
        (coherentColimitUnitPointedZeroFaceFamily B T k).diagram)
      (prismEndpoint 0 (leftUnstraightening F ⊗ K))
      (simplexPrismVertex 0 0 (leftUnstraightening F ⊗ K) ≫
        (α_ Δ[0] (leftUnstraightening F) K).inv ≫
        (coherentColimitUnitPointedZeroFaceFamily B T k).boundary)
      (prismEndpoint 1 (leftUnstraightening F ⊗ K)) Q₂
      (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) :=
  { coherentColimitUnitZeroFaceLongWitness B T k H he S hS true with
    extension := functorHomotopyPointedPrism c f
    «over» := by
      have hc : (functorHomotopyPointedWitness c).prism ≫ pointedSpaceProjection =
          (w).prism ≫ pointedSpaceProjection :=
        (functorHomotopyPointedWitness c).projection.trans (w).projection.symm
      have hc' := congrArg (fun z => prismParameterRestriction
        (lift f (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ z) hc
      have hh := coherentColimitUnitZeroFaceLong_original_extension B T k H he S hS
      have hext := congrArg (fun z => z ≫ pointedSpaceProjection) hh
      have hbase := hext.symm.trans
        (coherentColimitUnitZeroFaceLongWitness B T k H he S hS true).over
      simpa only [functorHomotopyPointedPrism, Category.assoc] using hc'.trans hbase
    initial := (functorHomotopyPointedPrism_source c f).trans
      (coherentColimitUnitZeroFaceLong_initial B T k H he).symm
    endpoint := coherentColimitUnitZeroFaceCanonicalLongMap B T k H he S
    endpoint_over := coherentColimitUnitZeroFaceCanonicalLongMap_projection B T k H he S
    evaluate := functorHomotopyPointedPrism_target c f }

end SerrePositivity.InfinityCategories.F2
