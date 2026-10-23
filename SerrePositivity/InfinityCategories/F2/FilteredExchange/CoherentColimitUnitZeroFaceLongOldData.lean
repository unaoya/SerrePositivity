module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitZeroFaceCanonicalLong
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyRestrictedData
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionWitnessDataEquality

/-!
概要：長辺三証拠の底・全初期値・終点底を、既存の指定三角形比較の実データへ揃える。
方針：元の普遍長辺の射影と、同じ実第一辺への一点代入を使う。
規約：元の実延長と実終点を保持。使われ方：直接比較と既存の指定比較の値の同定。
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
local notation "s₀" => f ≫ lift (𝟙 (leftUnstraightening Q₀))
  (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "D" => coherentColimitUnitPointedZeroFaceFamily B T k

include he hS in
/-- 三証拠の同じ長辺の底は、元の指定三角形比較の一点制限の底そのもの。 -/
lemma coherentColimitUnitZeroFaceLong_old_base :
    (stdSimplex.δ (1 : Fin 3) ▷ (leftUnstraightening F ⊗ K)) ≫
      (α_ Δ[2] (leftUnstraightening F) K).inv ≫
      ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫ (D).diagram =
    prismParameterRestriction s₀ ≫
      ((Δ[1] ◁ leftUnstraighteningProjection Q₀) ▷ (Δ[0] : SSet.{u + 1})) ≫
      functorParameterizedPrism (intervalMappingUncurry
        (SSet.const (coherentVertexOfHomotopy c))) :=
  (coherentColimitUnitZeroFaceCanonicalLongWitness B T k H he S hS).over.symm.trans
    (functorHomotopyRestricted_base c f)

/-- 三証拠の同じ全初期値は、元の指定三角形比較の一点制限の初期値そのもの。 -/
lemma coherentColimitUnitZeroFaceLong_old_initial :
    simplexPrismVertex 0 0 (leftUnstraightening F ⊗ K) ≫
      (α_ (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) K).inv ≫ (D).boundary =
    s₀ ≫ (fst (leftUnstraightening Q₀) (Δ[0] : SSet.{u + 1}) ≫
      𝟙 (leftUnstraightening Q₀) ≫ pullback.fst pointedSpaceProjection Q₀) :=
  (coherentColimitUnitZeroFaceLong_initial B T k H he).trans
    (functorHomotopyRestricted_initial f).symm

/-- 三証拠の同じ終点底は、元の指定三角形比較の一点制限の終点底そのもの。 -/
lemma coherentColimitUnitZeroFaceLong_old_apex :
    fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F =
    s₀ ≫ (fst (leftUnstraightening Q₀) (Δ[0] : SSet.{u + 1}) ≫
      leftUnstraighteningProjection Q₀) :=
  (coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k H he).symm.trans
    (functorHomotopyRestricted_apex f).symm

end SerrePositivity.InfinityCategories.F2
