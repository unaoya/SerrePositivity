module

public import
  SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFixedFaceLongComposition
public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyRestrictedData
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionWitnessDataEquality

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
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "f" => fst (leftUnstraightening F) K
local notation "s₀" => f ≫ lift (𝟙 (leftUnstraightening F))
  (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "D" => coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS

include hj hS in
/-- 三証拠の同じ長辺の底は、元の指定三角形比較の一点制限の底そのもの。 -/
lemma coherentColimitUnitPointedFixedFaceLong_old_base :
    (stdSimplex.δ (1 : Fin 3) ▷ (leftUnstraightening F ⊗ K)) ≫
      (α_ Δ[2] (leftUnstraightening F) K).inv ≫
      ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫ (D).diagram =
    prismParameterRestriction s₀ ≫
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ (Δ[0] : SSet.{u + 1})) ≫
      functorParameterizedPrism (intervalMappingUncurry
        (SSet.const (coherentVertexOfHomotopy c))) :=
  (coherentColimitUnitPointedFixedFaceCanonicalLongWitness B T k j hj S hS).over.symm.trans
    (functorHomotopyRestricted_base c f)

/-- 三証拠の同じ全初期値は、元の指定三角形比較の一点制限の初期値そのもの。 -/
lemma coherentColimitUnitPointedFixedFaceLong_old_initial :
    simplexPrismVertex 0 0 (leftUnstraightening F ⊗ K) ≫
      (α_ (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) K).inv ≫ (D).boundary =
    s₀ ≫ (fst (leftUnstraightening F) (Δ[0] : SSet.{u + 1}) ≫
      𝟙 (leftUnstraightening F) ≫ pullback.fst pointedSpaceProjection F) :=
  (coherentColimitUnitPointedFixedFaceLong_initial B T k j hj S hS).trans
    (functorHomotopyRestricted_initial f).symm

/-- 三証拠の同じ終点底は、元の指定三角形比較の一点制限の終点底そのもの。 -/
lemma coherentColimitUnitPointedFixedFaceLong_old_apex :
    fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F =
    s₀ ≫ (fst (leftUnstraightening F) (Δ[0] : SSet.{u + 1}) ≫
      leftUnstraighteningProjection F) :=
  (functorHomotopyRestricted_apex f).symm

end SerrePositivity.InfinityCategories.F2
