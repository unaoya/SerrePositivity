module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitZeroFaceSourceWitness

/-!
概要：元の第零面の指定始域比較を、F1 の同じ全族比較の成分へ同定する。
方針：全係数上の同じ実証拠へ、指定比較の成分公式を適用する。
規約：比較の値を保持。使われ方：既存の全族比較の成分への照合。
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
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "f" => coherentColimitUnitPointedFirstEdgeEndpoint B T k H he
local notation "hf" => coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k H he
local notation "Z" => coherentColimitUnitZeroFaceCanonicalLongWitness B T k H he S hS

/-- 元の第零面の長辺の指定始域比較を与える、同じ全族の F1 比較。 -/
def coherentColimitUnitZeroFaceSourceFamilyComparison :=
  functorHomotopySourceFamilyComparison c p f hf
    (coherentColimitUnitZeroFaceSourceWitness B T k H he S hS true)

/-- 元の第零面の長辺の指定始域比較は、F1 の同じ全族比較の指定成分。 -/
lemma coherentColimitUnitZeroFaceLongSourceIso_heq_component :
    HEq (coherentColimitUnitZeroFaceLongSourceIso B T k H he S hS)
      (VertexIso.map
        ((coherentColimitUnitZeroFaceSourceFamilyComparison B T k H he S hS).app
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
        (relativeFunctorPre (leftUnstraighteningProjection Q₂) p
          (𝟙 (leftUnstraightening F ⊗ K)))) :=
  (coherentColimitUnitZeroFaceLongSourceIso_heq_homotopy B T k H he S hS).trans
    (functorHomotopySourceEndpointIso_heq_component c p f hf
      (coherentColimitUnitZeroFaceSourceWitness B T k H he S hS true))

end SerrePositivity.InfinityCategories.F2
