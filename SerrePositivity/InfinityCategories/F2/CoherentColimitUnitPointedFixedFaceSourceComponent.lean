module

public import
  SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFixedFaceLongComposition

/-!
概要：元の固定始点の二面の実終点と、元の二作用を合成した射を同じ終点比較で結ぶ。
方針：元の二つの全持ち上げ・全初期値・実終点を一つの共通証拠型へ束ねる。
規約：全パラメータと既存の指定終点比較を保持。使われ方：三関係の native 終点表示。
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
local notation "D" => coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS
local notation "C" => leftUnstraightening F ⊗ K
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
/-- 固定面の元の実長辺を保持する、F1 の同じ全族の指定始域比較。 -/
def coherentColimitUnitPointedFixedFaceSourceFamilyComparison :=
  functorHomotopySourceFamilyComparison c p (fst (leftUnstraightening F) K) rfl
    (coherentColimitUnitPointedFixedFaceHomotopyWitness B T k j hj S hS false)

/-- 固定面の元の指定始域比較は、全係数を保つ F1 の同じ全族比較の成分。 -/
lemma coherentColimitUnitPointedFixedFaceLongSourceIso_heq_component :
    HEq (coherentColimitUnitPointedFixedFaceLongSourceIso B T k j hj S hS)
      (VertexIso.map
        ((coherentColimitUnitPointedFixedFaceSourceFamilyComparison B T k j hj S hS).app
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
        (relativeFunctorPre (leftUnstraighteningProjection Q₂) p (𝟙 C))) :=
  (coherentColimitUnitPointedFixedFaceLongSourceIso_heq_homotopy B T k j hj S hS).trans
    (functorHomotopySourceEndpointIso_heq_component c p (fst (leftUnstraightening F) K) rfl
      (coherentColimitUnitPointedFixedFaceHomotopyWitness B T k j hj S hS false))

end SerrePositivity.InfinityCategories.F2
