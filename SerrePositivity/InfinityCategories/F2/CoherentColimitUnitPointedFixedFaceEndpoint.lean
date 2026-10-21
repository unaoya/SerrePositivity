module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFixedFaceTarget

/-!
概要：固定始点を持つ元の二面と、元の指定三角形の実持ち上げを比較する。
方針：同じ全初期値の選択空間へ元の二頂点を入れ、長辺へ制限する。
規約：同じ全空間と同じ始点を保持。使われ方：共有面の指定比較を同じ空間で消去。
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
local notation "P" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "h₀" => coherentColimitUnitPointedFace_initial B T k j hj S.diagram hS

local notation "last" => simplexPrismVertex 2 2 (leftUnstraightening F) ▷ P

/-- 元の実二面の全終点を、元の標的図式の同じ全空間へ戻す。 -/
def coherentColimitUnitPointedFixedFaceEndpoint :
    leftUnstraightening F ⊗ P ⟶ leftUnstraightening Q₂ :=
  pullback.lift (last ≫ coherentColimitUnitPointedFixedFaceLift B T k j)
    (fst (leftUnstraightening F) P ≫ leftUnstraighteningProjection F) (by
      rw [Category.assoc, coherentColimitUnitPointedFixedFaceLift_projection B T k j hj S hS]
      exact coherentColimitUnitPointedFixedFaceBase_endpoint B T k j hj S hS)

/-- 元の実終点は、元の全選択パラメータの底を保持する。 -/
lemma coherentColimitUnitPointedFixedFaceEndpoint_projection :
    coherentColimitUnitPointedFixedFaceEndpoint B T k j hj S hS ≫
      leftUnstraighteningProjection Q₂ =
        fst (leftUnstraightening F) P ≫ leftUnstraighteningProjection F :=
  pullback.lift_snd _ _ _

/-- 元の実終点の pointed 成分は、元の同じ二面の実際の最終頂点。 -/
lemma coherentColimitUnitPointedFixedFaceEndpoint_pointed :
    last ≫ coherentColimitUnitPointedFixedFaceLift B T k j =
      coherentColimitUnitPointedFixedFaceEndpoint B T k j hj S hS ≫
        pullback.fst pointedSpaceProjection Q₂ :=
  (pullback.lift_fst _ _ _).symm

end SerrePositivity.InfinityCategories.F2
