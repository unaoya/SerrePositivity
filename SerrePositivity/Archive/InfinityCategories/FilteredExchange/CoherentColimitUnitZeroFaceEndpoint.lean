module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceOriginalTarget

/-!
概要：元の第零面の全終点を、元の標的の全空間へ厳密な底付きで戻す。
方針：元の指定三角形の native 合成の終点式で共通の底を同定し、引き戻しへ入れる。
規約：元の実終点を保持。使われ方：第零面の指定全族比較を native 合成比較へ移す。
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
local notation "j₂" => simplexPrismVertex 2 2 (leftUnstraightening F) ▷ K

include he hS in
/-- 第零面の共通の底の終点は、元の全パラメータの射影の後の同じ標的図式。 -/
lemma coherentColimitUnitZeroFaceBase_endpoint :
    j₂ ≫ ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫ (D).diagram =
      (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) ≫ Q₂ := by
  calc
    _ = (j₂ ≫ coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S) ≫
        pointedSpaceProjection := by
      rw [Category.assoc,
        coherentColimitUnitZeroFaceOriginalTriangleLift_projection B T k H he S hS]
    _ = (coherentColimitUnitZeroFaceOriginalTargetMap B T k H he S ≫
        pullback.fst pointedSpaceProjection Q₂) ≫ pointedSpaceProjection :=
      congrArg (fun z => z ≫ pointedSpaceProjection)
        (coherentColimitUnitZeroFaceOriginalTriangleLift_target B T k H he S)
    _ = _ := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun z => z ≫ Q₂)
        (coherentColimitUnitZeroFaceOriginalTargetMap_projection B T k H he S)

/-- 元の第零面の全実終点を、同じ元の標的の全空間へ戻す。 -/
def coherentColimitUnitZeroFaceEndpoint : leftUnstraightening F ⊗ K ⟶ leftUnstraightening Q₂ :=
  pullback.lift (j₂ ≫ coherentColimitUnitPointedZeroFaceLift B T k)
    (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) (by
      rw [Category.assoc, coherentColimitUnitPointedZeroFaceLift_projection]
      exact coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS)

/-- 元の実終点の底は、元の全パラメータの射影そのもの。 -/
lemma coherentColimitUnitZeroFaceEndpoint_projection :
    coherentColimitUnitZeroFaceEndpoint B T k H he S hS ≫ leftUnstraighteningProjection Q₂ =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F :=
  pullback.lift_snd _ _ _

/-- 元の実終点の pointed 成分は、元の同じ第零面の全終点制限そのもの。 -/
lemma coherentColimitUnitZeroFaceEndpoint_pointed :
    j₂ ≫ coherentColimitUnitPointedZeroFaceLift B T k =
      coherentColimitUnitZeroFaceEndpoint B T k H he S hS ≫
        pullback.fst pointedSpaceProjection Q₂ :=
  (pullback.lift_fst _ _ _).symm

/-- 同じ実終点は、元の全三単体の同じ最終頂点を全選択で制限したもの。 -/
lemma coherentColimitUnitZeroFaceEndpoint_pointed_tetrahedron :
    (simplexPrismVertex 3 3 (leftUnstraightening F) ▷ K) ≫
      coherentColimitUnitPointedTetrahedronUniversalLift B T k =
    coherentColimitUnitZeroFaceEndpoint B T k H he S hS ≫
      pullback.fst pointedSpaceProjection Q₂ := by
  have ht : simplexPrismVertex 2 2 (leftUnstraightening F) ≫
      (stdSimplex.δ (0 : Fin 4) ▷ leftUnstraightening F) =
        simplexPrismVertex 3 3 (leftUnstraightening F) := rfl
  rw [← ht, comp_whiskerRight, Category.assoc]
  exact coherentColimitUnitZeroFaceEndpoint_pointed B T k H he S hS

end SerrePositivity.InfinityCategories.F2
