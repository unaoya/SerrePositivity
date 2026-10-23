module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CylinderSquareRecoveredEndpoints

/-!
概要：円柱の中間模型から四角形への順比較は両端の fiber 写像を保つ。
方針：包含後の始点と終点を比較し、fiber の一意性で戻す。
規約：両端の同値を類まで弱めず厳密に保つ。
使われ方：同値な両端を持つ部分空間への順比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fiber 値の関手の族は包含後の射で一意に決まる。
方針：uncurry と fiber の包含の一意性を使う。
規約：任意のパラメーターと係数で成立する。
使われ方：両端の fiber 写像の厳密な比較。 -/
lemma functorVertexFiber_hom_ext {A L E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {F G : L ⟶ (ihom A).obj (vertexFiber p b)}
    (h : F ≫ (ihom A).map (vertexFiberι p b) = G ≫ (ihom A).map (vertexFiberι p b)) : F = G := by
  apply uncurry_injective
  apply vertexFiber_hom_ext p b
  simpa only [uncurry_natural_right] using congrArg uncurry h

/-- 概要：貼った全空間の族の始点は指定した始点 fiber の族。
方針：prism の始点への制限と貼り合わせの回収式を使う。
規約：包含後の射の厳密な等式。
使われ方：順比較の始点条件。 -/
lemma pointedCylinderPointedMap_source_ι {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPointedMap f s t ≫ (pre (cylinderSquareSourceInclusion f)).app _ =
      pointedCylinderPrismSource f s t ≫ (ihom K).map (vertexFiberι pointedSpaceProjection s) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_right]
  change (cylinderSquareSourceInclusion f ▷ _) ≫ uncurry (curry (pointedCylinderFamily f s t)) = _
  rw [uncurry_curry]
  have h : (pushout.inl (prismEndpoint 1 K) f ▷ pointedCylinderPrismSpace f s t) ≫
      pointedCylinderFamily f s t = pointedCylinderPrismEvaluation f s t :=
    parametrizedCylinderDesc_inl _ _ _ _
  rw [cylinderSquareSourceInclusion, comp_whiskerRight, Category.assoc, h]
  exact pointedCylinderPrismEvaluation_zero f s t

/-- 概要：順比較で回収した始点は元の始点同値の族。
方針：包含後の始点評価で比較する。
規約：fiber 値の写像自体の等式。
使われ方：始点同値の部分空間への持ち上げ。 -/
lemma pointedCylinderFixedSquareMap_source {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderFixedSquareMap f s t ≫ cylinderFixedEndpointSquareSource f s t =
      pointedCylinderPrismSource f s t := by
  apply functorVertexFiber_hom_ext pointedSpaceProjection s
  rw [Category.assoc, cylinderFixedEndpointSquareSource_ι, ← Category.assoc,
    pointedCylinderFixedSquareMap_pointed]
  exact pointedCylinderPointedMap_source_ι f s t

/-- 概要：順比較で回収した終点は元の終点同値の族。
方針：包含後の終点評価で比較する。
規約：fiber 値の写像自体の等式。
使われ方：終点同値の部分空間への持ち上げ。 -/
lemma pointedCylinderFixedSquareMap_target {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderFixedSquareMap f s t ≫ cylinderFixedEndpointSquareTarget f s t =
      pointedCylinderPrismTarget f s t := by
  apply functorVertexFiber_hom_ext pointedSpaceProjection t
  rw [Category.assoc, cylinderFixedEndpointSquareTarget_ι, ← Category.assoc,
    pointedCylinderFixedSquareMap_pointed]
  exact pointedCylinderPointedMap_inr f s t

end SerrePositivity.InfinityCategories
