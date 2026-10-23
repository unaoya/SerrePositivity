module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CylinderSquareEndpoints

/-!
概要：実際の円柱上の四角形から全 prism lift 空間へ戻す。
方針：円柱部分に制限した族を普遍 lift 空間へ戻す。
規約：始点の fiber 写像と底の区間の族を厳密に保つ。
使われ方：円柱の中間空間との逆比較の第一段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：四角形の円柱部分を実際の prism の族として回収する。
方針：pushout の第一包含へ制限して結合子の逆を使う。
規約：区間、係数、パラメーターの順。
使われ方：普遍 lift 空間へ戻す prism の族。 -/
def cylinderFixedEndpointSquarePrism {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    Δ[1] ⊗ (K ⊗ cylinderFixedEndpointSquareSpace f s t) ⟶ PointedSpaceInfinity.{u} :=
  (α_ Δ[1] K _).inv ≫ (pushout.inl (prismEndpoint 1 K) f ▷ _) ≫
    uncurry (cylinderFixedEndpointSquarePointed f s t)

/-- 概要：回収した prism の始点は回収した始点の fiber 写像の評価。
方針：始点の包含の定義と fiber 包含後の端点公式を使う。
規約：始点の族を厳密に保つ。
使われ方：普遍 lift 空間の初期値の条件。 -/
lemma cylinderFixedEndpointSquarePrism_zero {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    prismEndpoint 0 _ ≫ cylinderFixedEndpointSquarePrism f s t =
      uncurry (cylinderFixedEndpointSquareSource f s t) ≫
        vertexFiberι pointedSpaceProjection s := by
  have h := congrArg uncurry (cylinderFixedEndpointSquareSource_ι f s t)
  rw [uncurry_natural_right, uncurry_pre_app] at h
  exact h.symm

/-- 概要：回収した prism の底は元の四角形の区間の族。
方針：四角形の底の等式を円柱部分に制限する。
規約：元の区間の高次パラメーターを保つ。
使われ方：普遍 lift 空間の底の条件。 -/
lemma cylinderFixedEndpointSquarePrism_base {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquarePrism f s t ≫ pointedSpaceProjection =
      (Δ[1] ◁ snd K _) ≫ intervalMappingUncurry (cylinderFixedEndpointSquareInterval f s t) := by
  dsimp only [cylinderFixedEndpointSquarePrism]
  rw [Category.assoc, Category.assoc, cylinderFixedEndpointSquare_base,
    ← Category.assoc (pushout.inl _ _ ▷ _), ← comp_whiskerRight,
    mappingCylinderIntervalProjection_inl]
  rfl

/-- 概要：四角形から全 prism lift 空間へ戻す実際の射。
方針：回収した始点と区間をパラメーターとし、普遍性を適用する。
規約：元の prism と区間の族を厳密に保持する。
使われ方：同値な両端を指定した中間空間への逆比較。 -/
def cylinderFixedEndpointSquareLift {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareSpace f s t ⟶ pointedPrismLiftSpace K s t :=
  prismLiftSpaceLift pointedSpaceProjection (pointedPrismInitial K s t)
    (pointedPrismBase K s t) (pointedPrismInitial_base K s t)
    (lift (cylinderFixedEndpointSquareSource f s t) (cylinderFixedEndpointSquareInterval f s t))
    (cylinderFixedEndpointSquarePrism f s t)
    (by rw [pointedPrismInitial_precomp, lift_fst];
        exact cylinderFixedEndpointSquarePrism_zero f s t)
    (by rw [pointedPrismBase_precomp, lift_snd];
        exact cylinderFixedEndpointSquarePrism_base f s t)

/-- 概要：逆比較の lift は始点の fiber 写像と区間を回収する。
方針：全 lift 空間の普遍性の射影公式。
規約：二つのパラメーターを同時に保つ。
使われ方：逆比較の底変換の条件。 -/
lemma cylinderFixedEndpointSquareLift_parameters {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareLift f s t ≫ pointedPrismLiftParameters K s t =
      lift (cylinderFixedEndpointSquareSource f s t) (cylinderFixedEndpointSquareInterval f s t) :=
  prismLiftSpaceLift_projection _ _ _ _ _ _ _ _

/-- 概要：逆比較の lift は元の四角形の円柱部分を回収する。
方針：普遍性の curry の公式と前合成の評価を使う。
規約：prism 全体の回収。
使われ方：逆比較と順比較の往復の一意性。 -/
lemma cylinderFixedEndpointSquareLift_curry {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareLift f s t ≫
        prismLiftSpaceCurry pointedSpaceProjection K (pointedPrismData K s t) =
      cylinderFixedEndpointSquarePointed f s t ≫
        (pre (pushout.inl (prismEndpoint 1 K) f)).app _ := by
  refine (prismLiftSpaceLift_curry pointedSpaceProjection (pointedPrismInitial K s t)
    (pointedPrismBase K s t) (pointedPrismInitial_base K s t)
    (lift (cylinderFixedEndpointSquareSource f s t) (cylinderFixedEndpointSquareInterval f s t))
    (cylinderFixedEndpointSquarePrism f s t)
    (by rw [pointedPrismInitial_precomp, lift_fst];
        exact cylinderFixedEndpointSquarePrism_zero f s t)
    (by rw [pointedPrismBase_precomp, lift_snd];
        exact cylinderFixedEndpointSquarePrism_base f s t)).trans ?_
  apply uncurry_injective
  rw [uncurry_curry, uncurry_pre_app]
  dsimp only [cylinderFixedEndpointSquarePrism]
  rw [Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories
