module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CylinderEquivalenceSquareInverse

/-!
概要：円柱の順比較と逆比較が全空間・底・端点で元の族を回収する法則。
方針：引き戻しとパラメーター付き円柱の普遍性を順に使う。
規約：全高次単体についての厳密な往復を検査する。
使われ方：実際の四角形空間と prism 中間模型の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：順比較の後に prism を回収すると元の全 lift の射。
方針：curry とパラメーターの二射影で比較する。
規約：prism 全体と底を厳密に回収する。
使われ方：中間模型からの往復の一意性。 -/
lemma pointedCylinderFixedSquareMap_lift {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderFixedSquareMap f s t ≫ cylinderFixedEndpointSquareLift f s t =
      pointedCylinderPrismLift f s t := by
  apply prismLiftSpace_hom_ext pointedSpaceProjection (pointedPrismData K s t)
  · rw [Category.assoc, cylinderFixedEndpointSquareLift_curry, ← Category.assoc,
      pointedCylinderFixedSquareMap_pointed, pointedCylinderPointedMap_inl]
  · change (pointedCylinderFixedSquareMap f s t ≫ cylinderFixedEndpointSquareLift f s t) ≫
      pointedPrismLiftParameters K s t = pointedCylinderPrismLift f s t ≫
        pointedPrismLiftParameters K s t
    rw [Category.assoc, cylinderFixedEndpointSquareLift_parameters]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      change _ = pointedCylinderPrismLift f s t ≫ pointedPrismLiftSource K s t
      rw [pointedCylinderFixedSquareMap_source, pointedCylinderPrismLift_source]
    · simp only [Category.assoc, lift_snd]
      exact pointedCylinderFixedSquareMap_interval f s t

/-- 概要：逆比較は回収した終点の族を保持する。
方針：両端射影の回収式の第二成分を取る。
規約：終点の同値の包含後の厳密な回収。
使われ方：逆比較の後の円柱の終点部分の確認。 -/
lemma cylinderEquivalenceSquareInverse_target {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderEquivalenceSquareInverse f s t ≫ pointedCylinderPrismTarget f s t =
      cylinderEquivalenceSquareForget f s t ≫ cylinderFixedEndpointSquareTarget f s t := by
  change (cylinderEquivalenceSquareInverse f s t ≫ pointedCylinderPrismEndpoints f s t) ≫
    snd _ _ ≫ pointedPrismSourceEquivalenceι J t = _
  rw [cylinderEquivalenceSquareInverse_endpoints]
  exact (cylinderEquivalenceSquareForget_target f s t).symm

/-- 概要：逆比較は元の底の区間の族を保持する。
方針：普遍 lift のパラメーター射影の第二成分を回収する。
規約：底の射の厳密な回収。
使われ方：逆比較の後の四角形の底の確認。 -/
lemma cylinderEquivalenceSquareInverse_interval {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderEquivalenceSquareInverse f s t ≫ pointedCylinderInterval f s t =
      cylinderEquivalenceSquareForget f s t ≫ cylinderFixedEndpointSquareInterval f s t := by
  change (cylinderEquivalenceSquareInverse f s t ≫ pointedCylinderPrismLift f s t) ≫
    pointedPrismLiftParameters K s t ≫ snd _ _ = _
  rw [cylinderEquivalenceSquareInverse_lift, Category.assoc,
    ← Category.assoc (cylinderFixedEndpointSquareLift f s t)
      (pointedPrismLiftParameters K s t) (snd _ _),
    cylinderFixedEndpointSquareLift_parameters, lift_snd]

/-- 概要：逆比較の後に円柱上へ貼り直すと元の全空間の族。
方針：prism と終点の二部分で比較する。
規約：パラメーター付き pushout 全体での射の等式。
使われ方：実際の四角形への往復の一意性。 -/
lemma cylinderEquivalenceSquareInverse_pointed {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderEquivalenceSquareInverse f s t ≫ pointedCylinderPointedMap f s t =
      cylinderEquivalenceSquareForget f s t ≫ cylinderFixedEndpointSquarePointed f s t := by
  apply uncurry_injective
  apply parametrizedCylinder_hom_ext f
  · rw [← uncurry_pre_app, ← uncurry_pre_app]
    congr 1
    rw [Category.assoc, pointedCylinderPointedMap_inl, ← Category.assoc,
      cylinderEquivalenceSquareInverse_lift, Category.assoc, cylinderFixedEndpointSquareLift_curry,
      Category.assoc]
  · rw [← uncurry_pre_app, ← uncurry_pre_app]
    congr 1
    rw [Category.assoc, pointedCylinderPointedMap_inr, ← Category.assoc,
      cylinderEquivalenceSquareInverse_target, Category.assoc, cylinderFixedEndpointSquareTarget_ι,
      Category.assoc]

/-- 概要：逆比較の後に周囲の四角形へ進むと元の四角形。
方針：全空間の族と底の区間の二射影を比較する。
規約：両方を同時に厳密に保持する。
使われ方：両端同値の四角形への往復の第一成分。 -/
lemma cylinderEquivalenceSquareInverse_fixedSquare {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderEquivalenceSquareInverse f s t ≫ pointedCylinderFixedSquareMap f s t =
      cylinderEquivalenceSquareForget f s t := by
  apply pullback.hom_ext
  · change _ ≫ cylinderFixedEndpointSquarePointed f s t = _
    rw [Category.assoc, pointedCylinderFixedSquareMap_pointed]
    exact cylinderEquivalenceSquareInverse_pointed f s t
  · change _ ≫ cylinderFixedEndpointSquareInterval f s t = _
    rw [Category.assoc, pointedCylinderFixedSquareMap_interval]
    exact cylinderEquivalenceSquareInverse_interval f s t

end SerrePositivity.InfinityCategories
