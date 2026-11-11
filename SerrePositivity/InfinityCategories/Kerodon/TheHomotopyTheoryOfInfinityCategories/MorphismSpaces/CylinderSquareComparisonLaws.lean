module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CylinderEquivalenceSquareInverse

/-!
概要：円柱の順比較と逆比較が全空間・底・端点で元の族を回収する法則。
方針：引き戻しとパラメーター付き円柱の普遍性を順に使う。
規約：全高次単体についての厳密な往復を検査する。
使われ方：実際の四角形空間と prism 中間模型の同型。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：順比較の後に prism を回収すると元の全 lift の射。
方針：curry とパラメーターの二射影で比較する。
規約：prism 全体と底を厳密に回収する。
使われ方：中間模型からの往復の一意性。 -/
lemma pointedCylinderFixedSquareMap_lift {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareLift f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismLift f s t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.prismLiftSpace_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismData K s t)
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareLift_curry, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_pointed, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap_inl]
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareLift f s t) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismLift f s t ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareLift_parameters]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismLift f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSource K s t
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_source, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismLift_source]
    · simp only [Category.assoc, lift_snd]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_interval f s t

/-- 概要：逆比較は回収した終点の族を保持する。
方針：両端射影の回収式の第二成分を取る。
規約：終点の同値の包含後の厳密な回収。
使われ方：逆比較の後の円柱の終点部分の確認。 -/
lemma cylinderEquivalenceSquareInverse_target {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismTarget f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareForget f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareTarget f s t := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpoints f s t) ≫
    snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι J t = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse_endpoints]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareForget_target f s t).symm

/-- 概要：逆比較は元の底の区間の族を保持する。
方針：普遍 lift のパラメーター射影の第二成分を回収する。
規約：底の射の厳密な回収。
使われ方：逆比較の後の四角形の底の確認。 -/
lemma cylinderEquivalenceSquareInverse_interval {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderInterval f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareForget f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareInterval f s t := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismLift f s t) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t ≫ snd _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse_lift, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareLift f s t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t) (snd _ _),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareLift_parameters, lift_snd]

/-- 概要：逆比較の後に円柱上へ貼り直すと元の全空間の族。
方針：prism と終点の二部分で比較する。
規約：パラメーター付き pushout 全体での射の等式。
使われ方：実際の四角形への往復の一意性。 -/
lemma cylinderEquivalenceSquareInverse_pointed {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareForget f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquarePointed f s t := by
  apply uncurry_injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.parametrizedCylinder_hom_ext f
  · rw [← uncurry_pre_app, ← uncurry_pre_app]
    congr 1
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap_inl, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse_lift, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareLift_curry,
      Category.assoc]
  · rw [← uncurry_pre_app, ← uncurry_pre_app]
    congr 1
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPointedMap_inr, ← Category.assoc,
      cylinderEquivalenceSquareInverse_target, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareTarget_ι,
      Category.assoc]

/-- 概要：逆比較の後に周囲の四角形へ進むと元の四角形。
方針：全空間の族と底の区間の二射影を比較する。
規約：両方を同時に厳密に保持する。
使われ方：両端同値の四角形への往復の第一成分。 -/
lemma cylinderEquivalenceSquareInverse_fixedSquare {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareInverse f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderEquivalenceSquareForget f s t := by
  apply pullback.hom_ext
  · change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquarePointed f s t = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_pointed]
    exact cylinderEquivalenceSquareInverse_pointed f s t
  · change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareInterval f s t = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_interval]
    exact cylinderEquivalenceSquareInverse_interval f s t

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
