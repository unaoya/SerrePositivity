module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CylinderSquareEndpoints

/-!
概要：実際の円柱上の四角形から全 prism lift 空間へ戻す。
方針：円柱部分に制限した族を普遍 lift 空間へ戻す。
規約：始点の fiber 写像と底の区間の族を厳密に保つ。
使われ方：円柱の中間空間との逆比較の第一段階。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：四角形の円柱部分を実際の prism の族として回収する。
方針：pushout の第一包含へ制限して結合子の逆を使う。
規約：区間、係数、パラメーターの順。
使われ方：普遍 lift 空間へ戻す prism の族。 -/
def cylinderFixedEndpointSquarePrism {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    Δ[1] ⊗ (K ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSpace f s t) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  (α_ Δ[1] K _).inv ≫ (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ _) ≫
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquarePointed f s t)

/-- 概要：回収した prism の始点は回収した始点の fiber 写像の評価。
方針：始点の包含の定義と fiber 包含後の端点公式を使う。
規約：始点の族を厳密に保つ。
使われ方：普遍 lift 空間の初期値の条件。 -/
lemma cylinderFixedEndpointSquarePrism_zero {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ cylinderFixedEndpointSquarePrism f s t =
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s := by
  have h := congrArg uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource_ι f s t)
  rw [uncurry_natural_right, uncurry_pre_app] at h
  exact h.symm

/-- 概要：回収した prism の底は元の四角形の区間の族。
方針：四角形の底の等式を円柱部分に制限する。
規約：元の区間の高次パラメーターを保つ。
使われ方：普遍 lift 空間の底の条件。 -/
lemma cylinderFixedEndpointSquarePrism_base {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquarePrism f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (Δ[1] ◁ snd K _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareInterval f s t) := by
  dsimp only [cylinderFixedEndpointSquarePrism]
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquare_base,
    ← Category.assoc (pushout.inl _ _ ▷ _), ← comp_whiskerRight,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderIntervalProjection_inl]
  rfl

/-- 概要：四角形から全 prism lift 空間へ戻す実際の射。
方針：回収した始点と区間をパラメーターとし、普遍性を適用する。
規約：元の prism と区間の族を厳密に保持する。
使われ方：同値な両端を指定した中間空間への逆比較。 -/
def cylinderFixedEndpointSquareLift {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSpace f s t ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSpace K s t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.prismLiftSpaceLift _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismInitial K s t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismBase K s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismInitial_base K s t)
    (lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareInterval f s t))
    (cylinderFixedEndpointSquarePrism f s t)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismInitial_precomp, lift_fst];
        exact cylinderFixedEndpointSquarePrism_zero f s t)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismBase_precomp, lift_snd];
        exact cylinderFixedEndpointSquarePrism_base f s t)

/-- 概要：逆比較の lift は始点の fiber 写像と区間を回収する。
方針：全 lift 空間の普遍性の射影公式。
規約：二つのパラメーターを同時に保つ。
使われ方：逆比較の底変換の条件。 -/
lemma cylinderFixedEndpointSquareLift_parameters {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareLift f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareInterval f s t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.prismLiftSpaceLift_projection _ _ _ _ _ _ _ _

/-- 概要：逆比較の lift は元の四角形の円柱部分を回収する。
方針：普遍性の curry の公式と前合成の評価を使う。
規約：prism 全体の回収。
使われ方：逆比較と順比較の往復の一意性。 -/
lemma cylinderFixedEndpointSquareLift_curry {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareLift f s t ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismData K s t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquarePointed f s t ≫
        (pre (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f)).app _ := by
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.prismLiftSpaceLift_curry _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismInitial K s t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismBase K s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismInitial_base K s t)
    (lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareInterval f s t))
    (cylinderFixedEndpointSquarePrism f s t)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismInitial_precomp, lift_fst];
        exact cylinderFixedEndpointSquarePrism_zero f s t)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismBase_precomp, lift_snd];
        exact cylinderFixedEndpointSquarePrism_base f s t)).trans ?_
  apply uncurry_injective
  rw [uncurry_curry, uncurry_pre_app]
  dsimp only [cylinderFixedEndpointSquarePrism]
  rw [Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
