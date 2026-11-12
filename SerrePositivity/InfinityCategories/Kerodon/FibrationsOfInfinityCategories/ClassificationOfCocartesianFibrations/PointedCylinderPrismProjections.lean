module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ParametrizedCylinderGluing

/-!
概要：円柱の prism 中間空間の普遍 lift と両端の関手の射影。
方針：二つの引き戻しの条件を合成して同時端点の式を回収する。
規約：族全体について射そのものの等式を証明する。
使われ方：円柱上の実際の関手の族を作る厳密な貼り合わせ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：円柱の中間空間から元の全 prism lift 空間への射。
方針：二つの引き戻しの第一射影を合成する。
規約：区間と全ての高次 lift を保持する。
使われ方：普遍 prism の評価。 -/
def pointedCylinderPrismLift {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSpace K s t :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- 概要：円柱の中間空間から始点 fiber への関手の族。
方針：両端射影の始点同値の包含を取る。
規約：高次パラメーターごとの同値をまとめた射。
使われ方：円柱の始点での評価の確認。 -/
def pointedCylinderPrismSource {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpoints f s t ≫ fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι K s

/-- 概要：円柱の中間空間から終点 fiber への関手の族。
方針：両端射影の終点同値の包含を取る。
規約：係数は K でなく円柱の終点 J。
使われ方：prism の終点を貼る相手の射。 -/
def pointedCylinderPrismTarget {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t ⟶ (ihom J).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpoints f s t ≫ snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι J t

/-- 概要：普遍 lift の同時端点は円柱の両端データで指定されたものと一致する。
方針：二つの引き戻し条件を順に合成する。
規約：始点と終点の族全体の等式。
使われ方：円柱の貼り合わせの二つの端点公式。 -/
lemma pointedCylinderPrismLift_endpoints {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismLift f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoints K s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpoints f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpointData f s t ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι K s ▷
          ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t))) := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismEquivalenceEndpoints K s t) ≫ _ = _
  rw [pullback.condition, Category.assoc]
  rfl

/-- 概要：普遍 lift の始点は指定した始点同値の族。
方針：同時端点の等式を第一射影で評価する。
規約：厳密な射の等式。
使われ方：円柱上の族の始点条件。 -/
lemma pointedCylinderPrismLift_source {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismLift f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSource K s t =
      pointedCylinderPrismSource f s t := by
  have h := congrArg (fun w ↦ w ≫ fst _ _) (pointedCylinderPrismLift_endpoints f s t)
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoints, lift_fst,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpointData, tensorHom_fst, tensorHom_fst_assoc, whiskerRight_fst,
    Category.comp_id,
    Category.id_comp,
    pointedCylinderPrismSource] using h

/-- 概要：普遍 lift の終点は指定した終点同値の前合成。
方針：同時端点の等式を第二射影で評価する。
規約：貼り付け射 f に沿う厳密な前合成。
使われ方：prism と終点の族を貼り合わせる条件。 -/
lemma pointedCylinderPrismLift_endpoint {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismLift f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoint K s t =
      pointedCylinderPrismTarget f s t ≫ (pre f).app _ := by
  have h := congrArg (fun w ↦ w ≫ snd _ _) (pointedCylinderPrismLift_endpoints f s t)
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoints, lift_snd,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpointData, tensorHom_snd, whiskerRight_snd,
    pointedCylinderPrismTarget] using h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
