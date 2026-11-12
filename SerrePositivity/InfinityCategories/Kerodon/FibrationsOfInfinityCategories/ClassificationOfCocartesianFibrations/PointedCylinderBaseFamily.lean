module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedCylinderFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderIntervalExtension

/-!
概要：円柱の中間空間の区間の分類図式と prism の底の等式。
方針：元の全 lift 空間の区間パラメーターを回収して展開する。
規約：始点と終点は指定した s,t に厳密に固定する。
使われ方：貼り合わせた円柱の族が同じ底の族を覆うことの証明。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：円柱の中間空間の底の区間パラメーター。
方針：元の lift 空間の射影から区間成分を取る。
規約：係数の射影は忘れる。
使われ方：円柱上の表現の分類図式の族。 -/
def pointedCylinderInterval {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismLift f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t ≫ snd _ _

/-- 概要：円柱の中間空間の区間からの分類図式の族。
方針：両端固定の区間の族を展開して curry する。
規約：底の図式の全高次パラメーターを保持する。
使われ方：transport square の底側の成分。 -/
def pointedCylinderDiagram {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (pointedCylinderInterval f s t))

/-- 概要：prism の評価の底は底の区間の族を係数を忘れて評価したもの。
方針：全 lift の底の公式を引き戻し、区間の展開の自然性を使う。
規約：区間と係数を第一因子にまとめる。
使われ方：円柱部分での可換四角形の確認。 -/
lemma pointedCylinderPrismEvaluation_base {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEvaluation f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (fst (Δ[1] : SSet.{u + 1}) K ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (pointedCylinderInterval f s t) := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismLift f s t
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpacePrism _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismData K s t)
  have hb : H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = (Δ[1] ◁ snd K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSpace K s t)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t ≫ snd _ _) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismEvaluation_base K s t
  calc
    _ = (α_ Δ[1] K _).hom ≫ (Δ[1] ◁ (K ◁ P)) ≫ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection := by
      dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEvaluation]
      rw [uncurry_natural_left]
      rfl
    _ = (α_ Δ[1] K _).hom ≫ (Δ[1] ◁ (K ◁ P)) ≫
        (Δ[1] ◁ snd K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSpace K s t)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftParameters K s t ≫ snd _ _) := by rw [hb]
    _ = _ := by
      dsimp only [pointedCylinderInterval]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
