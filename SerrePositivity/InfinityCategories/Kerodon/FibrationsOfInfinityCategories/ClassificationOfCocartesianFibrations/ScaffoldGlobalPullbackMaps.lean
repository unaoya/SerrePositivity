module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldCorrectedSharedComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldStrictPullback

/-!
概要：元の全 Hom から補正比較と元の分類作用による同じ二区間の pullback への二射。
方針：既存の二つの指定成分の始点・終点を同じ共有頂点の可換式で貼り合わせる。
規約：元の全相対 Hom と既存の補正成分・分類 Hom 作用を保持する。
使われ方：元の分類 Hom 作用と補正 pullback 比較の実際の関手同型。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalTarget n k p q

/-- 元の全 Hom から、同じ二つの補正成分で同じ標的 pullback へ進む射。 -/
def cocartesianScaffoldCorrectedGlobalPullbackMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedFirstGlobalIso n k p q).sourceMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedSecondGlobalIso n k p q).sourceMap
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedFirstGlobalIso_shared_source n k p q).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedSecondGlobalIso_shared_source n k p q).symm)

/-- 元の分類 Hom 作用の最初の辺と尾部への制限を同じ標的 pullback へ束ねた射。 -/
def cocartesianScaffoldOriginalGlobalPullbackMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedFirstGlobalIso n k p q).targetMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedSecondGlobalIso n k p q).targetMap
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedFirstGlobalIso_shared_target n k p q).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedSecondGlobalIso_shared_target n k p q).symm)

/-- 補正比較の最初の射影は元の最初の補正成分。 -/
lemma cocartesianScaffoldCorrectedGlobalPullbackMap_fst :
    cocartesianScaffoldCorrectedGlobalPullbackMap n k p q ≫ pullback.fst _ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedFirstGlobalIso n k p q).sourceMap :=
  pullback.lift_fst _ _ _

/-- 補正比較の次の射影は元の次の補正成分。 -/
lemma cocartesianScaffoldCorrectedGlobalPullbackMap_snd :
    cocartesianScaffoldCorrectedGlobalPullbackMap n k p q ≫ pullback.snd _ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedSecondGlobalIso n k p q).sourceMap :=
  pullback.lift_snd _ _ _

/-- 元の分類作用の最初の射影は、同じ作用の最初の辺への制限。 -/
lemma cocartesianScaffoldOriginalGlobalPullbackMap_fst :
    cocartesianScaffoldOriginalGlobalPullbackMap n k p q ≫ pullback.fst _ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedFirstGlobalIso n k p q).targetMap :=
  pullback.lift_fst _ _ _

/-- 元の分類作用の次の射影は、同じ作用の次の辺への制限。 -/
lemma cocartesianScaffoldOriginalGlobalPullbackMap_snd :
    cocartesianScaffoldOriginalGlobalPullbackMap n k p q ≫ pullback.snd _ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedSecondGlobalIso n k p q).targetMap :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
