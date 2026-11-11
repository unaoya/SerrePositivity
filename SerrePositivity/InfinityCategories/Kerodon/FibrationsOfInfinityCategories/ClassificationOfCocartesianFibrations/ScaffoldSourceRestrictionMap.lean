module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.GlobalHomCellRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldGlobalPullbackMaps

/-!
概要：元の全 Hom を同じ最初の辺と尾部の元の全局所 Hom の pullback へ厳密に制限する。
方針：底変換の共有セルへの直接制限則で二脚を同じ共有頂点に貼り合わせる。
規約：元の全相対 Hom を保ち、分類比較や補正成分を制限の定義に入れない。
使われ方：補正比較の source Segal 射による因数分解。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalSource n k p q

/-- 最初の辺の元の Hom の制限は、同じ共有頂点への直接制限に一致。 -/
lemma cocartesianScaffoldSourceRestriction_first_shared :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k) p q ≫
      (S).map WalkingCospan.Hom.inl =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k) p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction_cellOver
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k) rfl p q

/-- 次の辺の元の Hom の制限も、同じ共有頂点への直接制限に一致。 -/
lemma cocartesianScaffoldSourceRestriction_second_shared :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) p q ≫
      (S).map WalkingCospan.Hom.inr =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k) p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction_cellOver
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteZeroVertex n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell_tail n k) p q

/-- 元の全 Hom から、同じ最初の辺と尾部の元の全局所 Hom の厳密な pullback への制限。 -/
def cocartesianScaffoldSourceRestrictionMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k) p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) p q)
    ((cocartesianScaffoldSourceRestriction_first_shared n k p q).trans
      (cocartesianScaffoldSourceRestriction_second_shared n k p q).symm)

/-- 同じ source 制限の最初の射影は元の最初の底変換。 -/
lemma cocartesianScaffoldSourceRestrictionMap_fst :
    cocartesianScaffoldSourceRestrictionMap n k p q ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k) p q :=
  pullback.lift_fst _ _ _

/-- 同じ source 制限の次の射影は元の次の底変換。 -/
lemma cocartesianScaffoldSourceRestrictionMap_snd :
    cocartesianScaffoldSourceRestrictionMap n k p q ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSingleBaseChangeHomAction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) p q :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
