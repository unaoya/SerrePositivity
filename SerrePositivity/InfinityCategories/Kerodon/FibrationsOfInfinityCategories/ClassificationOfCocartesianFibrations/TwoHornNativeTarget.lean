module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.AnodyneHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiniteHornOver
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerTwoHornImageCoreRestriction

/-!
概要：欠損長辺を持つ実際の二次内ホーン上でも、元の native Hom を実際の target と比較する。
方針：三角形で辺保存を反映した同じ自明 Kan 制限の逆に、元の二単体の作用を合成する。
規約：全辺被覆を仮定せず、同じ元の作用との関手同型を保持する。
使われ方：二次元境界の内ホーンと残りの面による帰納の入力。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver 2 1
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom

local instance : InnerFibration (pullback.fst (A).hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst (A).hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

/-- 欠ける長辺の保存を三角形で反映する、同じ native 制限の同値。 -/
lemma cocartesianTwoHornNativeLiftRestriction_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom A) := by
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p.val.hom q.val.hom A)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.core_cocartesianPullbackNativeRestriction_innerTwoHornImage_trivialKanFibration
      (stdSimplex.isoNerve.{u} 2) p.val.hom q.val.hom
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan _).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _)

/-- 以降で共有する、元の二次内ホーン制限そのものを順方向とする同値。 -/
def cocartesianTwoHornNativeLiftRestrictionEquivalence :=
  (cocartesianTwoHornNativeLiftRestriction_isQCatEquivalence p q).choose

/-- 実際の二次内ホーン上の native Hom から、元の分類先の区間 Hom への比較。 -/
def cocartesianTwoHornNativeTargetComparison :=
  (cocartesianTwoHornNativeLiftRestrictionEquivalence p q).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (A).hom) P Q

/-- 二次内ホーンの同じ比較を、元の二単体上の同じ全 Hom 作用へ戻す指定同型。 -/
def cocartesianTwoHornNativeTargetComparison_originalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom A ≫
        cocartesianTwoHornNativeTargetComparison p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (A).hom) P Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((cocartesianTwoHornNativeLiftRestrictionEquivalence p q).homInvIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (A).hom) P Q))
    (by simp only [cocartesianTwoHornNativeTargetComparison, Category.assoc]; rfl)
    (Category.id_comp _)

/-- 実際の二次内ホーン上の同じ native target 比較自身が同値。 -/
lemma cocartesianTwoHornNativeTargetComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianTwoHornNativeTargetComparison p q) :=
  (cocartesianTwoHornNativeLiftRestrictionEquivalence p q).symm.isQCatEquivalence.comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval_finite_isQCatEquivalence 2 p q).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_isQCatEquivalence_of_innerAnodyne _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.innerAnodyneExtensions_ulift_map (A).hom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver_innerAnodyne 1 (by decide) (by decide))) P Q))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
