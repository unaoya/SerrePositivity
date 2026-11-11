module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoHornNativeTarget
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift

/-!
概要：実際の二次内ホーンの辺保存 scaffold Hom から、同じ分類先の区間 Hom への比較。
方針：同じ native scaffold 比較の逆に、欠損長辺を三角形で処理した native 比較を合成する。
規約：元の二単体の全 Hom 作用との指定同型を保持し、全辺被覆は仮定しない。
使われ方：境界を内ホーンと残りの一面に分ける帰納の二次元の入力。

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

local instance : InnerFibration (pullback.fst (A).hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst (A).hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

local instance : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMarkedHom p.val.hom q.val.hom A) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q.val.hom _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMark p.val.hom A)))

local instance : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace
      (pullback.fst (A).hom p.val.hom) (pullback.fst (A).hom q.val.hom)))) :=
  inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst (A).hom p.val.hom)
      (pullback.fst (A).hom q.val.hom)) : SSet.{u})))

/-- 実際の二次内ホーンの同じ scaffold Hom から、同じ分類先 Hom への射。 -/
def cocartesianTwoHornScaffoldTargetComparison :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence p.val.hom q.val.hom A).choose.inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison p q

/-- 同じ scaffold 比較を前置すると、元の native target 比較を回収する。 -/
def cocartesianTwoHornScaffoldTargetComparison_nativeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre p.val.hom q.val.hom A ≫
        cocartesianTwoHornScaffoldTargetComparison p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison p q) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence p.val.hom q.val.hom A).choose.homInvIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison p q))
    (by simp only [cocartesianTwoHornScaffoldTargetComparison, Category.assoc]; rfl)
    (Category.id_comp _)

/-- 元の二単体の同じ全 Hom 作用を、同じ内ホーンの scaffold target 比較から回収する。 -/
def cocartesianTwoHornScaffoldTargetComparison_originalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom A ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre p.val.hom q.val.hom A) ≫
          cocartesianTwoHornScaffoldTargetComparison p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (A).hom)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((cocartesianTwoHornScaffoldTargetComparison_nativeIso p q).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom A))
    (Category.assoc _ _ _).symm rfl ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_originalIso p q

/-- 実際の二次内ホーンの同じ scaffold target 比較自身も同値。 -/
lemma cocartesianTwoHornScaffoldTargetComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianTwoHornScaffoldTargetComparison p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence p.val.hom q.val.hom A).choose.symm.isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoHornNativeTargetComparison_isQCatEquivalence p q)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
