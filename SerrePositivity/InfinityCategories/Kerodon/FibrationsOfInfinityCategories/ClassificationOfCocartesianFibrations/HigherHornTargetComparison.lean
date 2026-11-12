module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.AnodyneScaffoldTarget
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiniteHornOver

/-!
概要：三次元以上の実際の内ホーンで、native Hom と scaffold Hom を分類先の区間 Hom へ写す。
方針：実際のホーンの内 anodyne 性と全辺被覆を一般の比較へ適用する。
規約：元の有限単体の分類作用との指定関手同型を保持し、境界全体の比較とは区別する。
使われ方：境界の内ホーンと残りの面による帰納の入力。

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
variable {n : ℕ} (hn : 3 ≤ n) (i : Fin (n + 1)) (h0 : 0 < i) (hi : i < Fin.last n)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin (n + 1)))))
local notation "HA" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver_innerAnodyne i h0 hi
local notation "HE" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver_edgeSurjective hn i

local instance : InnerFibration (pullback.fst ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i)).hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i)).hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

local instance : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMarkedHom p.val.hom q.val.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i)) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q.val.hom _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMark p.val.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i))))

/-- 実際の高次内ホーン上の元の native Hom から、実際の分類先 Hom への比較。 -/
def cocartesianHigherHornNativeTargetComparison :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianAnodyneNativeHomComparison n p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i) HA HE

/-- 同じ高次内ホーン上の native target 比較自身が同値。 -/
lemma cocartesianHigherHornNativeTargetComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianHigherHornNativeTargetComparison hn i h0 hi p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianAnodyneNativeHomComparison_isQCatEquivalence n p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i) HA HE

/-- 元の有限単体の同じ作用と、高次内ホーンの native 比較を結ぶ指定同型。 -/
def cocartesianHigherHornNativeTargetComparison_originalIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianAnodyneNativeHomComparison_originalIso n p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i) HA HE

/-- 実際の高次内ホーン上の辺保存 scaffold Hom から、実際の分類先 Hom への比較。 -/
def cocartesianHigherHornScaffoldTargetComparison :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianAnodyneScaffoldTargetComparison n p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i) HA HE

/-- 同じ高次内ホーン上の scaffold target 比較自身も同値。 -/
lemma cocartesianHigherHornScaffoldTargetComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianHigherHornScaffoldTargetComparison hn i h0 hi p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianAnodyneScaffoldTargetComparison_isQCatEquivalence n p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i) HA HE

/-- 同じ元の有限単体の作用を scaffold と高次内ホーンの target 比較から回収する指定同型。 -/
def cocartesianHigherHornScaffoldTargetComparison_originalIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianAnodyneScaffoldTargetComparison_originalIso n p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFiniteHornOver.{u} n i) HA HE

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
