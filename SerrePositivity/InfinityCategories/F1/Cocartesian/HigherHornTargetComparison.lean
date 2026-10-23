module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.AnodyneScaffoldTarget
public import SerrePositivity.InfinityCategories.F1.Cocartesian.FiniteHornOver

/-!
概要：三次元以上の実際の内ホーンで、native Hom と scaffold Hom を分類先の区間 Hom へ写す。
方針：実際のホーンの内 anodyne 性と全辺被覆を一般の比較へ適用する。
規約：元の有限単体の分類作用との指定関手同型を保持し、境界全体の比較とは区別する。
使われ方：境界の内ホーンと残りの面による帰納の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {n : ℕ} (hn : 3 ≤ n) (i : Fin (n + 1)) (h0 : 0 < i) (hi : i < Fin.last n)
  (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin (n + 1)))))
local notation "HA" => cocartesianFiniteHornOver_innerAnodyne i h0 hi
local notation "HE" => cocartesianFiniteHornOver_edgeSurjective hn i

local instance : InnerFibration (pullback.fst ((cocartesianFiniteHornOver.{u} n i)).hom q.val.hom) :=
  ⟨innerFibrations.pullback_fst ((cocartesianFiniteHornOver.{u} n i)).hom q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

local instance : Quasicategory (cocartesianScaffoldPullbackMarkedHom p.val.hom q.val.hom (cocartesianFiniteHornOver.{u} n i)) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q.val.hom _
    (cocartesianScaffoldPullbackMark p.val.hom (cocartesianFiniteHornOver.{u} n i))))

/-- 実際の高次内ホーン上の元の native Hom から、実際の分類先 Hom への比較。 -/
def cocartesianHigherHornNativeTargetComparison :=
  cocartesianAnodyneNativeHomComparison n p q (cocartesianFiniteHornOver.{u} n i) HA HE

/-- 同じ高次内ホーン上の native target 比較自身が同値。 -/
lemma cocartesianHigherHornNativeTargetComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianHigherHornNativeTargetComparison hn i h0 hi p q) :=
  cocartesianAnodyneNativeHomComparison_isQCatEquivalence n p q (cocartesianFiniteHornOver.{u} n i) HA HE

/-- 元の有限単体の同じ作用と、高次内ホーンの native 比較を結ぶ指定同型。 -/
def cocartesianHigherHornNativeTargetComparison_originalIso :=
  cocartesianAnodyneNativeHomComparison_originalIso n p q (cocartesianFiniteHornOver.{u} n i) HA HE

/-- 実際の高次内ホーン上の辺保存 scaffold Hom から、実際の分類先 Hom への比較。 -/
def cocartesianHigherHornScaffoldTargetComparison :=
  cocartesianAnodyneScaffoldTargetComparison n p q (cocartesianFiniteHornOver.{u} n i) HA HE

/-- 同じ高次内ホーン上の scaffold target 比較自身も同値。 -/
lemma cocartesianHigherHornScaffoldTargetComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianHigherHornScaffoldTargetComparison hn i h0 hi p q) :=
  cocartesianAnodyneScaffoldTargetComparison_isQCatEquivalence n p q (cocartesianFiniteHornOver.{u} n i) HA HE

/-- 同じ元の有限単体の作用を scaffold と高次内ホーンの target 比較から回収する指定同型。 -/
def cocartesianHigherHornScaffoldTargetComparison_originalIso :=
  cocartesianAnodyneScaffoldTargetComparison_originalIso n p q (cocartesianFiniteHornOver.{u} n i) HA HE

end SerrePositivity.InfinityCategories
