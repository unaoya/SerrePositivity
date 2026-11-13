module

public import SerrePositivity.InfinityCategories.HA.Section4_1_4.EmptyRelativeFunctorHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalSimplicialCore
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeFunctor

/-!
概要：空の部分底上の元の native Hom、その core と宇宙持ち上げは終対象。
方針：空の引き戻しの始対象性を、実際の全相対 Hom と辺保存部分へ適用する。
規約：元の両射影の底変換と core を使い、射影の充填性を追加しない。
使われ方：標準零単体の空の境界の分類 Hom 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (a : Over B) (hA : IsInitial a.left)

/-- 空の部分底上の元の全 cocartesian 相対 Hom は終対象。 -/
def cocartesianPullbackNativeHom_isTerminal_of_isInitial :
    IsTerminal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q)) :=
  _root_.SerrePositivity.InfinityCategories.HA.Section4_1_4.markedCocartesianFunctorSpace_isTerminal_of_isInitial
    (pullback.fst a.hom q) (pullback.fst a.hom p) _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sset_pullback_isInitial_of_left a.hom p hA)

/-- 同じ空の部分底上の native Hom の core も終対象。 -/
def cocartesianPullbackNativeCore_isTerminal_of_isInitial :
    IsTerminal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q)) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.quasicategoryCore_isTerminal_of_isTerminal
    (cocartesianPullbackNativeHom_isTerminal_of_isInitial p q a hA)

/-- 同じ native core を分類先と同じ宇宙へ持ち上げても終対象。 -/
def cocartesianPullbackNativeLift_isTerminal_of_isInitial :
    IsTerminal ((SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q)) : SSet.{u})) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftSSet_isTerminal_of_isTerminal (cocartesianPullbackNativeCore_isTerminal_of_isInitial p q a hA)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
