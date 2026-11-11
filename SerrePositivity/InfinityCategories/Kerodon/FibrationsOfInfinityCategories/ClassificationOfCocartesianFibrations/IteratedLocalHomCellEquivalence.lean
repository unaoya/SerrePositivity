module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IteratedLocalHomComparison

/-!
概要：元の局所比較を零・一次元セルへさらに制限した全 Hom 比較は同値。
方針：同じ零・一次元の分類作用と、元の比較 path の底制限の輸送を使う。
規約：元の二回の pullback 対象の全相対 Hom を保持する。
使われ方：二次元 Segal 比較の共有頂点と辺における同値性の入力。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の零次元セルへさらに制限した同じ全 Hom 比較は同値。 -/
lemma cocartesianIteratedLocalHomComparison_zeroCell_isQCatEquivalence
    {D C : Type u} [Category.{u} D] [Category.{u} C]
    (l : ULift.{u} (Fin 1) ⥤ D) (k : D ⥤ C)
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalHomComparison l k p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison_zeroCell_isQCatEquivalence l _ _).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeRestrictedHomTransport_isQCatEquivalence l k p q)

/-- 元の一次元セルへさらに制限した同じ全 Hom 比較は同値。 -/
lemma cocartesianIteratedLocalHomComparison_oneCell_isQCatEquivalence
    {D C : Type u} [Category.{u} D] [Category.{u} C]
    (l : ULift.{u} (Fin 2) ⥤ D) (k : D ⥤ C)
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIteratedLocalHomComparison l k p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison_oneCell_isQCatEquivalence l _ _).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeRestrictedHomTransport_isQCatEquivalence l k p q)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
