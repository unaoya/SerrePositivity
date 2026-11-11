module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalHomOverNaturality

/-!
概要：共有セルを指定し、その同じセルへの両側の局所 Hom 制限を比較する。
方針：合成したセル添字の等式を元の底上の射に束ね、既存の自然性へ渡す。
規約：共有セルの表示を両脚で統一する。
使われ方：二次元 Segal 比較の同じ共有頂点。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]

/-- 指定した同じ共有セルへの、元の底上の射。 -/
def cocartesianCellOverMap (l : A ⥤ D) (k : D ⥤ C) (v : A ⥤ C) (h : l ⋙ k = v) :
    Over.mk (nerveMap v) ⟶ Over.mk (nerveMap k) :=
  Over.homMk (nerveMap l) (by change nerveMap (l ⋙ k) = nerveMap v; rw [h])

/-- 共有セルを同じ表示で指定しても、元の両側の制限は同じ局所比較に自然。 -/
def cocartesianLocalHomComparison_cellOverNaturalityIso
    (l : A ⥤ D) (k : D ⥤ C) (v : A ⥤ C) (h : l ⋙ k = v)
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre p.val.hom q.val.hom
            (cocartesianCellOverMap l k v h))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison v p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison k p q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre
          (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u})
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)
          (a := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap v)))
          (b := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (cocartesianCellOverMap l k v h))) := by
  subst v
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianLocalHomComparison_overNaturalityIso l k p q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
