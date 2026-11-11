module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OriginalCellOverNaturalityEndpoints

/-!
概要：同じ共有セルへの既存の cellOver 自然性は元の大域自然性と三角等式を満たす。
方針：端点表示だけを揃えた指定三辺に、同じ over 自然性の三角等式を移す。
規約：共有セルの表示と元の指定同型の値を保持する。
使われ方：二単体の Segal 比較の共有頂点での成分 path の整合。

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
  (l : A ⥤ D) (k : D ⥤ C) (v : A ⥤ C) (h : l ⋙ k = v)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 端点の表示だけを揃えた、同じ共有セルへの元の局所自然性。 -/
def cocartesianOriginalCellOverNaturalityNormalizedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso v p q).sourceMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalitySecondIso l k v h p q).sourceMap :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalityIso l k v h p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturality_source l k v h p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturality_middle l k v h p q)

/-- 終点の表示だけを揃えた、同じ共有セルでの第二辺。 -/
def cocartesianOriginalCellOverNaturalityNormalizedSecondIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalitySecondIso l k v h p q).sourceMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso v p q).targetMap :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalitySecondIso l k v h p q) rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturality_target l k v h p q)

/-- 既存の cellOver 自然性自身と同じ共有セルの大域自然性との三角等式。 -/
def CocartesianOriginalCellOverNaturalityTriangleCommutes : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleCommutes (cocartesianOriginalCellOverNaturalityNormalizedIso l k v h p q)
    (cocartesianOriginalCellOverNaturalityNormalizedSecondIso l k v h p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso v p q)

/-- 同じ元の全 Hom 上で、共有セルを指定した既存の自然性自身の三角等式。 -/
lemma cocartesianOriginalCellOverNaturalityTriangleCommutes :
    CocartesianOriginalCellOverNaturalityTriangleCommutes l k v h p q := by
  subst v
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalOverNaturalityTriangleCommutes l k p q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
