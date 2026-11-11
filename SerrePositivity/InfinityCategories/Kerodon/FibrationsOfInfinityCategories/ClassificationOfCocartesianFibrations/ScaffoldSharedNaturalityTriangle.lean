module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OriginalCellOverNaturalityTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldCellCospan

/-!
概要：最初の辺と尾部から共有頂点へ進む元の指定自然性は、同じ直接の大域自然性を回収する。
方針：同じ共有セルを指定した既存の三角等式を最初の辺と尾部のそれぞれへ適用する。
規約：元の全 Hom と両脚の指定自然性を保持する。
使われ方：補正 pullback 比較と元の分類作用の成分 path の共有頂点での整合。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 最初の辺から同じ共有頂点への、端点表示だけを揃えた元の局所自然性。 -/
def cocartesianScaffoldSharedFirstNaturalityIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalityNormalizedIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k) rfl p q

/-- 最初の辺の大域自然性を同じ共有頂点へ制限した指定第最初の辺と尾部。 -/
def cocartesianScaffoldSharedFirstGlobalNaturalityIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalityNormalizedSecondIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k) rfl p q

/-- 次の辺から同じ共有頂点への、端点表示だけを揃えた元の局所自然性。 -/
def cocartesianScaffoldSharedSecondNaturalityIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalityNormalizedIso
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteZeroVertex n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell_tail n k) p q

/-- 次の辺の大域自然性を同じ共有頂点へ制限した指定第最初の辺と尾部。 -/
def cocartesianScaffoldSharedSecondGlobalNaturalityIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalityNormalizedSecondIso
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteZeroVertex n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell_tail n k) p q

/-- 最初の辺からの指定合成は、同じ共有頂点の元の直接自然性に一致する。 -/
lemma cocartesianScaffoldSharedFirstNaturality_triangle :
    cocartesianScaffoldSharedFirstNaturalityIso n k p q ≪≫
      cocartesianScaffoldSharedFirstGlobalNaturalityIso n k p q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k) p q := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalityTriangleCommutes
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldFirstCell n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k) rfl p q

/-- 次の辺からの指定合成も、同じ共有頂点の元の直接自然性に一致する。 -/
lemma cocartesianScaffoldSharedSecondNaturality_triangle :
    cocartesianScaffoldSharedSecondNaturalityIso n k p q ≪≫
      cocartesianScaffoldSharedSecondGlobalNaturalityIso n k p q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomNaturalityIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k) p q := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOriginalCellOverNaturalityTriangleCommutes
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteZeroVertex n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldTailCell n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell n k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSharedCell_tail n k) p q

/-- 最初の辺と尾部から共有頂点へ進む指定合成は、元の全 Hom 上で同じ指定値を持つ。 -/
lemma cocartesianScaffoldSharedNaturality_coherence :
    cocartesianScaffoldSharedFirstNaturalityIso n k p q ≪≫
      cocartesianScaffoldSharedFirstGlobalNaturalityIso n k p q =
    cocartesianScaffoldSharedSecondNaturalityIso n k p q ≪≫
      cocartesianScaffoldSharedSecondGlobalNaturalityIso n k p q := by
  exact (cocartesianScaffoldSharedFirstNaturality_triangle n k p q).trans
    (cocartesianScaffoldSharedSecondNaturality_triangle n k p q).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
