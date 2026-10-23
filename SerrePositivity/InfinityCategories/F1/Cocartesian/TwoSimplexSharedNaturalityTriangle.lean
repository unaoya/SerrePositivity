module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OriginalCellOverNaturalityTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexCellCospan

/-!
概要：二辺から共有頂点へ進む元の指定自然性は、同じ直接の大域自然性を回収する。
方針：同じ共有セルを指定した既存の三角等式を二辺のそれぞれへ適用する。
規約：元の全 Hom と両脚の指定自然性を保持する。
使われ方：補正 pullback 比較と元の分類作用の成分 path の共有頂点での整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の辺から同じ共有頂点への、端点表示だけを揃えた元の局所自然性。 -/
def cocartesianTwoSimplexSharedFirstNaturalityIso :=
  cocartesianOriginalCellOverNaturalityNormalizedIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q

/-- 最初の辺の大域自然性を同じ共有頂点へ制限した指定第二辺。 -/
def cocartesianTwoSimplexSharedFirstGlobalNaturalityIso :=
  cocartesianOriginalCellOverNaturalityNormalizedSecondIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q

/-- 次の辺から同じ共有頂点への、端点表示だけを揃えた元の局所自然性。 -/
def cocartesianTwoSimplexSharedSecondNaturalityIso :=
  cocartesianOriginalCellOverNaturalityNormalizedIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
    (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k)
    (cocartesianTwoSimplexSharedCell_second k) p q

/-- 次の辺の大域自然性を同じ共有頂点へ制限した指定第二辺。 -/
def cocartesianTwoSimplexSharedSecondGlobalNaturalityIso :=
  cocartesianOriginalCellOverNaturalityNormalizedSecondIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
    (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k)
    (cocartesianTwoSimplexSharedCell_second k) p q

/-- 最初の辺からの指定合成は、同じ共有頂点の元の直接自然性に一致する。 -/
lemma cocartesianTwoSimplexSharedFirstNaturality_triangle :
    cocartesianTwoSimplexSharedFirstNaturalityIso k p q ≪≫
      cocartesianTwoSimplexSharedFirstGlobalNaturalityIso k p q =
    cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q := by
  exact cocartesianOriginalCellOverNaturalityTriangleCommutes
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q

/-- 次の辺からの指定合成も、同じ共有頂点の元の直接自然性に一致する。 -/
lemma cocartesianTwoSimplexSharedSecondNaturality_triangle :
    cocartesianTwoSimplexSharedSecondNaturalityIso k p q ≪≫
      cocartesianTwoSimplexSharedSecondGlobalNaturalityIso k p q =
    cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q := by
  exact cocartesianOriginalCellOverNaturalityTriangleCommutes
    (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
    (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k)
    (cocartesianTwoSimplexSharedCell_second k) p q

/-- 二辺から共有頂点へ進む指定合成は、元の全 Hom 上で同じ指定値を持つ。 -/
lemma cocartesianTwoSimplexSharedNaturality_coherence :
    cocartesianTwoSimplexSharedFirstNaturalityIso k p q ≪≫
      cocartesianTwoSimplexSharedFirstGlobalNaturalityIso k p q =
    cocartesianTwoSimplexSharedSecondNaturalityIso k p q ≪≫
      cocartesianTwoSimplexSharedSecondGlobalNaturalityIso k p q := by
  exact (cocartesianTwoSimplexSharedFirstNaturality_triangle k p q).trans
    (cocartesianTwoSimplexSharedSecondNaturality_triangle k p q).symm

end SerrePositivity.InfinityCategories
