module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OriginalCellOverNaturalityTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldCellCospan

/-!
概要：最初の辺と尾部から共有頂点へ進む元の指定自然性は、同じ直接の大域自然性を回収する。
方針：同じ共有セルを指定した既存の三角等式を最初の辺と尾部のそれぞれへ適用する。
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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の辺から同じ共有頂点への、端点表示だけを揃えた元の局所自然性。 -/
def cocartesianScaffoldSharedFirstNaturalityIso :=
  cocartesianOriginalCellOverNaturalityNormalizedIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q

/-- 最初の辺の大域自然性を同じ共有頂点へ制限した指定第最初の辺と尾部。 -/
def cocartesianScaffoldSharedFirstGlobalNaturalityIso :=
  cocartesianOriginalCellOverNaturalityNormalizedSecondIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q

/-- 次の辺から同じ共有頂点への、端点表示だけを揃えた元の局所自然性。 -/
def cocartesianScaffoldSharedSecondNaturalityIso :=
  cocartesianOriginalCellOverNaturalityNormalizedIso
    (scaffoldFiniteZeroVertex n)
    (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k)
    (cocartesianScaffoldSharedCell_tail n k) p q

/-- 次の辺の大域自然性を同じ共有頂点へ制限した指定第最初の辺と尾部。 -/
def cocartesianScaffoldSharedSecondGlobalNaturalityIso :=
  cocartesianOriginalCellOverNaturalityNormalizedSecondIso
    (scaffoldFiniteZeroVertex n)
    (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k)
    (cocartesianScaffoldSharedCell_tail n k) p q

/-- 最初の辺からの指定合成は、同じ共有頂点の元の直接自然性に一致する。 -/
lemma cocartesianScaffoldSharedFirstNaturality_triangle :
    cocartesianScaffoldSharedFirstNaturalityIso n k p q ≪≫
      cocartesianScaffoldSharedFirstGlobalNaturalityIso n k p q =
    cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q := by
  exact cocartesianOriginalCellOverNaturalityTriangleCommutes
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q

/-- 次の辺からの指定合成も、同じ共有頂点の元の直接自然性に一致する。 -/
lemma cocartesianScaffoldSharedSecondNaturality_triangle :
    cocartesianScaffoldSharedSecondNaturalityIso n k p q ≪≫
      cocartesianScaffoldSharedSecondGlobalNaturalityIso n k p q =
    cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q := by
  exact cocartesianOriginalCellOverNaturalityTriangleCommutes
    (scaffoldFiniteZeroVertex n)
    (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k)
    (cocartesianScaffoldSharedCell_tail n k) p q

/-- 最初の辺と尾部から共有頂点へ進む指定合成は、元の全 Hom 上で同じ指定値を持つ。 -/
lemma cocartesianScaffoldSharedNaturality_coherence :
    cocartesianScaffoldSharedFirstNaturalityIso n k p q ≪≫
      cocartesianScaffoldSharedFirstGlobalNaturalityIso n k p q =
    cocartesianScaffoldSharedSecondNaturalityIso n k p q ≪≫
      cocartesianScaffoldSharedSecondGlobalNaturalityIso n k p q := by
  exact (cocartesianScaffoldSharedFirstNaturality_triangle n k p q).trans
    (cocartesianScaffoldSharedSecondNaturality_triangle n k p q).symm

end SerrePositivity.InfinityCategories
