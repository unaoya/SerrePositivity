module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexSharedNaturalityTriangle
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoTriangleEvaluation

/-!
概要：二辺から共有頂点への元の指定合成は、各元の相対関手で同じ成分を持つ。
方針：元の全 Hom 上の同じ三角等式を各頂点で評価する。
規約：元の相対関手と指定自然性の成分を保持する。
使われ方：元の分類作用と補正 pullback 比較を結ぶ成分 path。
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
  (x : ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q)) _⦋0⦌)

/-- 最初の辺から同じ共有頂点へ進む指定成分は、元の直接自然性の成分に一致する。 -/
lemma cocartesianTwoSimplexSharedFirstNaturality_component_triangle :
    (cocartesianTwoSimplexSharedFirstNaturalityIso k p q).app x ≪≫
      (cocartesianTwoSimplexSharedFirstGlobalNaturalityIso k p q).app x =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).app x := by
  exact IsoTriangleCommutes.app
    (cocartesianTwoSimplexSharedFirstNaturality_triangle k p q) x

/-- 次の辺からも同じ共有頂点の元の直接自然性の成分を回収する。 -/
lemma cocartesianTwoSimplexSharedSecondNaturality_component_triangle :
    (cocartesianTwoSimplexSharedSecondNaturalityIso k p q).app x ≪≫
      (cocartesianTwoSimplexSharedSecondGlobalNaturalityIso k p q).app x =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).app x := by
  exact IsoTriangleCommutes.app
    (cocartesianTwoSimplexSharedSecondNaturality_triangle k p q) x

/-- 元の全相対関手で、二辺から共有頂点への指定成分の合成は厳密に一致する。 -/
lemma cocartesianTwoSimplexSharedNaturality_component_coherence :
    (cocartesianTwoSimplexSharedFirstNaturalityIso k p q).app x ≪≫
      (cocartesianTwoSimplexSharedFirstGlobalNaturalityIso k p q).app x =
    (cocartesianTwoSimplexSharedSecondNaturalityIso k p q).app x ≪≫
      (cocartesianTwoSimplexSharedSecondGlobalNaturalityIso k p q).app x := by
  exact (cocartesianTwoSimplexSharedFirstNaturality_component_triangle k p q x).trans
    (cocartesianTwoSimplexSharedSecondNaturality_component_triangle k p q x).symm

end SerrePositivity.InfinityCategories
