module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNaturalityFactorCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomTransport

/-!
概要：元の比較三角形の長辺の輸送比較は、元の大域自然性そのものを引き戻す。
方針：同じ切断の因子比較の前合成則と長辺作用の厳密な一致を使う。
規約：元の全相対 Hom の作用と既存の指定同型を保持する。
使われ方：共有頂点での三角形の等式を元の分類作用の自然性へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 Hom を同じ三角形へ写すと、長辺の輸送比較は大域の直接の自然性になる。 -/
lemma cocartesianBaseChangeTriangleHomLong_transportIso_naturality_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HEq ((cocartesianBaseChangeTriangleHomLong_transportIso l k p q).precomp
      (cocartesianBaseChangeTriangleHomComparison l k p q))
      (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q) := by
  have h := homSpanSectionTransportFactorIso_precomp_heq
    (cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)
    (cocartesianBaseChangeHomSpanZero (l ⋙ k) p q)
    (cocartesianBaseChangeHomSpanOneSection (l ⋙ k) p q)
    (cocartesianBaseChangeHomSpanOne_isFullyFaithful (l ⋙ k) p q)
    (cocartesianBaseChangeHomSpanOneSection_projection (l ⋙ k) p q)
    (cocartesianBaseChangeTriangleHomLong l k p q)
    (cocartesianBaseChangeTriangleHomComparison l k p q)
    (cocartesianBaseChangeHomComparison (l ⋙ k) p q)
    (cocartesianBaseChangeTriangleHomComparison_long l k p q)
  exact h.trans (cocartesianBaseChangeHomNaturalityIso_factor_heq (l ⋙ k) p q).symm

end SerrePositivity.InfinityCategories
