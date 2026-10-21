module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNaturalitySectionCoherence
public import SerrePositivity.InfinityCategories.F1.HomSpanSectionBoundaryCoherence

/-!
概要：元の大域分類 Hom の自然性は、既存の span 輸送の因子比較そのもの。
方針：両者を同じ切断の単位の前後合成に戻して照合する。
規約：元の全相対 Hom の作用と指定された比較を保持する。
使われ方：比較三角形の等式を大域分類 Hom のセル自然性へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の大域自然性と同じ span の輸送因子比較は、端点の表示変更を除いて同じ同型。 -/
lemma cocartesianBaseChangeHomNaturalityIso_factor_heq
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    HEq (cocartesianBaseChangeHomNaturalityIso k p q)
      (homSpanSectionTransportFactorIso
        (cocartesianBaseChangeHomSpanOne k p q)
        (cocartesianBaseChangeHomSpanZero k p q)
        (cocartesianBaseChangeHomSpanOneSection k p q)
        (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
        (cocartesianBaseChangeHomSpanOneSection_projection k p q)
        (cocartesianBaseChangeHomComparison k p q)) := by
  exact (cocartesianBaseChangeHomNaturalityIso_section_heq k p q).trans
    (homSpanSectionTransportFactorIso_heq
      (cocartesianBaseChangeHomSpanOne k p q)
      (cocartesianBaseChangeHomSpanZero k p q)
      (cocartesianBaseChangeHomSpanOneSection k p q)
      (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
      (cocartesianBaseChangeHomSpanOneSection_projection k p q)
      (cocartesianBaseChangeHomComparison k p q)).symm

/-- 元の大域自然性は、同じ指定 span 境界比較を元の全 Hom 作用で引き戻したもの。 -/
lemma cocartesianBaseChangeHomNaturalityIso_boundary_heq
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    HEq (cocartesianBaseChangeHomNaturalityIso k p q)
      ((homSpanSectionBoundaryIso
        (cocartesianBaseChangeHomSpanOne k p q) (cocartesianBaseChangeHomSpanZero k p q)
        (cocartesianBaseChangeHomSpanOneSection k p q)
        (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
        (cocartesianBaseChangeHomSpanOneSection_projection k p q)).precomp
          (cocartesianBaseChangeHomComparison k p q)) := by
  exact (cocartesianBaseChangeHomNaturalityIso_factor_heq k p q).trans
    (heq_of_eq (homSpanSectionBoundaryIso_precomp _ _ _ _ _ _)).symm

end SerrePositivity.InfinityCategories
