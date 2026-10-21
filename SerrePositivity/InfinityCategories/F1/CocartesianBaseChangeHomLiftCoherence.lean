module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomTransport

/-!
概要：元の大域 Hom 自然性と、同じ fiber 内比較の零射影の同一性。
方針：既存の証明の端点表示の輸送だけを取り除く。
規約：元の比較 span・切断・fiber 内同型を保持する。
使われ方：局所自然性との共有頂点の三角形を共通 Hom 上で照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の大域自然性は、同じ fiber 内比較の零射影を端点正規化したもの。 -/
lemma cocartesianBaseChangeHomNaturalityIso_lift_heq
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    HEq (cocartesianBaseChangeHomNaturalityIso k p q)
      ((cocartesianBaseChangeHomNaturalityLiftIso k p q).postcomp
        (cocartesianBaseChangeHomSpanZero k p q)) := by
  exact F2.functorIsoOfEq_heq ((cocartesianBaseChangeHomNaturalityLiftIso k p q).postcomp
    (cocartesianBaseChangeHomSpanZero k p q))
    (cocartesianBaseChangeHomNaturalityLift_zero_transport k p q)
    (cocartesianBaseChangeHomComparison_zero k p q)

end SerrePositivity.InfinityCategories
