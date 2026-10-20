module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeComparisonEvaluation
public import SerrePositivity.InfinityCategories.F1.CoherentQCatInvertible

/-!
概要：元の全 fibration にわたる底変換比較の実際の辺は可逆。
方針：各成分を元の比較成分と厳密に照合し、点ごとの可逆性判定を使う。
規約：元の section 評価と元の底変換の ∞ 関手の間の同じ辺を同型へ束ねる。
使われ方：分類主写像のセル制限の自然な比較と同じ Hom 作用の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) (d : D)

/-- 同じ底変換比較の辺は、元の全 fibration の coherent な族として可逆。 -/
lemma cocartesianBaseChangeComparisonEdge_isInvertible :
    IsInvertibleEdge (cocartesianBaseChangeComparisonEdge k d).toTruncated := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt
    (cocartesianBaseChangeComparisonEdge k d).toTruncated).mpr
  intro s
  rw [← coherentNerveVertex_object s]
  change IsInvertibleEdge (functorEdgeAt (cocartesianBaseChangeComparisonEdge k d)
    (coherentNerveVertex (coherentNerveObject s))).toTruncated
  apply (isInvertibleEdge_congr
    (cocartesianBaseChangeComparisonEdge_at k d (coherentNerveObject s))).mpr
  exact coherentQCatEdge_isInvertible_of_isQCatEquivalence
    (cocartesianStrictTransportBaseChangeComponent_isQCatEquivalence
      (coherentNerveObject s).val.hom k d)

/-- 同じ比較の実際の可逆辺は、元の二つの section 評価の ∞ 関手の同型。 -/
def cocartesianBaseChangeComparisonIso :
    FunctorIso (cocartesianSectionsInfinityEvaluation
      (Over.mk (nerveMap (Under.forget (k.obj d)))))
      (cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
        cocartesianSectionsInfinityEvaluation (Over.mk (nerveMap (Under.forget d)))) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (cocartesianBaseChangeComparisonEdge k d).toTruncated) :=
    cocartesianBaseChangeComparisonEdge_isInvertible k d
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (cocartesianBaseChangeComparisonEdge k d).toTruncated)

end SerrePositivity.InfinityCategories
