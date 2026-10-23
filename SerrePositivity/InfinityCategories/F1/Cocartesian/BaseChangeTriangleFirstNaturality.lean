module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictionSquareIdentity
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomRestrictedTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomSpanSectionBoundaryCoherence

/-!
概要：比較三角形の最初の面は、元の大域比較 Hom の底制限上の指定因子比較を回収する。
方針：最初の面の厳密な作用と因子比較の前合成則を使う。
規約：元の分類作用・最初の面・制限 span・指定切断を保持する。
使われ方：共有頂点における元の大域自然性と局所自然性の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ最初の面の大域作用は、元の比較 Hom 作用の底制限そのもの。 -/
lemma cocartesianBaseChangeTriangleHomComparison_first_restriction :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
        cocartesianBaseChangeTriangleHomFirst l k p q =
      cocartesianBaseChangeHomComparison k p q ≫
        cocartesianBaseChangeRestrictedHomMap l k p q := by
  rw [cocartesianBaseChangeTriangleHomComparison_first,
    cocartesianBaseChangeRestrictedHomMap_eq_post]

/-- 元の全 Hom 上で、同じ最初の面の比較は制限された元の span の指定因子比較になる。 -/
lemma cocartesianBaseChangeTriangleHomFirst_transportIso_naturality_heq :
    HEq ((cocartesianBaseChangeTriangleHomFirst_restrictedTransportIso l k p q).precomp
      (cocartesianBaseChangeTriangleHomComparison l k p q))
      (homSpanSectionTransportFactorIso
        (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
        (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
        (cocartesianBaseChangeHomComparison k p q ≫
          cocartesianBaseChangeRestrictedHomMap l k p q)) := by
  exact homSpanSectionTransportFactorIso_precomp_heq
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeTriangleHomFirst l k p q)
    (cocartesianBaseChangeTriangleHomComparison l k p q)
    (cocartesianBaseChangeHomComparison k p q ≫
      cocartesianBaseChangeRestrictedHomMap l k p q)
    (cocartesianBaseChangeTriangleHomComparison_first_restriction l k p q)

end SerrePositivity.InfinityCategories
