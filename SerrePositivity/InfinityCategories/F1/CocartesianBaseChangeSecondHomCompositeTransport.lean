module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondCompositeLift

/-!
概要：元の第二面の Hom 上で、元の結合比較と既存の二回目の輸送の合成を回収する。
方針：同じ分解三角形の長辺への Hom 射影の同値性で関手同型を降ろす。
規約：元の第二面の Hom と既存の輸送作用を保持する。
使われ方：元の直接の Hom 輸送を含む三角形則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ元の第二面の全 Hom 上で、実際の二段の輸送は元の両評価を結ぶ。 -/
def cocartesianBaseChangeSecondHomCompositeTransportIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      (cocartesianBaseChangeSecondHomSpanOne l k p q ≫
        (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
          cocartesianBaseChangeHomTransport l
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))
      (cocartesianBaseChangeSecondHomSpanZero l k p q) := by
  have hf := (cocartesianBaseChangeSecondTriangleHomLong_isQCatEquivalence l k p q).precompose
    (intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)))
  exact hf.isFullyFaithful.preimageVertexIso
    (cocartesianBaseChangeSecondHomCompositeLiftIso l k p q)

end SerrePositivity.InfinityCategories
