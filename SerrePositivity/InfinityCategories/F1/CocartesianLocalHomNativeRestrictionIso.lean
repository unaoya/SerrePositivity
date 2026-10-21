module

public import SerrePositivity.InfinityCategories.F1.CocartesianIteratedLocalHomNativeIso
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeRestriction

/-!
概要：元の局所 Hom の直接制限と、同じ分類先の制限は関手同型で自然。
方針：元の二重局所比較を指定結合同型で正規化し、既存の再底変換の自然性を使う。
規約：元の全局所 Hom・同じ直接制限・既存の分類比較を保持する。
使われ方：二次元 Segal 比較の共有頂点への自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全局所 Hom の直接制限は、同じ底上で局所分類の制限と整合する。 -/
def cocartesianLocalHomComparison_nativeRestrictionIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      (((SSet.uliftFunctor.{u + 1, u}).map
          (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
            (cocartesianBaseChangeOverMap l k))) ≫
        cocartesianLocalHomComparison (l ⋙ k) p q) ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q)
      (cocartesianLocalHomComparison k p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram p.val.hom)
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram q.val.hom)) := by
  have e₁ := FunctorIso.precomp (cocartesianIteratedLocalHomComparison_nativeIso l k p q)
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))
  have e := e₁ ≪≫ cocartesianIteratedLocalHomComparison_restrictionIso l k p q
  simp only [← Category.assoc] at e
  rw [← CategoryTheory.Functor.map_comp, cocartesianBaseChangeNativeHomIso_restriction] at e
  exact e

end SerrePositivity.InfinityCategories
