module

public import SerrePositivity.InfinityCategories.F1.CocartesianLocalHomOverNaturalityInput

/-!
概要：元の局所比較を、源・標的の同じ底上の射に沿う厳密な二つの制限で結ぶ。
方針：既存の端点正規化後の自然性を、その同型性で反映する。
規約：元の全局所 Hom・底上の射・分類比較を保持する。
使われ方：Segal の両脚と共有頂点への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ元の底上の射による直接制限は、両側の同じ局所比較に自然。 -/
def cocartesianLocalHomComparison_overNaturalityIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
          (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
            (cocartesianBaseChangeOverMap l k))) ≫
        cocartesianLocalHomComparison (l ⋙ k) p q)
      (cocartesianLocalHomComparison k p q ≫
        intervalDiagramOverPre
          (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
          (cocartesianStrictTransportCoherentDiagram p.val.hom)
          (cocartesianStrictTransportCoherentDiagram q.val.hom)
          (a := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k))))
          (b := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)))
          (uliftOverMorphism (cocartesianBaseChangeOverMap l k))) :=
  (cocartesianLocalHomOverNormalization_isFullyFaithful l k p q).preimageFunctorIso
    (F := cocartesianLocalHomOverNaturalitySource l k p q)
    (G := cocartesianLocalHomOverNaturalityTarget l k p q)
    (cocartesianLocalHomOverNaturalityInputIso l k p q)

end SerrePositivity.InfinityCategories
