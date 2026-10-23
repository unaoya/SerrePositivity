module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalHomNativeRestrictionIso
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramOverRestriction
public import SerrePositivity.InfinityCategories.F1.Universe.RelativeOverPre

/-!
概要：局所比較の標的制限を、同じ底上の射による元の厳密な制限へ正規化する。
方針：端点表示の恒等による変更を区間族へ展開し、同じ前合成を照合する。
規約：元の分類図式と底上の射を保持する。
使われ方：Segal 比較の共通頂点を持つ同じ二脚への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ底上の射による制限を端点正規化すると、既存の二回の底制限そのもの。 -/
lemma cocartesianLocalHomOverRestriction_normalization :
    intervalDiagramOverPre
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)
        (uliftOverMorphism (cocartesianBaseChangeOverMap l k)) ≫
      cocartesianBaseChangeHomCompositionNormalization l k p q =
    intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram p.val.hom)
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram q.val.hom) := by
  have hP := intervalDiagramOverPre_uncurry
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (uliftOverMorphism (cocartesianBaseChangeOverMap l k)) (𝟙 _)
  have hR := intervalDiagramRestriction_uncurry
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
      cocartesianStrictTransportCoherentDiagram p.val.hom)
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
      cocartesianStrictTransportCoherentDiagram q.val.hom) (𝟙 _)
  rw [Category.id_comp] at hP hR
  let r := intervalDiagramOverPre
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (uliftOverMorphism (cocartesianBaseChangeOverMap l k))
  have hN : intervalMappingUncurry
      (r ≫ cocartesianBaseChangeHomCompositionNormalization l k p q) =
      intervalMappingUncurry r ≫ 𝟙 (CatInfinityFunctor
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) := by
    exact intervalMappingPostOfEq_uncurry (𝟙 (CatInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫
        cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫
        cocartesianStrictTransportCoherentDiagram q.val.hom))
      (congrArg functorVertex (cocartesianBaseChangeClassifiedRestriction_comp l k _))
      (congrArg functorVertex (cocartesianBaseChangeClassifiedRestriction_comp l k _)) r
  apply intervalMappingUncurry_injective
  rw [hN]
  exact (Category.comp_id (intervalMappingUncurry r)).trans (hP.trans hR.symm)

end SerrePositivity.InfinityCategories
