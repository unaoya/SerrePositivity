module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalHomNativeRestrictionIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramOverRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.RelativeOverPre

/-!
概要：局所比較の標的制限を、同じ底上の射による元の厳密な制限へ正規化する。
方針：端点表示の恒等による変更を区間族へ展開し、同じ前合成を照合する。
規約：元の分類図式と底上の射を保持する。
使われ方：Segal 比較の共通頂点を持つ同じ二脚への接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 同じ底上の射による制限を端点正規化すると、既存の二回の底制限そのもの。 -/
lemma cocartesianLocalHomOverRestriction_normalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeOverMap l k)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomCompositionNormalization l k p q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom) := by
  have hP := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_uncurry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeOverMap l k)) (𝟙 _)
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction_uncurry
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom) (𝟙 _)
  rw [Category.id_comp] at hP hR
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeOverMap l k))
  have hN : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeHomCompositionNormalization l k p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry r ≫ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom))
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeClassifiedRestriction_comp l k _))
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeClassifiedRestriction_comp l k _)) r
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [hN]
  exact (Category.comp_id (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry r)).trans (hP.trans hR.symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
