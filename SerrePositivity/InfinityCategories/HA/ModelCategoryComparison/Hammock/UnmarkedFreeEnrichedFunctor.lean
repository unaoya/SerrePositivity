module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeDiscreteEnrichment
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeHammockEnrichedUniversal
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorPartition

/-!
# 元の非指定自由部分から任意の豊穣目標への関手

概要：同じ元の非指定生成矢の像を元の非指定自由圏の離散豊穣関手へ拡張する。
方針：元の生成 quiver から underlying 圏への前関手を元の自由圏で延長する。
規約：元の対象写像と全生成矢を保持する。
使われ方：自由積の二つの元の部分の包含による普遍性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
namespace EnrichedFoldData
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D] (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.EnrichedFoldData W D)

def unmarkedPrefunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W) ⥤q
    ForgetEnrichment SSet.{u} D where
  obj X := ForgetEnrichment.of SSet.{u} (F.obj X)
  map {X Y} f := ForgetEnrichment.homOf SSet.{u} (F.generator ⟨⟨X, Y, f.val⟩, f.property⟩)

def unmarkedEnrichedFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
      (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
    EnrichedFunctor SSet.{u} (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W))) D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftFunctor (Paths.lift F.unmarkedPrefunctor)

lemma unmarkedEnrichedFunctor_generator (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
      (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point
        (Quiver.Hom.toPath (show @Quiver.Hom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)) _ g.val.left g.val.right from
            ⟨g.val.hom, g.property⟩)) ≫
      F.unmarkedEnrichedFunctor.map g.val.left g.val.right = F.generator g := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.enrichedCategory
    (C := Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment.point _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftMap
    (Paths.lift F.unmarkedPrefunctor) g.val.left g.val.right = F.generator g
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichmentLift.liftMap_point, Paths.lift_toPath]
  rfl

end EnrichedFoldData
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
