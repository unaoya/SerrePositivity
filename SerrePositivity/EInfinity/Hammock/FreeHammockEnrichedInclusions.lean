module

public import SerrePositivity.EInfinity.Hammock.FreeHammockEnrichedPartsEquiv

/-!
# 元の自由積の二つの豊穣包含

概要：元の指定 hammock と非指定自由圏の離散豊穣化から同じ元の hammock へ含める。
方針：元の指定包含と元の生成矢の標準射を恒等の生成データに束ねる。
規約：同じ元の対象と同じ生成矢を保持する。
使われ方：自由積の普遍性の制限を二つの包含との合成で回収する。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

def identityFoldData :
    letI := Hammock.enrichedCategory W.paths
    EnrichedFoldData W (Paths C) := by
  letI := Hammock.enrichedCategory W.paths
  exact
    { obj := fun X => X
      marked := AllMarked.inclusion W
      generator := fun g => arrowMap W.paths g.val.hom.toPath
      marked_unit := AllMarked.inclusion_unit W
      marked_comp := AllMarked.inclusion_composition W }

def markedInclusionFunctor :
    letI := Hammock.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
    letI := Hammock.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (WideSubcategory W.paths) (Paths C) := by
  letI := Hammock.enrichedCategory (⊤ : MorphismProperty (WideSubcategory W.paths))
  letI := Hammock.enrichedCategory W.paths
  exact (identityFoldData W).markedEnrichedFunctor

def unmarkedInclusionFunctor :
    letI := DiscreteEnrichment.enrichedCategory
      (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
    letI := Hammock.enrichedCategory W.paths
    EnrichedFunctor SSet.{u} (Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
      (Paths C) := by
  letI := DiscreteEnrichment.enrichedCategory
    (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
  letI := Hammock.enrichedCategory W.paths
  exact (identityFoldData W).unmarkedEnrichedFunctor

lemma unmarkedInclusion_generator (g : FactorTarget.Index W) :
    letI := DiscreteEnrichment.enrichedCategory
      (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
    letI := Hammock.enrichedCategory W.paths
    DiscreteEnrichment.point (unmarkedGeneratorPath W g) ≫
      (unmarkedInclusionFunctor W).map g.val.left g.val.right =
        arrowMap W.paths g.val.hom.toPath := by
  let := DiscreteEnrichment.enrichedCategory
    (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
  let := Hammock.enrichedCategory W.paths
  exact (identityFoldData W).unmarkedEnrichedFunctor_generator g

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
