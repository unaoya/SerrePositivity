module

public import SerrePositivity.EInfinity.Hammock.FreeDiscreteEnrichment
public import SerrePositivity.EInfinity.Hammock.FreeHammockEnrichedUniversal
public import SerrePositivity.EInfinity.SimplicialLocalization.GeneratorPartition

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
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
namespace EnrichedFoldData
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D] (F : EnrichedFoldData W D)

def unmarkedPrefunctor : MarkedGenerators.quiver (GeneratorPartition.unmarked W) ⥤q
    ForgetEnrichment SSet.{u} D where
  obj X := ForgetEnrichment.of SSet.{u} (F.obj X)
  map {X Y} f := ForgetEnrichment.homOf SSet.{u} (F.generator ⟨⟨X, Y, f.val⟩, f.property⟩)

def unmarkedEnrichedFunctor :
    letI := DiscreteEnrichment.enrichedCategory
      (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
    EnrichedFunctor SSet.{u} (Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W))) D :=
  DiscreteEnrichment.liftFunctor (Paths.lift F.unmarkedPrefunctor)

lemma unmarkedEnrichedFunctor_generator (g : FactorTarget.Index W) :
    letI := DiscreteEnrichment.enrichedCategory
      (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
    DiscreteEnrichment.point
        (Quiver.Hom.toPath (show @Quiver.Hom
          (MarkedGenerators.quiver (GeneratorPartition.unmarked W)) _ g.val.left g.val.right from
            ⟨g.val.hom, g.property⟩)) ≫
      F.unmarkedEnrichedFunctor.map g.val.left g.val.right = F.generator g := by
  let := DiscreteEnrichment.enrichedCategory
    (C := Paths (MarkedGenerators.quiver (GeneratorPartition.unmarked W)))
  change DiscreteEnrichment.point _ ≫ DiscreteEnrichment.liftMap
    (Paths.lift F.unmarkedPrefunctor) g.val.left g.val.right = F.generator g
  rw [DiscreteEnrichment.liftMap_point, Paths.lift_toPath]
  rfl

end EnrichedFoldData
end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
