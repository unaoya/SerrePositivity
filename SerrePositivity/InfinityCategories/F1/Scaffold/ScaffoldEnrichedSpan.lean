module

public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplicialOverCategory
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldEnrichedNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportKanDiagramInclusion
public import SerrePositivity.InfinityCategories.F1.Scaffold.LeftScaffoldComparison

/-!
概要：strict transport の復元 span を、全相対 Hom に自然な二つの豊穣比較として束ねる。
方針：replacement と weighted nerve の実際の Hom の作用に scaffold の可換式を使う。
規約：共通始域の射影に left fibration 性を要求せず、各脚の前合成同値性を別に証明する。
使われ方：対象ごとに選んだ復元射の代わりとなる、全高次の自然な復元データ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- replacement は全 Kan 値通常図式から底上の全単体集合への豊穣関手。 -/
def simplicialReplacementOverEnriched (C : Type u) [Category.{u} C] :
    EnrichedFunctor SSet.{u} (KanDiagramObject C) (SimplicialOverObject (nerve C)) where
  obj F := ⟨Over.mk (simplicialReplacementProjection (F.val ⋙ kanObjectForget)), trivial⟩
  map F G := simplicialReplacementMappingSpaceMap
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)
  map_id _F := simplicialReplacementMappingSpaceMap_identity _
  map_comp _F _G _H := simplicialReplacementMappingSpaceMap_composition _ _ _

/-- 全 left fibrations に対する復元の共通始域の豊穣的な族。 -/
def strictTransportReplacementOverEnriched (C : Type u) [Category.{u} C] :
    EnrichedFunctor SSet.{u} (LeftFibrationObject (nerve C)) (SimplicialOverObject (nerve C)) :=
  ((leftStrictTransportEnriched (C := C)).comp SSet strictTransportKanDiagramEnriched).comp SSet
    (simplicialReplacementOverEnriched C)

/-- strict transport の weighted nerve の全対象の豊穣的な族。 -/
def strictTransportWeightedOverEnriched (C : Type u) [Category.{u} C] :
    EnrichedFunctor SSet.{u} (LeftFibrationObject (nerve C)) (SimplicialOverObject (nerve C)) :=
  (((leftStrictTransportEnriched (C := C)).comp SSet strictTransportKanDiagramEnriched).comp SSet
    (weightedNerveKanEnriched C)).comp SSet (leftFibrationOverEnriched (nerve C))

/-- universal scaffold は共通始域から元の fibration への、全高次に自然な比較。 -/
def universalScaffoldOverComparison (C : Type u) [Category.{u} C] :
    SimplicialOverComparison (strictTransportReplacementOverEnriched C)
      (leftFibrationOverEnriched (nerve C)) := by
  refine ⟨fun p ↦ Over.homMk (universalScaffold p.val.hom)
    (universalScaffold_projection p.val.hom), ?_⟩
  intro p q
  change (leftStrictTransportMappingSpaceMap p.val.hom q.val.hom ≫
    simplicialReplacementMappingSpaceMap _ _) ≫ HomotopyLimits.relativeFunctorPost
      (simplicialReplacementProjection (leftStrictTransportDiagram q.val.hom)) q.val.hom
      (universalScaffold q.val.hom) (universalScaffold_projection q.val.hom)
      (simplicialReplacementProjection (leftStrictTransportDiagram p.val.hom)) =
    (𝟙 _) ≫ relativeFunctorOverPre q.val.hom
      (Over.homMk (U := Over.mk (simplicialReplacementProjection
        (leftStrictTransportDiagram p.val.hom))) (V := Over.mk p.val.hom)
        (universalScaffold p.val.hom) (universalScaffold_projection p.val.hom))
  rw [Category.id_comp, Category.assoc, simplicialReplacementMappingSpaceMap_scaffold,
    leftStrictTransportMappingSpaceMap_scaffold]

/-- taut scaffold は同じ共通始域から weighted nerve への、全高次に自然な比較。 -/
def tautScaffoldOverComparison (C : Type u) [Category.{u} C] :
    SimplicialOverComparison (strictTransportReplacementOverEnriched C)
      (strictTransportWeightedOverEnriched C) := by
  refine ⟨fun p ↦ Over.homMk (tautScaffold (leftStrictTransportDiagram p.val.hom))
    (tautScaffold_projection (leftStrictTransportDiagram p.val.hom)), ?_⟩
  intro p q
  change (leftStrictTransportMappingSpaceMap p.val.hom q.val.hom ≫
    simplicialReplacementMappingSpaceMap _ _) ≫ HomotopyLimits.relativeFunctorPost
      (simplicialReplacementProjection (leftStrictTransportDiagram q.val.hom))
      (weightedNerveProjection (leftStrictTransportDiagram q.val.hom))
      (tautScaffold (leftStrictTransportDiagram q.val.hom))
      (tautScaffold_projection (leftStrictTransportDiagram q.val.hom))
      (simplicialReplacementProjection (leftStrictTransportDiagram p.val.hom)) =
    (leftStrictTransportMappingSpaceMap p.val.hom q.val.hom ≫
      weightedNerveMappingSpaceMap _ _ ≫ 𝟙 _) ≫
      relativeFunctorOverPre (weightedNerveProjection (leftStrictTransportDiagram q.val.hom))
        (Over.homMk (U := Over.mk (simplicialReplacementProjection
          (leftStrictTransportDiagram p.val.hom)))
          (V := Over.mk (weightedNerveProjection (leftStrictTransportDiagram p.val.hom)))
          (tautScaffold (leftStrictTransportDiagram p.val.hom))
          (tautScaffold_projection (leftStrictTransportDiagram p.val.hom)))
  rw [Category.comp_id, Category.assoc, tautScaffold_mappingSpaceMap, Category.assoc]

/-- 自然な復元 span の universal 側の各脚は、実際の前合成同値。 -/
lemma universalScaffoldOverComparison_isPrecompositionEquivalence
    (C : Type u) [Category.{u} C] (p : LeftFibrationObject (nerve C)) :
    IsPrecompositionEquivalence (((universalScaffoldOverComparison C).val p).left) :=
  universalScaffold_isPrecompositionEquivalence p.val.hom

/-- 同じ自然な復元 span の taut 側の各脚も、実際の前合成同値。 -/
lemma tautScaffoldOverComparison_isPrecompositionEquivalence
    (C : Type u) [Category.{u} C] (p : LeftFibrationObject (nerve C)) :
    IsPrecompositionEquivalence (((tautScaffoldOverComparison C).val p).left) :=
  tautScaffold_isPrecompositionEquivalence (leftStrictTransportDiagram p.val.hom)

end SerrePositivity.InfinityCategories
