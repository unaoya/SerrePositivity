module

public import SerrePositivity.KST.Spectra.D3CommonStageStructure
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の構造随伴射を成分とする、BF 段評価と次段 loop 評価の全関手同型。
方針：全 Hom 正方形を実豊穣自然変換へ束ね、元の Ω 条件で同じ辺の可逆性を認証する。
規約：同型成分を自由に選び直さず、元の BF 構造射そのものを使用する。
使われ方：実 loop 四角形全族の段間構造の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3StructureFunctorSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance d3StructureFunctorPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- 元の次段評価に通常の点つき Kan loop を施した全豊穣作用。 -/
def d3StageLoopKanEnriched (n : ℕ) :
    EnrichedFunctor SSet.{u} OmegaSpectrum.{u} PointedKanObject.{u} :=
  (d3StageKanEnriched (n + 1)).comp SSet pointedKanLoopEnrichedFunctor

/-- 次段 loop の同じ全 Hom 作用を、元の点つき作用へ厳密に戻す。 -/
lemma d3StageLoopKanEnriched_map (n : ℕ) (X Y : OmegaSpectrum.{u}) :
    (d3StageLoopKanEnriched n).map X Y = evaluation X Y (n + 1) ≫
      (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
        (X.level (n + 1)).space (Y.level (n + 1)).space := by
  have h := d3Stage_loop_action ((d3StageKanEnriched (n + 1)).obj X)
    ((d3StageKanEnriched (n + 1)).obj Y)
  change (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
    (X.level (n + 1)).space (Y.level (n + 1)).space = _ at h
  exact congrArg (evaluation X Y (n + 1) ≫ ·) h.symm

/-- 元の BF 構造随伴射そのものを成分とする実豊穣自然変換。 -/
def d3StageStructureGraded (n : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (d3StageKanEnriched n) (d3StageLoopKanEnriched n) where
  app X := eHomEquiv SSet
    (ObjectProperty.homMk ((KanSequence.adjointLoopTailUnit X.toKanSequence).app n))
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff SSet
    ((KanSequence.adjointLoopTailUnit X.toKanSequence).app n)
    ((KanSequence.adjointLoopTailUnit Y.toKanSequence).app n)
    ((d3StageLoopKanEnriched n).map X Y) ((d3StageKanEnriched n).map X Y)).mp
      (by
        rw [d3StageLoopKanEnriched_map]
        exact (d3StageStructure_raw X Y n).symm)).symm

/-- 同じ coherent 変換の成分も、元の BF 構造随伴射そのもの。 -/
lemma d3StageStructureGraded_component (n : ℕ) (X : OmegaSpectrum.{u}) :
    StrictEnrichedTransformation.componentHom (d3StageKanEnriched n)
      (d3StageLoopKanEnriched n) (d3StageStructureGraded n) X =
        ObjectProperty.homMk ((KanSequence.adjointLoopTailUnit X.toKanSequence).app n) := by
  change (SimplicialCategory.homEquiv' _ _).symm
    ((SSet.unitHomEquiv _) (eHomEquiv SSet
      (ObjectProperty.homMk ((KanSequence.adjointLoopTailUnit X.toKanSequence).app n) :
        (d3StageKanEnriched n).obj X ⟶ (d3StageLoopKanEnriched n).obj X))) = _
  exact Equiv.symm_apply_apply _ _

/-- 同じ元の Ω 条件により、構造随伴射を成分とする全関手同型を得る。 -/
def d3StageStructureFunctorIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched.{u} n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched (n + 1)) ≫ pointedKanLoopInfinity) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (StrictEnrichedTransformation.functorIso _ _ (d3StageStructureGraded.{u} n)
    (fun X ↦ by
      rw [d3StageStructureGraded_component]
      exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
        (KanSequence.adjointLoopTailUnit_levelwise X.toKanSequence_omega n))) rfl
    (by
      rw [d3StageLoopKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
      rfl)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
