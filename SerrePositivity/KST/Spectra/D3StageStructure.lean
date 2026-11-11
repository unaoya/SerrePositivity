module

public import SerrePositivity.KST.Spectra.D3CommonStageSourceComparison

/-!
概要：元の BF 構造随伴射を、全 Hom 上の段間の豊穣自然性へ束ねる。
方針：指定共通包含と指定右射影の実正方形を合成し、実 Hom 射影の切断で消去する。
規約：元の構造随伴射を成分として保持。円交換因子の直接比較は行わない。
使われ方：実段 loop 図式の比較を、元の段間 BF 構造へ接続する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3StructureSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance d3StructurePointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory
attribute [local irreducible] commonRefinement

/-- 同じ共通左包含の全 Hom 自然性を、元の段で厳密に評価する。 -/
lemma commonInclusion_stage_whiskered (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (commonOriginalMap X Y ≫ evaluation X Y n) ≫
      eHomWhiskerLeft SSet (X.level n).space ((commonInclusion Y).app n) =
        (commonRefinedMap X Y ≫ evaluation (commonRefinement X) (commonRefinement Y) n) ≫
          eHomWhiskerRight SSet ((commonInclusion X).app n)
            ((commonRefinement Y).level n).space := by
  have h := congrArg (· ≫ evaluation X (commonRefinement Y) n) (common_left_whiskered X Y).symm
  simpa only [Category.assoc, d3Stage_post, d3Stage_pre] using h

/-- 共通二因子の同じ自然性を合成すると、元の BF 構造随伴射を全 Hom で回収する。 -/
lemma commonStructure_stage_whiskered (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (commonOriginalMap X Y ≫ evaluation X Y n) ≫
      eHomWhiskerLeft SSet (X.level n).space
        ((KanSequence.adjointLoopTailUnit Y.toKanSequence).app n) =
      (commonBaseMap X Y ≫ fullOriginalLoopStage X Y n) ≫
        eHomWhiskerRight SSet ((KanSequence.adjointLoopTailUnit X.toKanSequence).app n)
          ((target Y).level n).space := by
  have h := d3PointedSquare_vertical
    ((commonInclusion X).app n) ((commonInclusion Y).app n)
    ((commonProjection X).app n) ((commonProjection Y).app n) _ _ _
    (commonInclusion_stage_whiskered X Y n) (commonProjection_stage_whiskered X Y n)
  simpa only [commonProjection_fac] using h

/-- 元の Hom 射影の実切断による消去で、同じ構造射の全 Hom 自然性を回収する。 -/
lemma d3StageStructure_raw (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    evaluation X Y n ≫ eHomWhiskerLeft SSet (X.level n).space
      ((KanSequence.adjointLoopTailUnit Y.toKanSequence).app n) =
    (evaluation X Y (n + 1) ≫
      (PointedMapping.ihomSimplicialFunctor PointedSimplicialSet.circle.{u}).map
        (X.level (n + 1)).space (Y.level (n + 1)).space) ≫
      eHomWhiskerRight SSet ((KanSequence.adjointLoopTailUnit X.toKanSequence).app n)
        ((target Y).level n).space := by
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (commonOriginalMap X Y)
  have : IsSplitEpi (commonOriginalMap X Y) := IsSplitEpi.mk' ⟨s, hs⟩
  apply (cancel_epi (commonOriginalMap X Y)).mp
  have h := commonStructure_stage_whiskered X Y n
  simpa only [commonOriginalMap, fullOriginalLoopStage, Category.assoc] using h

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
