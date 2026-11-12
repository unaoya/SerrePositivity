module

public import SerrePositivity.KST.Spectra.D3StageEvaluation

/-!
概要：共通 BF 右射影を、全 Hom 上の各段の実関手同型へ移す。
方針：同じ比較右脚と元の q の全 Hom 正方形を縦に合成する。
規約：各段の全関手比較。これだけから実 loop 始点との BF 全関手同型を推論しない。
使われ方：d3b② の元の補助標的を保持した自然性比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3ProjectionStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance d3ProjectionStagePointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- 全パラメータの二つの指定正方形を縦に合成する。 -/
lemma d3PointedSquare_vertical {P : SSet.{u}} {A B C A' B' C' : PointedSimplicialSet.{u}}
    (a : A ⟶ B) (b : A' ⟶ B') (c : B ⟶ C) (d : B' ⟶ C')
    (f : P ⟶ SimplicialCategory.sHom A A')
    (g : P ⟶ SimplicialCategory.sHom B B')
    (h : P ⟶ SimplicialCategory.sHom C C')
    (hf : f ≫ eHomWhiskerLeft SSet A b = g ≫ eHomWhiskerRight SSet a B')
    (hg : g ≫ eHomWhiskerLeft SSet B d = h ≫ eHomWhiskerRight SSet c C') :
    f ≫ eHomWhiskerLeft SSet A (b ≫ d) =
      h ≫ eHomWhiskerRight SSet (a ≫ c) C' := by
  rw [eHomWhiskerLeft_comp, ← Category.assoc, hf, Category.assoc,
    ← eHom_whisker_exchange, ← Category.assoc, hg, Category.assoc,
    ← eHomWhiskerRight_comp]

/-- 共通 BF 対象を元の全 Hom 作用で段評価する。 -/
def commonRefinedStageKanEnriched (n : ℕ) :
    EnrichedFunctor SSet.{u} CommonObject PointedKanObject.{u} :=
  commonRefinedEnriched.comp SSet (d3StageKanEnriched n)

/-- 同じ元の全 Hom に対する、補助標的の同じ段の通常 loop 作用。 -/
def commonTargetStageKanEnriched (n : ℕ) :
    EnrichedFunctor SSet.{u} CommonObject PointedKanObject.{u} :=
  d3KanEnrichedLift (commonBaseEnriched.comp SSet (fullTargetStageEnriched n))
    (fun X ↦ ((target X.val).level n).kan)

/-- 同じ共通右射影の段成分を、元の二つの段射の合成として固定する。 -/
lemma commonProjection_app (X : OmegaSpectrum.{u}) (n : ℕ) :
    (commonProjection X).app n =
      (commonComparison X).app n ≫ (projection X).app n := rfl

/-- 同じ比較右脚の全 Hom 可換性を、元の段射へ厳密に評価する。 -/
lemma commonComparison_stage_whiskered (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (commonRefinedMap X Y ≫ evaluation (commonRefinement X) (commonRefinement Y) n) ≫
        eHomWhiskerLeft SSet ((commonRefinement X).level n).space
          ((commonComparison Y).app n) =
      (commonMiddleMap X Y ≫ evaluation (middle X) (middle Y) n) ≫
        eHomWhiskerRight SSet ((commonComparison X).app n) ((middle Y).level n).space := by
  have h := congrArg (· ≫ evaluation (commonRefinement X) (middle Y) n)
    (common_right_whiskered X Y)
  simpa only [Category.assoc, d3Stage_post, d3Stage_pre] using h

/-- 共通右射影は、全 Hom 上で元の補助標的の段作用と厳密に可換。 -/
lemma commonProjection_stage_whiskered (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (commonRefinedMap X Y ≫ evaluation (commonRefinement X) (commonRefinement Y) n) ≫
        eHomWhiskerLeft SSet ((commonRefinement X).level n).space
          ((commonProjection Y).app n) =
      (commonBaseMap X Y ≫ fullOriginalLoopStage X Y n) ≫
        eHomWhiskerRight SSet ((commonProjection X).app n) ((target Y).level n).space := by
  have hq := congrArg (commonBaseMap X Y ≫ ·) (full_right_whiskered X Y n).symm
  have hq' : (commonMiddleMap X Y ≫ evaluation (middle X) (middle Y) n) ≫
      eHomWhiskerLeft SSet ((middle X).level n).space ((projection Y).app n) =
      (commonBaseMap X Y ≫ fullOriginalLoopStage X Y n) ≫
        eHomWhiskerRight SSet ((projection X).app n) ((target Y).level n).space := by
    simpa only [commonMiddleMap, fullReplacedStage, Category.assoc] using hq
  rw [commonProjection_app, commonProjection_app]
  exact d3PointedSquare_vertical ((commonComparison X).app n) ((commonComparison Y).app n)
    ((projection X).app n) ((projection Y).app n) _ _ _
    (commonComparison_stage_whiskered X Y n) hq'

/-- 元の共通右射影の全段 π 同型。 -/
lemma commonProjection_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((commonProjection X).app n).right :=
  (commonComparison_levelwise X n).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (projection_rlp X n))

/-- 同じ元の右射影を成分とする、各段の厳密豊穣自然変換。 -/
def commonStageGradedProjection (n : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (commonRefinedStageKanEnriched n) (commonTargetStageKanEnriched n) where
  app X := eHomEquiv SSet (ObjectProperty.homMk ((commonProjection X.val).app n))
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff SSet
    ((commonProjection X.val).app n) ((commonProjection Y.val).app n)
    (commonBaseMap X.val Y.val ≫ fullOriginalLoopStage X.val Y.val n)
    (commonRefinedMap X.val Y.val ≫ evaluation (commonRefinement X.val)
      (commonRefinement Y.val) n)).mp (commonProjection_stage_whiskered X.val Y.val n).symm).symm

/-- coherent な変換の成分は元の共通右射影の同じ段射そのもの。 -/
lemma commonStageGradedProjection_component (n : ℕ) (X : CommonObject.{u}) :
    StrictEnrichedTransformation.componentHom
      (commonRefinedStageKanEnriched n) (commonTargetStageKanEnriched n)
      (commonStageGradedProjection n) X =
        ObjectProperty.homMk ((commonProjection X.val).app n) := by
  change (SimplicialCategory.homEquiv' _ _).symm
    ((SSet.unitHomEquiv _) (eHomEquiv SSet
      (ObjectProperty.homMk ((commonProjection X.val).app n) :
        (commonRefinedStageKanEnriched n).obj X ⟶ (commonTargetStageKanEnriched n).obj X))) = _
  exact Equiv.symm_apply_apply _ _

/-- 指定共通右射影そのものを成分に持つ、各段の全関手同型。 -/
def commonStageProjectionFunctorIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonRefinedStageKanEnriched n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonTargetStageKanEnriched n)) :=
  StrictEnrichedTransformation.functorIso _ _ (commonStageGradedProjection n) (fun X ↦ by
    rw [commonStageGradedProjection_component]
    exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
      (commonProjection_levelwise X.val n))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
