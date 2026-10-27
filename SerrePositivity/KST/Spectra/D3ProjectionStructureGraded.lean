module

public import SerrePositivity.KST.Spectra.D3StageLoopImageComparison
public import SerrePositivity.KST.Spectra.D3GradedCompositionNerve

/-!
概要：共通 BF 右射影の構造条件を、同じ全 Hom の厳密豊穣変換の正方形へ束ねる。
方針：既存の右射影・構造変換へ前後合成と縦合成を施し、元の列射条件で比較する。
規約：普通の loop と元の構造随伴射を保持し、円交換因子を比較しない。
使われ方：段の右射影比較と実図式比較を、BF 全体の構造整合へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3ProjectionStructureSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ次段通常 loop 作用を終点とする、元の右射影の厳密変換。 -/
def commonStageLoopGradedProjection (n : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (commonRefinedStageKanEnriched n)
      ((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 1))).comp SSet
        pointedKanLoopEnrichedFunctor) :=
  d3GradedOfEq (commonStageGradedProjection n) rfl (commonTargetStageKanEnriched_eq_loop n)

/-- 同じ元の右射影の通常の段成分を回収する。 -/
lemma commonStageLoopGradedProjection_component (n : ℕ) (X : CommonObject.{u}) :
    StrictEnrichedTransformation.componentHom _ _ (commonStageLoopGradedProjection n) X =
      ObjectProperty.homMk ((commonProjection X.val).app n) := by
  exact eq_of_heq ((d3GradedOfEq_component_heq (commonStageGradedProjection n) rfl
    (commonTargetStageKanEnriched_eq_loop n) X).trans
      (heq_of_eq (commonStageGradedProjection_component n X)))

/-- 三つの豊穣関手の括弧だけを厳密に正規化する。 -/
lemma d3EnrichedComp_assoc {C D E F : Type (u + 1)}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    [EnrichedCategory SSet.{u} E] [EnrichedCategory SSet.{u} F]
    (a : EnrichedFunctor SSet.{u} C D) (b : EnrichedFunctor SSet.{u} D E)
    (c : EnrichedFunctor SSet.{u} E F) :
    (a.comp SSet b).comp SSet c = a.comp SSet (b.comp SSet c) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id, Category.assoc]

/-- 元の段間構造を同じ共通 refined 全 Hom へ前合成した厳密変換。 -/
def commonRefinedStageStructureGraded (n : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (commonRefinedStageKanEnriched n)
      ((commonRefinedStageKanEnriched (n + 1)).comp SSet pointedKanLoopEnrichedFunctor) := by
  exact d3GradedOfEq
    (d3GradedPrecomp commonRefinedEnriched (d3StageStructureGraded.{u} n)) rfl
    (d3EnrichedComp_assoc commonRefinedEnriched (d3StageKanEnriched (n + 1))
      pointedKanLoopEnrichedFunctor).symm

/-- 元の次段構造へ同じ通常 loop を施し、共通元作用へ前合成した厳密変換。 -/
def commonOriginalLoopStructureGraded (n : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      ((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 1))).comp SSet
        pointedKanLoopEnrichedFunctor)
      (((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 2))).comp SSet
        pointedKanLoopEnrichedFunctor).comp SSet pointedKanLoopEnrichedFunctor) := by
  exact d3GradedOfEq (d3GradedPostcomp
    (d3GradedPrecomp commonOriginalEnriched (d3StageStructureGraded.{u} (n + 1)))
      pointedKanLoopEnrichedFunctor) rfl
    (congrArg (fun F ↦ F.comp SSet pointedKanLoopEnrichedFunctor)
      (d3EnrichedComp_assoc commonOriginalEnriched (d3StageKanEnriched (n + 2))
        pointedKanLoopEnrichedFunctor).symm)

/-- 右射影から同じ元の次段 loop 構造へ進む、全 Hom の厳密変換。 -/
def commonProjectionStructureLeftGraded (n : ℕ) :=
  d3GradedComp (commonStageLoopGradedProjection.{u} n) (commonOriginalLoopStructureGraded n)

/-- refined 構造から同じ次段右射影の loop へ進む、全 Hom の厳密変換。 -/
def commonProjectionStructureRightGraded (n : ℕ) :=
  d3GradedComp (commonRefinedStageStructureGraded.{u} n)
    (d3GradedPostcomp (commonStageLoopGradedProjection (n + 1)) pointedKanLoopEnrichedFunctor)

/-- refined 構造変換の指定成分は、元の同じ構造随伴射。 -/
lemma commonRefinedStageStructureGraded_component (n : ℕ) (X : CommonObject.{u}) :
    StrictEnrichedTransformation.componentHom _ _ (commonRefinedStageStructureGraded n) X =
      ObjectProperty.homMk
        ((KanSequence.adjointLoopTailUnit (commonRefinement X.val).toKanSequence).app n) := by
  have h := d3GradedOfEq_component_heq
    (d3GradedPrecomp commonRefinedEnriched (d3StageStructureGraded.{u} n)) rfl
    (d3EnrichedComp_assoc commonRefinedEnriched (d3StageKanEnriched (n + 1))
      pointedKanLoopEnrichedFunctor).symm X
  exact eq_of_heq (h.trans (heq_of_eq
    (d3StageStructureGraded_component n (commonRefinement X.val))))

/-- 通常 loop の同じ後合成の成分を、元の点つき射の loop として回収する。 -/
lemma d3LoopGraded_component {F G : EnrichedFunctor SSet.{u} CommonObject PointedKanObject.{u}}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) (X : CommonObject.{u}) :
    (StrictEnrichedTransformation.componentHom _ _
      (d3GradedPostcomp η pointedKanLoopEnrichedFunctor) X).hom =
    (ihom PointedSimplicialSet.circle.{u}).map
      (StrictEnrichedTransformation.componentHom F G η X).hom := by
  rw [d3GradedPostcomp_component]
  exact pointedKanLoopFunctor_map_hom _

/-- 同じ元の次段構造の loop を、指定変換の実成分として回収する。 -/
lemma commonOriginalLoopStructureGraded_component (n : ℕ) (X : CommonObject.{u}) :
    (StrictEnrichedTransformation.componentHom _ _ (commonOriginalLoopStructureGraded n) X).hom =
      (ihom PointedSimplicialSet.circle.{u}).map
        ((KanSequence.adjointLoopTailUnit X.val.toKanSequence).app (n + 1)) := by
  have h := d3GradedOfEq_component_heq (d3GradedPostcomp
    (d3GradedPrecomp commonOriginalEnriched (d3StageStructureGraded.{u} (n + 1)))
      pointedKanLoopEnrichedFunctor) rfl
    (congrArg (fun F ↦ F.comp SSet pointedKanLoopEnrichedFunctor)
      (d3EnrichedComp_assoc commonOriginalEnriched (d3StageKanEnriched (n + 2))
        pointedKanLoopEnrichedFunctor).symm) X
  have hc := eq_of_heq h
  unfold commonOriginalLoopStructureGraded
  rw [hc, d3LoopGraded_component]
  change (ihom PointedSimplicialSet.circle.{u}).map
    (StrictEnrichedTransformation.componentHom _ _
      (d3StageStructureGraded (n + 1)) X.val).hom = _
  rw [d3StageStructureGraded_component]
  rfl

/-- 右射影と元の構造の厳密可換性を、全 Hom を持つ二つの豊穣変換の等式へ束ねる。 -/
lemma commonProjectionStructureGraded_square (n : ℕ) :
    commonProjectionStructureLeftGraded.{u} n = commonProjectionStructureRightGraded n := by
  apply d3Graded_ext
  intro X
  apply ObjectProperty.hom_ext
  dsimp only [commonProjectionStructureLeftGraded, commonProjectionStructureRightGraded]
  rw [d3GradedComp_component, d3GradedComp_component]
  change (StrictEnrichedTransformation.componentHom _ _ (commonStageLoopGradedProjection n) X).hom ≫
      (StrictEnrichedTransformation.componentHom _ _ (commonOriginalLoopStructureGraded n) X).hom =
    (StrictEnrichedTransformation.componentHom _ _ (commonRefinedStageStructureGraded n) X).hom ≫
      (StrictEnrichedTransformation.componentHom _ _
        (d3GradedPostcomp (commonStageLoopGradedProjection (n + 1))
          pointedKanLoopEnrichedFunctor) X).hom
  rw [commonStageLoopGradedProjection_component, commonOriginalLoopStructureGraded_component,
    commonRefinedStageStructureGraded_component, d3LoopGraded_component,
    commonStageLoopGradedProjection_component]
  exact commonProjection_structure X.val n

/-- 同じ右射影の構造正方形は、coherent な全関手空間の射としても厳密に可換。 -/
lemma commonProjectionStructureHom_square (n : ℕ) :
    d3GradedHom (commonStageLoopGradedProjection.{u} n) ≫
      d3GradedHom (commonOriginalLoopStructureGraded n) =
    d3GradedHom (commonRefinedStageStructureGraded n) ≫
      d3GradedHom (d3GradedPostcomp (commonStageLoopGradedProjection (n + 1))
        pointedKanLoopEnrichedFunctor) := by
  rw [d3GradedHom_comp, d3GradedHom_comp]
  change d3GradedHom (commonProjectionStructureLeftGraded n) =
    d3GradedHom (commonProjectionStructureRightGraded n)
  rw [commonProjectionStructureGraded_square]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
