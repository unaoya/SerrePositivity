module

public import SerrePositivity.KST.Spectra.D3ProjectionStructureGraded
public import SerrePositivity.KST.Spectra.D3GradedWhiskeringHom

/-!
概要：元の共通右射影・BF 構造の指定関手同型で、段間構造の正方形を回収する。
方針：指定同型の端点正規化と前後合成の順射を、構成済み厳密変換の実現と照合する。
規約：同型の指定値を保持する。段の正方形を BF 全体の自然同型とは数えない。
使われ方：実 loop 図式の段比較と元の右射影の構造正方形の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3ProjectionIsoSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

private lemma d3ProjectionGraded_inv (n : ℕ) (X : CommonObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (StrictEnrichedTransformation.componentHom _ _
      (commonStageGradedProjection n) X)).toTruncated := by
  rw [commonStageGradedProjection_component]
  exact pointedKanObject_edge_isInvertible_of_piIsomorphism _ (commonProjection_levelwise X.val n)

private lemma d3StructureGraded_inv (n : ℕ) (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (StrictEnrichedTransformation.componentHom _ _
      (d3StageStructureGraded n) X)).toTruncated := by
  rw [d3StageStructureGraded_component]
  exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
    (KanSequence.adjointLoopTailUnit_levelwise X.toKanSequence_omega n)

/-- 既存の段右射影同型の順射は、同じ指定厳密変換の実現値。 -/
lemma commonStageLoopFunctorIso_hom_heq (n : ℕ) :
    HEq (commonStageLoopFunctorIso.{u} n).hom
      (d3GradedHom (commonStageLoopGradedProjection n)) := by
  unfold commonStageLoopFunctorIso
  apply HEq.trans (d3FunctorIsoOfEq_hom_heq _ _ _)
  exact (d3GradedHom_ofEq_heq (commonStageGradedProjection n) rfl
    (commonTargetStageKanEnriched_eq_loop n)).symm

/-- 既存段右射影同型の通常 loop 像も、同じ指定厳密変換の後合成の実現値。 -/
lemma commonStageLoopFunctorIso_postcomp_hom_heq (n : ℕ) :
    HEq ((commonStageLoopFunctorIso.{u} n).postcomp pointedKanLoopInfinity).hom
      (d3GradedHom (d3GradedPostcomp (commonStageLoopGradedProjection n)
        pointedKanLoopEnrichedFunctor)) := by
  unfold commonStageLoopFunctorIso
  apply HEq.trans (d3FunctorIsoOfEq_postcomp_hom_heq _ _ _ _)
  have h := d3GradedIso_postcomp_hom_heq (commonStageGradedProjection n)
    pointedKanLoopEnrichedFunctor (d3ProjectionGraded_inv n)
  exact h.trans (d3GradedHom_postcomp_ofEq_heq (commonStageGradedProjection n) rfl
    (commonTargetStageKanEnriched_eq_loop n) pointedKanLoopEnrichedFunctor).symm

/-- 既存の構造同型を同じ refined 関手へ前合成した順射の指定値を回収する。 -/
lemma commonRefinedStageStructureIso_hom_heq (n : ℕ) :
    HEq ((d3StageStructureFunctorIso.{u} n).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched)).hom
      (d3GradedHom (commonRefinedStageStructureGraded n)) := by
  unfold d3StageStructureFunctorIso
  apply HEq.trans (d3FunctorIsoOfEq_precomp_hom_heq _ _ _ _)
  have h := d3GradedIso_precomp_hom_heq commonRefinedEnriched (d3StageStructureGraded n)
    (d3StructureGraded_inv n)
  exact h.trans (d3GradedHom_ofEq_heq
    (d3GradedPrecomp commonRefinedEnriched (d3StageStructureGraded n)) rfl
    (d3EnrichedComp_assoc commonRefinedEnriched (d3StageKanEnriched (n + 1))
      pointedKanLoopEnrichedFunctor).symm).symm

/-- 既存次段構造同型の同じ元関手への前合成・通常 loop 後合成の指定値。 -/
lemma commonOriginalLoopStructureIso_hom_heq (n : ℕ) :
    HEq (((d3StageStructureFunctorIso.{u} (n + 1)).precomp commonOriginalInfinityMap).postcomp
      pointedKanLoopInfinity).hom (d3GradedHom (commonOriginalLoopStructureGraded n)) := by
  unfold d3StageStructureFunctorIso
  apply HEq.trans (d3FunctorIsoOfEq_precomp_postcomp_hom_heq _ _ _ _ _)
  have h := d3GradedIso_precomp_postcomp_hom_heq commonOriginalEnriched
    (d3StageStructureGraded (n + 1)) pointedKanLoopEnrichedFunctor (d3StructureGraded_inv (n + 1))
  exact h.trans (d3GradedHom_ofEq_heq (d3GradedPostcomp
    (d3GradedPrecomp commonOriginalEnriched (d3StageStructureGraded (n + 1)))
      pointedKanLoopEnrichedFunctor) rfl
    (congrArg (fun F ↦ F.comp SSet pointedKanLoopEnrichedFunctor)
      (d3EnrichedComp_assoc commonOriginalEnriched (d3StageKanEnriched (n + 2))
        pointedKanLoopEnrichedFunctor).symm)).symm

/-- 元の段右射影同型を、同じ厳密豊穣関手の端点表示に正規化する。 -/
def commonProjectionStructureQIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonRefinedStageKanEnriched.{u} n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 1))).comp
        SSet pointedKanLoopEnrichedFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (commonStageLoopFunctorIso n)
    (by rw [commonRefinedStageKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp])
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]; rfl)

/-- 元の refined 構造同型を、同じ厳密豊穣関手の端点表示に正規化する。 -/
def commonProjectionStructureRefinedIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonRefinedStageKanEnriched.{u} n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonRefinedStageKanEnriched (n + 1)).comp
        SSet pointedKanLoopEnrichedFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((d3StageStructureFunctorIso n).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched))
    (by rw [commonRefinedStageKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp])
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, commonRefinedStageKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
      Category.assoc]; rfl)

/-- 元の次段右射影の通常 loop 像を、同じ厳密豊穣関手の端点表示に正規化する。 -/
def commonProjectionStructureLoopQIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonRefinedStageKanEnriched.{u} (n + 1)).comp
      SSet pointedKanLoopEnrichedFunctor))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 2))).comp
        SSet pointedKanLoopEnrichedFunctor).comp SSet pointedKanLoopEnrichedFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((commonStageLoopFunctorIso (n + 1)).postcomp pointedKanLoopInfinity)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, commonRefinedStageKanEnriched, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]; rfl)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]; rfl)

/-- 元の次段構造同型の通常 loop 像を、同じ厳密豊穣関手の端点表示に正規化する。 -/
def commonProjectionStructureOriginalIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonOriginalEnriched.comp SSet
      (d3StageKanEnriched.{u} (n + 1))).comp SSet pointedKanLoopEnrichedFunctor))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 2))).comp
        SSet pointedKanLoopEnrichedFunctor).comp SSet pointedKanLoopEnrichedFunctor)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (((d3StageStructureFunctorIso (n + 1)).precomp commonOriginalInfinityMap).postcomp
      pointedKanLoopInfinity)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]; rfl)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
      Category.assoc]; rfl)

lemma commonProjectionStructureQIso_hom (n : ℕ) :
    (commonProjectionStructureQIso.{u} n).hom =
      d3GradedHom (commonStageLoopGradedProjection n) := by
  unfold commonProjectionStructureQIso
  exact eq_of_heq ((d3FunctorIsoOfEq_hom_heq _ _ _).trans (commonStageLoopFunctorIso_hom_heq n))

lemma commonProjectionStructureRefinedIso_hom (n : ℕ) :
    (commonProjectionStructureRefinedIso.{u} n).hom =
      d3GradedHom (commonRefinedStageStructureGraded n) := by
  unfold commonProjectionStructureRefinedIso
  exact eq_of_heq ((d3FunctorIsoOfEq_hom_heq _ _ _).trans
    (commonRefinedStageStructureIso_hom_heq n))

lemma commonProjectionStructureLoopQIso_hom (n : ℕ) :
    (commonProjectionStructureLoopQIso.{u} n).hom =
      d3GradedHom (d3GradedPostcomp (commonStageLoopGradedProjection (n + 1))
        pointedKanLoopEnrichedFunctor) := by
  unfold commonProjectionStructureLoopQIso
  exact eq_of_heq ((d3FunctorIsoOfEq_hom_heq _ _ _).trans
    (commonStageLoopFunctorIso_postcomp_hom_heq (n + 1)))

lemma commonProjectionStructureOriginalIso_hom (n : ℕ) :
    (commonProjectionStructureOriginalIso.{u} n).hom =
      d3GradedHom (commonOriginalLoopStructureGraded n) := by
  unfold commonProjectionStructureOriginalIso
  exact eq_of_heq ((d3FunctorIsoOfEq_hom_heq _ _ _).trans
    (commonOriginalLoopStructureIso_hom_heq n))

/-- 元の右射影・BF 構造の指定関手同型は、同じ全関手空間の構造正方形を満たす。 -/
lemma commonProjectionStructureIso_square (n : ℕ) :
    commonProjectionStructureQIso.{u} n ≪≫ commonProjectionStructureOriginalIso n =
      commonProjectionStructureRefinedIso n ≪≫ commonProjectionStructureLoopQIso n := by
  apply Iso.ext
  simp only [Iso.trans_hom, commonProjectionStructureQIso_hom,
    commonProjectionStructureOriginalIso_hom, commonProjectionStructureRefinedIso_hom,
    commonProjectionStructureLoopQIso_hom]
  exact commonProjectionStructureHom_square n

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
