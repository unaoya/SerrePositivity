module

public import SerrePositivity.KST.Spectra.D3StageReflectedStructureCriterion

/-!
概要：実全図式反転を奇数段に保つ、共通 refined／実始点の段比較を構成する。
方針：同じ段比較と反転を合成し、次段の実 loop 像と構造正方形を指定値で照合する。
規約：転置模型の単位整合は未証明。段比較を BF 全体の FunctorIso と取り違えない。
使われ方：正しい補正を保持する B の候補で、残る全段構造条件を同じ三角形に帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra

private lemma d3AlternatingIso_normalize_trans {A X : SSet.{u}}
    {f g h f' g' h' : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h)
    (hf : f = f') (hg : g = g') (hh : h = h') :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e ≪≫ d) hf hh =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d hg hh := by
  subst f' g' h'
  rfl

private lemma d3Iso_right_involution_iff {C : Type v} [Category C]
    {a b : C} (x y : a ≅ b) (ρ : b ≅ b) (hρ : ρ ≪≫ ρ = Iso.refl _) :
    x ≪≫ ρ = y ↔ x = y ≪≫ ρ := by
  constructor
  · intro h
    have hh := congrArg (fun e ↦ e ≪≫ ρ) h
    simpa only [Iso.trans_assoc, hρ, Iso.trans_refl] using hh
  · intro h
    rw [h, Iso.trans_assoc, hρ, Iso.trans_refl]

namespace OmegaSpectrum.AdjointLoopRelativeBF
local instance d3AlternatingSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 偶数段は元の同じ比較、奇数段は同じ実全図式反転を保った比較。 -/
def commonChosenStageAlternatingSourceIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (commonRefinedStageKanEnriched.{u} n))
      (commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  if Even n then commonChosenStageRefinedSourceNormalizedIso n
  else commonChosenStageRefinedSourceNormalizedIso n ≪≫ commonChosenStageReflection n

/-- 実際に構成した同じ次段比較へ通常 loop を施し、同じ実像へ端点だけ正規化する。 -/
def commonChosenStageAlternatingLoopSourceIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((commonRefinedStageKanEnriched.{u} (n + 1)).comp
      SSet pointedKanLoopEnrichedFunctor))
      (commonChosenStageLoopImageFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((commonChosenStageAlternatingSourceIso (n + 1)).postcomp
    pointedKanLoopInfinity) (commonChosenStageRefinedLoopSource_enriched n)
      (commonChosenStageLoopImageFamily_corner n 0 0).symm

/-- 次段比較の loop 像も、元の実次段像の指定反転だけを同じ偶奇で保持する。 -/
lemma commonChosenStageAlternatingLoopSourceIso_eq (n : ℕ) :
    commonChosenStageAlternatingLoopSourceIso.{u} n =
    if Even (n + 1) then commonChosenStageLoopedRefinedSourceIso n
    else commonChosenStageLoopedRefinedSourceIso n ≪≫ commonChosenStageImageReflection n := by
  unfold commonChosenStageAlternatingLoopSourceIso commonChosenStageAlternatingSourceIso
  split_ifs
  · rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, d3AlternatingIso_normalize_trans _ _ _
      (commonChosenStageLoopImageFamily_corner n 0 0).symm,
      commonChosenStageImageReflection_loop]
    rfl

/-- 同じ実次段像の反転も、全関手空間で二回合成が恒等になる。 -/
lemma commonChosenStageImageReflection_involution (n : ℕ) :
    commonChosenStageImageReflection.{u} n ≪≫ commonChosenStageImageReflection n =
      Iso.refl _ := by
  have h := congrArg (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e (commonChosenStageLoopImageFamily.{u} n))
    (d3LoopDiagramReflection_involution d3PointedKanLoopSection d3PointedKanLoopSection_target)
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans] at h
  have hr : (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity.{u} 0 0)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) from Iso.refl _).precomp
        (commonChosenStageLoopImageFamily n) = Iso.refl _ := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
    exact Functor.mapIso_refl _ _
  rw [hr] at h
  exact h

/-- 実際の補正済み段比較と同じ次段比較の loop 像との構造整合は、転置模型の単位条件。
条件自体と BF 全体の自然同型は未供給であり、全段の判定だけを実証する。 -/
lemma commonChosenStageAlternatingSource_structure_iff (n : ℕ) :
    (commonChosenStageAlternatingSourceIso.{u} n ≪≫
      (commonChosenStageStructureDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    commonProjectionStructureRefinedIso n ≪≫ commonChosenStageAlternatingLoopSourceIso n) ↔
    commonChosenStageLoopedCanonicalUnitIso.{u} n ≪≫
      commonChosenStageLoopReflectedSourceIso n = commonChosenStageCanonicalImageUnitIso n := by
  rw [commonChosenStageAlternatingLoopSourceIso_eq]
  unfold commonChosenStageAlternatingSourceIso
  by_cases hn : Even n
  · have hn' : ¬Even (n + 1) := by simpa only [Nat.even_add_one, not_not] using hn
    simpa only [ite_eq_left hn, ite_eq_right hn'] using
      (commonChosenStageRefinedSource_reflected_structure_iff.{u} n)
  · have hn' : Even (n + 1) := Nat.even_add_one.mpr hn
    simp only [ite_eq_right hn, ite_eq_left hn']
    have hs := commonChosenStageReflection_structure.{u} n
    rw [commonChosenStageImageReflection_loop] at hs
    rw [Iso.trans_assoc, ← hs, ← Iso.trans_assoc]
    exact (d3Iso_right_involution_iff _ _ _ (commonChosenStageImageReflection_involution n)).trans
      (by simpa only [Iso.trans_assoc] using
        (commonChosenStageRefinedSource_reflected_structure_iff.{u} n))

end OmegaSpectrum.AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra
