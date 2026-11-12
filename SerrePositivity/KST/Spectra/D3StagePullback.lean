module

public import SerrePositivity.KST.Spectra.D3StageEvaluation
public import SerrePositivity.KST.Spectra.Limits.SpectrumHomFibrations
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StrictConeFunctorImage

/-!
概要：元の BF 引き戻し錐の全 coherent 段評価は、点つき Kan ∞ 圏の極限錐。
方針：上流の同じ段ごとの実極限性を、点つき Kan Hom の極限性へ移す。
規約：固定 K・局所化不変量に依存しない。一般 Sp 安定性も要求しない。
使われ方：d3b② の実 loop 錐の段極限性を、K-B3 が消費する Sp 側で供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3StagePullbackSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance d3StagePullbackPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- 同じ豊穣段評価の通常の作用。 -/
abbrev d3StageOrdinary (n : ℕ) : OmegaSpectrum.{u} ⥤ PointedKanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (d3StageKanEnriched n)

lemma d3StageOrdinary_map (n : ℕ) {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    (d3StageOrdinary n).map f = ObjectProperty.homMk (f.app n) := by
  change (eHomEquiv SSet).symm (eHomEquiv SSet f ≫ (d3StageKanEnriched n).map X Y) = _
  rw [d3Stage_vertex]
  exact Equiv.symm_apply_apply _ _

/-- Kan 性だけを忘れると同じ元の通常段評価である。 -/
lemma d3StageOrdinary_forget (n : ℕ) :
    d3StageOrdinary.{u} n ⋙ pointedKanProperty.ι = _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor n := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congrArg (fun g ↦ g.hom) (d3StageOrdinary_map n f)

/-- 同じ点つき Kan 豊穣 Hom の通常の後合成を、元の点つき Hom 関手に照合。 -/
lemma d3PointedKanHomFunctor (Z : PointedKanObject.{u}) :
    (SimplicialCategory.sHomFunctor PointedKanObject.{u}).obj (Opposite.op Z) =
      pointedKanProperty.ι ⋙ _root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change eHomWhiskerLeft SSet Z.obj f.hom = _
  exact PointedEnrichment.whiskerLeft_eq _ _

variable {E X B : OmegaSpectrum.{u}} (p : E ⟶ B) (q : X ⟶ B)
  [∀ k, Fibration (p.app k).right]

/-- 元の BF 引き戻し錐を同じ点つき Kan 段で評価した通常錐。 -/
def d3StagePullbackCone (n : ℕ) :
    Cone (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p q ⋙ d3StageOrdinary n) :=
  (d3StageOrdinary n).mapCone (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackCone p q)

/-- 元の段の実極限性から、同じ段錐の全 Kan 豊穣 Hom の極限性を得る。 -/
def d3StagePullbackCone_hom_isLimit (n : ℕ) (Z : PointedKanObject.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (d3StagePullbackCone p q n) Z) := by
  have hc : IsLimit (pointedKanProperty.ι.mapCone (d3StagePullbackCone p q n)) := by
    have h : IsLimit ((d3StageOrdinary n ⋙ pointedKanProperty.ι).mapCone
        (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackCone p q)) := by
      rw [d3StageOrdinary_forget]
      exact _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackCone_level_isLimit p q n
    exact IsLimit.ofIsoLimit h (CategoryTheory.Functor.mapConeMapCone
      (H := d3StageOrdinary n) (H' := pointedKanProperty.ι) (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackCone p q)).symm
  change IsLimit (((SimplicialCategory.sHomFunctor PointedKanObject.{u}).obj
    (Opposite.op Z)).mapCone (d3StagePullbackCone p q n))
  rw [d3PointedKanHomFunctor]
  have hm := isLimitOfPreserves (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj) hc
  exact IsLimit.ofIsoLimit hm (CategoryTheory.Functor.mapConeMapCone
    (H := pointedKanProperty.ι) (H' := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj) (d3StagePullbackCone p q n))

/-- 同じ元の BF 引き戻し錐の段評価は、実際の ∞ 極限錐。 -/
lemma d3StagePullbackCone_isLimit (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (d3StagePullbackCone p q n)) := by
  have h : ∀ Z : PointedKanObject.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p q ⋙ d3StageOrdinary n) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z ↦ by
    change Fibration (eHomWhiskerLeft SSet Z ((d3StageOrdinary n).map p))
    rw [d3StageOrdinary_map]
    change Fibration (eHomWhiskerLeft SSet Z.obj (p.app n))
    rw [PointedEnrichment.whiskerLeft_eq]
    exact PointedMapping.post_fibration Z.obj (p.app n)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (d3StagePullbackCone p q n)
    (d3StagePullbackCone_hom_isLimit p q n)

/-- 結論の錐は、元の全 coherent BF 錐を同じ実段関手で後合成した錐そのもの。 -/
lemma d3StagePullbackInfinityCone_isLimit (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone p q).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))) := by
  have h := d3StagePullbackCone_isLimit p q n
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (d3StageKanEnriched n)).mapCone
      (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackCone p q))) at h
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.strictCoherentCone_postcomp] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeCast_isLimit_iff _ _).mp h

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
