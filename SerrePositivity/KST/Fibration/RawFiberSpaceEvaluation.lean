module
public import SerrePositivity.KST.Fibration.SpectrumSpaceEvaluation
public import SerrePositivity.KST.LocalizingInvariants.RawFiberInfinityCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits

/-! # 基点を忘れた同じ BF fiber 錐の、全 Kan Hom による極限性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

local instance rawSpaceSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance rawSpacePointedForgetAdjoint :
    PointedSimplicialSet.forget.{u}.IsRightAdjoint :=
  PointedObject.adjoinForgetAdjunction.isRightAdjoint

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) [hp : ∀ n, Fibration (p.app n).right]

/-- 元の実 BF fiber 錐を、同じ段で基点を忘れて評価した通常の錐。 -/
def rawFiberSpaceEvaluationCone (n : ℕ) :
    Cone (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (OmegaSpectrum.fromPoint Y) ⋙
      spectrumSpaceEvaluationOrdinary n) :=
  (spectrumSpaceEvaluationOrdinary n).mapCone (FiberModel.smallCone p)

/-- 元の段の極限錐は、同じ基点忘却後の台でも極限錐となる。 -/
def rawFiberSpaceEvaluationCone_forget_isLimit (n : ℕ) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (rawFiberSpaceEvaluationCone p n)) := by
  have hl := FiberModel.smallCone_level_isLimit p n
  have hm : IsLimit (PointedSimplicialSet.forget.mapCone
      ((_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor n).mapCone (FiberModel.smallCone p))) :=
    isLimitOfPreserves PointedSimplicialSet.forget hl
  have hc : IsLimit ((_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor n ⋙ PointedSimplicialSet.forget).mapCone
      (FiberModel.smallCone p)) :=
    IsLimit.ofIsoLimit hm (CategoryTheory.Functor.mapConeMapCone
      (H := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor n) (H' := PointedSimplicialSet.forget) (FiberModel.smallCone p))
  rw [← spectrumSpaceEvaluationOrdinary_forget] at hc
  exact IsLimit.ofIsoLimit hc (CategoryTheory.Functor.mapConeMapCone
    (H := spectrumSpaceEvaluationOrdinary n) (H' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (FiberModel.smallCone p)).symm

/-- 同じ元の錐は、空間の ∞ 圏で実極限錐となる。 -/
theorem rawFiberSpaceEvaluationCone_isLimit (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (rawFiberSpaceEvaluationCone p n)) := by
  have : ∀ Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
        (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (OmegaSpectrum.fromPoint Y) ⋙ spectrumSpaceEvaluationOrdinary n)
          Z).map (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z => by
    change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op Z)).map
      ((spectrumSpaceEvaluationOrdinary n).map p))
    have : Fibration (show ((spectrumSpaceEvaluationOrdinary n).obj X).obj ⟶
        ((spectrumSpaceEvaluationOrdinary n).obj Y).obj from
          (spectrumSpaceEvaluationOrdinary n).map p) := by
      rw [spectrumSpaceEvaluationOrdinary_map]
      exact hp n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHom_map_fibration Z _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (rawFiberSpaceEvaluationCone p n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ (rawFiberSpaceEvaluationCone_forget_isLimit p n))

end SerrePositivity.KST.Fibration
