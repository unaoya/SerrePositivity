module
public import SerrePositivity.KST.Fibration.SpectrumKanEvaluationOrdinary
public import SerrePositivity.KST.LocalizingInvariants.RawFiberInfinityCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits

/-! # 元の段ごとの fiber 錐の、点つき Kan 複体の ∞ 圏での極限性 -/

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

local instance rawEvaluationSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance rawEvaluationPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- Kan 全部分圏の元の Hom 後合成は、同じ点つき写像空間の後合成。 -/
theorem pointedKan_whiskerLeft (Z : PointedKanObject.{u}) {V W : PointedKanObject.{u}}
    (f : V ⟶ W) : eHomWhiskerLeft SSet Z f =
      (PointedObject.basedHomMap Z.obj f.hom).right := by
  change eHomWhiskerLeft SSet Z.obj f.hom = _
  exact PointedEnrichment.whiskerLeft_eq Z.obj f.hom

/-- 元の Kan Hom 関手は、同じ点つき写像空間の通常の関手である。 -/
theorem pointedKanHomFunctor_eq (Z : PointedKanObject.{u}) :
    (SimplicialCategory.sHomFunctor PointedKanObject.{u}).obj (Opposite.op Z) =
      pointedKanProperty.ι ⋙ _root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro V W f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact pointedKan_whiskerLeft Z f

/-- 元の点つき錐の極限性は、同じ Kan 全部分圏の全豊穣 Hom の極限性を与える。 -/
def pointedKanHomCone_isLimit {I : Type u} [SmallCategory I]
    {F : I ⥤ PointedKanObject.{u}} (c : Cone F)
    (hc : IsLimit (pointedKanProperty.ι.mapCone c)) (Z : PointedKanObject.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c Z) := by
  change IsLimit (((SimplicialCategory.sHomFunctor PointedKanObject.{u}).obj
    (Opposite.op Z)).mapCone c)
  rw [pointedKanHomFunctor_eq]
  have : PreservesLimits (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj) :=
    _root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor_preservesLimits Z.obj
  have hm : IsLimit ((_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj).mapCone
      (pointedKanProperty.ι.mapCone c)) :=
    isLimitOfPreserves (K := F ⋙ pointedKanProperty.ι) (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj) hc
  exact IsLimit.ofIsoLimit hm
    (CategoryTheory.Functor.mapConeMapCone
      (H := pointedKanProperty.ι) (H' := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj) c)

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
  [hp : ∀ n, Fibration (p.app n).right]

/-- 元の実 fiber 錐を、同じ Kan な段で評価した通常の錐。 -/
def rawFiberKanEvaluationCone (n : ℕ) :
    Cone (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (OmegaSpectrum.fromPoint Y) ⋙
      spectrumKanEvaluationOrdinary n) :=
  (spectrumKanEvaluationOrdinary n).mapCone (FiberModel.smallCone p)

/-- 元の段ごとの普遍性を、同じ点つき Kan 錐の各 Hom の普遍性へ移す。 -/
def rawFiberKanEvaluationCone_hom_isLimit (n : ℕ) (Z : PointedKanObject.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (rawFiberKanEvaluationCone p n) Z) := by
  apply pointedKanHomCone_isLimit
  have h : IsLimit ((spectrumKanEvaluationOrdinary n ⋙ pointedKanProperty.ι).mapCone
      (FiberModel.smallCone p)) := by
    rw [spectrumKanEvaluationOrdinary_forget]
    exact FiberModel.smallCone_level_isLimit p n
  exact IsLimit.ofIsoLimit h (CategoryTheory.Functor.mapConeMapCone
    (H := spectrumKanEvaluationOrdinary n) (H' := pointedKanProperty.ι)
      (FiberModel.smallCone p)).symm

/-- 同じ元の fiber 錐の各段は、点つき Kan 複体の ∞ 圏で実極限錐となる。 -/
theorem rawFiberKanEvaluationCone_isLimit (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (rawFiberKanEvaluationCone p n)) := by
  have : ∀ Z : PointedKanObject.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
        (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (OmegaSpectrum.fromPoint Y) ⋙ spectrumKanEvaluationOrdinary n)
          Z).map (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z => by
    change Fibration (eHomWhiskerLeft SSet Z ((spectrumKanEvaluationOrdinary n).map p))
    rw [pointedKan_whiskerLeft, spectrumKanEvaluationOrdinary_map]
    exact PointedMapping.post_fibration Z.obj (p.app n)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (rawFiberKanEvaluationCone p n)
    (rawFiberKanEvaluationCone_hom_isLimit p n)

end SerrePositivity.KST.Fibration
