module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedCosliceStageCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility

/-!
概要：元の weighted 全空間から元の通常の全空間余極限への比較は right cofinal。
方針：小さい coslice 図式を一段へ輸送し、後続段で余錐を作って Quillen A を適用する。
規約：元の比較射自体と元の全 coslice を扱う。使われ方：密度表示の二重余極限の比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [IsCardinalFiltered I κ]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C) [∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (F.obj i).val.left]

/-- 元の全比較の同じ coslice 引き戻しは、全 κ-small 図式について κ-filtered。 -/
instance weightedTotalCoslice_isKappaFiltered [IsFiltered I]
    (x : (colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTotalCoslice F x) where
  cocone_nonempty hK a := by
    let f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationTotalAssembly F
    let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)
    have : Quasicategory (pullback f p) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTotalCoslice_quasicategory F x
    obtain ⟨i, g, H, h₀, h₁, hH, _⟩ :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_weightedTotal_stageTransport F hK (a ≫ pullback.fst f p)
    have hw : (a ≫ pullback.fst f p) ≫ f = (a ≫ pullback.snd f p) ≫ p := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hH' : H ≫ f = (snd (Δ[1] : SSet.{u}) _ ≫ a ≫ pullback.snd f p) ≫ p :=
      hH.trans (by simpa only [Category.assoc] using congrArg (fun t => snd Δ[1] _ ≫ t) hw)
    let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pullbackFixedPrism f p a H hH'
    let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ P
    have hb : b ≫ pullback.fst f p = g ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i := by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ P) ≫ pullback.fst f p = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pullbackFixedPrism_fst, h₁]
    obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nonempty_weightedTotalCoslice_cocone_of_stage F x hK b i g hb
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nonempty_joinCocone_of_prism P (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pullbackFixedPrism_zero f p a H hH' h₀) rfl c

include κ in
/-- 元の weighted 全空間から元の通常の全空間余極限への比較射自体は right cofinal。 -/
lemma strictRightFibrationTotalAssembly_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationTotalAssembly F) := by
  have hκ : κ.IsRegular := Fact.out
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  have : Quasicategory (colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F)) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimitProjection F)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
  intro x
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTotalCoslice F x) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTotalCoslice F x)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTotalCoslice F x)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
