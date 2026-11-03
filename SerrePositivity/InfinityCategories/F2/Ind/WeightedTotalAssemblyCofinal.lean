module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCosliceStageCocone
public import SerrePositivity.InfinityCategories.F1B.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.Stable.Filtered.FilteredWeakContractibility

/-!
概要：元の weighted 全空間から元の通常の全空間余極限への比較は right cofinal。
方針：小さい coslice 図式を一段へ輸送し、後続段で余錐を作って Quillen A を適用する。
規約：元の比較射自体と元の全 coslice を扱う。使われ方：密度表示の二重余極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]

/-- 元の全比較の同じ coslice 引き戻しは、全 κ-small 図式について κ-filtered。 -/
instance weightedTotalCoslice_isKappaFiltered [IsFiltered I]
    (x : (colimit (rightFibrationTotalDiagram F)) _⦋0⦌) :
    IsKappaFiltered κ (weightedTotalCoslice F x) where
  cocone_nonempty hK a := by
    let f := strictRightFibrationTotalAssembly F
    let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
    have : Quasicategory (pullback f p) := weightedTotalCoslice_quasicategory F x
    obtain ⟨i, g, H, h₀, h₁, hH, _⟩ :=
      exists_weightedTotal_stageTransport F hK (a ≫ pullback.fst f p)
    have hw : (a ≫ pullback.fst f p) ≫ f = (a ≫ pullback.snd f p) ≫ p := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hH' : H ≫ f = (snd (Δ[1] : SSet.{u}) _ ≫ a ≫ pullback.snd f p) ≫ p :=
      hH.trans (by simpa only [Category.assoc] using congrArg (fun t => snd Δ[1] _ ≫ t) hw)
    let P := pullbackFixedPrism f p a H hH'
    let b := prismEndpoint 1 _ ≫ P
    have hb : b ≫ pullback.fst f p = g ≫
        weightedNerveConstantLift (rightFibrationTotalDiagram F) i := by
      change (prismEndpoint 1 _ ≫ P) ≫ pullback.fst f p = _
      rw [Category.assoc, pullbackFixedPrism_fst, h₁]
    obtain ⟨c⟩ := nonempty_weightedTotalCoslice_cocone_of_stage F x hK b i g hb
    exact nonempty_joinCocone_of_prism P (pullbackFixedPrism_zero f p a H hH' h₀) rfl c

include κ in
/-- 元の weighted 全空間から元の通常の全空間余極限への比較射自体は right cofinal。 -/
lemma strictRightFibrationTotalAssembly_isRightCofinal :
    IsRightCofinal (strictRightFibrationTotalAssembly F) := by
  have hκ : κ.IsRegular := Fact.out
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  have : Quasicategory (colimit (rightFibrationTotalDiagram F)) :=
    quasicategory_of_innerFibration (strictRightFibrationColimitProjection F)
  apply isRightCofinal_of_weaklyContractible_coslices
  intro x
  have : IsFilteredInfinity (weightedTotalCoslice F x) :=
    isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le (weightedTotalCoslice F x)
  exact isWeaklyContractible_of_isFilteredInfinity (weightedTotalCoslice F x)

end SerrePositivity.InfinityCategories.F2.Ind
