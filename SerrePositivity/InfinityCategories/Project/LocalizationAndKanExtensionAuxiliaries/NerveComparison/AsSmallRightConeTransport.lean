module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.AsSmallStructuredArrow
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightConeTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AsSmallCoefficientCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence

/-!
概要：既存の指定右 Kan 局所錐の輸送を AsSmall に沿って比較する。
方針：通常の comma の既存同値と、元の指定全錐の宇宙移送則を合成する。
規約：HTT 4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の法則。
使われ方：S8 の局所被覆篩の降下を、同じ係数の指定右 Kan 条件へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
variable {I J D : Type u} [SmallCategory I] [SmallCategory J] [SmallCategory D]
variable (L : I ⥤ J) {F₀ : I ⥤ D} {F : J ⥤ D} (α : L ⋙ F ⟶ F₀)

/-- 元の指定余単位を既存の二つの宇宙移送関手で包んだ自然変換。 -/
abbrev asSmallRightCounit :
    asSmallLocalFunctor L ⋙ asSmallLocalFunctor F ⟶ asSmallLocalFunctor F₀ :=
  Functor.whiskerLeft AsSmall.down (Functor.whiskerRight α AsSmall.up)

/-- 同じ指定余単位の通常の局所全錐は、comma の既存比較で厳密に戻る。 -/
lemma asSmallRightCounit_cone (j : J) :
    ((Functor.RightExtension.mk (asSmallLocalFunctor F) (asSmallRightCounit L α)).coneAt
      (AsSmall.up.obj j)).whisker (asSmallStructuredArrowFunctor L j) =
        asSmallCone ((Functor.RightExtension.mk F α).coneAt j) := rfl

/-- 宇宙表示を包んだ指定局所輸送の極限性は、元の同じ全錐の極限性と同値。 -/
lemma asSmallRightConeTransportPostcomp_isLimit_iff
    {E : SSet.{u + 1}} [Quasicategory E] (j : J)
    (U : (SSet.uliftFunctor.{u + 1, u}).obj (nerve D) ⟶ E) :
    IsLimitCone (nerveRightConeTransportPostcomp (asSmallLocalFunctor L)
      (asSmallRightCounit L α) (AsSmall.up.obj j) ((nerveAsSmallIso D).inv ≫ U)).cone ↔
      IsLimitCone (((nerveCone ((Functor.RightExtension.mk F α).coneAt j)).ulift).postcomp U) := by
  let c := (Functor.RightExtension.mk (asSmallLocalFunctor F)
    (asSmallRightCounit L α)).coneAt (AsSmall.up.obj j)
  let A := asSmallStructuredArrowFunctor L j
  let V := (nerveAsSmallIso D).inv ≫ U
  have he := (nerveQCatEquivalence A.asEquivalence).isQCatEquivalence
  have hv : (restrictJoinCone ((nerveCone c).postcomp V) (nerveMap A)).val =
      ((nerveCone (asSmallCone ((Functor.RightExtension.mk F α).coneAt j))).postcomp V).val := by
    change joinMap (𝟙 _) (nerveMap A) ≫ ((nerveCone c).val ≫ V) = _
    rw [← Category.assoc, nerveCone_whisker]
    rw [asSmallRightCounit_cone]
    rfl
  exact (nerveRightConeTransportPostcomp_isLimit_iff (asSmallLocalFunctor L)
    (asSmallRightCounit L α) (AsSmall.up.obj j) V).trans
      (((isLimitCone_iff_restrict_equivalentShape (nerveMap A) he _).trans
        (isLimitCone_iff_of_cone_val_eq _ _ hv)).trans
          (isLimitCone_asSmallCoefficient_iff ((Functor.RightExtension.mk F α).coneAt j) U))

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
