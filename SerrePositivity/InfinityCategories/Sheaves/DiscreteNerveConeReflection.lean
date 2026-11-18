module

public import SerrePositivity.InfinityCategories.Sheaves.CechShapeCofinality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.SmallNerveDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AsSmallCoefficientCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BNerveComparisonLimit
public import Mathlib.CategoryTheory.Limits.Final

/-!
概要：集合値係数に送った元の小さい通常錐の極限性を、同じ nerve の全錐から回収する。
方針：対象と射の宇宙を AsSmall でそろえ、既存の通常極限比較と反映を使う。
規約：HTT 1.2.13.4 の通常圏の場合の宇宙表示の法則。係数の宇宙は変えない。
使われ方：離散層条件の逆向きの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 元の全錐の nerve の極限性から、係数で送った同じ通常錐の極限性を回収する。 -/
lemma smallNerveDiagram_reflects_limit {I C : Type u} [SmallCategory I] [SmallCategory C]
    {F : I ⥤ C} (c : Cone F) (P : C ⥤ Type u)
    (hc : IsLimitCone (((nerveCone c).ulift).postcomp (smallNerveDiagram P))) :
    Nonempty (IsLimit (P.mapCone c)) := by
  let H : AsSmall.{u + 1} C ⥤ AsSmall.{u + 1} (Type u) :=
    AsSmall.down ⋙ P ⋙ AsSmall.up
  let e := nerveAsSmallMaxIso (Type u)
  have hl := (isLimitCone_asSmallCoefficient_iff c (smallNerveDiagram P)).mpr hc
  have he := hl.postcomp_of_isIso e.hom
  have hv :
      ((mapJoinCone ((nerveAsSmallIso C).inv ≫ smallNerveDiagram P)
        (nerveCone (asSmallCone c))).postcomp e.hom).val =
      (nerveCone (H.mapCone (asSmallCone c))).val := by
    rw [← nerveCone_mapCone]
    rfl
  have hn := (isLimitCone_iff_of_cone_val_eq _ _ hv).mp he
  obtain ⟨hh⟩ := (nerveCone_isLimit_iff _).mp hn
  letI : (AsSmall.up : Type u ⥤ AsSmall.{u + 1} (Type u)).IsEquivalence :=
    (AsSmall.equiv (C := Type u)).isEquivalence_functor
  letI : (AsSmall.down : AsSmall.{u + 1} I ⥤ I).IsEquivalence :=
    (AsSmall.equiv (C := I)).isEquivalence_inverse
  have hw : IsLimit ((P.mapCone c).whisker
      (AsSmall.down : AsSmall.{u + 1} I ⥤ I)) :=
    isLimitOfReflects (AsSmall.up : Type u ⥤ AsSmall.{u + 1} (Type u)) hh
  exact ⟨Functor.Initial.isLimitWhiskerEquiv AsSmall.down _ hw⟩

end SerrePositivity.InfinityCategories.Sheaves
