module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightConeTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality

/-!
概要：通常の右 Kan の局所錐を任意の準圏値へ写し、元の指定輸送と比較する。
方針：構成済みの輸送の円柱へ同じ射を合成し、元の局所形状の同型で全錐を回収する。
使われ方：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の降下の局所右 Kan 条件。
規約：通常の係数圏での極限性や、係数射の極限保存性は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
variable {K C D : Type u} [SmallCategory K] [SmallCategory C] [SmallCategory D]
variable (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (α : L ⋙ F ⟶ F₀) (c : C)
variable {E : SSet.{u}}

/-- 同じ指定余単位の局所輸送を、係数の射へ後合成する。 -/
abbrev nerveRightConeTransportPostcomp (U : nerve D ⟶ E) :=
  kanRightTransportPostcomp (nerveRightConeTransport L α c) U

/-- 元の通常の局所形状へ制限すると、同じ指定局所錐を係数で写した全射になる。 -/
lemma nerveRightConeTransportPostcomp_cone_val (U : nerve D ⟶ E) :
    (restrictJoinCone (nerveRightConeTransportPostcomp L α c U).cone
      (nerveRightKanShapeIso c L).hom).val =
        ((nerveCone ((Functor.RightExtension.mk F α).coneAt c)).postcomp U).val := by
  change joinMap (𝟙 _) (nerveRightKanShapeIso c L).hom ≫
    (kanRightTransportPostcomp (nerveRightConeTransport L α c) U).cone.val = _
  rw [kanRightTransportPostcomp_cone_val, ← Category.assoc, nerveRightConeTransport_cone]
  rfl

/-- 任意の準圏値で、元の指定輸送の極限性は同じ局所錐の像の極限性と同値。 -/
lemma nerveRightConeTransportPostcomp_isLimit_iff [Quasicategory E]
    (U : nerve D ⟶ E) :
    IsLimitCone (nerveRightConeTransportPostcomp L α c U).cone ↔
      IsLimitCone ((nerveCone ((Functor.RightExtension.mk F α).coneAt c)).postcomp U) := by
  have he := (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (nerveRightKanShapeIso c L)).isQCatEquivalence
  exact (SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLimitCone_iff_restrict_equivalentShape
    (nerveRightKanShapeIso c L).hom he _).trans
      (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _
        (nerveRightConeTransportPostcomp_cone_val L α c U))

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
