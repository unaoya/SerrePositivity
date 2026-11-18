module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightConstantFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomUniversal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality

/-!
概要：指定余単位を保つ右 Kan 延長を任意の定値パラメータ族へ移す。
方針：元の全局所輸送を後合成し、定値族が同じ極限錐を保つことを使う。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の降下の合成での全写像空間の普遍性。
規約：パラメータに準圏性や有限性を課さず、指定した変換の代表を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 指定右 Kan 変換の同じ局所輸送は、任意の定値パラメータ族でも極限錐となる。 -/
lemma IsRightKanExtension.constantFamily {A K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (hα : IsRightKanExtension δ F₀ F α) :
    IsRightKanExtension δ (F₀ ≫ constantFunctorMap A D) (F ≫ constantFunctorMap A D)
      (kanRightCounitPostcomp α (constantFunctorMap A D)) := by
  intro c
  obtain ⟨t, ht⟩ := hα c
  refine ⟨kanRightTransportPostcomp t (constantFunctorMap A D), ?_⟩
  exact (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _
    (kanRightTransportPostcomp_cone_val t (constantFunctorMap A D))).mpr
      (kanIsLimitCone_constantFamily t.cone ht)

/-- 任意の追加パラメータの族でも、元の指定余単位の Hom 対応は全単射である。 -/
lemma kanRightKanExtension_constantFamily_homUniversal {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (hα : IsRightKanExtension δ F₀ F α)
    (A : SSet.{u}) :
    RightKanHomUniversal δ (SSet.Truncated.HomotopyCategory.homMk
      (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (kanRightCounitPostcomp α (constantFunctorMap A D)))) :=
  kanRightKanExtension_homUniversal δ _ (hα.constantFamily (A := A))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
