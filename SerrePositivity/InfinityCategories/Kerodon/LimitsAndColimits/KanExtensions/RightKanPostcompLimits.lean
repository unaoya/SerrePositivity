module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality

/-!
概要：指定右 Kan 変換の局所極限を保つ後合成は、同じ指定変換の右 Kan 条件を保つ。
方針：既存の局所輸送の後合成を用い、その終端の全錐の射を元の像錐と照合する。
規約：保存性は元の局所錐について明示する。対象ごとの値の一致を Kan 条件の代用にしない。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 5.1.5.6 の全 Hom 係数への後合成。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 同じ指定局所極限を保つ後合成は、その同じ余単位の右 Kan 条件を保つ。
Kerodon §7.3（Tag 02Y1）、既存の輸送の後合成と全錐の射の照合。 -/
lemma kanRightKanExtension_postcomp_of_localLimits {K C D E : SSet.{u}}
    (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (hα : IsRightKanExtension δ F₀ F α) (U : D ⟶ E)
    (hU : ∀ (v : C _⦋0⦌) (c : JoinCone (rightKanDiagram δ F₀ v)),
      IsLimitCone c → IsLimitCone (mapJoinCone U c)) :
    IsRightKanExtension δ (F₀ ≫ U) (F ≫ U) (kanRightCounitPostcomp α U) := by
  intro v
  obtain ⟨t, ht⟩ := hα v
  refine ⟨kanRightTransportPostcomp t U, ?_⟩
  exact (isLimitCone_iff_of_cone_val_eq (mapJoinCone U t.cone)
    (kanRightTransportPostcomp t U).cone (kanRightTransportPostcomp_cone_val t U).symm).mp
      (hU v t.cone ht)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
