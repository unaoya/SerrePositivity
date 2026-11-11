module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalConeRestriction
/-!
概要：left cofinal な任意形状写像に沿う、指定錐の極限性と極限の存在の同値を記録する。
方針：錐圏の実同値による終対象性の保存・反映を使う。
規約：頂点は元の錐の同じ頂点を保持する。使われ方：実分母図式での右 Kan 錐の検査。

対応節は Kerodon 7.2（Tag 02MZ）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open CategoryTheory SSet
/-- 任意 left cofinal な形状写像は、指定錐の極限性を保存し反映する。 -/
lemma isLimitCone_iff_restrict_of_leftCofinal {A B X : SSet.{u}}
    [Quasicategory B] [Quasicategory X] (u : A ⟶ B) (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal u)
    (F : B ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceOverRestrict_isQCatEquivalence_of_leftCofinal u hu F).choose.isTerminalVertex_iff c
/-- 任意 left cofinal な形状写像への制限は、極限の存在を保存し反映する。 -/
lemma hasLimit_iff_restrict_of_leftCofinal {A B X : SSet.{u}}
    [Quasicategory B] [Quasicategory X] (u : A ⟶ B) (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal u) (F : B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (u ≫ F) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c u, (isLimitCone_iff_restrict_of_leftCofinal u hu F c).mp hc⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_of_leftCofinal u hu F
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
