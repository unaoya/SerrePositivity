module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ParametrizedSectionRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransport

/-!
概要：一つの底をパラメータとし、もう一方の図式だけを変化させる切断の族の底。
方針：元の積上の図式を curry し、前合成との整合性を積の二射影で照合する。
規約：パラメータ側の底は全次数で保持する。
使われ方：under 圏上の切断を、元の底上の strict な fibration 図式へ束ねる。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の底をパラメータとし、指定図式をもう一方の成分とする族。 -/
def sectionFamilyProductBase {A D : SSet.{u}} (B : SSet.{u}) (a : A ⟶ D) :
    B ⟶ (ihom A).obj (B ⊗ D) := curry (lift (snd A B) (fst A B ≫ a))

/-- 同じ図式の族は、指定因子上の前合成と厳密に整合する。 -/
lemma sectionFamilyProductBase_pre {A A' D : SSet.{u}} (B : SSet.{u}) (a : A ⟶ D)
    (i : A' ⟶ A) :
    sectionFamilyProductBase B a ≫ (pre i).app (B ⊗ D) = sectionFamilyProductBase B (i ≫ a) := by
  apply uncurry_injective
  simp only [sectionFamilyProductBase, uncurry_pre_app, uncurry_curry]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, lift_fst, whiskerRight_snd]
  · rw [Category.assoc, lift_snd, lift_snd, ← Category.assoc, whiskerRight_fst, Category.assoc]

/-- 元の under 圏の射は、同じ底の族を厳密に保持する。 -/
lemma sectionFamilyProductBase_under {I : Type u} [Category.{u} I] (B : SSet.{u})
    {i j : I} (f : i ⟶ j) :
    sectionFamilyProductBase B (nerveMap (Under.forget i)) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f)).app (B ⊗ nerve I) =
        sectionFamilyProductBase B (nerveMap (Under.forget j)) := by
  rw [sectionFamilyProductBase_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
