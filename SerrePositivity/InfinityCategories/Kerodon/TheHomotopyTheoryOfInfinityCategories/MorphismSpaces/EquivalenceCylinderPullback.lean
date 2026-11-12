module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeEquivalenceCylinder

/-!
概要：可逆な円柱の端点の逆像。
方針：第一射影から持ち上げを作り、第二射影が定値であることを使う。
規約：底の単体集合の射に単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の自然な写像円柱への置換。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：可逆な円柱の端点を第二射影へ写すと定値射になる。
方針：各次数で直積の第二成分を計算する。
規約：両端に適用する。
使われ方：Kerodon §4.6.2（Tag 01HM） の端点の逆像。 -/
lemma equivalenceCylinderEndpoint_snd (A : SSet.{u}) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b ≫ snd A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval =
      SSet.const (nerveEquiv.symm (Codiscrete.mk (ULift.up b))) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：可逆な円柱の端点の自然性の正方形は pullback。
方針：第一射影から持ち上げを取る。
規約：射 i は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の可逆な写像円柱の比較。 -/
lemma isPullback_equivalenceCylinderEndpoint_naturality {A B : SSet.{u}}
    (i : A ⟶ B) (b : Bool) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b) i (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint B b) := by
  apply IsPullback.mk' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceCylinderEndpoint_naturality i b).symm
  · intro T f g h₁ h₂
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint_fst, Category.comp_id] using
      h₁ =≫ fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval
  · intro T f g h
    refine ⟨f ≫ fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval, ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint_fst, Category.comp_id]
      · have he := h =≫ snd B _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval
        simpa only [Category.assoc, whiskerRight_snd, equivalenceCylinderEndpoint_snd,
          SSet.comp_const] using he.symm
    · simpa only [Category.assoc, whiskerRight_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint_fst,
        Category.comp_id] using h =≫ fst B _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
