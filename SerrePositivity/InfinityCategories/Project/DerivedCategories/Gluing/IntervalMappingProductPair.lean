module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostIso
/-! # 二つの固定端点区間族を同じ積の区間族へ入れる

概要：固定した二端点を持つ二つの全区間族を、積の同じ固定端点区間族へ厳密にまとめる。
方針：全区間族を展開し、積の持ち上げを同じ端点で curry する。
規約：辺やパラメーターを選び直さず、両射影で元の全時間を回収する。
使われ方：pinched Hom 模型から区間 Hom 模型への比較で二入力を保つ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} (x₀ x₁ : X _⦋0⦌) (y₀ y₁ : Y _⦋0⦌)

def dgGluingIntervalProductUncurry :
    (Δ[1] : SSet.{u}) ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁ ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁) ⟶ X ⊗ Y :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁)))

lemma dgGluingIntervalProductUncurry_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ dgGluingIntervalProductUncurry x₀ x₁ y₀ y₁ =
      SSet.const (x₀, y₀) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [dgGluingIntervalProductUncurry, Category.assoc, lift_fst, lift_snd,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero, SSet.const_comp] <;> rfl

lemma dgGluingIntervalProductUncurry_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ dgGluingIntervalProductUncurry x₀ x₁ y₀ y₁ =
      SSet.const (x₁, y₁) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [dgGluingIntervalProductUncurry, Category.assoc, lift_fst, lift_snd,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, SSet.const_comp] <;> rfl

def dgGluingIntervalProductPair :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁ ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁ ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (X := X ⊗ Y) (x₀, y₀) (x₁, y₁) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (dgGluingIntervalProductUncurry x₀ x₁ y₀ y₁)
    (dgGluingIntervalProductUncurry_zero x₀ x₁ y₀ y₁)
    (dgGluingIntervalProductUncurry_one x₀ x₁ y₀ y₁)

lemma dgGluingIntervalProductPair_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingIntervalProductPair x₀ x₁ y₀ y₁) =
      dgGluingIntervalProductUncurry x₀ x₁ y₀ y₁ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _

lemma dgGluingIntervalProductPair_fst :
    dgGluingIntervalProductPair x₀ x₁ y₀ y₁ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost (fst X Y) (x₀, y₀) (x₁, y₁) =
    fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x₀ x₁
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost_uncurry, dgGluingIntervalProductPair_uncurry,
    dgGluingIntervalProductUncurry, lift_fst]

lemma dgGluingIntervalProductPair_snd :
    dgGluingIntervalProductPair x₀ x₁ y₀ y₁ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost (snd X Y) (x₀, y₀) (x₁, y₁) =
    snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective y₀ y₁
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost_uncurry, dgGluingIntervalProductPair_uncurry,
    dgGluingIntervalProductUncurry, lift_snd]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
