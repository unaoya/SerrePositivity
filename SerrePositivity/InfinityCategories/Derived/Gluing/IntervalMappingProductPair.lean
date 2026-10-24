module
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X Y : SSet.{u}} (x₀ x₁ : X _⦋0⦌) (y₀ y₁ : Y _⦋0⦌)

def dgGluingIntervalProductUncurry :
    (Δ[1] : SSet.{u}) ⊗ (intervalMappingSpace x₀ x₁ ⊗ intervalMappingSpace y₀ y₁) ⟶ X ⊗ Y :=
  lift (intervalMappingUncurry (fst (intervalMappingSpace x₀ x₁) (intervalMappingSpace y₀ y₁)))
    (intervalMappingUncurry (snd (intervalMappingSpace x₀ x₁) (intervalMappingSpace y₀ y₁)))

lemma dgGluingIntervalProductUncurry_zero :
    prismEndpoint 0 _ ≫ dgGluingIntervalProductUncurry x₀ x₁ y₀ y₁ =
      SSet.const (x₀, y₀) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [dgGluingIntervalProductUncurry, Category.assoc, lift_fst, lift_snd,
      intervalMappingUncurry_zero, SSet.const_comp] <;> rfl

lemma dgGluingIntervalProductUncurry_one :
    prismEndpoint 1 _ ≫ dgGluingIntervalProductUncurry x₀ x₁ y₀ y₁ =
      SSet.const (x₁, y₁) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [dgGluingIntervalProductUncurry, Category.assoc, lift_fst, lift_snd,
      intervalMappingUncurry_one, SSet.const_comp] <;> rfl

def dgGluingIntervalProductPair :
    intervalMappingSpace x₀ x₁ ⊗ intervalMappingSpace y₀ y₁ ⟶
      intervalMappingSpace (X := X ⊗ Y) (x₀, y₀) (x₁, y₁) :=
  intervalMappingCurryOfEndpoints (dgGluingIntervalProductUncurry x₀ x₁ y₀ y₁)
    (dgGluingIntervalProductUncurry_zero x₀ x₁ y₀ y₁)
    (dgGluingIntervalProductUncurry_one x₀ x₁ y₀ y₁)

lemma dgGluingIntervalProductPair_uncurry :
    intervalMappingUncurry (dgGluingIntervalProductPair x₀ x₁ y₀ y₁) =
      dgGluingIntervalProductUncurry x₀ x₁ y₀ y₁ :=
  intervalMappingUncurry_curryOfEndpoints _ _ _

lemma dgGluingIntervalProductPair_fst :
    dgGluingIntervalProductPair x₀ x₁ y₀ y₁ ≫
      intervalMappingPost (fst X Y) (x₀, y₀) (x₁, y₁) =
    fst (intervalMappingSpace x₀ x₁) (intervalMappingSpace y₀ y₁) := by
  apply intervalMappingUncurry_injective x₀ x₁
  rw [intervalMappingPost_uncurry, dgGluingIntervalProductPair_uncurry,
    dgGluingIntervalProductUncurry, lift_fst]

lemma dgGluingIntervalProductPair_snd :
    dgGluingIntervalProductPair x₀ x₁ y₀ y₁ ≫
      intervalMappingPost (snd X Y) (x₀, y₀) (x₁, y₁) =
    snd (intervalMappingSpace x₀ x₁) (intervalMappingSpace y₀ y₁) := by
  apply intervalMappingUncurry_injective y₀ y₁
  rw [intervalMappingPost_uncurry, dgGluingIntervalProductPair_uncurry,
    dgGluingIntervalProductUncurry, lift_snd]
end SerrePositivity.InfinityCategories
