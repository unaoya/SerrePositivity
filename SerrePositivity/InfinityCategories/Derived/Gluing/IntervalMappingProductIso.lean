module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalMappingProductPair
/-!
概要：積の固定二端点区間族と二つの固定二端点区間族の積の厳密同型。
方針：同じ全区間族の二射影と積の持ち上げを curry・uncurry の単射性で比較する。
規約：二つの元の入力と全時間を保持する。
使われ方：正本 Hom 比較の pinched 標的から入力付き四座標標的へ移す。
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

def dgGluingIntervalProductSplit :
    intervalMappingSpace (X := X ⊗ Y) (x₀, y₀) (x₁, y₁) ⟶
      intervalMappingSpace x₀ x₁ ⊗ intervalMappingSpace y₀ y₁ :=
  lift (intervalMappingPost (fst X Y) (x₀, y₀) (x₁, y₁))
    (intervalMappingPost (snd X Y) (x₀, y₀) (x₁, y₁))

lemma dgGluingIntervalProductPair_split :
    dgGluingIntervalProductPair x₀ x₁ y₀ y₁ ≫ dgGluingIntervalProductSplit x₀ x₁ y₀ y₁ = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [dgGluingIntervalProductSplit, Category.assoc, lift_fst, lift_snd,
      dgGluingIntervalProductPair_fst, dgGluingIntervalProductPair_snd, Category.id_comp]

lemma dgGluingIntervalProductSplit_pair :
    dgGluingIntervalProductSplit x₀ x₁ y₀ y₁ ≫ dgGluingIntervalProductPair x₀ x₁ y₀ y₁ = 𝟙 _ := by
  apply intervalMappingUncurry_injective (X := X ⊗ Y)
    (A := intervalMappingSpace (X := X ⊗ Y) (x₀, y₀) (x₁, y₁)) (x₀, y₀) (x₁, y₁)
  rw [intervalMappingUncurry_precomp, dgGluingIntervalProductPair_uncurry]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, dgGluingIntervalProductUncurry, lift_fst,
      ← intervalMappingUncurry_precomp, dgGluingIntervalProductSplit, lift_fst,
      ← intervalMappingPost_uncurry, Category.id_comp]
  · rw [Category.assoc, dgGluingIntervalProductUncurry, lift_snd,
      ← intervalMappingUncurry_precomp, dgGluingIntervalProductSplit, lift_snd,
      ← intervalMappingPost_uncurry, Category.id_comp]

def dgGluingIntervalMappingProductIso :
    intervalMappingSpace x₀ x₁ ⊗ intervalMappingSpace y₀ y₁ ≅
      intervalMappingSpace (X := X ⊗ Y) (x₀, y₀) (x₁, y₁) where
  hom := dgGluingIntervalProductPair x₀ x₁ y₀ y₁
  inv := dgGluingIntervalProductSplit x₀ x₁ y₀ y₁
  hom_inv_id := dgGluingIntervalProductPair_split x₀ x₁ y₀ y₁
  inv_hom_id := dgGluingIntervalProductSplit_pair x₀ x₁ y₀ y₁
end SerrePositivity.InfinityCategories
