module
public import SerrePositivity.InfinityCategories.Stable.CosliceLaxEquivalence
public import SerrePositivity.InfinityCategories.Stable.FatJoinRightTensorComparison

/-! # Coslice と固定図式上の余錐の族の同値

概要：直接定義した coslice と、固定図式上の余錐の関手圏は同値である。
方針：太い coslice への二つの比較を同定し、同値の二対三則を使う。
規約：図式を高次単体でも厳密に固定する。使われ方：余極限性と族の普遍性の接続。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coslice から余錐の族を経た太い coslice への比較は、直接の比較に一致する。
方針：fiber の包含後に uncurry し、二つの右直積比較の整合性を使う。
規約：quasicategory 性は不要。使われ方：比較同値の二対三則。 -/
lemma cosliceCoconeFamilyMap_comp_coconeFamilyLaxCosliceMap {K X : SSet.{u}} (p : K ⟶ X) :
    cosliceCoconeFamilyMap p ≫ coconeFamilyLaxCosliceMap p = cosliceLaxMap p := by
  let S := sliceUnder p
  apply vertexFiber_hom_ext ((pre (fatJoinInl K (Δ[0] : SSet.{u}))).app X) (functorVertex p)
  change curry (cosliceCoconeFamilyUncurry p) ≫
    (pre (fatJoinComparison K (Δ[0] : SSet.{u}))).app X =
    curry (laxCosliceCurryFamily (fatJoinComparison K S ≫ sliceUnderUncurry (𝟙 S)))
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry,
    cosliceCoconeFamilyUncurry, laxCosliceCurryFamily]
  rw [← Category.assoc (fatJoinComparison K (Δ[0] : SSet.{u}) ▷ S),
    ← stableFatJoinTensorRight_comparison]
  simp only [Category.assoc]
  rw [← Category.assoc (fatJoinComparison K ((Δ[0] : SSet.{u}) ⊗ S)),
    ← fatJoinComparison_naturality]
  rfl

/-- 概要：coslice と固定図式上の余錐の族の比較は quasicategory の同値。
方針：太い coslice への二つの比較の同値性と合成の同定を使う。
規約：値域は quasicategory、図式の形状は任意。使われ方：余極限の族の比較。 -/
lemma isQCatEquivalence_cosliceCoconeFamilyMap {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) : IsQCatEquivalence (cosliceCoconeFamilyMap p) := by
  apply (isQCatEquivalence_coconeFamilyLaxCosliceMap p).cancel_right
  rw [cosliceCoconeFamilyMap_comp_coconeFamilyLaxCosliceMap]
  exact isQCatEquivalence_cosliceLaxMap p

end SerrePositivity.InfinityCategories
