module

public import SerrePositivity.InfinityCategories.Core.SliceLaxEquivalence
public import SerrePositivity.InfinityCategories.Core.FatJoinTensorComparison

/-!
概要：slice と錐の関手単体集合の fiber の同値。
方針：太い slice への二つの比較を同定して二対三則を使う。
規約：既存の比較射 sliceConeFamilyMap をそのまま使う。
使われ方：Kerodon Example 4.6.6.8、Proposition 4.6.6.7。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：slice から錐の関手圏を経た太い slice への比較は対角比較に一致する。
方針：fiber の包含後に uncurry し、直積比較と fat join 比較の可換性を使う。
規約：quasicategory 性はこの等式には不要。
使われ方：Kerodon Example 4.6.6.8 の比較射の同定。 -/
lemma sliceConeFamilyMap_comp_coneFamilyLaxSliceMap {K X : SSet.{u}} (p : K ⟶ X) :
    sliceConeFamilyMap p ≫ coneFamilyLaxSliceMap p = sliceLaxMap p := by
  let S := sliceOver p
  apply vertexFiber_hom_ext ((pre (fatJoinInr (Δ[0] : SSet.{u}) K)).app X) (functorVertex p)
  change curry (sliceConeFamilyUncurry p) ≫
    (pre (fatJoinComparison (Δ[0] : SSet.{u}) K)).app X =
    curry (laxSliceCurryFamily (fatJoinComparison S K ≫ sliceOverUncurry (𝟙 S)))
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
  have hs : (fatJoinComparison (Δ[0] : SSet.{u}) K ▷ S) ≫
      (β_ (join (Δ[0] : SSet.{u}) K) S).hom =
        (β_ (fatJoin (Δ[0] : SSet.{u}) K) S).hom ≫ (S ◁ fatJoinComparison Δ[0] K) := rfl
  rw [sliceConeFamilyUncurry, laxSliceCurryFamily,
    ← Category.assoc (fatJoinComparison (Δ[0] : SSet.{u}) K ▷ S), hs]
  simp only [Category.assoc]
  rw [← Category.assoc (S ◁ fatJoinComparison Δ[0] K), ← fatJoinTensorLeft_comparison]
  simp only [Category.assoc]
  rw [← Category.assoc (fatJoinComparison (S ⊗ (Δ[0] : SSet.{u})) K),
    ← fatJoinComparison_naturality]
  simp only [Category.assoc]
  rfl

/-- 概要：slice と固定図式上の錐の関手圏の fiber の比較は同値。
方針：太い slice への二つの比較の同値性と合成の同定から二対三則を使う。
規約：X は quasicategory、添字 K は任意。
使われ方：Kerodon Example 4.6.6.8 と Proposition 4.6.6.7 の錐の模型の比較。 -/
lemma isQCatEquivalence_sliceConeFamilyMap {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) : IsQCatEquivalence (sliceConeFamilyMap p) := by
  apply (isQCatEquivalence_coneFamilyLaxSliceMap p).cancel_right
  rw [sliceConeFamilyMap_comp_coneFamilyLaxSliceMap]
  exact isQCatEquivalence_sliceLaxMap p

end SerrePositivity.InfinityCategories
