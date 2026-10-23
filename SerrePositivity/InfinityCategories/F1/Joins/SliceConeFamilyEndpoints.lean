module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeFamilyApex

/-!
概要：元の slice から native な錐の内部 Hom 表示へ移す普遍族の左端を公開する。
方針：直積と join の比較の左端で、元の可変頂点への射影を計算する。
規約：元の比較・全パラメータを保持し、充填性を要求しない。
使われ方：元の right Hom 輸送で頂点が動く錐の円柱。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の錐の普遍族の左端は、元の可変頂点への射影そのもの。 -/
lemma sliceConeFamilyUncurry_inl {K X : SSet.{u}} (p : K ⟶ X) :
    (joinInl (Δ[0] : SSet.{u}) K ▷ sliceOver p) ≫ sliceConeFamilyUncurry p =
      snd (Δ[0] : SSet.{u}) (sliceOver p) ≫ sliceOverProjection p := by
  let S := sliceOver p
  have hswap : (joinInl (Δ[0] : SSet.{u}) K ▷ S) ≫
      (β_ (join (Δ[0] : SSet.{u}) K) S).hom =
      (β_ (Δ[0] : SSet.{u}) S).hom ≫ (S ◁ joinInl Δ[0] K) := rfl
  change (joinInl (Δ[0] : SSet.{u}) K ▷ S) ≫
    (β_ (join (Δ[0] : SSet.{u}) K) S).hom ≫ joinTensorLeft S Δ[0] K ≫
      joinMap (fst S Δ[0]) (𝟙 K) ≫ sliceOverUncurry (𝟙 S) = _
  rw [← Category.assoc (joinInl (Δ[0] : SSet.{u}) K ▷ S), hswap]
  simp only [Category.assoc]
  rw [← Category.assoc (S ◁ joinInl (Δ[0] : SSet.{u}) K), joinTensorLeft_inl]
  rw [← Category.assoc (joinInl (S ⊗ Δ[0]) K), joinInl_joinMap]
  simp only [Category.assoc]
  rw [sliceOverUncurry_projection, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories
